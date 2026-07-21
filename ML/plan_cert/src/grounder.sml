(* Unverified SML grounder (interim; self-contained in this repo, independent of the
   verified Temporal_Grounding effort).

   The verified reduction accepts a GROUND temporal problem in this fragment:
     - 0-parameter action schemas, 0-ary predicate atoms (objects inlined into the NAME,
       e.g. (light ?m) at match0 -> (light_match0));
     - NO domain constants / objects (so any ground (in)equality (= o1 o2) must be folded
       away, not left as an object-typed atom);
     - preconditions that are conjunctions of POSITIVE literals -- so numeric preconditions
       (>=, <=, ...) are NOT allowed and must be relaxed;
     - numeric EFFECTS and numeric DURATION constraints ARE allowed and are kept.

   So this grounder does the TFD-style delete-relaxation of numeric PRECONDITIONS while
   KEEPING numeric effects (cf. David's recipe):
     (1) instantiate each lifted temporal action schema over the objects (type-consistent,
         honouring subtypes) and substitute the parameters;
     (2) constant-fold ground (in)equalities (= o1 o2) by object identity -- dropping a
         satisfied literal, or the whole action instance when a precondition literal is
         statically false;
     (3) relax every numeric PRECONDITION atom to positive definedness predicates
         def_<fluent>(args) (one per fluent mentioned -- threading not-None definedness),
         and ADD def_<fluent>(args) for every fluent ASSIGNED by a numeric effect (and every
         numeric init assignment); the numeric EFFECTS themselves are kept;
     (4) propositionalise every predicate atom AND every numeric function-application, inlining
         objects into the name; redeclare the resulting 0-ary predicates + functions; empty the
         objects/constants.

   UNVERIFIED and (for now) a full cross-product instantiation with no reachability pruning --
   task #22b replaces that with datalog reachability via nemo. *)

structure Grounder =
struct

  structure C = Converter

  (* ---------- type hierarchy ---------- *)
  fun supertypes types t0 =
    let
      fun step acc [] = acc
        | step acc (x :: xs) =
            let val ups = List.mapPartial
                  (fn (sub, sup) => if sub = x andalso not (List.exists (fn y => y = sup) acc)
                                    then SOME sup else NONE) types
            in step (acc @ ups) (xs @ ups) end
    in step [t0] [t0] end

  fun type_fits types onames (C.Either pnames) =
    List.exists (fn on =>
      let val sups = supertypes types on
      in List.exists (fn pn => List.exists (fn s => s = pn) sups) pnames end) onames

  fun candidates types objs_typed pty =
    List.mapPartial
      (fn (ob, C.Either onames) => if type_fits types onames pty then SOME ob else NONE)
      objs_typed

  fun cartesian [] = [[]]
    | cartesian (xs :: rest) =
        List.concat (map (fn x => map (fn tl => x :: tl) (cartesian rest)) xs)

  (* ---------- parameter substitution (variable-name -> object) ---------- *)
  fun subst_term sigma (C.VAR (C.Vara v)) =
        (case sigma v of SOME ob => C.CONST ob | NONE => C.VAR (C.Vara v))
    | subst_term _ t = t
  fun subst_atom sigma a = C.map_atom (subst_term sigma) a
  fun subst_form sigma (C.Atom a)     = C.Atom (subst_atom sigma a)
    | subst_form _     C.Bot          = C.Bot
    | subst_form sigma (C.Not f)      = C.Not (subst_form sigma f)
    | subst_form sigma (C.And (f, g)) = C.And (subst_form sigma f, subst_form sigma g)
    | subst_form sigma (C.Or (f, g))  = C.Or (subst_form sigma f, subst_form sigma g)
    | subst_form sigma (C.Imp (f, g)) = C.Imp (subst_form sigma f, subst_form sigma g)
  fun subst_pne sigma (C.PNE (f, args)) = C.PNE (f, map (subst_term sigma) args)
  fun subst_nexp sigma e =
    (case e of
        C.ConstantExpr r  => C.ConstantExpr r
      | C.DurationExpr    => C.DurationExpr
      | C.PiExpr          => C.PiExpr
      | C.FunctionExpr p  => C.FunctionExpr (subst_pne sigma p)
      | C.AddExpr (a, b)  => C.AddExpr (subst_nexp sigma a, subst_nexp sigma b)
      | C.SubExpr (a, b)  => C.SubExpr (subst_nexp sigma a, subst_nexp sigma b)
      | C.MulExpr (a, b)  => C.MulExpr (subst_nexp sigma a, subst_nexp sigma b)
      | C.DivExpr (a, b)  => C.DivExpr (subst_nexp sigma a, subst_nexp sigma b)
      | C.SinExpr a       => C.SinExpr (subst_nexp sigma a)
      | C.CosExpr a       => C.CosExpr (subst_nexp sigma a)
      | C.ExpExpr a       => C.ExpExpr (subst_nexp sigma a))
  fun subst_neff sigma (C.NumericEffect (op_, C.PNE (f, args), e)) =
        C.NumericEffect (op_, C.PNE (f, map (subst_term sigma) args), subst_nexp sigma e)
  fun subst_eff sigma (C.Effect (adds, dels, neffs)) =
        C.Effect (map (subst_form sigma) adds, map (subst_form sigma) dels,
                  map (subst_neff sigma) neffs)
  fun subst_dc sigma (C.DurationConstraint (dop, e)) =
        C.DurationConstraint (dop, subst_nexp sigma e)

  fun sigma_of params objs =
    let val binds = ListPair.zip (map (fn (C.Vara v, _) => v) params, objs)
    in fn v => Option.map #2 (List.find (fn (v', _) => v' = v) binds) end

  (* ---------- propositionalisation: object inlined into predicate / function NAMES ---------- *)
  fun mangle p names = foldl (fn (nm, acc) => acc ^ "_" ^ nm) p names
  fun term_name (C.CONST (C.Obj o_)) = o_
    | term_name (C.VAR (C.Vara v))   = v   (* not expected post-grounding *)
  fun obj_name (C.Obj o_) = o_

  fun mangle_pne name_of (C.PNE (C.Func f, args)) = C.PNE (C.Func (mangle f (map name_of args)), [])
  fun mangle_nexp name_of e =
    (case e of
        C.FunctionExpr p  => C.FunctionExpr (mangle_pne name_of p)
      | C.AddExpr (a, b)  => C.AddExpr (mangle_nexp name_of a, mangle_nexp name_of b)
      | C.SubExpr (a, b)  => C.SubExpr (mangle_nexp name_of a, mangle_nexp name_of b)
      | C.MulExpr (a, b)  => C.MulExpr (mangle_nexp name_of a, mangle_nexp name_of b)
      | C.DivExpr (a, b)  => C.DivExpr (mangle_nexp name_of a, mangle_nexp name_of b)
      | C.SinExpr a       => C.SinExpr (mangle_nexp name_of a)
      | C.CosExpr a       => C.CosExpr (mangle_nexp name_of a)
      | C.ExpExpr a       => C.ExpExpr (mangle_nexp name_of a)
      | C.ConstantExpr r  => C.ConstantExpr r
      | C.DurationExpr    => C.DurationExpr
      | C.PiExpr          => C.PiExpr)
  (* only PredAtm survives to be mangled in the relaxed output (numeric atoms are relaxed away);
     mangle keeps any residual atom's numeric func-apps 0-ary defensively *)
  fun mangle_atom name_of a =
    (case a of
        C.PredAtm (C.Pred p, args)  => C.PredAtm (C.Pred (mangle p (map name_of args)), [])
      | C.NumericEqAtm (x, y)       => C.NumericEqAtm (mangle_nexp name_of x, mangle_nexp name_of y)
      | C.NumericLessAtm (x, y)     => C.NumericLessAtm (mangle_nexp name_of x, mangle_nexp name_of y)
      | C.NumericLEAtm (x, y)       => C.NumericLEAtm (mangle_nexp name_of x, mangle_nexp name_of y)
      | C.NumericGreaterAtm (x, y)  => C.NumericGreaterAtm (mangle_nexp name_of x, mangle_nexp name_of y)
      | C.NumericGEAtm (x, y)       => C.NumericGEAtm (mangle_nexp name_of x, mangle_nexp name_of y)
      | other                       => other)
  fun mangle_neff name_of (C.NumericEffect (op_, pne, e)) =
        C.NumericEffect (op_, mangle_pne name_of pne, mangle_nexp name_of e)

  fun map_form g (C.Atom a)     = C.Atom (g a)
    | map_form _ C.Bot          = C.Bot
    | map_form g (C.Not f)      = C.Not (map_form g f)
    | map_form g (C.And (f, h)) = C.And (map_form g f, map_form g h)
    | map_form g (C.Or (f, h))  = C.Or (map_form g f, map_form g h)
    | map_form g (C.Imp (f, h)) = C.Imp (map_form g f, map_form g h)

  (* ---------- numeric-precondition relaxation + (in)equality folding ---------- *)
  val fTrue = C.Not C.Bot
  fun conj [] = fTrue
    | conj [f] = f
    | conj (f :: fs) = C.And (f, conj fs)
  (* a fluent (f args) -> its positive definedness proposition def_f(args) (args mangled later) *)
  fun def_atom (C.PNE (C.Func f, args)) = C.Atom (C.PredAtm (C.Pred ("def_" ^ f), args))
  fun pnes_of_nexp acc e =
    (case e of
        C.FunctionExpr p  => p :: acc
      | C.AddExpr (a, b)  => pnes_of_nexp (pnes_of_nexp acc a) b
      | C.SubExpr (a, b)  => pnes_of_nexp (pnes_of_nexp acc a) b
      | C.MulExpr (a, b)  => pnes_of_nexp (pnes_of_nexp acc a) b
      | C.DivExpr (a, b)  => pnes_of_nexp (pnes_of_nexp acc a) b
      | C.SinExpr a       => pnes_of_nexp acc a
      | C.CosExpr a       => pnes_of_nexp acc a
      | C.ExpExpr a       => pnes_of_nexp acc a
      | _                 => acc)
  fun def_conj xs ys = conj (map def_atom (pnes_of_nexp (pnes_of_nexp [] xs) ys))
  fun eq_names (C.CONST (C.Obj a), C.CONST (C.Obj b)) = SOME (a = b)  (* term-level (actions) *)
    | eq_names _ = NONE

  (* relax a GROUND precondition/condition formula: keep PredAtm; fold (in)equalities;
     numeric comparison -> conjunction of definedness props; simplify away True/False. *)
  fun relax_pre (C.Atom (C.PredAtm p)) = C.Atom (C.PredAtm p)
    | relax_pre (C.Atom (C.EqAtm (a, b))) =
        (case eq_names (a, b) of SOME true => fTrue | SOME false => C.Bot
                               | NONE => C.Atom (C.EqAtm (a, b)))
    | relax_pre (C.Atom (C.NumericEqAtm (x, y)))      = def_conj x y
    | relax_pre (C.Atom (C.NumericLessAtm (x, y)))    = def_conj x y
    | relax_pre (C.Atom (C.NumericLEAtm (x, y)))      = def_conj x y
    | relax_pre (C.Atom (C.NumericGreaterAtm (x, y))) = def_conj x y
    | relax_pre (C.Atom (C.NumericGEAtm (x, y)))      = def_conj x y
    | relax_pre C.Bot = C.Bot
    | relax_pre (C.Not f) =
        (case relax_pre f of C.Bot => fTrue | C.Not C.Bot => C.Bot | f' => C.Not f')
    | relax_pre (C.And (f, g)) =
        (case (relax_pre f, relax_pre g) of
            (C.Bot, _) => C.Bot | (_, C.Bot) => C.Bot
          | (C.Not C.Bot, g') => g' | (f', C.Not C.Bot) => f'
          | (f', g') => C.And (f', g'))
    | relax_pre (C.Or (f, g)) =
        (case (relax_pre f, relax_pre g) of
            (C.Not C.Bot, _) => fTrue | (_, C.Not C.Bot) => fTrue
          | (C.Bot, g') => g' | (f', C.Bot) => f' | (f', g') => C.Or (f', g'))
    | relax_pre (C.Imp (f, g)) =
        (case (relax_pre f, relax_pre g) of
            (C.Bot, _) => fTrue | (_, C.Not C.Bot) => fTrue
          | (C.Not C.Bot, g') => g' | (f', g') => C.Imp (f', g'))
  fun isBot C.Bot = true | isBot _ = false

  (* relax an effect: keep adds/dels; DROP the numeric effects (the reduction's network entry is
     fully propositional -- no functions), but record definedness by ADDing def_<fluent>(args)
     for every fluent assigned by a numeric effect. *)
  fun relax_eff (C.Effect (adds, dels, neffs)) =
        let val def_adds = map (fn (C.NumericEffect (_, pne, _)) => def_atom pne) neffs
        in C.Effect (adds @ def_adds, dels, []) end

  (* term-level (in actions) and object-level (in init/goal) propositionalisers *)
  val prop_term_atom = mangle_atom term_name
  val prop_obj_atom  = mangle_atom obj_name
  fun prop_eff (C.Effect (adds, dels, neffs)) =
        C.Effect (map (map_form prop_term_atom) adds, map (map_form prop_term_atom) dels,
                  map (mangle_neff term_name) neffs)
  fun prop_dc (C.DurationConstraint (dop, e)) = C.DurationConstraint (dop, mangle_nexp term_name e)

  (* ---------- ground one schema (instantiate + substitute + relax + propositionalise) ---------- *)
  fun ground_name base objs = foldl (fn (C.Obj o_, acc) => acc ^ "_" ^ o_) base objs

  fun ground_schema types objs_typed sch =
    let
      val (name, params, mk) =
        (case sch of
            C.SimpleActionSchemaa (C.ActionHead (n, ps), C.SimpleActionBody (pre, eff)) =>
              (n, ps, fn (n', sg) =>
                 let val pre' = relax_pre (subst_form sg pre)
                 in if isBot pre' then NONE     (* statically infeasible ground instance *)
                    else SOME (C.SimpleActionSchemaa
                      (C.ActionHead (n', []),
                       C.SimpleActionBody (map_form prop_term_atom pre',
                                           prop_eff (relax_eff (subst_eff sg eff)))))
                 end)
          | C.DurativeActionSchema (C.ActionHead (n, ps),
                                    C.DurativeActionBody (durs, conds, effs)) =>
              (n, ps, fn (n', sg) =>
                 let val conds' = map (fn (ta, f) => (ta, relax_pre (subst_form sg f))) conds
                 in if List.exists (fn (_, f) => isBot f) conds' then NONE
                    else SOME (C.DurativeActionSchema
                      (C.ActionHead (n', []),
                       C.DurativeActionBody
                         (map (fn (ta, dc) => (ta, prop_dc (subst_dc sg dc))) durs,
                          map (fn (ta, f)  => (ta, map_form prop_term_atom f)) conds',
                          map (fn (ta, e)  => (ta, prop_eff (relax_eff (subst_eff sg e)))) effs)))
                 end))
      val cand = map (fn (_, pty) => candidates types objs_typed pty) params
    in
      List.mapPartial (fn objs => mk (ground_name name objs, sigma_of params objs)) (cartesian cand)
    end

  (* ---------- init relaxation: numeric assignments -> definedness props ---------- *)
  fun relax_init_form (C.Atom (C.PredAtm p))          = [C.Atom (C.PredAtm p)]
    | relax_init_form (C.Atom (C.NumericEqAtm (x, y))) = [def_conj x y]
    | relax_init_form (C.Atom (C.EqAtm _))            = []   (* static; carries no state *)
    | relax_init_form (C.Atom _)                       = []
    | relax_init_form f                                = [f]

  (* ---------- collect declared 0-ary predicate + function names ---------- *)
  fun add x xs = if List.exists (fn y => y = x) xs then xs else x :: xs
  fun atom_pred acc (C.PredAtm (C.Pred p, _)) = add p acc
    | atom_pred acc _ = acc
  fun form_preds acc (C.Atom a)     = atom_pred acc a
    | form_preds acc C.Bot          = acc
    | form_preds acc (C.Not f)      = form_preds acc f
    | form_preds acc (C.And (f, g)) = form_preds (form_preds acc f) g
    | form_preds acc (C.Or (f, g))  = form_preds (form_preds acc f) g
    | form_preds acc (C.Imp (f, g)) = form_preds (form_preds acc f) g

  fun nexp_funcs acc e =
    (case e of
        C.FunctionExpr (C.PNE (C.Func f, _)) => add f acc
      | C.AddExpr (a, b) => nexp_funcs (nexp_funcs acc a) b
      | C.SubExpr (a, b) => nexp_funcs (nexp_funcs acc a) b
      | C.MulExpr (a, b) => nexp_funcs (nexp_funcs acc a) b
      | C.DivExpr (a, b) => nexp_funcs (nexp_funcs acc a) b
      | C.SinExpr a      => nexp_funcs acc a
      | C.CosExpr a      => nexp_funcs acc a
      | C.ExpExpr a      => nexp_funcs acc a
      | _                => acc)
  fun eff_funcs acc (C.Effect (_, _, neffs)) =
        foldl (fn (C.NumericEffect (_, C.PNE (C.Func f, _), e), a) => nexp_funcs (add f a) e)
          acc neffs
  fun dc_funcs acc (C.DurationConstraint (_, e)) = nexp_funcs acc e

  fun schema_preds acc sch =
    (case sch of
        C.SimpleActionSchemaa (_, C.SimpleActionBody (pre, C.Effect (a, d, _))) =>
          foldl (fn (f, ac) => form_preds ac f) (form_preds acc pre) (a @ d)
      | C.DurativeActionSchema (_, C.DurativeActionBody (_, conds, effs)) =>
          let val ac1 = foldl (fn ((_, f), ac) => form_preds ac f) acc conds
          in foldl (fn ((_, C.Effect (a, d, _)), ac) =>
                      foldl (fn (f, ac') => form_preds ac' f) ac (a @ d)) ac1 effs end)
  fun schema_funcs acc sch =
    (case sch of
        C.SimpleActionSchemaa (_, C.SimpleActionBody (_, eff)) => eff_funcs acc eff
      | C.DurativeActionSchema (_, C.DurativeActionBody (durs, _, effs)) =>
          let val a1 = foldl (fn ((_, dc), ac) => dc_funcs ac dc) acc durs
          in foldl (fn ((_, e), ac) => eff_funcs ac e) a1 effs end)

  (* ---------- ground the whole problem ---------- *)
  fun ground_problem
        (C.Problem (C.Domain (types, _, _, consts, actions), objs, init, goal)) =
    let
      val all_objs = objs @ consts
      val ground_actions = List.concat (map (ground_schema types all_objs) actions)
      val prop_init = map (map_form prop_obj_atom) (List.concat (map relax_init_form init))
      val prop_goal = map_form prop_obj_atom goal
      val pnames =
        foldl (fn (s, acc) => schema_preds acc s)
          (form_preds (foldl (fn (f, acc) => form_preds acc f) [] prop_init) prop_goal)
          ground_actions
      val fnames =
        foldl (fn (s, acc) => schema_funcs acc s) [] ground_actions
      val prop_preds = map (fn nm => C.PredDecl (C.Pred nm, [])) pnames
      val prop_funcs = map (fn nm => C.FuncDecl (C.Func nm, [])) fnames
    in
      C.Problem
        (C.Domain (types, prop_preds, prop_funcs, [], ground_actions), [], prop_init, prop_goal)
    end

  (* ---------- pretty-print a GROUND (propositional) problem as PDDL, for inspection ----------
     Predicate/init/goal atoms are 0-ary (objects inlined); numeric content has been relaxed to
     definedness predicates.  Exact duration rat values are shown as `#` (the export exposes no
     rat destructor); the constraint operator + structure are shown. *)
  fun predD_name (C.PredDecl (C.Pred p, _)) = p
  fun atom_str (C.PredAtm (C.Pred p, _)) = "(" ^ p ^ ")"
    | atom_str (C.EqAtm _) = "(= ?)"
    | atom_str _ = "(numeric)"
  fun conjuncts (C.And (f, g)) = conjuncts f @ conjuncts g
    | conjuncts (C.Not C.Bot)  = []          (* True: contributes no conjunct *)
    | conjuncts f = [f]
  fun lit_str (C.Atom a)          = atom_str a
    | lit_str (C.Not (C.Atom a))  = "(not " ^ atom_str a ^ ")"
    | lit_str C.Bot               = "(and)"  (* unsatisfiable; shouldn't reach a kept action *)
    | lit_str (C.Not f)           = "(not " ^ lit_str f ^ ")"
    | lit_str (C.Or (f, g))       = "(or " ^ lit_str f ^ " " ^ lit_str g ^ ")"
    | lit_str (C.Imp (f, g))      = "(imply " ^ lit_str f ^ " " ^ lit_str g ^ ")"
    | lit_str (f as C.And _)      = "(and " ^ String.concatWith " " (map lit_str (conjuncts f)) ^ ")"
  fun conj_str f = "(and " ^ String.concatWith " " (map lit_str (conjuncts f)) ^ ")"
  fun eff_str (C.Effect (adds, dels, _)) =
        "(and " ^ String.concatWith " "
          (map lit_str adds @ map (fn f => "(not " ^ lit_str f ^ ")") dels) ^ ")"
  fun ta_str C.At_Start = "at start" | ta_str C.At_End = "at end" | ta_str C.Over_All = "over all"
  fun dop_str C.EQ = "=" | dop_str C.LEQ = "<=" | dop_str C.GEQ = ">="
  fun dc_str (ta, C.DurationConstraint (dop, _)) =
        "(" ^ dop_str dop ^ " ?duration #)"   (* exact rat not destructurable via the export *)
  fun tcond_str (ta, f) = "(" ^ ta_str ta ^ " " ^ conj_str f ^ ")"
  fun teff_str (ta, e)  = "(" ^ ta_str ta ^ " " ^ eff_str e ^ ")"
  fun action_str (C.SimpleActionSchemaa (C.ActionHead (n, _), C.SimpleActionBody (pre, eff))) =
        "  (:action " ^ n ^ "\n   :parameters ()\n   :precondition " ^ conj_str pre ^
        "\n   :effect " ^ eff_str eff ^ ")\n"
    | action_str (C.DurativeActionSchema (C.ActionHead (n, _),
                                          C.DurativeActionBody (durs, conds, effs))) =
        "  (:durative-action " ^ n ^ "\n   :parameters ()\n   :duration (and " ^
        String.concatWith " " (map dc_str durs) ^ ")\n   :condition (and " ^
        String.concatWith " " (map tcond_str conds) ^ ")\n   :effect (and " ^
        String.concatWith " " (map teff_str effs) ^ "))\n"

  fun problem_to_pddl (C.Problem (C.Domain (_, preds, _, _, actions), _, init, goal)) =
    let
      val preds_str = String.concatWith " " (map (fn p => "(" ^ predD_name p ^ ")") preds)
      val domain =
        "(define (domain ground)\n  (:requirements :strips :durative-actions)\n" ^
        "  (:predicates " ^ preds_str ^ ")\n" ^
        String.concat (map action_str actions) ^ ")\n"
      val init_str = String.concatWith "\n  " (map lit_str init)
      val problem =
        "(define (problem groundproblem) (:domain ground)\n (:init\n  " ^ init_str ^
        "\n )\n (:goal " ^ lit_str goal ^ ")\n)\n"
    in domain ^ "\n" ^ problem end
end

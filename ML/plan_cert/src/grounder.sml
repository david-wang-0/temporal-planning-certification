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
  structure Q = QAst

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

  (* ---------- Strategy A ("grounded"): expand quantifiers AFTER a schema's own params are
     substituted (sigma), so per-instance relaxation can prune.  `expand_gform`/`expand_geff`/
     `expand_gteff` collapse the forall-carrying QAst into plain C formulas/effects; the empty
     conjunction/disjunction is True/False -- the forall/exists semantics over an empty domain. *)
  fun disj [] = C.Bot | disj [f] = f | disj (f :: fs) = C.Or (f, disj fs)
  fun extend sigma pairs =
    fn v => (case List.find (fn (v', _) => v' = v) pairs of SOME (_, ob) => SOME ob | NONE => sigma v)
  fun q_assigns types objs sigma binder =
    map (fn combo => extend sigma combo)
      (cartesian (map (fn (v, ty) => map (fn ob => (v, ob)) (candidates types objs ty)) binder))
  fun expand_gform types objs sigma g =
    (case g of
        Q.QF f          => subst_form sigma f
      | Q.QNot g'       => C.Not (expand_gform types objs sigma g')
      | Q.QAnd gs       => conj (map (expand_gform types objs sigma) gs)
      | Q.QOr gs        => disj (map (expand_gform types objs sigma) gs)
      | Q.QImp (a, b)   => C.Imp (expand_gform types objs sigma a, expand_gform types objs sigma b)
      | Q.QAll (bnd, b) => conj (map (fn s' => expand_gform types objs s' b) (q_assigns types objs sigma bnd))
      | Q.QEx (bnd, b)  => disj (map (fn s' => expand_gform types objs s' b) (q_assigns types objs sigma bnd)))
  fun flatten_eff effs =
    C.Effect (List.concat (map (fn C.Effect (a, _, _) => a) effs),
              List.concat (map (fn C.Effect (_, d, _) => d) effs),
              List.concat (map (fn C.Effect (_, _, n) => n) effs))
  fun expand_geff types objs sigma e =
    (case e of
        Q.QE eff         => subst_eff sigma eff
      | Q.QESeq es       => flatten_eff (map (expand_geff types objs sigma) es)
      | Q.QEAll (bnd, b) =>
          flatten_eff (List.concat (map (fn s' => map (expand_geff types objs s') b)
                                         (q_assigns types objs sigma bnd))))
  fun expand_gteff types objs sigma te =
    (case te of
        Q.QTE (ta, eff) => [(ta, subst_eff sigma eff)]
      | Q.QTAll (bnd, b) =>
          List.concat (map (fn s' => List.concat (map (expand_gteff types objs s') b))
                           (q_assigns types objs sigma bnd)))

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

  (* Strategy A twin of ground_schema: params instantiated first, THEN quantifiers expanded. *)
  fun ground_schema_q types objs sch =
    (case sch of
        Q.QSimple (n, ps, preG, effG) =>
          let val cand = map (fn (_, pty) => candidates types objs pty) ps
              fun mk objs_tuple =
                let val sg = sigma_of ps objs_tuple
                    val pre' = relax_pre (expand_gform types objs sg preG)
                in if isBot pre' then NONE
                   else SOME (C.SimpleActionSchemaa
                     (C.ActionHead (ground_name n objs_tuple, []),
                      C.SimpleActionBody (map_form prop_term_atom pre',
                                          prop_eff (relax_eff (expand_geff types objs sg effG)))))
                end
          in List.mapPartial mk (cartesian cand) end
      | Q.QDurative (n, ps, durs, condsG, effsG) =>
          let val cand = map (fn (_, pty) => candidates types objs pty) ps
              fun mk objs_tuple =
                let val sg = sigma_of ps objs_tuple
                    val conds' = map (fn (ta, g) => (ta, relax_pre (expand_gform types objs sg g))) condsG
                in if List.exists (fn (_, f) => isBot f) conds' then NONE
                   else SOME (C.DurativeActionSchema
                     (C.ActionHead (ground_name n objs_tuple, []),
                      C.DurativeActionBody
                        (map (fn (ta, dc) => (ta, prop_dc (subst_dc sg dc))) durs,
                         map (fn (ta, f)  => (ta, map_form prop_term_atom f)) conds',
                         map (fn (ta, e)  => (ta, prop_eff (relax_eff e)))
                             (List.concat (map (expand_gteff types objs sg) effsG)))))
                end
          in List.mapPartial mk (cartesian cand) end)

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

  (* ---------- uniform duration scaling: make every duration constant an integer ----------
     Some domains give NON-integer durations (painter's domain_container: (= ?duration 15.004)
     alongside integer 4/5/6).  The integer-duration network builder rejects non-integer
     durations, so as a post-pass over the assembled ground actions we scale EVERY duration
     constant uniformly by  K = lcm of all duration denominators  (15.004 = 15004/1000, the
     others /1  =>  K = 1000  =>  x1000  ->  15004 / 4000 / 5000 / 6000).  Uniform scaling of
     ALL durations preserves the temporal structure.

     GATED: when every duration is already integer, K = 1 and the pass is a strict no-op
     (the actions list is returned untouched -- durations are never rebuilt when K = 1), so
     integer-duration problems produce byte-identical output.

     Epsilon / min-separation: the grounder exposes NO epsilon on the SML boundary -- duration
     constants are the ONLY time constants crossing into the reduction (they enter the locale
     via lower/upper), and ground_schema* pass no separation constant -- so uniform duration
     scaling is self-consistent here.  This assumes the reduction's internal min-separation
     epsilon is 0 (or is scaled in lock-step); that constant is not visible/controllable from
     SML, so a nonzero, un-scaled epsilon inside the reduction would need matching there.

     The rat num/den come from C.quotient_of (rat -> inta * inta); scaled rats are rebuilt
     with C.fract (which re-normalises).  Arithmetic is over the export's native `inta`. *)
  fun rat_num_den r = let val (n, d) = C.quotient_of r
                      in (C.integer_of_int n, C.integer_of_int d) end
  fun igcd (a, 0) = Int.abs a
    | igcd (a, b) = igcd (b, a mod b)
  fun ilcm (a, b) = if a = 0 orelse b = 0 then 0
                    else (Int.abs a div igcd (Int.abs a, Int.abs b)) * Int.abs b

  (* fold the lcm of the denominators of every ConstantExpr leaf into k *)
  fun nexp_dur_lcm k e =
    (case e of
        C.ConstantExpr r  => ilcm (k, #2 (rat_num_den r))
      | C.AddExpr (a, b)  => nexp_dur_lcm (nexp_dur_lcm k a) b
      | C.SubExpr (a, b)  => nexp_dur_lcm (nexp_dur_lcm k a) b
      | C.MulExpr (a, b)  => nexp_dur_lcm (nexp_dur_lcm k a) b
      | C.DivExpr (a, b)  => nexp_dur_lcm (nexp_dur_lcm k a) b
      | C.SinExpr a       => nexp_dur_lcm k a
      | C.CosExpr a       => nexp_dur_lcm k a
      | C.ExpExpr a       => nexp_dur_lcm k a
      | _                 => k)   (* DurationExpr, PiExpr, FunctionExpr: no constant leaf *)

  (* multiply every ConstantExpr leaf by kK; NVar/FunctionExpr (fluent refs) left alone *)
  fun scale_nexp kK e =
    (case e of
        C.ConstantExpr r  =>
          let val (n, d) = rat_num_den r
          in C.ConstantExpr (C.fract (C.Int_of_integer (n * kK)) (C.Int_of_integer d)) end
      | C.AddExpr (a, b)  => C.AddExpr (scale_nexp kK a, scale_nexp kK b)
      | C.SubExpr (a, b)  => C.SubExpr (scale_nexp kK a, scale_nexp kK b)
      | C.MulExpr (a, b)  => C.MulExpr (scale_nexp kK a, scale_nexp kK b)
      | C.DivExpr (a, b)  => C.DivExpr (scale_nexp kK a, scale_nexp kK b)
      | C.SinExpr a       => C.SinExpr (scale_nexp kK a)
      | C.CosExpr a       => C.CosExpr (scale_nexp kK a)
      | C.ExpExpr a       => C.ExpExpr (scale_nexp kK a)
      | C.FunctionExpr _  =>
          (TextIO.output (TextIO.stdErr,
             "WARNING: duration constraint references a fluent; not scaling that leaf\n");
           e)
      | _                 => e)   (* DurationExpr, PiExpr: unchanged *)

  fun scale_dc kK (C.DurationConstraint (dop, e)) = C.DurationConstraint (dop, scale_nexp kK e)
  fun action_durs (C.DurativeActionSchema (_, C.DurativeActionBody (durs, _, _))) = durs
    | action_durs _ = []
  fun scale_action kK (C.DurativeActionSchema (h, C.DurativeActionBody (durs, conds, effs))) =
        C.DurativeActionSchema
          (h, C.DurativeActionBody (map (fn (ta, dc) => (ta, scale_dc kK dc)) durs, conds, effs))
    | scale_action _ a = a   (* simple (non-durative) actions carry no durations *)

  fun scale_durations actions =
    let val kK = foldl (fn (a, k) => foldl (fn ((_, C.DurationConstraint (_, e)), kk) =>
                                              nexp_dur_lcm kk e) k (action_durs a))
                       1 actions
    in if kK = 1 then actions           (* all durations integer: strict no-op *)
       else map (scale_action kK) actions
    end

  (* ---------- ground the whole problem ---------- *)
  (* shared assembly of the propositional (delete-relaxed) ground problem from already-grounded
     actions; shared by the C-input entry (ground_problem) and the QAst entry (ground_problem_q). *)
  fun assemble_prop types ground_actions0 init goal =
    let
      val ground_actions = scale_durations ground_actions0
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

  fun ground_problem
        (C.Problem (C.Domain (types, _, _, consts, actions), objs, init, goal)) =
      assemble_prop types
        (List.concat (map (ground_schema types (objs @ consts)) actions)) init goal

  (* Strategy A entry: same output as ground_problem, from forall-carrying QAst schemas. *)
  fun ground_problem_q (Q.QProblem (types, objs, consts, actions, init, goal)) =
      assemble_prop types
        (List.concat (map (ground_schema_q types (objs @ consts)) actions)) init goal

  (* ================ numeric-KEEPING grounding (for the numeric network builder) ================
     Same instantiation + propositionalisation as ground_problem, but numeric preconditions and
     numeric effects are KEPT (their func-applications inlined to 0-ary names) rather than
     delete-relaxed.  Feeds Converter.check_and_make_numeric_network_opt, which reads the numeric
     content directly.  Ground object (in)equalities are still folded (the reduction has no
     constants), and statically-infeasible ground instances are still pruned. *)

  (* fold ground object (in)equalities + simplify boolean structure, but KEEP numeric comparison
     atoms (they are mangled to 0-ary funcs later by prop_term_atom / prop_obj_atom) *)
  fun fold_eq_pre (C.Atom (C.PredAtm p)) = C.Atom (C.PredAtm p)
    | fold_eq_pre (C.Atom (C.EqAtm (a, b))) =
        (case eq_names (a, b) of SOME true => fTrue | SOME false => C.Bot
                               | NONE => C.Atom (C.EqAtm (a, b)))
    | fold_eq_pre (C.Atom a) = C.Atom a   (* numeric comparison atoms: keep *)
    | fold_eq_pre C.Bot = C.Bot
    | fold_eq_pre (C.Not f) =
        (case fold_eq_pre f of C.Bot => fTrue | C.Not C.Bot => C.Bot | f' => C.Not f')
    | fold_eq_pre (C.And (f, g)) =
        (case (fold_eq_pre f, fold_eq_pre g) of
            (C.Bot, _) => C.Bot | (_, C.Bot) => C.Bot
          | (C.Not C.Bot, g') => g' | (f', C.Not C.Bot) => f'
          | (f', g') => C.And (f', g'))
    | fold_eq_pre (C.Or (f, g)) =
        (case (fold_eq_pre f, fold_eq_pre g) of
            (C.Not C.Bot, _) => fTrue | (_, C.Not C.Bot) => fTrue
          | (C.Bot, g') => g' | (f', C.Bot) => f' | (f', g') => C.Or (f', g'))
    | fold_eq_pre (C.Imp (f, g)) =
        (case (fold_eq_pre f, fold_eq_pre g) of
            (C.Bot, _) => fTrue | (_, C.Not C.Bot) => fTrue
          | (C.Not C.Bot, g') => g' | (f', g') => C.Imp (f', g'))

  (* numeric-keeping init: keep predicate atoms AND numeric assignments; drop static EqAtm *)
  fun keep_init_form (C.Atom (C.PredAtm p))           = [C.Atom (C.PredAtm p)]
    | keep_init_form (C.Atom (C.NumericEqAtm (x, y)))  = [C.Atom (C.NumericEqAtm (x, y))]
    | keep_init_form (C.Atom (C.EqAtm _))             = []
    | keep_init_form (C.Atom _)                        = []
    | keep_init_form f                                 = [f]

  (* filt: optional nemo-reachability filter (schema name, parameter tuple) -> keep? *)
  fun keep_tuple filt name objs =
    (case filt of NONE => true | SOME f => f (name, objs))

  fun ground_schema_numeric filt types objs_typed sch =
    let
      val (name, params, mk) =
        (case sch of
            C.SimpleActionSchemaa (C.ActionHead (n, ps), C.SimpleActionBody (pre, eff)) =>
              (n, ps, fn (n', sg) =>
                 let val pre' = fold_eq_pre (subst_form sg pre)
                 in if isBot pre' then NONE
                    else SOME (C.SimpleActionSchemaa
                      (C.ActionHead (n', []),
                       C.SimpleActionBody (map_form prop_term_atom pre',
                                           prop_eff (subst_eff sg eff))))
                 end)
          | C.DurativeActionSchema (C.ActionHead (n, ps),
                                    C.DurativeActionBody (durs, conds, effs)) =>
              (n, ps, fn (n', sg) =>
                 let val conds' = map (fn (ta, f) => (ta, fold_eq_pre (subst_form sg f))) conds
                 in if List.exists (fn (_, f) => isBot f) conds' then NONE
                    else SOME (C.DurativeActionSchema
                      (C.ActionHead (n', []),
                       C.DurativeActionBody
                         (map (fn (ta, dc) => (ta, prop_dc (subst_dc sg dc))) durs,
                          map (fn (ta, f)  => (ta, map_form prop_term_atom f)) conds',
                          map (fn (ta, e)  => (ta, prop_eff (subst_eff sg e))) effs)))
                 end))
      val cand = map (fn (_, pty) => candidates types objs_typed pty) params
    in
      List.mapPartial (fn objs => mk (ground_name name objs, sigma_of params objs))
        (List.filter (keep_tuple filt name) (cartesian cand))
    end

  (* Strategy A twin of ground_schema_numeric (KEEPS numeric pre/effects). *)
  fun ground_schema_numeric_q filt types objs sch =
    (case sch of
        Q.QSimple (n, ps, preG, effG) =>
          let val cand = map (fn (_, pty) => candidates types objs pty) ps
              fun mk objs_tuple =
                let val sg = sigma_of ps objs_tuple
                    val pre' = fold_eq_pre (expand_gform types objs sg preG)
                in if isBot pre' then NONE
                   else SOME (C.SimpleActionSchemaa
                     (C.ActionHead (ground_name n objs_tuple, []),
                      C.SimpleActionBody (map_form prop_term_atom pre',
                                          prop_eff (expand_geff types objs sg effG))))
                end
          in List.mapPartial mk (List.filter (keep_tuple filt n) (cartesian cand)) end
      | Q.QDurative (n, ps, durs, condsG, effsG) =>
          let val cand = map (fn (_, pty) => candidates types objs pty) ps
              fun mk objs_tuple =
                let val sg = sigma_of ps objs_tuple
                    val conds' = map (fn (ta, g) => (ta, fold_eq_pre (expand_gform types objs sg g))) condsG
                in if List.exists (fn (_, f) => isBot f) conds' then NONE
                   else SOME (C.DurativeActionSchema
                     (C.ActionHead (ground_name n objs_tuple, []),
                      C.DurativeActionBody
                        (map (fn (ta, dc) => (ta, prop_dc (subst_dc sg dc))) durs,
                         map (fn (ta, f)  => (ta, map_form prop_term_atom f)) conds',
                         map (fn (ta, e)  => (ta, prop_eff e))
                             (List.concat (map (expand_gteff types objs sg) effsG)))))
                end
          in List.mapPartial mk (List.filter (keep_tuple filt n) (cartesian cand)) end)

  (* func names occurring in a formula's numeric comparison atoms *)
  fun atom_funcs acc (C.NumericEqAtm (x, y))      = nexp_funcs (nexp_funcs acc x) y
    | atom_funcs acc (C.NumericLessAtm (x, y))    = nexp_funcs (nexp_funcs acc x) y
    | atom_funcs acc (C.NumericLEAtm (x, y))      = nexp_funcs (nexp_funcs acc x) y
    | atom_funcs acc (C.NumericGreaterAtm (x, y)) = nexp_funcs (nexp_funcs acc x) y
    | atom_funcs acc (C.NumericGEAtm (x, y))      = nexp_funcs (nexp_funcs acc x) y
    | atom_funcs acc _                             = acc
  fun form_funcs acc (C.Atom a)     = atom_funcs acc a
    | form_funcs acc C.Bot          = acc
    | form_funcs acc (C.Not f)      = form_funcs acc f
    | form_funcs acc (C.And (f, g)) = form_funcs (form_funcs acc f) g
    | form_funcs acc (C.Or (f, g))  = form_funcs (form_funcs acc f) g
    | form_funcs acc (C.Imp (f, g)) = form_funcs (form_funcs acc f) g
  fun schema_funcs_num acc sch =
    (case sch of
        C.SimpleActionSchemaa (_, C.SimpleActionBody (pre, eff)) =>
          eff_funcs (form_funcs acc pre) eff
      | C.DurativeActionSchema (_, C.DurativeActionBody (durs, conds, effs)) =>
          let val a0 = foldl (fn ((_, dc), ac) => dc_funcs ac dc) acc durs
              val a1 = foldl (fn ((_, f), ac) => form_funcs ac f) a0 conds
          in foldl (fn ((_, e), ac) => eff_funcs ac e) a1 effs end)

  (* ---- STATIC numeric fluents: fold DURATIONS ONLY (never assigned by any action) ----
     A ground fluent that is on NO effect's LHS is static: its value stays its init assignment.
     The net format requires constant integer durations (per-action int clock bounds), so a
     duration constraint referencing a static fluent (sync's  (= ?duration (dur_c1 r0)) ) MUST
     be folded to its init constant.  Guards, effect RHSs and the goal are NOT folded: the
     verified bound-inference/certificate layer handles true fluent-vs-fluent guards (static
     point boxes + relational refinement), so the certified problem is the true grounded
     problem everywhere except durations.  Statics left entirely unread after the duration
     fold (sync's dur_ fluents) are dropped from funcs/init as dead. *)
  fun mem x xs = List.exists (fn y => y = x) xs
  fun assocv _ [] = NONE
    | assocv x ((k, v) :: t) = if k = x then SOME v else assocv x t
  fun eff_lhs (C.Effect (_, _, neffs)) =
        foldl (fn (C.NumericEffect (_, C.PNE (C.Func f, _), _), a) => add f a) [] neffs
  fun schema_assigned acc sch =
    (case sch of
        C.SimpleActionSchemaa (_, C.SimpleActionBody (_, e)) =>
          foldl (fn (x, a) => add x a) acc (eff_lhs e)
      | C.DurativeActionSchema (_, C.DurativeActionBody (_, _, effs)) =>
          foldl (fn ((_, e), a) => foldl (fn (x, b) => add x b) a (eff_lhs e)) acc effs)

  fun fold_nexp st cm e =
    (case e of
        C.FunctionExpr (C.PNE (C.Func f, _)) =>
          if mem f st then (case assocv f cm of SOME v => C.ConstantExpr v | NONE => e) else e
      | C.AddExpr (a, b) => C.AddExpr (fold_nexp st cm a, fold_nexp st cm b)
      | C.SubExpr (a, b) => C.SubExpr (fold_nexp st cm a, fold_nexp st cm b)
      | C.MulExpr (a, b) => C.MulExpr (fold_nexp st cm a, fold_nexp st cm b)
      | C.DivExpr (a, b) => C.DivExpr (fold_nexp st cm a, fold_nexp st cm b)
      | C.SinExpr a => C.SinExpr (fold_nexp st cm a)
      | C.CosExpr a => C.CosExpr (fold_nexp st cm a)
      | C.ExpExpr a => C.ExpExpr (fold_nexp st cm a)
      | _ => e)
  (* Operand normalization: when exactly one side of a numeric comparison is a constant, put the
     non-constant (fluent-bearing) side on the LEFT, flipping the comparator.  Semantically identical
     (same comparison), and it is what the downstream var-vs-const projection/refine layers expect
     (they only match  Comp op (NVar f) (NConst c)).  Fires after constant-folding a static fluent
     like  (= (item_id ?i) (counter ?t))  ->  (= <const> (counter ?t)) , renormalized to
     (= (counter ?t) <const>). *)
  fun is_const_expr (C.ConstantExpr _) = true | is_const_expr _ = false
  fun norm_cmp a =
    (case a of
        C.NumericEqAtm (x, y)      => if is_const_expr x andalso not (is_const_expr y) then C.NumericEqAtm (y, x) else a
      | C.NumericLessAtm (x, y)    => if is_const_expr x andalso not (is_const_expr y) then C.NumericGreaterAtm (y, x) else a
      | C.NumericLEAtm (x, y)      => if is_const_expr x andalso not (is_const_expr y) then C.NumericGEAtm (y, x) else a
      | C.NumericGreaterAtm (x, y) => if is_const_expr x andalso not (is_const_expr y) then C.NumericLessAtm (y, x) else a
      | C.NumericGEAtm (x, y)      => if is_const_expr x andalso not (is_const_expr y) then C.NumericLEAtm (y, x) else a
      | other => other)
  fun fold_dc st cm (C.DurationConstraint (dop, e)) = C.DurationConstraint (dop, fold_nexp st cm e)
  fun fold_eff st cm (C.Effect (adds, dels, neffs)) =
        C.Effect (adds, dels, map (fn C.NumericEffect (o_, p, e) => C.NumericEffect (o_, p, fold_nexp st cm e)) neffs)
  (* GUARDS-ONLY unfold: statics are folded in DURATIONS (the net needs constant int clock
     bounds) and EFFECT RHSs (the mlunta update grammar is x:=c | x:=x+-c | x:=v+-c -- a
     variable offset like  battery := battery - distance  is inexpressible in the model
     format), but NOT in guard comparisons: those stay true fluent-vs-fluent and are handled
     by the verified relational bound-inference/certificate layer (static point boxes).
     Guard comparisons are only operand-normalized (norm_cmp). *)
  fun norm_fold_sch st cm sch =
    (case sch of
        C.SimpleActionSchemaa (h, C.SimpleActionBody (pre, eff)) =>
          C.SimpleActionSchemaa (h, C.SimpleActionBody (map_form norm_cmp pre, fold_eff st cm eff))
      | C.DurativeActionSchema (h, C.DurativeActionBody (durs, conds, effs)) =>
          C.DurativeActionSchema (h, C.DurativeActionBody
            (map (fn (ta, dc) => (ta, fold_dc st cm dc)) durs,
             map (fn (ta, f)  => (ta, map_form norm_cmp f)) conds,
             map (fn (ta, e)  => (ta, fold_eff st cm e)) effs)))

  (* the static map: (fluent, init value) for every fluent no action's effect assigns *)
  fun static_cm actions init =
    let val assigned = foldl (fn (s, a) => schema_assigned a s) [] actions
    in List.mapPartial
         (fn C.Atom (C.NumericEqAtm (C.FunctionExpr (C.PNE (C.Func f, _)), C.ConstantExpr v)) =>
               if mem f assigned then NONE else SOME (f, v)
           | _ => NONE) init
    end

  (* shared assembly of the numeric-KEEPING ground problem; shared by the C-input entry
     (ground_problem_numeric) and the QAst entry (ground_problem_numeric_q). *)
  fun assemble_numeric types ground_actions0 init goal =
    let
      val num_init = map (map_form prop_obj_atom) (List.concat (map keep_init_form init))
      val num_goal = map_form norm_cmp (map_form prop_obj_atom goal)
      (* statics + their init values; fold DURATIONS before integer-scaling so a folded
         rational duration is scaled like any literal *)
      val cm = static_cm ground_actions0 num_init
      val st = map #1 cm
      val ground_actions = scale_durations (map (norm_fold_sch st cm) ground_actions0)
      val pnames =
        foldl (fn (s, acc) => schema_preds acc s)
          (form_preds (foldl (fn (f, acc) => form_preds acc f) [] num_init) num_goal)
          ground_actions
      (* fluents referenced by the ACTIONS (guards/effects/remaining durations) or the GOAL:
         a static read only in now-folded durations (sync's dur_ fluents) does not appear and is
         dropped from funcs/init as dead; live statics (painter's item_id, majsp's distance)
         stay declared + init'd and get point boxes from the bound inference *)
      val fnames =
        foldl (fn (s, acc) => schema_funcs_num acc s) (form_funcs [] num_goal) ground_actions
      val prop_preds = map (fn nm => C.PredDecl (C.Pred nm, [])) pnames
      val num_funcs  = map (fn nm => C.FuncDecl (C.Func nm, [])) fnames
      val init' = List.filter
        (fn C.Atom (C.NumericEqAtm (C.FunctionExpr (C.PNE (C.Func f, _)), _)) => mem f fnames
          | _ => true) num_init
    in
      C.Problem
        (C.Domain (types, prop_preds, num_funcs, [], ground_actions), [], init', num_goal)
    end

  fun ground_problem_numeric filt
        (C.Problem (C.Domain (types, _, _, consts, actions), objs, init, goal)) =
      assemble_numeric types
        (List.concat (map (ground_schema_numeric filt types (objs @ consts)) actions)) init goal

  (* Strategy A entry (numeric-keeping): from forall-carrying QAst schemas. *)
  fun ground_problem_numeric_q filt (Q.QProblem (types, objs, consts, actions, init, goal)) =
      assemble_numeric types
        (List.concat (map (ground_schema_numeric_q filt types (objs @ consts)) actions)) init goal

  (* ---------- pretty-print a GROUND (propositional) problem as PDDL, for inspection ----------
     Predicate/init/goal atoms are 0-ary (objects inlined); numeric content has been relaxed to
     definedness predicates.  Duration rat values are shown exactly (via C.quotient_of); the
     constraint operator + structure are shown. *)
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
  (* render a duration nexp; rat constants now destructurable via C.quotient_of *)
  fun dnexp_str (C.ConstantExpr r) =
        let val (n, d) = rat_num_den r
        in if d = 1 then Int.toString n else Int.toString n ^ "/" ^ Int.toString d end
    | dnexp_str C.DurationExpr = "?duration"
    | dnexp_str C.PiExpr       = "pi"
    | dnexp_str (C.AddExpr (a, b)) = "(+ " ^ dnexp_str a ^ " " ^ dnexp_str b ^ ")"
    | dnexp_str (C.SubExpr (a, b)) = "(- " ^ dnexp_str a ^ " " ^ dnexp_str b ^ ")"
    | dnexp_str (C.MulExpr (a, b)) = "(* " ^ dnexp_str a ^ " " ^ dnexp_str b ^ ")"
    | dnexp_str (C.DivExpr (a, b)) = "(/ " ^ dnexp_str a ^ " " ^ dnexp_str b ^ ")"
    | dnexp_str (C.SinExpr a)      = "(sin " ^ dnexp_str a ^ ")"
    | dnexp_str (C.CosExpr a)      = "(cos " ^ dnexp_str a ^ ")"
    | dnexp_str (C.ExpExpr a)      = "(exp " ^ dnexp_str a ^ ")"
    | dnexp_str (C.FunctionExpr (C.PNE (C.Func f, _))) = "(" ^ f ^ ")"
  fun dc_str (ta, C.DurationConstraint (dop, e)) =
        "(" ^ dop_str dop ^ " ?duration " ^ dnexp_str e ^ ")"
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

(* Unverified SML grounder.

   The verified reduction requires FULLY-PROPOSITIONAL ground PDDL: 0-parameter action schemas
   whose atoms are 0-ary predicates with the objects inlined into the predicate NAME
   (e.g. (light ?m) instantiated at match0 becomes the 0-ary atom (light_match0)), and an empty
   objects/constants set.  (Cf. the pre-ground examples in examples/ground/.)

   This grounder: (1) instantiates each lifted temporal action schema over the problem's objects
   (type-consistent, honouring subtype declarations) and substitutes the parameters; (2)
   propositionalises every predicate atom -- in the actions and in the init/goal -- to a 0-ary
   predicate named `p_o1_..._on`; (3) redeclares those 0-ary predicates and empties the objects.

   It is UNVERIFIED and does a full cross-product instantiation (no reachability pruning), so it
   is only for small instances.  EqAtm/numeric atoms are passed through unmangled (fine for the
   propositional temporal benchmarks such as MatchCellar/sync). *)

structure Grounder =
struct

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

  fun type_fits types onames (Converter.Either pnames) =
    List.exists (fn on =>
      let val sups = supertypes types on
      in List.exists (fn pn => List.exists (fn s => s = pn) sups) pnames end) onames

  fun candidates types objs_typed pty =
    List.mapPartial
      (fn (ob, Converter.Either onames) => if type_fits types onames pty then SOME ob else NONE)
      objs_typed

  fun cartesian [] = [[]]
    | cartesian (xs :: rest) =
        List.concat (map (fn x => map (fn tl => x :: tl) (cartesian rest)) xs)

  (* ---------- parameter substitution (variable-name -> object) ---------- *)
  fun subst_term sigma (Converter.VAR (Converter.Vara v)) =
        (case sigma v of SOME ob => Converter.CONST ob | NONE => Converter.VAR (Converter.Vara v))
    | subst_term _ t = t
  fun subst_atom sigma a = Converter.map_atom (subst_term sigma) a
  fun subst_form sigma (Converter.Atom a)     = Converter.Atom (subst_atom sigma a)
    | subst_form _     Converter.Bot          = Converter.Bot
    | subst_form sigma (Converter.Not f)      = Converter.Not (subst_form sigma f)
    | subst_form sigma (Converter.And (f, g)) = Converter.And (subst_form sigma f, subst_form sigma g)
    | subst_form sigma (Converter.Or (f, g))  = Converter.Or (subst_form sigma f, subst_form sigma g)
    | subst_form sigma (Converter.Imp (f, g)) = Converter.Imp (subst_form sigma f, subst_form sigma g)
  fun subst_pne sigma (Converter.PNE (f, args)) = Converter.PNE (f, map (subst_term sigma) args)
  fun subst_nexp sigma e =
    (case e of
        Converter.ConstantExpr r  => Converter.ConstantExpr r
      | Converter.DurationExpr    => Converter.DurationExpr
      | Converter.PiExpr          => Converter.PiExpr
      | Converter.FunctionExpr p  => Converter.FunctionExpr (subst_pne sigma p)
      | Converter.AddExpr (a, b)  => Converter.AddExpr (subst_nexp sigma a, subst_nexp sigma b)
      | Converter.SubExpr (a, b)  => Converter.SubExpr (subst_nexp sigma a, subst_nexp sigma b)
      | Converter.MulExpr (a, b)  => Converter.MulExpr (subst_nexp sigma a, subst_nexp sigma b)
      | Converter.DivExpr (a, b)  => Converter.DivExpr (subst_nexp sigma a, subst_nexp sigma b)
      | Converter.SinExpr a       => Converter.SinExpr (subst_nexp sigma a)
      | Converter.CosExpr a       => Converter.CosExpr (subst_nexp sigma a)
      | Converter.ExpExpr a       => Converter.ExpExpr (subst_nexp sigma a))
  (* numeric_effect's ctor is not exported (opaque); pass through -- fine for propositional problems *)
  fun subst_neff _ (neff : Converter.term Converter.numeric_effect) = neff
  fun subst_eff sigma (Converter.Effect (adds, dels, neffs)) =
        Converter.Effect (map (subst_form sigma) adds, map (subst_form sigma) dels,
                          map (subst_neff sigma) neffs)
  fun subst_dc sigma (Converter.DurationConstraint (dop, e)) =
        Converter.DurationConstraint (dop, subst_nexp sigma e)

  fun sigma_of params objs =
    let val binds = ListPair.zip (map (fn (Converter.Vara v, _) => v) params, objs)
    in fn v => Option.map #2 (List.find (fn (v', _) => v' = v) binds) end

  (* ---------- propositionalisation: predicate atoms -> 0-ary, object inlined into the name ---------- *)
  fun mangle p names = foldl (fn (nm, acc) => acc ^ "_" ^ nm) p names
  fun term_name (Converter.CONST (Converter.Obj o_)) = o_
    | term_name (Converter.VAR (Converter.Vara v))   = v   (* not expected post-grounding *)
  fun obj_name (Converter.Obj o_) = o_

  (* atom transformer families (term atoms in actions, object atoms in init/goal) *)
  fun prop_term_atom (Converter.PredAtm (Converter.Pred p, args)) =
        Converter.PredAtm (Converter.Pred (mangle p (map term_name args)), [])
    | prop_term_atom a = a
  fun prop_obj_atom (Converter.PredAtm (Converter.Pred p, args)) =
        Converter.PredAtm (Converter.Pred (mangle p (map obj_name args)), [])
    | prop_obj_atom a = a

  fun map_form g (Converter.Atom a)     = Converter.Atom (g a)
    | map_form _ Converter.Bot          = Converter.Bot
    | map_form g (Converter.Not f)      = Converter.Not (map_form g f)
    | map_form g (Converter.And (f, h)) = Converter.And (map_form g f, map_form g h)
    | map_form g (Converter.Or (f, h))  = Converter.Or (map_form g f, map_form g h)
    | map_form g (Converter.Imp (f, h)) = Converter.Imp (map_form g f, map_form g h)

  fun prop_eff (Converter.Effect (adds, dels, neffs)) =
        Converter.Effect (map (map_form prop_term_atom) adds, map (map_form prop_term_atom) dels, neffs)

  (* ---------- ground one schema over the objects (instantiate + substitute + propositionalise) ---------- *)
  fun ground_name base objs = foldl (fn (Converter.Obj o_, acc) => acc ^ "_" ^ o_) base objs

  fun ground_schema types objs_typed sch =
    let
      val (name, params, mk) =
        (case sch of
            Converter.SimpleActionSchemaa (Converter.ActionHead (n, ps),
                                           Converter.SimpleActionBody (pre, eff)) =>
              (n, ps, fn (n', sg) =>
                 Converter.SimpleActionSchemaa
                   (Converter.ActionHead (n', []),
                    Converter.SimpleActionBody (map_form prop_term_atom (subst_form sg pre),
                                                prop_eff (subst_eff sg eff))))
          | Converter.DurativeActionSchema (Converter.ActionHead (n, ps),
                                            Converter.DurativeActionBody (durs, conds, effs)) =>
              (n, ps, fn (n', sg) =>
                 Converter.DurativeActionSchema
                   (Converter.ActionHead (n', []),
                    Converter.DurativeActionBody
                      (map (fn (ta, dc) => (ta, subst_dc sg dc)) durs,
                       map (fn (ta, f)  => (ta, map_form prop_term_atom (subst_form sg f))) conds,
                       map (fn (ta, e)  => (ta, prop_eff (subst_eff sg e))) effs))))
      val cand = map (fn (_, pty) => candidates types objs_typed pty) params
    in
      map (fn objs => mk (ground_name name objs, sigma_of params objs)) (cartesian cand)
    end

  (* ---------- collect the 0-ary predicate names that appear ---------- *)
  fun add x xs = if List.exists (fn y => y = x) xs then xs else x :: xs
  fun form_preds acc (Converter.Atom (Converter.PredAtm (Converter.Pred p, _))) = add p acc
    | form_preds acc (Converter.Atom _)     = acc
    | form_preds acc Converter.Bot          = acc
    | form_preds acc (Converter.Not f)      = form_preds acc f
    | form_preds acc (Converter.And (f, g)) = form_preds (form_preds acc f) g
    | form_preds acc (Converter.Or (f, g))  = form_preds (form_preds acc f) g
    | form_preds acc (Converter.Imp (f, g)) = form_preds (form_preds acc f) g

  fun schema_forms sch =
    (case sch of
        Converter.SimpleActionSchemaa (_, Converter.SimpleActionBody (pre, Converter.Effect (a, d, _))) =>
          pre :: (a @ d)
      | Converter.DurativeActionSchema (_, Converter.DurativeActionBody (_, conds, effs)) =>
          (map #2 conds) @ List.concat (map (fn (_, Converter.Effect (a, d, _)) => a @ d) effs))

  (* ---------- ground the whole problem ---------- *)
  fun ground_problem
        (Converter.Problem
           (Converter.Domain (types, _, funcs, consts, actions), objs, init, goal)) =
    let
      val all_objs = objs @ consts
      val ground_actions = List.concat (map (ground_schema types all_objs) actions)
      val prop_init = map (map_form prop_obj_atom) init
      val prop_goal = map_form prop_obj_atom goal
      (* collect every 0-ary predicate name from the grounded actions + init + goal *)
      val pnames =
        foldl (fn (f, acc) => form_preds acc f)
          (form_preds (foldl (fn (f, acc) => form_preds acc f) [] prop_init) prop_goal)
          (List.concat (map schema_forms ground_actions))
      val prop_preds =
        map (fn nm => Converter.PredDecl (Converter.Pred nm, [])) pnames
    in
      Converter.Problem
        (Converter.Domain (types, prop_preds, funcs, [], ground_actions), [], prop_init, prop_goal)
    end
end

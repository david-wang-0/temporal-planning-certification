(* Numeric bound-inference glue.

   Bridges the two Isabelle code exports:
     NumericProjection.numeric_draft_actions P  -- reduction-side snap projection,
        an INT-ified (fluents, snaps, init) triple keyed by fluent NAME (string);
     NumericBoundInference.infer_fluent_bounds  -- compute-side threshold interval AI,
        polymorphic in the fluent type, returning a per-fluent finite int box (or NONE).

   The two modules carry distinct SML `int` datatypes (both wrap IntInf.int); we bridge
   through IntInf.  The compute side is polymorphic in the fluent type `'a` and needs
   `'a enum`/`'a equal` dictionaries: `String.literal` (= SML string here) has no Isabelle
   `enum` instance, but the fixpoint stability check only ever inspects fluents in the
   carrier list `fs` (every other fluent is unchanged across the iteration), so a dict whose
   `enum`/`enum_all`/`enum_ex` range over `fs` yields the correct result.  We fabricate that
   dict here.

   This projection is UNTRUSTED: a lossy box only widens/mis-sizes the inferred bounds; the
   reduction re-checks any box with `NumericProjection.check_gbounds_opt` (the eval-decidable
   `is_gbound_inv'` gate), which fails closed.  So a wrong box is rejected, never unsound. *)

structure NumericBoundGlue =
struct
  structure NP = NumericProjection
  structure NBI = NumericBoundInference

  (* the raw result shape of NumericProjection.numeric_draft_actions *)
  type draft =
    string list
    * ((NP.g_int list * (string * NP.e_int) list) list
       * (string * NP.int) list)

  (* an inferred box keyed by fluent name, values in NP.int -- exactly the shape
     NumericProjection.check_gbounds_opt consumes *)
  type box = (string * (NP.int * NP.int)) list

  (* --- integer bridging: NP.int <-> IntInf.int <-> NBI.int --- *)
  fun npToII (i : NP.int) : IntInf.int = NP.integer_of_int i
  fun iiToNbi (k : IntInf.int) : NBI.int = NBI.int_of_integer k
  fun npToNbi (i : NP.int) : NBI.int = iiToNbi (npToII i)
  fun npOff (i : NP.int) (d : IntInf.int) : NBI.int = iiToNbi (IntInf.+ (npToII i, d))
  fun nbiToNp (i : NBI.int) : NP.int = NP.Int_of_integer (NBI.integer_of_int i)

  (* --- datatype projection (reduction-side g_int/e_int -> compute-side gcomp/nexp) --- *)
  (* strict comparisons collapse to non-strict on integers *)
  fun pGint (NP.GLe_i (f, c)) = NBI.GLe (f, npToNbi c)
    | pGint (NP.GGe_i (f, c)) = NBI.GGe (f, npToNbi c)
    | pGint (NP.GEq_i (f, c)) = NBI.GEq (f, npToNbi c)
    | pGint (NP.GLt_i (f, c)) = NBI.GLe (f, npOff c (~1))  (* x < c  <=>  x <= c-1 *)
    | pGint (NP.GGt_i (f, c)) = NBI.GGe (f, npOff c 1)     (* x > c  <=>  x >= c+1 *)

  fun pEint (NP.EC c)        = NBI.NConst (npToNbi c)
    | pEint (NP.EV f)        = NBI.NVar f
    | pEint (NP.EAdd (a, b)) = NBI.NAdd (pEint a, pEint b)
    | pEint (NP.ESub (a, b)) = NBI.NSub (pEint a, pEint b)
    | pEint (NP.EMul (a, b)) = NBI.NMul (pEint a, pEint b)
    | pEint (NP.EDiv (a, b)) = NBI.NDiv (pEint a, pEint b)

  fun pSnap (gs, ups) =
    (List.map pGint gs, List.map (fn (f, e) => (f, pEint e)) ups)

  (* --- fluent-list-backed dictionaries for the compute-side polymorphic call --- *)
  val strEqual : string NBI.equal = {equal = (fn (a : string) => fn b => a = b)}
  fun strEnum (fs : string list) : string NBI.enum =
    {finite_enum = (),
     enum       = fs,
     enum_all   = (fn p => List.all p fs),
     enum_ex    = (fn p => List.exists p fs)}

  (* infer a finite int box for every tracked fluent, or NONE if any comes out unbounded
     ("bound inference failed / out of scope") *)
  fun infer_box ((fs, (snaps, init)) : draft) : box option =
    let
      val acts = List.map pSnap snaps
      val zero = NBI.int_of_integer 0
      fun v0 f = case List.find (fn (g, _) => g = f) init of
                   SOME (_, c) => npToNbi c
                 | NONE        => zero
      val thr = NBI.thr_set strEqual fs v0 acts
      val res = NBI.infer_fluent_bounds (strEnum fs, strEqual) thr fs acts v0
    in
      Option.map
        (fn boxfn =>
          List.map
            (fn f => let val (lo, hi) = boxfn f
                     in (f, (nbiToNp lo, nbiToNp hi)) end)
            fs)
        res
    end
end

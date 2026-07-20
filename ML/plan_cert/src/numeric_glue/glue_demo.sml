(* Standalone smoke test of the numeric bound-inference glue.

   Reproduces the Isabelle `value` demo from Numeric_Bound_Inference_Extract.thy: a guarded
   counter `counter := counter + 1` guarded by `counter <= 0`, init `counter = 0`.  Threshold
   widening lands the reachable set at the finite box counter in [0, 1].

   Builds hand-made `numeric_draft_actions`-shaped data (independent of the PDDL parser) so it
   exercises the whole projection + AI + read-back path.  Also runs an unbounded case
   (`counter := counter + 1` with NO guard) which must come out NONE ("out of scope"). *)

structure GlueDemo =
struct
  structure NP = NumericProjection
  fun npi n = NP.Int_of_integer (IntInf.fromInt n)

  fun showBox NONE = "  <NONE: out of scope / unbounded>\n"
    | showBox (SOME box) =
        String.concat
          (List.map
            (fn (f, (lo, hi)) =>
               "  " ^ f ^ " in [" ^ IntInf.toString (NP.integer_of_int lo)
               ^ ", " ^ IntInf.toString (NP.integer_of_int hi) ^ "]\n")
            box)

  (* guarded counter: reachable {0,1} -> finite box *)
  val guarded : NumericBoundGlue.draft =
    (["counter"],
     ([([NP.GLe_i ("counter", npi 0)],
        [("counter", NP.EAdd (NP.EV "counter", NP.EC (npi 1)))])],
      [("counter", npi 0)]))

  (* unguarded counter: reachable {0,1,2,...} -> unbounded, must reject *)
  val unguarded : NumericBoundGlue.draft =
    (["counter"],
     ([([],
        [("counter", NP.EAdd (NP.EV "counter", NP.EC (npi 1)))])],
      [("counter", npi 0)]))

  fun run () =
    (print "guarded counter (counter := counter+1, guard counter<=0, init 0):\n";
     print (showBox (NumericBoundGlue.infer_box guarded));
     print "unguarded counter (no guard):\n";
     print (showBox (NumericBoundGlue.infer_box unguarded)))
end

val () = GlueDemo.run ()

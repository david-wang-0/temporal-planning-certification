(* Checker-side LU clock bounds for the aLU subsumption test (UNTRUSTED SML prototype).

   FEASIBILITY_alu_subsumption.md obligation 5: the L/U bounds must be computed by the
   CHECKER from the model, never trusted from the certificate producer.  We recompute them
   here from the muntax JSON with MLunta's own ceiling machinery:

     - LocalLU (default): IntLocalClockCeiling(Entry) with extra_lu = true -- the
       per-location LU ceilings (Behrmann-style static analysis, LocalCeilingFunction /
       NonTrivialLocalCeiling underneath), the same family tck-reach's clockbounds solver
       uses for aLU-covreach.  Local bounds maximize the chance the certificate's
       (local-LU) subsumptions are admitted.
     - GlobalM (ALU_BOUNDS=global): GlobalClockCeiling(Entry) -- one global M ceiling per
       clock used for both L and U (the aM test).  Coarser bound computation, finer
       subsumption relation: strictly fail-closed w.r.t. LocalLU.

   Ceiling convention (see GlobalClockCeiling.ceiling / dbm.sml extra_lu):
     k_pos L x = (<=,  L(x))   -- the lower-bound ceiling, as a DBM entry
     k_neg L x = (<,  -U(x))   -- the negated upper-bound ceiling
   both total over 0..dim-1 with the zero clock at index 0 mapped to 0.  MLunta ceilings
   initialize at 0 (never -oo); Inf maps to AluDBM.PosInf (identity abstraction on that
   clock -- the finer, fail-closed direction). *)

structure AluBounds =
struct

  datatype bounds_mode = LocalLU | GlobalM

  structure LocalCeil = IntLocalClockCeiling(Entry)
  structure GlobalCeil = GlobalClockCeiling(Entry)

  fun mode_from_env () =
    case OS.Process.getEnv "ALU_BOUNDS" of
        SOME "global" => GlobalM
      | _ => LocalLU

  fun mode_to_string LocalLU = "local-LU"
    | mode_to_string GlobalM = "global-M"

  fun ext_of_pos e =            (* k_pos entry -> L(x) *)
    case Entry.to_int e of
        IntRep.Inf => AluDBM.PosInf
      | IntRep.LT c => AluDBM.Fin c
      | IntRep.LTE c => AluDBM.Fin c

  fun ext_of_neg e =            (* k_neg entry (<, -U(x)) -> U(x) *)
    case Entry.to_int e of
        IntRep.Inf => AluDBM.PosInf
      | IntRep.LT c => AluDBM.Fin (~c)
      | IntRep.LTE c => AluDBM.Fin (~c)

  (* Soundness gates (ALU_CERTIFICATE_ADMISSION_DRAFT / feasibility study):
     - the LU abstraction is UNSOUND in the presence of DIAGONAL clock guards
       (x - y <~ c with x, y both real clocks), so reject the whole run on any;
     - non-simple clock updates (copy/shift/arbitrary) fall outside the TA_LU
       simulation proof, so reject those too (our planning nets only reset to 0). *)
  fun diag_free (rcnet : RewriteConstraintTypes.network) =
    let
      fun edge_ok (e : RewriteConstraintTypes.edge) = List.null (#g_diag e)
      fun auto_ok (_, a : RewriteConstraintTypes.automaton) =
        List.all edge_ok (#edges_in a) andalso List.all edge_ok (#edges_out a)
        andalso List.all edge_ok (#edges_internal a)
        andalso List.all edge_ok (#broadcast_in a)
        andalso List.all edge_ok (#broadcast_out a)
    in List.all auto_ok (#automata rcnet) end

  (* _urge-augmented muntax -> per-location-vector LU maps (tabulated per query
     location).  Left = MLunta parse/renaming errors; raises Fail on the soundness
     gates.  Uses the SAME AluUrgency.parse_augmented network as the successor
     relation, so the ceilings see the `_urge <= 0` invariants too. *)
  fun of_muntax (mode : bounds_mode) (dim : int) (muntax_str : string) =
    muntax_str
    |> AluUrgency.parse_augmented
    |> Either.bindR BasicSteps.construct
    |> Either.mapR (fn rcnet =>
         let
           val () =
             if diag_free rcnet then ()
             else raise Fail "model has diagonal clock guards -- aLU abstraction unsound; rejecting"
           val () =
             if #only_simple_updates rcnet then ()
             else raise Fail "model has non-simple clock updates -- outside the LU simulation; rejecting"
           val cnet =
             case mode of
                 LocalLU => LocalCeil.network true rcnet
               | GlobalM => GlobalCeil.network true rcnet
           val k_pos = #k_pos cnet
           val k_neg = #k_neg cnet
         in
           fn (L : int Array.array) =>
             let
               val ls = Vector.tabulate (dim, fn x => ext_of_pos (k_pos L x))
               val us = Vector.tabulate (dim, fn x => ext_of_neg (k_neg L x))
             in
               {l = fn x => Vector.sub (ls, x),
                u = fn x => Vector.sub (us, x)} : AluDBM.lu
             end
         end)

end

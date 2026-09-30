(* aLU-subsumption test over MLunta DBMs (UNTRUSTED SML prototype).

   Implements the O(n^2) non-convex inclusion test  Z1 <= aLU(Z2)  of Herbreteau /
   Srivathsan / Walukiewicz ("Better abstractions for timed automata"), ported from
   tchecker's `tchecker::dbm::is_alu_le` (src/dbm/dbm.cc) so the checker-side relation
   matches what `tck-reach -a aLU-covreach` uses at exploration time:

     Z1 NOT<= aLU(Z2)  iff  exists clocks x <> y (0 = zero clock included) with
        (A)  Z1(0,x) >= (<=, -U(x))
        (B)  Z2(y,x) <  Z1(y,x)
        (C)  Z2(y,x) + (<, -L(y))  <  Z1(0,x)

   with L(0) = U(0) = 0.  Both DBMs MUST be in canonical (closed/tight) form.

   Bounds come from the MLunta ceiling machinery (see alu_bounds.sml), which bottoms out
   at 0 rather than -oo, so the tchecker "no bound" (-oo) skip cases never arise; a bound
   CAN be +oo (Entry Inf ceiling), in which direction the test only gets FINER (closer to
   plain inclusion), never coarser -- fail-closed.

   This module is part of the untrusted harness: an "accepted" verdict here is NOT a
   machine-checked proof (that is the verified Munta checker); it is the executable
   prototype of the FEASIBILITY_alu_subsumption.md checker generalization. *)

structure AluDBM =
struct

  (* clock bound: finite or +oo (MLunta ceilings never produce -oo; they init at 0) *)
  datatype ext = Fin of int | PosInf

  (* per-target-location bound maps, indexed 0..dim-1 (0 = zero clock) *)
  type lu = {l : int -> ext, u : int -> ext}

  (* a canonical DBM as a flat vector of IntRep bounds, row-major, dim x dim *)
  type mat = {dim : int, entries : IntRep.t Vector.vector}

  fun sub ({dim, entries} : mat) i j = Vector.sub (entries, i * dim + j)

  fun of_rows (rows : IntRep.t list list) : mat =
    let val dim = List.length rows
    in {dim = dim, entries = Vector.fromList (List.concat rows)} end

  (* bound comparisons / addition: Entry.t = IntRep.t (transparent), so the MLunta
     entry operations apply directly *)
  fun blt (x, y) = Entry.|<| (x, y)
  val badd = Entry.add

  (* Z1 <= aLU(Z2) ?  Both mats must share dim and be canonical. *)
  fun is_alu_le ({l, u} : lu) (z1 : mat) (z2 : mat) : bool =
    let
      val dim = #dim z1
      (* (A): Z1(0,x) >= (<=, -U(x)); with U(x) = +oo the RHS is bottom, so A holds *)
      fun condA x =
        case u x of
            PosInf => true
          | Fin ux => not (blt (sub z1 0 x, IntRep.LTE (~ux)))
      (* (B) /\ (C) for a fixed x over y *)
      fun condBC x y =
        y <> x andalso
        let val z2yx = sub z2 y x in
          blt (z2yx, sub z1 y x) andalso
          (case l y of
               (* (<, -oo) drags the sum to bottom whenever Z2(y,x) is finite,
                  which (B) guarantees, so (C) holds *)
               PosInf => true
             | Fin ly => blt (badd z2yx (IntRep.LT (~ly)), sub z1 0 x))
        end
      fun existsBelow n p =
        let fun go i = i < n andalso (p i orelse go (i + 1)) in go 0 end
      fun bad x = condA x andalso existsBelow dim (condBC x)
    in
      #dim z2 = dim andalso not (existsBelow dim bad)
    end

end

(* UNTRUSTED in-process aLU certificate checker (SML only -- no Isabelle involved).

   Executable prototype of the FEASIBILITY_alu_subsumption.md checker generalization:
   admit tck-reach `aLU-covreach` certificates, whose passed sets are closed only under
   aLU subsumption (Z <= aLU(Z')), not under the plain zone inclusion the verified Munta
   checker (`convert_check`) requires.

   The check mirrors the verified checker's three obligations (Unreachability_Misc's
   certify_unreachable), with MLunta's product construction as the successor relation E
   and the aLU test of AluDBM as the subsumption preorder:

     1. INIT     the initial state's zone is aLU-covered by some stored zone at the
                 initial location;
     2. INVARIANT  for every stored (l, Z) and every successor (l', S) in E(l, Z):
                 S is empty, or S <= aLU_{LU(l')}(Z'') for some stored Z'' at l';
     3. TARGET   no stored state satisfies the reachability formula's target predicate.

   Certificate, model, and renaming all come from the SAME MLunta parse/index convention
   (parse_rename wrote the renaming convert_certificate.py used), so the deserialized
   locations / variables / clock indices line up with MLunta's internal Location keys
   without any re-renaming.  Stored DBMs are closed (Floyd-Warshall) after deserialization
   -- convert_certificate.py leaves unconstrained entries at oo, so they arrive untight.

   TRUST STATUS: everything here is untrusted.  "ACCEPTED" is evidence the certificate
   is aLU-admissible (and the intended verified generalization would accept it), NOT a
   machine-checked unsolvability proof.  A verified verdict still requires the Munta
   checker (plain inclusion certificates) or the future aLU-extended Isabelle checker. *)

structure AluCertify =
struct

  structure D = Mlunta.D
  structure Basic = BasicSetup(D)

  (* deserializer instantiated with MLunta's own entry representation (native ints) *)
  structure MBound : BOUND =
  struct
    type bound = IntRep.t
    type isabelle_int = int
    type isabelle_nat = int
    fun isabelle_int n = n
    fun isabelle_nat n = n
    val magic_number = 42
    fun lt n = IntRep.LT n
    fun lte n = IntRep.LTE n
    val inf = IntRep.Inf
  end
  structure Deser = Deserializer64Bit(MBound)

  val array_to_list = Array.foldr (op ::) []

  fun chunk n xs =
    let
      fun go [] rows = List.rev rows
        | go ys rows = go (List.drop (ys, n)) (List.take (ys, n) :: rows)
    in go xs [] end

  fun read_certificate path
      : ((int list * int list) * IntRep.t list list) list option =
    let
      val strm = BinIO.openIn path
      val r = Deser.deserialize strm false
      val _ = BinIO.closeIn strm
    in
      case r of
          SOME (Deser.Reachable_Set x) => SOME x
        | SOME (Deser.Buechi_Set _) => NONE
        | NONE => NONE
    end

  (* one stored zone: the DBM (for successor generation) + its flat form (for aLU) *)
  type stored_zone = D.t * AluDBM.mat

  (* Pad a (dim-1) x (dim-1) certificate DBM with an unconstrained `_urge` row/column
     at the LAST index (the augmented model's extra clock, see alu_urgency.sml):
     (i, u) = oo, (u, j) = oo, (u, u) = (<=, 0), (0, u) = (<=, 0)  [_urge >= 0].
     A sound over-approximation of the stored zone in the _urge dimension. *)
  fun pad_urge dim (rows : IntRep.t list list) : IntRep.t list list =
    let
      fun pad_row i r = r @ [if i = 0 then IntRep.LTE 0 else IntRep.Inf]
      val urge_row =
        List.tabulate (dim, fn j => if j = dim - 1 then IntRep.LTE 0 else IntRep.Inf)
    in
      List.foldr (fn (r, (i, acc)) => (i - 1, pad_row i r :: acc))
        (dim - 2, [urge_row]) rows
      |> #2
    end

  fun close_zone dim (flat : IntRep.t list) : stored_zone option =
    let
      val len = List.length flat
      val rows =
        if len = dim * dim then chunk dim flat
        else if len = (dim - 1) * (dim - 1) then pad_urge dim (chunk (dim - 1) flat)
        else
          raise Fail ("certificate DBM has " ^ Int.toString len
                      ^ " entries, expected " ^ Int.toString (dim * dim)
                      ^ " or " ^ Int.toString ((dim - 1) * (dim - 1))
                      ^ " (clock-dimension skew between model and certificate)")
      val zd = D.close (D.from_int_rep_list rows)
    in
      if D.empty zd then NONE
      else SOME (zd, AluDBM.of_rows (D.to_int_rep_list zd))
    end

  fun loc_key (locs : int list, vars : int list) : Network.location =
    (Array.fromList locs, Array.fromList vars)

  fun key_of_loc ((l, vs) : Network.location) =
    (array_to_list l, array_to_list vs)

  fun loc_to_string (locs, vars) =
    "<[" ^ String.concatWith "," (List.map Int.toString locs) ^ "], ["
    ^ String.concatWith "," (List.map Int.toString vars) ^ "]>"

  (* result: accepted?, plus diagnostics *)
  fun check_certificate {muntax_str : string, cert_path : string} : bool =
    let
      val bounds_mode = AluBounds.mode_from_env ()
      val () = Log.info ("aLU bounds mode: " ^ AluBounds.mode_to_string bounds_mode)

      (* construct from the _urge-AUGMENTED parse (alu_urgency.sml) so urgent
         locations genuinely stop time in the successor relation *)
      val system =
        case muntax_str
             |> AluUrgency.parse_augmented
             |> Either.bindR (Mlunta.Construction.construct true)
             |> Either.mapL Mlunta.Construction.print_log of
            Either.Right (_, system) => system
          | Either.Left _ => raise Fail "MLunta could not parse/construct the model"
      val dim = IndexDict.size (#clock_dict system)

      val lu_of =
        case AluBounds.of_muntax bounds_mode dim muntax_str of
            Either.Right f => f
          | Either.Left _ => raise Fail "MLunta could not derive LU ceilings"

      val cert =
        case TCheckerCertify.timeStage "alu-deserialize" (fn () =>
               read_certificate cert_path) of
            SOME c => c
          | NONE => raise Fail "could not deserialize certificate (malformed or Buechi)"

      (* stored set: per state the Location key + non-empty closed zones *)
      val stored =
        TCheckerCertify.timeStage "alu-close" (fn () =>
          List.map (fn (k, dbms) =>
              (k, loc_key k, List.mapPartial (close_zone dim) dbms))
            cert)
      val n_states = List.length stored
      val n_zones = List.foldl (fn ((_, _, zs), n) => n + List.length zs) 0 stored
      val () = Log.info ("certificate: " ^ Int.toString n_states ^ " discrete states, "
                         ^ Int.toString n_zones ^ " non-empty zones, dim " ^ Int.toString dim)

      val passed =
        Isa_Map.hashmap_of_list1 (List.map (fn (k, _, zs) => (k, zs)) stored)

      val setup = Basic.initial_setup system
      val P = Basic.P setup
      (* MLunta initializes all discrete variables to 0, but the muntax convention
         (NetworkConversion + convert.py, and the numeric nets' point-bounded static
         fluents) is the declared LOWER bound -- repair the initial state's var array *)
      val initial =
        let
          val ((l0, _), z0) = Basic.initial setup
          val var_bounds = #var_bounds system
          val vars0 =
            Array.tabulate (IndexDict.size var_bounds,
                            fn i => #1 (IndexDict.find i var_bounds))
        in ((l0, vars0), z0) end
      val trans = #trans system

      val n_failures = Unsynchronized.ref 0
      val max_report = 5
      fun report_failure msg =
        let val n = Unsynchronized.inc n_failures
        in
          if n <= max_report then Log.info ("aLU-check FAIL: " ^ msg)
          else if n = max_report + 1 then Log.info "aLU-check FAIL: (further failures suppressed)"
          else ()
        end

      fun covered (l' : Network.location) (s : D.t) : bool =
        let
          val lu = lu_of (#1 l')
          val smat = AluDBM.of_rows (D.to_int_rep_list s)
        in
          case Isa_Map.hm_lookup1 (key_of_loc l') passed of
              NONE => false
            | SOME zs => List.exists (fn (_, zmat) => AluDBM.is_alu_le lu smat zmat) zs
        end

      (* 1. INIT *)
      val init_ok =
        D.empty (Network.zone initial)
        orelse covered (Network.discrete initial) (Network.zone initial)
      val () = if init_ok then ()
               else report_failure ("initial state "
                      ^ loc_to_string (key_of_loc (Network.discrete initial))
                      ^ " not covered")

      val debug = case OS.Process.getEnv "ALU_DEBUG" of SOME "1" => true | _ => false

      (* 2. INVARIANT + 3. TARGET, fused over the stored set *)
      fun succs_ok k l (zd, _) =
        List.all (fn (l', s) =>
            D.empty s orelse covered l' s
            orelse
            let
              val present = Option.isSome (Isa_Map.hm_lookup1 (key_of_loc l') passed)
              val () = report_failure
                ("successor at " ^ loc_to_string (key_of_loc l')
                 ^ (if present then " present but no stored zone aLU-covers it"
                    else " ABSENT from the certificate")
                 ^ " (source " ^ loc_to_string k ^ ")")
              val () =
                if debug then
                  (Log.info ("successor zone:\n" ^ D.to_string s);
                   case Isa_Map.hm_lookup1 (key_of_loc l') passed of
                       NONE => ()
                     | SOME zs =>
                         List.app (fn (z, _) =>
                             Log.info ("stored zone:\n" ^ D.to_string z)) zs)
                else ()
            in false end)
          (trans (l, zd))

      fun state_ok (k, l, zs) =
        (case zs of
             [] => true
           | (zd, _) :: _ =>
               not (P (l, zd))
               orelse (report_failure ("stored state " ^ loc_to_string k
                                       ^ " satisfies the target"); false))
        andalso List.all (succs_ok k l) zs

      (* early exit on the first failing state (majsp-scale certs make a full
         diagnostic sweep after a failure too expensive) *)
      val closed_ok =
        TCheckerCertify.timeStage "alu-check" (fn () =>
          List.foldl (fn (st, ok) => ok andalso state_ok st) init_ok stored)
    in
      closed_ok
    end

  fun check_and_report args =
    let
      val ok = check_certificate args
                 handle Fail msg => (Log.info ("aLU-check error: " ^ msg); false)
                      | Subscript => (Log.info "aLU-check error: index skew (Subscript)"; false)
    in
      if ok then
        println "aLU certificate ACCEPTED (UNTRUSTED SML check -- not a verified verdict)."
      else
        println "aLU certificate REJECTED (untrusted SML check).";
      ok
    end

end

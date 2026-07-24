(* In-process VERIFIED certification with tck-reach as the certificate ORACLE.

   MLunta (the old in-process checker) has a bug, so we do NOT check with it.  Instead we run
   Munta's own VERIFIED certificate checker (Converter.parse_convert_check -- exactly the entry the
   external `muntac` binary uses) IN-PROCESS, feeding it a certificate produced externally by
   tck-reach as an ORACLE:

     0. PRINT  -- build the muntax net from the ground PDDL (check_and_make_network_opt +
                  NetworkConversion.convert_network) and its renaming (parse_rename).
     1. WAIT   -- run the external tck-reach pipeline (TCheckerCertify.make_cert) -> binary cert.
     2. READ   -- deserialize the binary cert into a Converter.inta state_space, then run
                  Converter.parse_convert_check on the (model, renaming) JSON strings + that
                  state_space.  parse_convert_check parses the renaming ITSELF, so its index
                  convention matches the tck-reach cert exactly (no MLunta<->Munta renaming skew).

   parse_convert_check is Munta's verified checker: if it accepts the certificate the reachability
   formula is unreachable, and by the (Isabelle-proved) reduction that means the ground planning
   problem has no valid plan.  A bad oracle only yields a rejected certificate. *)

structure InProcessCertify =
struct

  (* Deserializer Bound instantiated with Converter's certificate-checker types, so
     DeserializeCert.Reachable_Set x : (((inta list * inta list) * inta dBMEntry list list) list)
     is exactly Converter.Reachable_Set's argument (a Converter.inta state_space). *)
  structure Bound : BOUND = struct
    type bound = Converter.inta Converter.dBMEntry
    type isabelle_int = Converter.inta
    type isabelle_nat = Converter.nat
    fun isabelle_int n = Converter.Int_of_integer n
    fun isabelle_nat n = Converter.nat_of_integer n
    val magic_number = 42
    fun lte n = Converter.Le (Converter.Int_of_integer n)
    fun lt  n = Converter.Lt (Converter.Int_of_integer n)
    val inf = Converter.INF
  end

  structure DeserializeCert = Deserializer64Bit(Bound)
  structure CertConv = CertificateConversion(MLuntaAdapter.Setup)

  fun read_certificate_from_file is_buechi f =
    let val file = BinIO.openIn f
        val r = DeserializeCert.deserialize file is_buechi
        val _ = BinIO.closeIn file
    in case r of
         SOME (DeserializeCert.Reachable_Set x) => SOME (Converter.Reachable_Set x)
       | SOME (DeserializeCert.Buechi_Set x)    => SOME (Converter.Buechi_Set x)
       | NONE => NONE
    end

  (* NB: this export's parallel Impl3 (rename_check3) enters certificate_checker but its verdict
     continuation does not fire in-process; Impl1/Impl2/Debug all print the verdict correctly.  Map
     "3" onto Impl2 so -mode 3 keeps working; default to Impl2 too. *)
  fun mode_of_str "0" = Converter.Debug
    | mode_of_str "1" = Converter.Impl1
    | mode_of_str "2" = Converter.Impl2
    | mode_of_str "3" = Converter.Impl2
    | mode_of_str _   = Converter.Impl2

  (* The ORACLE certifier passed into the VERIFIED capstone
     (Converter.check_and_cert_numeric_pddl_problem_no_return): receives the built net
     IN-PROCESS (so the explicit initial variable values survive -- the muntax JSON cannot
     express them), writes the muntax + renaming for the external toolchain, runs tck-reach,
     and returns the renaming functions + deserialized certificate state space.  Every
     external stage prints its "+ STAGE <name>: <ms> ms" line; the closure accumulates its
     own wall time in `oracle_ms` so the caller can report the verified-check remainder.
     A bad oracle only yields a rejected certificate (fail-closed). *)
  fun oracle_certifier {pkg_root, tck_reach_bin, show_cert, model, renaming, cert, oracle_ms} net =
    let
      val t0 = Timer.startRealTimer ()
      (* write muntax, sanitise identifiers (tck-reach forbids '-') *)
      val _ = NetworkConversion.convert_network show_cert model net
      val _ = TCheckerCertify.sanitize_file model
      val muntax = TextIOUtil.read_file model
      (* renaming functions from MLunta's construct (construct only, NOT its retired checker);
         parse_rename writes the renaming file convert_certificate.py consumes -- both come
         from the same MLunta parse, so they are name-consistent with the tck certificate *)
      val ren_opt =
        TCheckerCertify.timeStage "renaming" (fn () =>
          (case MLuntaAdapter.parse_construct true muntax of
              Either.Right (_, system) => SOME (CertConv.convert_renaming system)
            | Either.Left _ => NONE))
      val _ = MLuntaAdapter.parse_rename renaming muntax
      (* external tck-reach -> binary munta certificate (stages convert-tck / tck / convert-back) *)
      val _ = TCheckerCertify.make_cert
                {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin,
                 muntax = model, renaming = renaming, cert = cert, buechi = false}
      val ss_opt = read_certificate_from_file false cert
      val () = oracle_ms := Time.toMilliseconds (Timer.checkRealTimer t0)
    in
      case (ren_opt, ss_opt) of
          (SOME r, SOME ss) => SOME (r, ss)
        | _ => NONE
    end

  (* full driver: ground PDDL -> muntax -> tck-reach oracle -> in-process verified check. *)
  fun check_and_cert {pkg_root, tck_reach_bin}
                     domain problem model renaming cert mode_str nthreads show_cert =
    let
      val parsed_prob = PddlParser.get_prob domain problem
      val mode = mode_of_str mode_str
      val nthreads_n =
        Converter.nat_of_integer (Option.getOpt (Int.fromString nthreads, 1))
    in
      case Converter.check_and_make_network_opt (Grounder.ground_problem parsed_prob) of
        NONE => Log.info "Admission check rejected the problem (no network built)."
      | SOME net =>
        let
          (* 0. PRINT: write the muntax net + sanitise for tck-reach, then its renaming. *)
          val _ = NetworkConversion.convert_network show_cert model net
          val _ = TCheckerCertify.sanitize_file model
          val _ = MLuntaAdapter.parse_rename renaming (TextIOUtil.read_file model)
          (* 1. WAIT: external tck-reach -> binary munta certificate. *)
          val _ = TCheckerCertify.make_cert
                    {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin,
                     muntax = model, renaming = renaming, cert = cert, buechi = false}
          (* 2. READ: deserialize the binary cert -> state_space. *)
          val ss_opt = read_certificate_from_file false cert
        in
          case ss_opt of
            NONE => Log.info "Failed to read certificate (malformed)."
          | SOME state_space =>
            let
              val model_str    = TextIOUtil.read_file model
              val renaming_str = TextIOUtil.read_file renaming
            in
              (* 3. in-process VERIFIED check (Munta's parse_convert_check -- same as external muntac). *)
              Converter.parse_convert_check mode nthreads_n false model_str renaming_str
                state_space show_cert ()
            end
        end
    end
end

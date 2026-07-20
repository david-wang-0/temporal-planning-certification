(* In-process VERIFIED certification with tck-reach as the certificate ORACLE.

   MLunta (the old in-process checker) has a bug, so we do NOT use it to CHECK.
   Instead we keep the Isabelle-verified Converter.check_and_cert_pddl_problem_no_return
   running in-process and feed it a `certifier` (the oracle f) that:

     0. PRINT  -- write the muntax network (NetworkConversion.convert_network) + renaming.
     1. WAIT   -- run the external tck-reach pipeline (TCheckerCertify.make_cert) to produce
                  the binary munta certificate.
     2. READ   -- deserialize the binary cert into an int state_space (Deserializer64Bit with
                  Converter's checker types), and build the renaming from MLunta's *construct*
                  (construct only -- NOT the buggy check) via CertificateConversion.convert_renaming.

   The verified convert_check inside check_and_cert_pddl_problem then VALIDATES the certificate,
   so a bad/incomplete oracle only fails validation -- soundness is preserved
   (check_and_cert_pddl_problem_okay: a "Sat" verdict means no valid ground plan exists). *)

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

  fun mode_of_str "0" = Converter.Debug
    | mode_of_str "1" = Converter.Impl1
    | mode_of_str "2" = Converter.Impl2
    | mode_of_str "3" = Converter.Impl3
    | mode_of_str _   = Converter.Impl1

  (* the ORACLE certifier: clocks_name_network -> (isa_renaming * isa_state_space) option *)
  fun oracle_certifier {pkg_root, tck_reach_bin, extra_lu, show_cert, model, renaming, cert} net =
    let
      (* 0. PRINT: write muntax, sanitise identifiers (tck-reach forbids '-') *)
      val _ = NetworkConversion.convert_network show_cert model net
      val _ = TCheckerCertify.sanitize_file model
      val muntax = TextIOUtil.read_file model
      (* renaming from MLunta's construct (safe: construct only, not the buggy check) *)
      val ren_opt =
        (case MLuntaAdapter.parse_construct extra_lu muntax of
            Either.Right (_, system) => SOME (CertConv.convert_renaming system)
          | Either.Left _ => NONE)
      (* write the renaming file convert_certificate.py consumes (name-consistent with tck) *)
      val _ = MLuntaAdapter.parse_rename renaming muntax
      (* 1. WAIT: external tck-reach -> binary munta certificate *)
      val _ = TCheckerCertify.make_cert
                {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin,
                 muntax = model, renaming = renaming, cert = cert, buechi = false}
      (* 2. READ: deserialize the binary cert -> int state_space *)
      val ss_opt = read_certificate_from_file false cert
    in
      case (ren_opt, ss_opt) of
          (SOME r, SOME ss) => SOME (r, ss)
        | _ => NONE
    end

  (* full driver: build the net from PDDL, run the in-process verified check with the oracle. *)
  fun check_and_cert {pkg_root, tck_reach_bin, extra_lu}
                     domain problem model renaming cert mode_str nthreads show_cert =
    let
      val parsed_prob = PddlParser.get_prob domain problem
      val mode = mode_of_str mode_str
      val show_cert = (case mode of Converter.Debug => true | _ => show_cert)
      val nthreads_n =
        Converter.nat_of_integer (Option.getOpt (Int.fromString nthreads, 1))
      val f = oracle_certifier
                {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin, extra_lu = extra_lu,
                 show_cert = show_cert, model = model, renaming = renaming, cert = cert}
    in
      Converter.check_and_cert_pddl_problem_no_return parsed_prob mode nthreads_n f show_cert ()
    end
end

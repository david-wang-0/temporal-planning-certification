val usage = "Usage: $ plan_cert " ^ "\n" ^
            "[-domain <pddl domain file>] " ^ "\n" ^
            "[-problem <pddl problem file>] " ^ "\n" ^
            "-model <model (input/output) path> " ^ "\n" ^
            "-certificate <certificate (output) path> " ^ "\n" ^
            "-renaming <renaming (output) path> " ^ "\n" ^
            "-mode <0 | 1 | 2 | 3> (where 0 is debug and 1 - 3 are implementations) " ^ "\n" ^
            "-extra <lu | local> " ^ "\n" ^
            "[-compression <compression level>] " ^ "\n" ^
            "[-certify <certifier version>] " ^ "\n" ^
            "[-num-threads <number of threads>]" ^ "\n" ^
            "[-show-cert <1>]" ^ "\n"

(* Very low prio to-do: print the generated network *)

fun dissect_arguments p args =
    let
      fun get' (flag::arg::args) = if p flag then SOME (arg) else
                                   get' args |
          get' (_) = NONE
    in
      get' args
    end

fun find_flag p args = List.exists p args

datatype extrapolation =
         Local |
         LU

(* Munta model-checking mode retired with the in-process certifier; kept as a plain string. *)
fun mode_from_str s = s
fun extra_from_str "lu" = SOME LU |
    extra_from_str "local" = SOME Local |
    extra_from_str _ = NONE

fun flags args =
    let
        val domain =
            dissect_arguments
                (fn "-domain" => true | "-d" => true | _ => false) args
        val problem =
            dissect_arguments
                (fn "-problem" => true | "-p" => true | _ => false) args
        val network =
            dissect_arguments
                (fn "-model" => true | "-m" => true | _ => false) args
        val renaming_path =
            dissect_arguments
                (fn "-renaming" => true | "-r" => true | _ => false) args
        val cert_path =
            dissect_arguments
                (fn "-certificate" => true | "-c" => true | _ => false) args
        val compression =
            dissect_arguments
                (fn "-compression" => true | "-cl" => true | _ => false) args
        val certification =
            dissect_arguments
                (fn "-certify" => true | "-cc" => true | _ => false) args
        val num_threads =
            dissect_arguments
                (fn "-num-threads" => true | "-n" => true | _ => false) args

        val show_cert =
            (case (dissect_arguments (fn "-show-cert" => true | "-S" => true | _ => false) args) of 
                NONE => false |
                SOME x => true)
        

        val is_mode = (fn "-mode" => true | "-M" => true | _ => false)
        val mode = 
            (case dissect_arguments is_mode args of
                NONE => (print "ok"; "1") |
                SOME str => str)
            |> mode_from_str

        val is_extra = fn "-extra" => true | "-e" => true | _ => false
        val extra =
            case dissect_arguments is_extra args of
                NONE => (print "ok"; SOME Local) |
                SOME str => extra_from_str str
    in
      (domain, problem, network, renaming_path, cert_path, extra, compression, certification,
       num_threads, mode, show_cert)
    end

fun read_json json = TextIOUtil.read_file json


val log_renaming_file = Log.log "Renaming File"
val log_certificate_file = Log.log "Certificate File"
val log_problem_file = Log.log "Problem File"
val log_domain_file = Log.log "Domain File"
val log_network_file = Log.log "Network File"
val log_compression = Log.log "Compression Level"
val log_certification = Log.log "Certification Level"
val log_num_threads = Log.log "Number of Threads"
fun log_extra Local = Log.log "Extrapolation" "local ceilings"
  | log_extra LU    = Log.log "Extrapolation" "local lu-ceilings"
fun log_mode _ = ()  (* mode retired with the in-process certifier *)
fun log_show_cert true = Log.log "Show Certificate" "true"
  | log_show_cert false = Log.log "Show Certificate" "false"

fun log_config (domain, problem, network, renaming, cert, extra, compression, certification, num_threads, mode, show_cert) =
    (
      log_extra extra;
      log_domain_file domain;
      log_problem_file problem;
      log_network_file network;
      log_renaming_file renaming;
      log_certificate_file cert;
      log_compression compression;
      log_certification certification;
      log_num_threads num_threads;
      log_mode mode;
      log_show_cert show_cert
    )

fun log_model_checking_config (network, renaming, cert, extra, compression, certification, num_threads) =
    (
      log_extra extra;
      log_network_file network;
      log_renaming_file renaming;
      log_certificate_file cert;
      log_compression compression;
      log_certification certification;
      log_num_threads num_threads
    )

fun log_conversion_config (domain, problem, network) =
    (
      log_domain_file domain;
      log_problem_file problem;
      log_network_file network
    )

fun log_renaming_config (network, renaming) =
    (
      log_network_file network;
      log_renaming_file renaming
    )

fun log_config1 (extra, domain, problem) =
    (log_extra extra; log_domain_file domain; log_problem_file problem)

fun opt_from_either (Either.Left _) = NONE |
    opt_from_either (Either.Right x) = SOME x

(* opt_from_nested_either removed (only used by the retired in-process cert) *)

(* In-process MLunta certification retired -- superseded by the external tck-reach + muntac flow
   (certify_tchecker / TCheckerCertify.certify_via_tchecker).  The old path used Converter symbols
   (check_and_cert_pddl_problem_no_return, Reachable_Set, DBMEntry, Impl modes, CertificateConversion)
   that need the (arity-conflicting) certificate stack, not part of the current export. *)
fun check_and_cert_problem _ _ _ _ _ _ _ _ _ _ _ =
    exit_fail "in-process certification retired; use  -certify tchecker  (external tck-reach + muntac)"

fun parse_check_and_cert_network _ _ _ _ _ _ _ =
    exit_fail "in-process certification retired; use  -certify tchecker  (external tck-reach + muntac)"

fun make_network domain problem model =
    let
        val _ = log_conversion_config (domain, problem, model)
        val parsed_prob = PddlParser.get_prob domain problem 
        val res = Converter.check_and_make_network_opt parsed_prob 
            |> Option.map (NetworkConversion.convert_network true model)
        val _ = res
    in ()
    end

fun make_renaming model renaming =
    (
        log_renaming_config (model, renaming);
        MLuntaAdapter.parse_rename renaming (read_json model);
        ()
    )

fun getEnvDefault k d = case OS.Process.getEnv k of SOME x => x | NONE => d

(* Part B: external tchecker/muntac certification of the PROPOSITIONAL net.  Writes
   muntax + renaming, then runs convert_models/main.py (-> tchecker -> munta cert) and
   muntac, printing the verdict.  Replaces the non-terminating in-process MLunta path.
   Tool locations come from env with repo-relative defaults: TCHECKER_PKG_ROOT (".",
   the directory containing the convert_models package), TCK_REACH_BIN (./tck-reach),
   MUNTAC_BIN (./muntac). *)
fun certify_tchecker domain problem model renaming cert =
    let
        val () = make_network domain problem model
        (* make identifiers tck-reach-safe (hyphen -> underscore) before the renaming is
           derived, so muntax + renaming + tck stay name-consistent *)
        val () = TCheckerCertify.sanitize_file model
        val () = make_renaming model renaming
        val pkg_root      = getEnvDefault "TCHECKER_PKG_ROOT" "."
        val tck_reach_bin = getEnvDefault "TCK_REACH_BIN" "./tck-reach"
        val muntac_bin    = getEnvDefault "MUNTAC_BIN" "./muntac"
        val v = TCheckerCertify.certify_via_tchecker
                  {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin, muntac_bin = muntac_bin,
                   muntax = model, renaming = renaming, cert = cert, buechi = false}
    in
        println ("Verdict: " ^ TCheckerCertify.verdict_to_string v)
    end

(* Part B': the SAME external tck-reach oracle, but the certificate is CHECKED IN-PROCESS by
   the Isabelle-verified Converter.check_and_cert_pddl_problem_no_return (its convert_check),
   not by an external muntac.  tck-reach only PRODUCES the certificate (oracle); the verified
   in-process checker validates it -> "The planning problem is unsolvable." on Sat. *)
fun certify_inprocess domain problem model renaming cert extra num_threads mode show_cert =
    let
        val () = log_conversion_config (domain, problem, model)
        val pkg_root      = getEnvDefault "TCHECKER_PKG_ROOT" "."
        val tck_reach_bin = getEnvDefault "TCK_REACH_BIN" "./tck-reach"
        val _ = extra
        val _ = InProcessCertify.check_and_cert
                  {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin}
                  domain problem model renaming cert mode num_threads show_cert
    in () end

(* Numeric bound-inference self-test: exercises the two extra Isabelle code exports
   (NumericBoundInference compute side + NumericProjection reduction side) linked into
   this binary alongside Converter, on hand-built draft data -- the guarded counter
   `counter := counter+1` guarded by `counter <= 0`, init 0 (box [0,1]).  Proves the
   three exports co-link and run; the full -numeric mode additionally needs a
   Converter->NumericProjection AST coercion and the numeric-net code-gen. *)
fun numeric_selftest () =
    let
        fun npi n = NumericProjection.Int_of_integer (IntInf.fromInt n)
        val guarded : NumericBoundGlue.draft =
          (["counter"],
           ([([NumericProjection.GLe_i ("counter", npi 0)],
              [("counter",
                NumericProjection.EAdd (NumericProjection.EV "counter",
                                        NumericProjection.EC (npi 1)))])],
            [("counter", npi 0)]))
        fun showBox NONE = "<NONE: unbounded / out of scope>"
          | showBox (SOME box) =
              String.concatWith ", "
                (List.map (fn (f, (lo, hi)) =>
                   f ^ " in [" ^ IntInf.toString (NumericProjection.integer_of_int lo)
                   ^ "," ^ IntInf.toString (NumericProjection.integer_of_int hi) ^ "]") box)
    in
        println ("numeric bound-inference self-test: "
                 ^ showBox (NumericBoundGlue.infer_box guarded))
    end

fun check args =
    case args of
        (_, _, _, _, _, _, _, SOME "numeric-selftest", _, _, _) =>
            numeric_selftest () |
        (SOME domain, SOME problem, SOME model, SOME renaming, SOME cert, _, _,
         SOME "tchecker", _, _, _) =>
            certify_tchecker domain problem model renaming cert |
        (SOME domain, SOME problem, SOME model, SOME renaming, SOME cert, SOME extra, _,
         SOME "inprocess", num_threads, mode, show_cert) =>
            certify_inprocess domain problem model renaming cert extra
              (the_default "1" num_threads) mode show_cert |
        (SOME domain, SOME problem, SOME model, SOME renaming, SOME cert, SOME extra, compression,
         certification, num_threads, mode, show_cert) =>
            check_and_cert_problem
                domain
                problem
                model
                renaming
                cert
                extra
                (the_default "0" compression)
                (the_default "0" certification)
                (the_default "1" num_threads)
                mode
                show_cert |
        (NONE, NONE, SOME model, SOME renaming, SOME cert, SOME extra, compression,
         certification, num_threads, mode, show_cert) => 
            parse_check_and_cert_network
                model
                renaming
                cert
                extra
                (the_default "0" compression)
                (the_default "0" certification)
                (the_default "1" num_threads) |
        (SOME domain, SOME problem, SOME model, _, _, _, _, _, _, _, _) => 
            make_network
                domain
                problem
                model |
        (NONE, NONE, SOME model, SOME renaming, _, _, _, _, _, _, _) => 
            make_renaming
                model
                renaming |
        _ => Exn.error usage handle Exn.ERROR msg => (println msg)

fun main () =
    flags (CommandLine.arguments ())
    |> Benchmark.time_it check
    |> Benchmark.add_time (apfst (Log.time "Total Time: ") #> snd)
    handle Fail s => println s
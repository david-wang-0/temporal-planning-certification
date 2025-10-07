val usage = "Usage: $ plan_cert " ^ "\n" ^
            "-domain <pddl domain file> " ^ "\n" ^
            "-problem <pddl problem file> " ^ "\n" ^
            "-certificate <certificate (output) path> " ^ "\n" ^
            "-renaming <renaming (output) path> " ^ "\n" ^
            "-mode <0 | 1 | 2 | 3> (where 0 is debug and 1 - 3 are implementations) " ^ "\n" ^
            "-extra <lu | local> " ^ "\n" ^
            "[-compression <compression level>] " ^ "\n" ^
            "[-certify <certifier version>] " ^ "\n" ^
            "[-num-threads <number of threads>]" ^ "\n" ^
            "[-show-cert]" ^ "\n"

(* Very low prio to-do: print the generated network *)

fun dissect_arguments p args =
    let
      fun get' [] = NONE |
          get' (flag::arg::args) = if p flag then SOME (arg) else
                                   get' args |
          get' (_::_) = NONE
    in
      get' args
    end

fun find_flag p args = List.exists p args

datatype extrapolation =
         Local |
         LU

fun mode_from_str s =
    let val n = Int.fromString s |> the
    in 
        if n > 4 then
            raise Fail "Implementation needs to be in the range 0 to 4"
        else if n = 0 then Model_Checker.Debug
        else if n = 1 then Model_Checker.Impl1
        else if n = 2 then Model_Checker.Impl2
        else if n = 3 then Model_Checker.Impl3
        else raise Fail "Büchi model checking not supported"
    end
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
            find_flag
                (fn "-show-cert" => true | "-S" => true | _ => false) args
        

        val is_mode = (fn "-mode" => true | "-M" => true | _ => false)
        val mode = 
            (case dissect_arguments is_mode args of
                NONE => (print "ok"; "3") |
                SOME str => str)
            |> mode_from_str

        val is_extra = fn "-extra" => true | "-e" => true | _ => false
        val extra =
            case dissect_arguments is_extra args of
                NONE => (print "ok"; SOME Local) |
                SOME str => extra_from_str str
    in
      (domain, problem, extra, renaming_path, cert_path, compression, certification,
       num_threads, mode, show_cert)
    end

fun read_json json = TextIOUtil.read_file json


val log_renaming_file = Log.log "Renaming File"
val log_certificate_file = Log.log "Certificate File"
val log_problem_file = Log.log "Problem File"
val log_domain_file = Log.log "Domain File"
val log_compression = Log.log "Compression Level"
val log_certification = Log.log "Certification Level"
val log_num_threads = Log.log "Number of Threads"
fun log_extra Local = Log.log "Extrapolation" "local ceilings"
  | log_extra LU    = Log.log "Extrapolation" "local lu-ceilings"
fun log_mode Model_Checker.Debug = Log.log "Mode" "Debug"
  | log_mode Model_Checker.Impl1 = Log.log "Mode" "Implementation 1"
  | log_mode Model_Checker.Impl2 = Log.log "Mode" "Implementation 2"
  | log_mode Model_Checker.Impl3 = Log.log "Mode" "Implementation 3"
fun log_show_cert true = Log.log "Show Certificate" "true"
  | log_show_cert false = Log.log "Show Certificate" "false"

fun log_config (extra, domain, problem, renaming, cert, compression, certification, num_threads, mode, show_cert) =
    (
      log_extra extra;
      log_domain_file domain;
      log_problem_file problem;
      log_renaming_file renaming;
      log_certificate_file cert;
      log_compression compression;
      log_certification certification;
      log_num_threads num_threads;
      log_mode mode;
      log_show_cert show_cert
    )

fun log_config1 (extra, domain, problem) =
    (log_extra extra; log_domain_file domain; log_problem_file problem)

fun check_and_cert_network extra renaming cert compression certification num_threads model =
    (
        Par_List.set_num_threads (Int.fromString num_threads |> the);
        (case extra of
            Local => MLuntaAdapter.check_and_cert_return |
            LU => MLuntaAdapter.check_and_cert_return_lu)
        renaming
        cert
        model
        (Int.fromString compression |> the)
        (Int.fromString certification |> the)
    )

fun check_and_cert_problem extra domain problem renaming cert compression certification num_threads mode show_cert = 
    let
        val _ = log_config (extra, domain, problem, renaming, cert, compression, certification, num_threads, mode, show_cert)
        val parsedProb = PddlParser.get_prob domain problem;
        
        val certifier = 
            NetworkConversion.convert_network 
            #> (check_and_cert_network extra renaming cert compression certification num_threads)       
            #> Either.mapR CertificateConversion.convert_certificate
            #> Either.either (fn err => NONE) (fn res => SOME res);
            
        val show_cert = (case mode of Model_Checker.Debug => true | _ => show_cert);
        val f = (fn a => fn b => fn c => fn d => fn e => fn x => Either.succeed ()); (* XXX: Isabelle export*)
    in f parsedProb mode num_threads false certifier show_cert 
    end

(* 
(* Useful for testing *)
fun check_problem domain problem = (
    log_config1 (Local, domain, problem);
    let
        val parsedDom = parse_pddl_dom dom_file;
        val parsedProb = parse_pddl_prob prob_file;
    in ()
);

fun check_problem_lu extra domain problem  = (
    log_config1 (LU, domain, problem);
    let
        val parsedDom = parse_pddl_dom dom_file;
        val parsedProb = parse_pddl_prob prob_file;
    in ()
); *)


fun check args =
    case args of
        (SOME domain, SOME problem, SOME extra, SOME renaming, SOME cert, compression,
         certification, num_threads, mode, show_cert) => check_and_cert_problem
                                            extra
                                            domain
                                            problem
                                            renaming
                                            cert
                                            (the_default "0" compression)
                                            (the_default "0" certification)
                                            (the_default "1" num_threads)
                                            mode
                                            show_cert
      (* | (SOME domain, SOME problem, NONE, NONE, NONE, NONE, NONE, NONE, NONE) => check_network model
      | (SOME domain, SOME problem, SOME Local, NONE, NONE, NONE, NONE, NONE, NONE) => check_network model
      | (SOME domain, SOME problem, SOME LU, NONE, NONE, NONE, NONE, NONE, NONE) => check_network_lu model *)
      | _ => Exn.error usage

fun main () =
    flags (CommandLine.arguments ())
    |> Benchmark.time_it check
    |> Benchmark.add_time (apfst (Log.time "Total Time: ") #> snd)
    handle Exn.ERROR msg => Either.fail (println msg)

val _ = main ()
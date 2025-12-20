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

fun mode_from_str s =
    let val n = Int.fromString s |> the
    in 
        if n > 4 then
            raise Fail "Implementation needs to be in the range 0 to 4"
        else if n = 0 then Converter.Debug
        else if n = 1 then Converter.Impl1
        else if n = 2 then Converter.Impl2
        else if n = 3 then Converter.Impl3
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
fun log_mode Converter.Debug = Log.log "Mode" "Debug"
  | log_mode Converter.Impl1 = Log.log "Mode" "Implementation 1"
  | log_mode Converter.Impl2 = Log.log "Mode" "Implementation 2"
  | log_mode Converter.Impl3 = Log.log "Mode" "Implementation 3"
  | log_mode _ = Log.log "Mode" "Unknown"
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

fun log_config1 (extra, domain, problem) =
    (log_extra extra; log_domain_file domain; log_problem_file problem)

fun opt_from_either (Either.Left _) = NONE |
    opt_from_either (Either.Right x) = SOME x

val opt_from_nested_either = 
    opt_from_either
    #> Option.map opt_from_either
    #> Option.join

fun check_and_cert_network extra renaming cert compression certification num_threads model =
    let 
        val _ = Par_List.set_num_threads (Int.fromString num_threads |> the)
        val res = (case extra of
            Local => MLuntaAdapter.check_and_cert_return |
            LU => MLuntaAdapter.check_and_cert_return_lu)
            renaming
            cert
            model
            (Int.fromString compression |> the)
            (Int.fromString certification |> the)
    in res
    end

structure CertificateConversion = CertificateConversion(MLuntaAdapter.Setup)


fun check_and_cert_problem domain problem model renaming cert extra compression certification num_threads mode show_cert = 
    let
        val _ = log_config (domain, problem, model, renaming, cert, extra, compression, certification, num_threads, mode, show_cert)
        val parsed_prob = PddlParser.get_prob domain problem
        
        val certifier = 
            NetworkConversion.convert_network show_cert model
            #> (check_and_cert_network extra renaming cert compression certification num_threads) 
            #> opt_from_nested_either
            #> (Option.map CertificateConversion.convert_certificate)
            
        val show_cert = (case mode of Converter.Debug => true | _ => show_cert)
        val num_threads = num_threads |> Int.fromString |> the |> Converter.nat_of_integer
        val res = Converter.check_and_cert_pddl_problem_no_return parsed_prob mode num_threads certifier show_cert ()
    in res
    end

fun show_certificate (renaming, state_space) = 
    let 
        val (renum_vars,
            (renum_clocks,
              (renum_states,
                (inv_renum_vars,
                  (inv_renum_clocks, inv_renum_states))))) = renaming
        val state_space = case state_space of Converter.Reachable_Set s => s
        val inv_renum_states = Converter.integer_of_int #> Converter.nat_of_integer #> inv_renum_states
        val inv_renum_vars = Converter.nat_of_integer #> inv_renum_vars
        val show_states_and_vars = (fn ((states, vars), i) => 
            "Entry: " ^ Int.toString i ^ "" ^
            "\tStates: " ^
            (states
            |> map (Converter.integer_of_int #> Int.toString)
            |> ListUtils.intersperse ", " 
            |> foldr (op ^) "") ^
            "\tVars: " ^
            (vars
            |> ListUtils.zip_with_index
            |> map (fn (u, i) => inv_renum_vars i ^ "=" ^ (u |> Converter.integer_of_int |> Int.toString))
            |> ListUtils.intersperse ", " |> foldr (op ^) "") 
        )
    in
        state_space 
        |> ListUtils.zip_with_index
        |> List.map (fn ((sv, d), i) => show_states_and_vars (sv, i))
        |> ListUtils.intersperse "\n" 
        |> foldr (op ^) ""
        |> print
    end

fun parse_check_and_cert_network model renaming cert extra compression certification num_threads =
    (
        log_model_checking_config  (model, renaming, cert, extra, compression, certification, num_threads);
        Par_List.set_num_threads (Int.fromString num_threads |> the);
        (case extra of
            Local => MLuntaAdapter.parse_check_and_cert_return |
            LU => MLuntaAdapter.parse_check_and_cert_return_lu
            )
            renaming
            cert
            (read_json model)
            (Int.fromString compression |> the)
            (Int.fromString certification |> the)
        |> opt_from_nested_either
        |> Option.map (CertificateConversion.convert_certificate)
        |> Option.map (show_certificate);
        ()
    )

fun make_network domain problem model =
    let
        val _ = log_conversion_config (domain, problem, model)
        val parsed_prob = PddlParser.get_prob domain problem 
        val res = Converter.check_and_make_network_opt parsed_prob 
            |> Option.map (NetworkConversion.convert_network true model)
        val _ = res
    in ()
    end
    

fun check args =
    case args of
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
      _ => Exn.error usage handle Exn.ERROR msg => (println msg)

fun main () =
    flags (CommandLine.arguments ())
    |> Benchmark.time_it check
    |> Benchmark.add_time (apfst (Log.time "Total Time: ") #> snd)
    handle Fail s => println s
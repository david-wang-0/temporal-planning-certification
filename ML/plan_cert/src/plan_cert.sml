val usage = "Usage: $ checker " ^ "\n" ^
            "-domain <pddl domain file> " ^ "\n" ^
            "-problem <pddl problem file> " ^ "\n" ^
            "-certificate <certificate (output) path> " ^ "\n" ^
            "-renaming <renaming (output) path> " ^ "\n" ^
            "-extra <lu | local> " ^ "\n" ^
            "[-compression <compression level>] " ^ "\n" ^
            "[-certify <certifier version>] " ^ "\n" ^
            "[-num-threads <number of threads>]" ^ "\n" ^
            "[-debug 1]"

(* Very low prio to-do: print the generated network *)

fun dissect_arguments p args =
    let
      fun get' [] = NONE |
          get' (flag::arg::args) = if p flag then SOME (arg) else
                                   get' args |
          get' (_::_) = Exn.error usage
    in
      get' args
    end

datatype extrapolation =
         Local |
         LU

fun extra_from_str "lu" = SOME LU |
    extra_from_str "local" = SOME Local |
    extra_from_str _ = NONE

fun flags args =
    let
        val domain =
            dissect_arguments
                (fn "-domain" => true | "-m" => true | _ => false) args
        val problem =
            dissect_arguments
                (fn "-problem" => true | "-m" => true | _ => false) args
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
        val is_extra = fn "-extra" => true | "-e" => true | _ => false
        val extra =
            case dissect_arguments is_extra args of
                NONE => (print "ok"; SOME Local) |
                SOME str => extra_from_str str
        val debug = 
            dissect_arguments
                (fn "-debug" => true | "-d" => true | _ => false) args
    in
      (domain, problem, extra, renaming_path, cert_path, compression, certification,
       num_threads, debug)
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

fun log_config (extra, domain, problem, renaming, cert, compression, certification, num_threads) =
    (
      log_extra extra;
      log_domain_file domain;
      log_problem_file problem;
      log_renaming_file renaming;
      log_certificate_file cert;
      log_compression compression;
      log_certification certification;
      log_num_threads num_threads
    )

fun log_config1 (extra, domain, problem) =
    (log_extra extra; log_domain_file domain; log_problem_file problem)

fun check_and_cert_network extra renaming cert compression certification num_threads model =
    (
      Par_List.set_num_threads (Int.fromString num_threads |> the);
      (case extra of
           Local => MLuntaAdapter.check_and_cert |
           LU => MLuntaAdapter.check_and_cert_lu)
          renaming
          cert
          model
          (Int.fromString compression |> the)
          (Int.fromString certification |> the)
    )

fun check_and_cert_problem extra domain problem renaming cert compression certification num_threads debug = (
    log_config (extra, domain, problem, renaming, cert, compression, certification, num_threads);
    let
        val parsedDom = parse_pddl_dom dom_file;
        val parsedProb = parse_pddl_prob prob_file;
        val certifier = convert_certificate o 
            (check_and_cert_network extra renaming cert compression certification num_threads) o 
            convert_network;
        val f = (fn a b c d e f g => ()); (* XXX: Isabelle export*)
        val show_cert = (case debug of NONE => false | SOME _ => true);
    in f parsedDom parsedProb mode num_split false certifier show_cert 
)

(* fun check_problem domain problem = (
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


(*  
    - How is a certificate stored in memory (types)? 
    - How is a renaming stored in memory (types)? 

- The serialiser and deserialiser are built into MLuntaAdapter.
- The deserialiser outputs ML equivalents of types:
      SOME (Deserialize.Reachable_Set x) => SOME (Reachable_Set x)
    | SOME (Deserialize.Buechi_Set x)    => SOME (Buechi_Set x)
- The serialiser does ???
*)

(* To do: Implement a conversion from whatever the certifier outputs to 
    the Isabelle types. *)

fun check args = (* Todo: This should be implemented at a later point. *)
    case args of
        (SOME domain, SOME problem, SOME extra, SOME renaming, SOME cert, compression,
         certification, num_threads, debug) => check_and_cert_problem
                                            extra
                                            domain
                                            problem
                                            renaming
                                            cert
                                            (the_default "0" compression)
                                            (the_default "0" certification)
                                            (the_default "1" num_threads)
                                            debug
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
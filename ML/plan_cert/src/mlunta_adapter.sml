(* From MLunta by Simon Wimmer. 
Changes:
    - Use abstract type rather than JSON to represent network of timed automata
    - Skip parsing *)

structure MLuntaAdapter = struct
open Mlunta

fun parse_construct_and_check extra_lu net =
    net
    |> construct extra_lu
    |> Either.mapR (snd #> (` Network.info))
    |> Either.mapR (apsnd (` check_network))

fun construct' extra_lu net =
    net
    |> Construction.construct extra_lu 
    |> Either.mapL Construction.print_log

fun construct_and_check' extra_lu net =
    net
    |> construct' extra_lu
    |> Either.mapR (snd #> (` Network.info))
    |> Either.mapR (apsnd (` check_network))

val use_time' =
    Benchmark.add_time (fn (time, res) => Either.mapR (fn succ => (time, succ)) res) 

fun check' extra_lu net =
    net
    |> Benchmark.time_it (construct_and_check' extra_lu)
    |> use_time'
    |> Either.mapR (fn (time, (info, (prop, net))) => (time, info, prop, net))


fun parse_check extra_lu net =
    net
    |> Benchmark.time_it (parse_construct_and_check extra_lu)
    |> use_time'
    |> Either.mapR (fn (time, (info, (prop, net))) => (time, info, prop, net))

fun compress' compression net =
    case net of
        Either.Left _ => id
    |   Either.Right (net, trans) => 
        Comp.compress compression net trans

fun certify' version net =
    case net of
        Either.Left _ => id
    |   Either.Right (net, trans) => fn x => (
        if Certify.check version net trans x
        then print "Certificate check passed.\n"
        else print "Certificate check failed.\n";
        x)

local
  open Formula
  open Property
in
    fun cert' compress certify time info result =
        let
            fun certs ht =
                Diagnostic.make_with_cert time info ht

            val prop =
                result |> the_formula |> just_prop

            val no_certs =
                Diagnostic.make_without_cert time prop
        in
        case result of
            Ex (Unsatisfied ht) => 
                let val ccert = ht |> compress |> certify
                in (certs ccert prop, Either.Right ccert)
                end |
            Ag (Satisfied ht)   => 
                let val ccert = ht |> compress |> certify
                in (certs ccert prop, Either.Right ccert)
                end |
            Ex (Satisfied ht) => 
                (no_certs, Either.Left ht)
                |> tap (K (Log.info "* No certificate extraction possible")) |
            Ag (Unsatisfied ht) => 
                (no_certs, Either.Left ht) 
                |> tap (K (Log.info "* No certificate extraction possible")) 
        end
end

fun explore compress certify renaming_path cert_path (time, info, prop, net) =
    let 
        val (cont, explored) = cert' compress certify time info prop
        val _ = cont |> Diagnostic.finish (SOME (renaming_path, cert_path))
    in explored
        |> Either.mapL (fn passed => (net, passed)) 
        |> Either.mapR (fn passed => (net, passed))
    end

fun check_and_cert_return extra_lu renaming_path cert_path net compression certification =
    net
    |> check' extra_lu
    |> Either.mapR (
        explore
            (if compression > 0 then compress' compression (construct' extra_lu net) else id)
            (if certification > 0 then certify' certification (construct' extra_lu net) else id)
            renaming_path
            cert_path)


val check_and_cert_return_lu = check_and_cert_return true
val check_and_cert_return = check_and_cert_return false

fun parse_check_and_cert_return extra_lu renaming_path cert_path json_str compression certification =
    json_str
    |> parse_check extra_lu
    |> Either.mapR (
        explore
            (if compression > 0 then compress' compression (construct extra_lu json_str) else id)
            (if certification > 0 then certify' certification (construct extra_lu json_str) else id)
            renaming_path 
            cert_path)


val parse_check_and_cert_return_lu = parse_check_and_cert_return true
val parse_check_and_cert_return = parse_check_and_cert_return false

end
(* From MLunta by Simon Wimmer. 
Changes:
    - Use abstract type rather than JSON to represent network of timed automata
    - Skip parsing *)

structure MLuntaAdapter = struct
open Mlunta

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
    Benchmark.add_time (fn (time, res) => 
        res
        (* |> Either.mapL (fn err => (time, err))  *)
        |> Either.mapR (fn succ => (time, succ))) 

fun check' extra_lu net =
    net
    |> Benchmark.time_it (construct_and_check' extra_lu)
    |> use_time'
    |> Either.mapR (fn (time, (info, (prop, net))) => (time, info, prop, net))
(* 
fun check_and_then' extra_lu post net =
    net
    |> Benchmark.time_it (construct_and_check' extra_lu)
    |> use_time (fn time => fn (info, (prop, orig)) => (orig, post info time prop)) *)

fun compress' extra_lu compression net =
    case net |> construct' extra_lu of
        Either.Left _ => id
    |   Either.Right (net, trans) => Comp.compress compression net trans

fun certify' extra_lu version net =
    case net |> construct' extra_lu of
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

fun cert' compress time info result =
    let
      fun certs ht =
          Diagnostic.make_with_cert time info ht
      val prop =
          result |> the_formula |> just_prop
    in
      case result of
          Ex (Unsatisfied ht) => 
            let val ccert = compress ht
            in (certs ccert prop, SOME ccert)
            end |
          Ag (Satisfied ht)   => 
            let val ccert = compress ht
            in (certs ccert prop, SOME ccert)
            end |
          _  => (Diagnostic.make_without_cert time prop, NONE)
                    |> tap (K (Log.info "* No certificate extraction possible"))
    end
end

fun certc' compress renaming_path cert_path (time, info, prop, net) =
    let val (res, ccert) = cert' compress time info prop
        val _ = Diagnostic.finish (SOME (renaming_path, cert_path)) res
    in ccert
        |> Either.from_option ()
        |> Either.mapR (fn states => (net, states))
    end

fun check_and_cert_return extra_lu renaming_path cert_path net compression certification =
    net
    |> check' extra_lu
    |> Either.bindR (
        certc'
            ((if compression > 0 then compress' extra_lu compression net else id) o
                (if certification > 0 then certify' extra_lu certification net else id))
            renaming_path 
            cert_path)


val check_and_cert_return_lu = check_and_cert_return true
val check_and_cert_return = check_and_cert_return false

end
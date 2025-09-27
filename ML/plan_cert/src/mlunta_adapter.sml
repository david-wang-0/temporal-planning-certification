(* From MLunta by Simon Wimmer. 
Changes:
    - Use abstract type rather than JSON to represent network of timed automata
    - Skip parsing *)

functor MLuntaAdapter = struct
open Mlunta

fun construct_and_check' extra_lu json_str =
    json_str
    |> construct extra_lu
    |> Either.mapR (snd #> (` Network.info))
    |> Either.mapR (apsnd (` check_network))
    |> Either.mapR (fn (info, (orig, res)) => (info, orig, res))

fun check_and_then' extra_lu post json_str =
    json_str
    |> Benchmark.time_it (construct_and_check' extra_lu)
    |> use_time (fn time => fn (info, orig, prop) => (orig, post info time prop))
    

fun check_and_cert_return extra_lu renaming_path cert_path net compression certification =
    net
    |> check_and_then' extra_lu (
        certcc
            ((if compression > 0 then compress extra_lu compression net else id) o
                (if certification > 0 then certify extra_lu certification net else id))
            renaming_path cert_path
    )
    |> fst 


val check_and_cert_return_lu = check_and_cert_return true
val check_and_cert_return = check_and_cert_return false

end
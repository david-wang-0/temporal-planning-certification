open TP_NTA_Printing
open Util

fun read_and_convert domain_file problem_file output_file =
  let 
    val dom = read_file domain_file
    val prob = read_file problem_file
  in case parse_tp_to_opt_JSON dom prob of
      NONE => println "Error"
    | SOME s => string_to_file output_file s
  end

val arguments = [
  (["domain", "d"], "Ground domain.", Arg),
  (["problem", "p"], "Ground problem.", Arg),
  (["output", "o"], "Output file ", Arg)
]



fun main () =
  let
    val _ = read_arguments arguments
    val domf = find_arg "domain"
    val probf = find_arg "problem"
    val outf = find_arg "output"
    fun get_arg a s f = (case a of 
      NONE => "Missing argument: " ^ s |> println
    | SOME x => f x)
  in
    get_arg domf "domain file" (
      fn domf => get_arg probf "problem file" (
        fn probf => get_arg outf "output file" (
          fn outf => 
          let 
            val _ = "** Arguments **" |> println
            val _ = "* Domain file: " ^ domf |> println
            val _ = "* Problem file: " ^ probf |> println
            val _ = "* Output file: " ^ outf |> println
          in
            read_and_convert domf probf outf
          end
        )
      )
    )
  end
(* Standalone smoke test for TCheckerCertify's pure helpers (no tchecker/muntac needed):
   run_capture (subprocess + stdout capture) and sanitize_identifiers (the hyphen fix). *)
val () =
  let
    (* run_capture + stdout verdict parsing *)
    val (ok, out) = TCheckerCertify.run_capture ("/bin/echo", ["Certificate was accepted"])
    val () = print ("run_capture echo: ok=" ^ Bool.toString ok ^ " parsed="
                    ^ (if String.isSubstring "Certificate was accepted" out
                       then "Accepted" else "?") ^ "\n")

    (* sanitize_identifiers: hyphen between identifier chars -> underscore; operators and
       negative numbers left alone *)
    fun chk (input, expected) =
      let val got = TCheckerCertify.sanitize_identifiers input
      in print ("sanitize " ^ input ^ " -> " ^ got
                ^ (if got = expected then "  OK\n" else "  MISMATCH (want " ^ expected ^ ")\n"))
      end
    val () = chk ("lock_on-table_a", "lock_on_table_a")
    val () = chk ("var_arm-empty = 1", "var_arm_empty = 1")
    val () = chk ("x >= -5", "x >= -5")                (* negative number untouched *)
    val () = chk ("a := b - 1", "a := b - 1")          (* spaced operator untouched *)
  in () end

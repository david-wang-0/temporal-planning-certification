(* Part B: external model-checking orchestration.

   Replaces the in-process MLunta certifier (plan_cert.sml `check_and_cert_problem`),
   which does not terminate, with the working external flow -- exactly the steps of the
   repo's run.sh, but driven from SML:

     0. PRINT   -- the caller has already written <muntax> + <renaming>
                   (make_network / make_numeric_network + make_renaming).
     1. muntax -> tck     : python3 -m convert_models.convert <muntax> <tck>
     2. tck    -> dot     : tck-reach -a covreach -C graph -s dfs -o <dot> <tck>
     3. dot    -> cert    : python3 -m convert_models.convert_certificate -m <muntax>
                            <dot> <renaming> <cert>
     4. CHECK             : muntac -m <muntax> -r <renaming> -c <cert> -i <3|4>, then
                            parse stdout for "Certificate was accepted" / "rejected".

   Tool locations are parameters (defaulted repo-root-relative by the caller / env),
   so nothing is hard-coded here. *)

structure TCheckerCertify =
struct
  datatype verdict = Accepted | Rejected | NoVerdict

  fun verdict_to_string Accepted  = "accepted"
    | verdict_to_string Rejected  = "rejected"
    | verdict_to_string NoVerdict = "no verdict"

  (* per-stage wall-clock profiling: every named pipeline stage prints a machine-parseable
     "+ STAGE <name>: <ms> ms" line (the unsolvability-benchmarks harness reads these) *)
  fun timeStage name f =
    let
      val t = Timer.startRealTimer ()
      val r = f ()
      val ms = Time.toMilliseconds (Timer.checkRealTimer t)
    in
      print ("+ STAGE " ^ name ^ ": " ^ LargeInt.toString ms ^ " ms\n"); r
    end

  (* run a program (PATH-searched via execvp), wait, capture stdout; stderr passes
     through to our stderr.  Returns (exit-succeeded?, captured-stdout). *)
  fun run_capture (cmd : string, args : string list) : bool * string =
    let
      val proc = Unix.execute (cmd, args)
      val ins  = Unix.textInstreamOf proc
      val out  = TextIO.inputAll ins
      val _    = TextIO.closeIn ins
      val st   = Unix.reap proc
    in (OS.Process.isSuccess st, out) end

  fun absOf p =
    if OS.Path.isAbsolute p then p
    else OS.Path.mkAbsolute {path = p, relativeTo = OS.FileSys.getDir ()}

  fun sq s = "'" ^ s ^ "'"   (* single-quote a shell argument (paths have no quotes) *)

  (* tck-reach's grammar forbids '-' in identifiers, but muntax variable names carry PDDL
     predicate hyphens verbatim (e.g. lock_on-table_a).  Replace '-' with '_' ONLY when it
     sits between two identifier characters (so operators and negative numbers -- where '-'
     is preceded by a space/operator -- are untouched).  Applied to the muntax file BEFORE
     the renaming is derived from it, so muntax + renaming + tck stay name-consistent (the
     cert conversion matches variables by name). *)
  fun sanitize_identifiers s =
    let
      fun isIdent c = Char.isAlphaNum c orelse c = #"_"
      val n = String.size s
      fun step i =
        let val c = String.sub (s, i) in
          if c = #"-" andalso i > 0 andalso i < n - 1
             andalso isIdent (String.sub (s, i - 1))
             andalso isIdent (String.sub (s, i + 1))
          then #"_" else c
        end
    in CharVector.tabulate (n, step) end

  fun read_all path =
    let val ins = TextIO.openIn path
        val s = TextIO.inputAll ins
    in TextIO.closeIn ins; s end

  fun write_all path s =
    let val out = TextIO.openOut path
    in TextIO.output (out, s); TextIO.closeOut out end

  (* rewrite <path> in place with hyphens in identifiers replaced by underscores *)
  fun sanitize_file path = write_all path (sanitize_identifiers (read_all path))

  fun run_step name (cmd, args) : unit =
    let val (ok, out) = run_capture (cmd, args)
    in if ok then () else raise Fail (name ^ " failed:\n" ^ out) end

  (* run a `python3 -m convert_models.<mod> ...` step from `pkg_root` (the directory
     containing the convert_models package) so its relative imports resolve. *)
  fun py_step name pkg_root modpath argstr =
    run_step name ("/bin/sh",
      ["-c", "cd " ^ sq pkg_root ^ " && python3 -m convert_models." ^ modpath ^ " " ^ argstr])

  (* steps 1-3: muntax + renaming -> munta cert (mirrors run.sh).  Intermediate .tck /
     .dot files are placed next to <cert>.  All file args are absolutised. *)
  fun make_cert {pkg_root : string, tck_reach_bin : string,
                 muntax, renaming, cert, buechi : bool} : unit =
    let
      val muntaxA = absOf muntax
      val renamingA = absOf renaming
      val certA = absOf cert
      val tck = certA ^ ".tck"
      val dot = certA ^ ".dot"
    in
      (* 1. muntax -> tck *)
      timeStage "convert-tck" (fn () =>
        py_step "muntax->tck (convert)" pkg_root "convert" (sq muntaxA ^ " " ^ sq tck));
      (* 2. tck -> dot (zone-graph certificate) *)
      timeStage "tck" (fn () =>
        run_step "tck-reach"
          (tck_reach_bin, ["-a", "covreach", "-C", "graph", "-s", "dfs", "-o", dot, tck]));
      (* 3. dot -> munta cert *)
      timeStage "convert-back" (fn () =>
        py_step "dot->cert (convert_certificate)" pkg_root "convert_certificate"
          ((if buechi then "-b " else "") ^ "-m " ^ sq muntaxA ^ " "
           ^ sq dot ^ " " ^ sq renamingA ^ " " ^ sq certA))
    end

  (* step 3: muntac check -> verdict *)
  fun check_cert {muntac_bin : string, muntax, renaming, cert, buechi : bool} : verdict =
    let
      val mode = if buechi then "4" else "3"
      val (_, out) = timeStage "check" (fn () => run_capture (muntac_bin,
        ["-m", muntax, "-r", renaming, "-c", cert, "-i", mode]))
    in
      if      String.isSubstring "Certificate was accepted" out then Accepted
      else if String.isSubstring "Certificate was rejected" out then Rejected
      else NoVerdict
    end

  (* full pipeline: caller has already written <muntax> and <renaming>. *)
  fun certify_via_tchecker {pkg_root, tck_reach_bin, muntac_bin,
                            muntax, renaming, cert, buechi} : verdict =
    ( make_cert  {pkg_root = pkg_root, tck_reach_bin = tck_reach_bin, muntax = muntax,
                  renaming = renaming, cert = cert, buechi = buechi}
    ; check_cert {muntac_bin = muntac_bin, muntax = muntax, renaming = renaming,
                  cert = cert, buechi = buechi} )
end

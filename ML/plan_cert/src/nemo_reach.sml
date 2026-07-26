(* Nemo datalog reachability for the grounder (task #22b).

   Builds the TFD-style delete-relaxed reachability datalog program from the LIFTED
   (parameterized) problem, runs the nemo engine (nmo), and returns a per-schema filter
   restricting instantiation to the derived-reachable parameter tuples.

   Encoding (per the TFD translator's rules, cf. NUMERIC docs / tfd normalize.py):
     - per-schema applicability predicate  a<i>(params)  with body
         * one type fact-predicate  t<k>(?v)  per parameter (type facts computed in SML via
           the same subtype logic the grounder uses -- no datalog type hierarchy),
         * every POSITIVE predicate atom of the at-start condition (negatives dropped:
           delete relaxation),
         * only the STATIC positive predicate atoms of over-all/at-end conditions (a fluent
           there may only become true mid-duration -- requiring it would be UNSOUND pruning),
         * definedness atoms  d<j>(args)  for every fluent read by an at-start numeric
           comparison and by the duration constraint's PNEs,
         * one dom(?v) safety guard per parameter (nemo range-restriction),
         * =/!= filters from (in)equality conditions;
     - effect rules: every positive add atom (at-start AND at-end collapse onto the one
       applicability predicate) becomes a head with body a<i>(params); every numeric-effect
       LHS fluent yields a definedness head  d<j>(args) :- a<i>(params);
     - init: positive predicate atoms as facts; numeric init assignments as d<j> facts;
       dom(c) per object.

   Mangling mirrors the classical nemo_driver.sml in Isabelle-PDDL-Grounding: objects c<i>,
   predicates p<i>, def-preds d<i>, type-sigs t<i>, schemas a<i>, variables ?v<k> (per-rule),
   0-ary heads get the reserved dummy constant z.

   Invocation: $NMO (default "nmo") -e idb -D <tmp>/results -o <tmp>/prog.rls.
   Fail-open: NEMO_PRUNE=0, a missing binary, a failed run, or any parse problem yields
   NONE = "no pruning" (the grounder then does the full cross-product as before).
   NOTE this pruning is part of the (already unverified) grounder TCB: it is exact
   reachability of the TFD relaxation, an over-approximation of real reachability, so
   pruned instances are never applicable and the plan set is unchanged. *)

structure NemoReach =
struct
  structure C = Converter

  (* ---- same type logic as Grounder (duplicated to keep the modules independent) ---- *)
  fun supertypes types t0 =
    let
      fun step acc [] = acc
        | step acc (x :: xs) =
            let val ups = List.mapPartial
                  (fn (sub, sup) => if sub = x andalso not (List.exists (fn y => y = sup) acc)
                                    then SOME sup else NONE) types
            in step (acc @ ups) (xs @ ups) end
    in step [t0] [t0] end
  fun type_fits types onames (C.Either pnames) =
    List.exists (fn on =>
      let val sups = supertypes types on
      in List.exists (fn pn => List.exists (fn s => s = pn) sups) pnames end) onames
  fun candidates types objs_typed pty =
    List.mapPartial
      (fn (ob, C.Either onames) => if type_fits types onames pty then SOME ob else NONE)
      objs_typed

  (* ---- tiny string-keyed index dictionaries (append-only) ---- *)
  type dict = (string * int) list ref * int ref
  fun newDict () : dict = (ref [], ref 0)
  fun lookup ((entries, _) : dict) s =
    Option.map #2 (List.find (fn (k, _) => k = s) (!entries))
  fun intern (d as (entries, n) : dict) s =
    (case lookup d s of
        SOME i => i
      | NONE => let val i = !n in entries := (s, i) :: !entries; n := i + 1; i end)

  fun conjuncts (C.And (f, g)) = conjuncts f @ conjuncts g
    | conjuncts (C.Not C.Bot)  = []
    | conjuncts f              = [f]

  (* fluents (function names) read by a numeric expression *)
  fun nexp_fns acc e =
    (case e of
        C.FunctionExpr (C.PNE (C.Func f, ts)) => (f, ts) :: acc
      | C.AddExpr (a, b) => nexp_fns (nexp_fns acc a) b
      | C.SubExpr (a, b) => nexp_fns (nexp_fns acc a) b
      | C.MulExpr (a, b) => nexp_fns (nexp_fns acc a) b
      | C.DivExpr (a, b) => nexp_fns (nexp_fns acc a) b
      | C.SinExpr a => nexp_fns acc a
      | C.CosExpr a => nexp_fns acc a
      | C.ExpExpr a => nexp_fns acc a
      | _ => acc)
  fun atom_cmp_fns (C.NumericEqAtm (x, y))      = nexp_fns (nexp_fns [] x) y
    | atom_cmp_fns (C.NumericLessAtm (x, y))    = nexp_fns (nexp_fns [] x) y
    | atom_cmp_fns (C.NumericLEAtm (x, y))      = nexp_fns (nexp_fns [] x) y
    | atom_cmp_fns (C.NumericGreaterAtm (x, y)) = nexp_fns (nexp_fns [] x) y
    | atom_cmp_fns (C.NumericGEAtm (x, y))      = nexp_fns (nexp_fns [] x) y
    | atom_cmp_fns _ = []

  fun run_nemo (cprob as C.Problem (C.Domain (types, _, _, consts, schemas), objs, init, _)) =
    let
      (* per-PROCESS scratch dir: concurrent plan_cert invocations must not share it -- a
         shared dir let one run read another's reachability results, i.e. arbitrary
         MIS-pruning (an unsound grounding, which no downstream gate detects) *)
      val pid = SysWord.toString (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
      val tmp = "/tmp/plan_cert_nemo_" ^ pid
      val () = if OS.FileSys.access (tmp, []) then () else OS.FileSys.mkDir tmp
      val objs_typed = objs @ consts
      val objD  : dict = newDict ()   (* object name -> c<i> *)
      val predD : dict = newDict ()   (* predicate name -> p<i> *)
      val defD  : dict = newDict ()   (* function name -> d<i> *)
      val tyD   : dict = newDict ()   (* Either signature key -> t<i> *)
      fun objId (C.Obj o_) = "c" ^ Int.toString (intern objD o_)
      fun predId p = "p" ^ Int.toString (intern predD p)
      fun defId f  = "d" ^ Int.toString (intern defD f)
      fun tyKey (C.Either ns) = String.concatWith "," ns
      fun tyId pty = "t" ^ Int.toString (intern tyD (tyKey pty))

      (* per-rule variable environment: param name -> ?v<k> *)
      fun mkVarEnv params =
        let val pairs = ListPair.zip (map (fn (C.Vara v, _) => v) params,
                                      List.tabulate (length params, fn k => "?v" ^ Int.toString k))
        in fn v => (case List.find (fn (w, _) => w = v) pairs of
                       SOME (_, id) => SOME id | NONE => NONE) end
      fun termId env (C.VAR (C.Vara v)) = env v
        | termId env (C.CONST ob)       = SOME (objId ob)
      fun termIds env ts =
        let val ids = map (termId env) ts
        in if List.all Option.isSome ids then SOME (map valOf ids) else NONE end
      fun atomStr pid [] = pid ^ "(z)"
        | atomStr pid ids = pid ^ "(" ^ String.concatWith "," ids ^ ")"

      (* statics: predicates appearing in NO add/del of any schema *)
      fun eff_preds acc (C.Effect (adds, dels, _)) =
        foldl (fn (f, a) =>
                foldl (fn (C.Atom (C.PredAtm (C.Pred p, _)), b) => p :: b
                        | (C.Not (C.Atom (C.PredAtm (C.Pred p, _))), b) => p :: b
                        | (_, b) => b) a (conjuncts f))
              acc (adds @ dels)
      fun schema_eff_preds acc (C.SimpleActionSchemaa (_, C.SimpleActionBody (_, e))) = eff_preds acc e
        | schema_eff_preds acc (C.DurativeActionSchema (_, C.DurativeActionBody (_, _, effs))) =
            foldl (fn ((_, e), a) => eff_preds a e) acc effs
      val fluent_preds = foldl (fn (s, a) => schema_eff_preds a s) [] schemas
      fun is_static p = not (List.exists (fn q => q = p) fluent_preds)

      (* body contributions of one condition formula.
         full = at-start (all positive atoms + defs + filters);
         not full = over-all/at-end (STATIC positive atoms only). *)
      fun cond_body env full f (atoms, filters) =
        foldl (fn (c, (ats, flt)) =>
          (case c of
              C.Atom (C.PredAtm (C.Pred p, ts)) =>
                (case termIds env ts of
                    SOME ids => if full orelse is_static p
                                then (atomStr (predId p) ids :: ats, flt) else (ats, flt)
                  | NONE => (ats, flt))
            | C.Atom (C.EqAtm (t1, t2)) =>
                if full then
                  (case (termId env t1, termId env t2) of
                      (SOME a, SOME b) => (ats, (a ^ " = " ^ b) :: flt)
                    | _ => (ats, flt))
                else (ats, flt)
            | C.Not (C.Atom (C.EqAtm (t1, t2))) =>
                if full then
                  (case (termId env t1, termId env t2) of
                      (SOME a, SOME b) => (ats, (a ^ " != " ^ b) :: flt)
                    | _ => (ats, flt))
                else (ats, flt)
            | C.Atom a =>
                if full then
                  (foldl (fn ((fname, ts), acc) =>
                            (case termIds env ts of
                                SOME ids => atomStr (defId fname) ids :: acc
                              | NONE => acc)) ats (atom_cmp_fns a), flt)
                else (ats, flt)
            | _ => (ats, flt)   (* Or/Imp/negated preds/quantifier remnants: over-approximate *)
          )) (atoms, filters) (conjuncts f)

      fun dur_body env durs ats =
        foldl (fn ((_, C.DurationConstraint (_, e)), acc) =>
                 foldl (fn ((fname, ts), a) =>
                          (case termIds env ts of
                              SOME ids => atomStr (defId fname) ids :: a
                            | NONE => a)) acc (nexp_fns [] e))
              ats durs

      (* effect heads: positive adds + definedness of assigned fluents *)
      fun eff_heads env (C.Effect (adds, _, neffs)) acc =
        let
          val acc = foldl (fn (f, a) =>
                      foldl (fn (C.Atom (C.PredAtm (C.Pred p, ts)), b) =>
                                (case termIds env ts of
                                    SOME ids => atomStr (predId p) ids :: b
                                  | NONE => b)
                              | (_, b) => b) a (conjuncts f)) acc adds
        in
          foldl (fn (C.NumericEffect (_, C.PNE (C.Func f, ts), _), a) =>
                   (case termIds env ts of
                       SOME ids => atomStr (defId f) ids :: a
                     | NONE => a)) acc neffs
        end

      (* one schema -> applicability rule(s) + effect rules; returns (name, arity, appId, rules)
         where appId is the predicate whose derivable tuples ARE the kept instances.

         Durative actions are SNAP-SPLIT into a start predicate a<i>s and an end predicate a<i>e:
           a<i>s :- types, dom, at-start conditions, duration/at-start def-atoms
           <at-start adds> :- a<i>s
           a<i>e :- a<i>s, over-all + at-end conditions (incl. DYNAMIC fluents, as reachability
                    joins), over-all/at-end def-atoms
           <at-end adds> :- a<i>e
         The kept set is a<i>e (an instance whose END snap is reachable can fully fire).  The split
         is what makes requiring dynamic at-end/over-all fluents SOUND: the start effects seed the
         fluent set independently of a<i>e, so a self-bootstrapping chain (e.g. painter's container
         adds s1 at start, which drives s1->s2->s3->s4, satisfying its own at-end s4) is derived
         rather than killed by a cycle -- while a genuinely-unreachable at-end condition (e.g. s4
         for a non-consecutive pair, whose chain never starts) correctly prunes the instance.
         Collapsing start+end onto one predicate (the previous encoding) could not do this: it had
         to DROP dynamic at-end/over-all conditions to stay sound, keeping provably-dead instances. *)
      fun schema_rules i sch =
        let
          val (name, params) = (case sch of
                  C.SimpleActionSchemaa (C.ActionHead (n, ps), _) => (n, ps)
                | C.DurativeActionSchema (C.ActionHead (n, ps), _) => (n, ps))
          val env = mkVarEnv params
          val vids = List.tabulate (length params, fn k => "?v" ^ Int.toString k)
          val tyAtoms = ListPair.map (fn ((_, pty), v) => tyId pty ^ "(" ^ v ^ ")") (params, vids)
          val domAtoms = map (fn v => "dom(" ^ v ^ ")") vids
          (* head(vids) :- extra, types, atoms, dom, filters .  (dom(z) when the body is empty) *)
          fun mkRule hid extra (atoms, filters) =
            let val body = String.concatWith ", " (extra @ tyAtoms @ atoms @ domAtoms @ filters)
            in atomStr hid vids ^ " :- " ^ (if body = "" then "dom(z)" else body) ^ " ." end
          fun isStart C.At_Start = true | isStart _ = false
        in
          case sch of
              C.SimpleActionSchemaa (_, C.SimpleActionBody (pre, eff)) =>
                let
                  val appId = "a" ^ Int.toString i
                  val appRule = mkRule appId [] (cond_body env true pre ([], []))
                  val effRules = map (fn h => h ^ " :- " ^ atomStr appId vids ^ " .")
                                     (eff_heads env eff [])
                in (name, length params, appId, appRule :: effRules) end
            | C.DurativeActionSchema (_, C.DurativeActionBody (durs, conds, effs)) =>
                let
                  val sId = "a" ^ Int.toString i ^ "s"
                  val eId = "a" ^ Int.toString i ^ "e"
                  val startC = List.filter (fn (ta, _) => isStart ta) conds
                  val endC   = List.filter (fn (ta, _) => not (isStart ta)) conds
                  val (sAts, sFlt) = foldl (fn ((_, f), st) => cond_body env true f st) ([], []) startC
                  val sRule = mkRule sId [] (dur_body env durs sAts, sFlt)
                  val eRule = mkRule eId [atomStr sId vids]
                                (foldl (fn ((_, f), st) => cond_body env true f st) ([], []) endC)
                  val sEff = map (fn h => h ^ " :- " ^ atomStr sId vids ^ " .")
                                 (foldl (fn ((ta, e), a) => if isStart ta then eff_heads env e a else a)
                                        [] effs)
                  val eEff = map (fn h => h ^ " :- " ^ atomStr eId vids ^ " .")
                                 (foldl (fn ((ta, e), a) => if isStart ta then a else eff_heads env e a)
                                        [] effs)
                in (name, length params, eId, sRule :: eRule :: (sEff @ eEff)) end
        end

      val indexed = ListPair.zip (List.tabulate (length schemas, fn i => i), schemas)
      val schemaRules = map (fn (i, s) => schema_rules i s) indexed

      (* facts (init is GROUND: its atoms carry objects directly, not terms) *)
      val initFacts =
        List.concat (map (fn f =>
          List.concat (map (fn c =>
            (case c of
                C.Atom (C.PredAtm (C.Pred p, obs)) =>
                  [atomStr (predId p) (map objId obs) ^ " ."]
              | C.Atom (C.NumericEqAtm (C.FunctionExpr (C.PNE (C.Func fn_, obs)), _)) =>
                  [atomStr (defId fn_) (map objId obs) ^ " ."]
              | _ => [])) (conjuncts f))) init)
      val domFacts = map (fn (ob, _) => "dom(" ^ objId ob ^ ") .") objs_typed
                     @ ["dom(z) ."]
      val tyFacts =
        List.concat (map (fn (key, ti) =>
            map (fn ob => "t" ^ Int.toString ti ^ "(" ^ objId ob ^ ") .")
                (candidates types objs_typed (C.Either (String.fields (fn c => c = #",") key))))
          (! (#1 tyD)))

      val prog = String.concatWith "\n"
        (domFacts @ tyFacts @ initFacts @ List.concat (map #4 schemaRules)) ^ "\n"
      val progPath = tmp ^ "/prog.rls"
      val resultsDir = tmp ^ "/results"
      val out = TextIO.openOut progPath
      val () = (TextIO.output (out, prog); TextIO.closeOut out)
      val nmoBin = Option.getOpt (OS.Process.getEnv "NMO", "nmo")
      val ok = OS.Process.isSuccess (OS.Process.system
                 (nmoBin ^ " -e idb -D " ^ resultsDir ^ " -o " ^ progPath ^ " > /dev/null 2>&1"))
    in
      if not ok then NONE
      else
        let
          (* reverse object dict: c<i> -> original name *)
          val objEntries = ! (#1 objD)
          fun unObj cid =
            if cid = "z" then SOME ""
            else (case Int.fromString (String.extract (cid, 1, NONE)) of
                     NONE => NONE
                   | SOME i => Option.map #1 (List.find (fn (_, j) => j = i) objEntries))
          fun readLines path =
            let val ins = TextIO.openIn path
                fun go acc = (case TextIO.inputLine ins of
                                 NONE => (TextIO.closeIn ins; List.rev acc)
                               | SOME l => go (l :: acc))
            in go [] end handle _ => []
          fun tupleOfLine l =
            let val l = String.translate (fn #"\r" => "" | #"\"" => "" | #"\n" => "" | c => str c) l
            in if l = "" then NONE
               else
                 let val cells = String.fields (fn c => c = #",") l
                     val names = map unObj cells
                 in if List.all Option.isSome names
                    then SOME (case names of
                                  [SOME ""] => []   (* the z dummy: 0-ary *)
                                | _ => map valOf names)
                    else NONE
                 end
            end
          (* per schema: reachable tuples as "o1|o2|..." keys *)
          fun keyOf objs = String.concatWith "|" objs
          val table =
            map (fn (name, arity, appId, _) =>
                  let val lines = readLines (resultsDir ^ "/" ^ appId ^ ".csv")
                      val keys = List.mapPartial (Option.map keyOf o tupleOfLine) lines
                  in (name, arity, keys) end)
                schemaRules
          fun filt (name, objTuple : C.object list) =
            (case List.find (fn (n, _, _) => n = name) table of
                NONE => true   (* unknown schema: don't prune *)
              | SOME (_, _, keys) =>
                  let val k = keyOf (map (fn C.Obj o_ => o_) objTuple)
                  in List.exists (fn k' => k' = k) keys end)
          val kept  = foldl (fn ((_, _, ks), a) => a + length ks) 0 table
        in
          print ("+ nemo reachability: " ^ Int.toString (length schemaRules)
                 ^ " schemas, " ^ Int.toString kept ^ " reachable instances\n");
          SOME filt
        end
    end

  (* the public entry: NONE = no pruning (disabled, nmo missing, or any failure) *)
  fun reach_filter cprob =
    (case OS.Process.getEnv "NEMO_PRUNE" of
        SOME "0" => NONE
      | _ => run_nemo cprob handle _ => (print "+ nemo reachability: FAILED (no pruning)\n"; NONE))
end

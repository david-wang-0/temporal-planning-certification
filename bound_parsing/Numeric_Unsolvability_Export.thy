theory Numeric_Unsolvability_Export
  imports
    "PDDL_TP_Reduction.Check_Unsolvability"
    Ground_PDDL_Numeric_Code_Export
begin

text \<open>Containers instances for the reduction's OWN numeric expression / comparison types
  (\<open>nexp\<close> / \<open>comp\<close> / \<open>cmp_op\<close> from theory \<open>Temporal_Plans\<close>) -- these are distinct from the FPS
  \<open>numeric_expression\<close> that \<open>Check_Unsolvability\<close> already derives.  The numeric admission check
  @{const check_and_make_numeric_network} sets \<open>func \<times> nexp\<close> update-lists (in
  \<open>upds_no_cross_read_list\<close>), so these element types need \<open>ceq\<close>/\<open>ccompare\<close>/\<open>set_impl\<close>; DList set
  impls keep any nesting \<open>ceq\<close>-only (Containers Userguide S3.5, same rationale as \<open>Check_Unsolvability\<close>).\<close>
derive (eq) ceq cmp_op nexp comp
derive ccompare cmp_op nexp comp
text \<open>\<open>nexp\<close>/\<open>comp\<close> carry a \<^type>\<open>rat\<close> leaf (\<open>NConst\<close>); the numeric admission check puts
  \<open>func \<times> nexp\<close> update-lists into sets, so \<open>rat\<close> needs the full Containers set sort
  \<open>ceq\<close>/\<open>ccompare\<close>/\<open>set_impl\<close> that \<open>Check_Unsolvability\<close> does not provide (it gives only
  \<open>compare\<close>/\<open>linorder\<close>).  Derive \<open>ccompare\<close> from the existing \<open>compare\<close> instance, \<open>ceq\<close> from \<open>equal\<close>.\<close>
derive (eq) ceq rat
derive (compare) ccompare rat
derive (dlist) set_impl rat

text \<open>Suppress the \<open>Eval\<close>-target \<open>term_of\<close>/enumeration machinery for the numeric types (as
  \<open>Check_Unsolvability\<close> does for the propositional AST types): without a \<open>(no) cenum\<close> instance the
  \<open>Eval\<close> code target emits \<open>Code_Evaluation.term_of\<close> code that references \<^ML_structure>\<open>Term\<close> and
  the arbitrary-precision \<open>Bit_Shifts\<close>/\<open>divMod\<close> integer helpers -- none of which survive the
  standalone MLton build.  These types are never enumerated, so \<open>(no) cenum\<close> is sound.\<close>
derive (no) cenum cmp_op nexp comp func rat
derive (dlist) set_impl cmp_op nexp comp

text \<open>@{type func} carries \<open>ceq\<close>/\<open>linorder\<close>/\<open>set_impl\<close> (from \<open>Check_Unsolvability\<close>) but no
  \<open>ccompare\<close> -- the propositional path never put \<open>func\<close> into an RBT/generic set.  The numeric
  admission check does, so derive it here (registers the comparator law the \<open>cproper_interval\<close>
  instance below relies on).\<close>
derive ccompare func

text \<open>@{type func} (the fluent-name wrapper \<open>Func (name: name)\<close>) additionally needs
  \<open>card_UNIV\<close>/\<open>cproper_interval\<close>: the numeric admission check runs \<open>is_empty\<close>/\<open>inf\<close>/\<open>remove\<close> on
  \<open>func set\<close>s (fluent sets in \<open>upds_no_cross_read_list\<close>), whose generic Containers code path
  requires them.  Same construction and rationale as \<open>predicate\<close> in \<open>Check_Unsolvability\<close>:
  \<open>func\<close> is infinite (injects from the infinite \<^type>\<open>String.literal\<close> name).\<close>
lemma infinite_UNIV_func: "infinite (UNIV :: func set)"
proof
  assume "finite (UNIV :: func set)"
  hence "finite (Func ` (UNIV :: name set))" by (blast intro: finite_subset)
  moreover have "inj_on Func (UNIV :: name set)" by (simp add: inj_on_def)
  ultimately have "finite (UNIV :: name set)" by (rule finite_imageD)
  thus False using infinite_literal by simp
qed

instantiation func :: card_UNIV begin
definition "finite_UNIV = Phantom(func) False"
definition "card_UNIV = Phantom(func) 0"
instance by intro_classes (simp_all add: finite_UNIV_func_def card_UNIV_func_def infinite_UNIV_func)
end

instantiation func :: cproper_interval begin
definition cproper_interval_func :: "func proper_interval" where "cproper_interval_func _ _ = undefined"
instance by intro_classes (simp add: infinite_UNIV_func)
end

text \<open>\<^bold>\<open>Unified \<open>Converter\<close> export (propositional + numeric).\<close>  This supersedes the
  propositional-only export in theory \<open>Check_Unsolvability\<close>: it emits the SAME module name
  (\<open>Converter\<close>) and file (\<open>code/Check_Unsolvability.ML\<close>), but from the TOP of the reduction
  stack (session \<open>bound_parsing\<close>), so the numeric network builder
  @{const check_and_make_numeric_network_opt} -- which needs the bound-inference machinery
  (@{const numeric_ground_ast_problem_defs.is_gbound_inv_exec}) that lives ABOVE
  \<open>Check_Unsolvability\<close> -- lands in the same \<open>Converter\<close> structure and shares the parser's
  \<open>problem\<close> type.  The SML tool feeds a parsed problem to BOTH
  @{const check_and_make_network_opt} (propositional path) and
  @{const check_and_make_numeric_network_opt} (numeric path) without a second parser.

  The numeric additions are:
    \<^item> @{const numeric_ground_ast_problem_defs.numeric_draft_actions} -- the INT-ified snap
      projection the (compute-side) bound inference consumes;
    \<^item> @{const check_and_make_numeric_network_opt} -- gate (@{const check_gbounds_opt}) + build;
    \<^item> the neutral projection datatype constructors (\<open>g_int\<close>/\<open>e_int\<close>) the SML glue matches on.\<close>

text \<open>Locale constants carry no auto-generated code equations; wire the one the numeric
  admission check @{const check_and_make_numeric_network} reaches transitively (its ground-data
  accessors are already \<open>[code]\<close> via the classical \<open>ground_ast_problem_code\<close> bundle and the
  \<open>numeric_ground_data_code\<close> bundle in theory \<open>Ground_PDDL_Numeric_Code_Export\<close>).\<close>
declare numeric_ground_ast_problem_defs.check_numeric_ground_problem_def[code]
declare numeric_ground_ast_problem_defs.check_numeric_ground_problem_diag_def[code]

section \<open>The NUMERIC certifier capstone (net passed in-process, no muntax round-trip)\<close>

text \<open>Numeric twin of @{const make_certified_net} / @{const check_and_cert_pddl_problem}: the
  verified pipeline builds the numeric net (admission + static bound gate + builder), hands the
  net to an UNTRUSTED SML \<open>certifier\<close> callback (which runs the external tck-reach oracle and
  returns the renaming + certificate state space), and checks the certificate IN-PROCESS with
  Munta's verified @{const convert_check} -- the net never round-trips through the muntax JSON,
  so the explicit initial variable values (point-bounded static fluents!) are preserved.  A bad
  oracle only yields a rejected certificate.

  The gate @{const numeric_ground_ast_problem_defs.is_gbound_inv_exec} now PROVABLY decides the
  cert-locale assumption (lemma \<open>is_gbound_inv_exec_eq\<close>, theory
  \<open>Ground_PDDL_Numeric_Code_Export\<close>), so the capstone triple below carries no residual
  boundedness hypothesis.\<close>

definition numeric_lo_of :: "(String.literal \<times> int \<times> int) list \<Rightarrow> func \<Rightarrow> int" where
  "numeric_lo_of B = (\<lambda>f. case map_of B (func.name f) of Some (l, _) \<Rightarrow> l | None \<Rightarrow> 0)"

definition numeric_hi_of :: "(String.literal \<times> int \<times> int) list \<Rightarrow> func \<Rightarrow> int" where
  "numeric_hi_of B = (\<lambda>f. case map_of B (func.name f) of Some (_, h) \<Rightarrow> h | None \<Rightarrow> 0)"

definition make_certified_numeric_net where
"make_certified_numeric_net P B certifier \<equiv>
  (if \<not> numeric_ground_ast_problem_defs.is_gbound_inv_exec P (numeric_lo_of B) (numeric_hi_of B)
   then Error [STR ''static bound certificate (is_gbound_inv_exec) rejected the box'']
   else
     (case check_and_make_numeric_network P (numeric_lo_of B) (numeric_hi_of B) of
        Inl e \<Rightarrow> Error [STR ''Could not make numeric network'']
      | Inr (clocks, autos, ids_to_names, process_names_to_index, broadcast,
             automata, bounds, formula, init_locs, init_vars) \<Rightarrow>
        do {
          (renaming, cert) \<leftarrow>
            (case certifier (clocks, (autos, (ids_to_names, process_names_to_index, broadcast,
                                              automata, bounds, formula, init_locs, init_vars))) of
               None \<Rightarrow> (Error [STR ''Certificate could not be generated''])
             | Some x \<Rightarrow> (Result x));
          Result ((ids_to_names, process_names_to_index, broadcast,
                   automata, bounds, formula, init_locs, init_vars), renaming, cert)
        }))"

lemma make_certified_numeric_net_okay:
  assumes "make_certified_numeric_net P B certifier = Result (network, renaming, cert)"
      and net: "network = (ids_to_names, process_names_to_index, broadcast, automata, bounds,
                           formula, init_locs, init_vars)"
      and not_sat: "\<not> (Simple_Network_Impl.sem automata broadcast bounds,
                        (init_locs, map_of init_vars, (\<lambda>_. 0)) \<Turnstile> formula)"
    shows "\<nexists>\<pi>. numeric_valid_ground_plan_cert P (numeric_lo_of B) (numeric_hi_of B) \<pi>"
proof (cases "numeric_ground_ast_problem_defs.is_gbound_inv_exec P (numeric_lo_of B) (numeric_hi_of B)")
  case gate: True
  show ?thesis
  proof (cases "check_and_make_numeric_network P (numeric_lo_of B) (numeric_hi_of B)")
    case (Inl a)
    thus ?thesis using assms(1) gate unfolding make_certified_numeric_net_def by simp
  next
    case inr: (Inr k)
    obtain clocks autos idn pni bc aut bnds frm il iv where
      kc: "k = (clocks, autos, idn, pni, bc, aut, bnds, frm, il, iv)"
      by (cases k) auto
    have chk: "numeric_ground_ast_problem_defs.check_numeric_ground_problem P (numeric_lo_of B) (numeric_hi_of B) = Inr ()"
      by (cases "numeric_ground_ast_problem_defs.check_numeric_ground_problem P (numeric_lo_of B) (numeric_hi_of B)")
         (use inr in \<open>auto simp: check_and_make_numeric_network_def\<close>)
    have leaf: "numeric_ground_ast_problem P (numeric_lo_of B) (numeric_hi_of B)"
      using chk by (rule check_numeric_ground_problem_sound)
    interpret L: numeric_ground_ast_problem P "numeric_lo_of B" "numeric_hi_of B" by (rule leaf)
    have ginv: "L.nred'.is_gbound_inv'"
      using gate L.is_gbound_inv_exec_eq by simp
    have cert: "numeric_ground_ast_problem_cert P (numeric_lo_of B) (numeric_hi_of B)"
      by (rule numeric_ground_ast_problem_cert.intro[OF leaf numeric_ground_ast_problem_cert_axioms.intro[OF ginv]])
    show ?thesis
    proof (cases "certifier (clocks, autos, idn, pni, bc, aut, bnds, frm, il, iv)")
      case None
      thus ?thesis using assms(1) gate inr kc unfolding make_certified_numeric_net_def by simp
    next
      case (Some y)
      obtain rn ct where y: "y = (rn, ct)" by (cases y)
      have vars: "((idn, pni, bc, aut, bnds, frm, il, iv), rn, ct)
                  = ((ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars), renaming, cert)"
        using assms(1) net gate inr kc Some y unfolding make_certified_numeric_net_def by simp
      have cmnn: "check_and_make_numeric_network P (numeric_lo_of B) (numeric_hi_of B)
                  = Inr (clocks, autos, ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars)"
        using inr kc vars by simp
      show ?thesis
        using check_and_make_numeric_network_and_plan_cert[OF cmnn cert] not_sat by simp
    qed
  qed
next
  case False
  thus ?thesis using assms(1) unfolding make_certified_numeric_net_def by simp
qed

definition check_and_cert_numeric_pddl_problem where
"check_and_cert_numeric_pddl_problem P B mode num_split certifier show_cert \<equiv>
case make_certified_numeric_net P B certifier of
  Result (network, renaming, cert) \<Rightarrow> do {
    res \<leftarrow> convert_check mode num_split False network renaming cert show_cert;
    let _ = (case res of
      Result r \<Rightarrow> (case r of
        Sat \<Rightarrow> do {let _ = println STR ''The numeric planning problem is unsolvable.''; Heap_Monad.return ()}
      | _   \<Rightarrow> do {let _ = println STR ''Something went wrong.''; Heap_Monad.return ()})
    | Error es \<Rightarrow> do {let _ = map println es; Heap_Monad.return ()});
    Heap_Monad.return (res)
  }
| Error es \<Rightarrow> do {let _ = map println es; Heap_Monad.return (Error es)}
" for num_split

lemma check_and_cert_numeric_pddl_problem_okay:
  assumes mode: "mode \<noteq> Buechi" "mode \<noteq> Debug"
  shows "
    <emp>
      check_and_cert_numeric_pddl_problem P B mode num_split certifier show_cert
    <\<lambda> Result Sat \<Rightarrow> \<up>(\<nexists>\<pi>. numeric_valid_ground_plan_cert P (numeric_lo_of B) (numeric_hi_of B) \<pi>)
     | _ \<Rightarrow> true>\<^sub>t"
proof (cases "make_certified_numeric_net P B certifier")
  case (Result res)
  obtain network renaming cert where
    res: "res = (network, renaming, cert)" by (cases res) auto
  obtain ids_to_names process_names_to_index
    broadcast automata bounds formula init_locs init_vars where
    net: "network = (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars)"
    by (cases network) auto

  have intermediate_res: "\<not> Simple_Network_Impl.sem automata broadcast bounds,(init_locs, map_of init_vars, \<lambda>_. 0) \<Turnstile> formula
    \<Longrightarrow> \<nexists>\<pi>. numeric_valid_ground_plan_cert P (numeric_lo_of B) (numeric_hi_of B) \<pi>"
    apply (rule make_certified_numeric_net_okay[OF Result[simplified res net]])
    by auto

  have conv_commute: "(Simple_Network_Language.conv_A \<circ> automaton_of) x = (automaton_of \<circ> conv_automaton) x" for x
  proof -
    have 1: "map conv_ac (default_map_of [] d x) = default_map_of [] (map (\<lambda>(s, cc). (s, map conv_ac cc)) d) x" for d x
      unfolding default_map_of_def unfolding FinFun.map_default_def unfolding map_of_map
      by (cases "map_of d x") auto
    show ?thesis
      apply (induction x)
      unfolding Simple_Network_Language.conv_A_def Simple_Network_Language.conv_t_def
      unfolding conv_automaton_def
      unfolding automaton_of_def
      unfolding comp_def
      unfolding prod.case
      unfolding set_map
      unfolding 1 by simp
  qed

  show ?thesis
    unfolding check_and_cert_numeric_pddl_problem_def
    unfolding Result Error_List_Monad.result.case
    unfolding res prod.case
    apply (rule bind_rule)
     apply (rule convert_check_okay[OF mode])
     apply (rule net)
    unfolding Let_def
    apply (rule return_cons_rule)
    subgoal for x
      apply (cases x)
      subgoal for b apply (cases b)
           apply simp
          apply simp
         apply simp
         apply (intro strip)
         apply (erule conjE)
        unfolding Simple_Network_Language.conv_def
        unfolding prod.case
        unfolding map_map
        unfolding conv_commute
        using intermediate_res
        unfolding Simple_Network_Impl.sem_def
        by auto
      by auto
    done
next
  case (Error x2)
  show ?thesis unfolding check_and_cert_numeric_pddl_problem_def
    unfolding Error
    unfolding Error_List_Monad.result.case Let_def
    apply (rule return_cons_rule)
    by auto
qed

definition check_and_cert_numeric_pddl_problem_no_return where
"check_and_cert_numeric_pddl_problem_no_return P B mode num_split certifier show_cert =
do {
  _ \<leftarrow> check_and_cert_numeric_pddl_problem P B mode num_split certifier show_cert;
  Heap_Monad.return ()
}" for num_split

export_code
  \<comment> \<open>--- propositional entries (verbatim from theory Check_Unsolvability) ---\<close>
  check_and_cert_pddl_problem_no_return check_and_make_network_opt
  parse_convert_run
  parse_convert_check
  rbt_to_list
  Inl Inr
  Result Error
  nat_of_integer integer_of_nat int_of_integer integer_of_int DBMEntry.Le DBMEntry.Lt DBMEntry.INF
  Impl1 Impl2 Impl3 Buechi Reachable_Set Buechi_Set
  formula.EX formula.EG formula.AX formula.AG formula.Leadsto
  sexp.true sexp.not sexp.and sexp.or sexp.imply sexp.eq sexp.le sexp.lt sexp.lt sexp.ge sexp.gt sexp.loc
  bexp.true bexp.not bexp.and bexp.or bexp.imply bexp.eq bexp.le bexp.lt bexp.ge bexp.gt
  exp.const exp.var exp.if_then_else exp.binop exp.unop
  acconstraint.LT acconstraint.LE acconstraint.EQ acconstraint.GT acconstraint.GE
  act.In act.Out act.Sil
  Rat.Fract Rat.of_int rat_of_digits_pair quotient_of
  predAtm eqAtm predicate Pred Func Either Var Obj PredDecl FuncDecl BigAnd BigOr
  formula.Not formula.Bot Effect duration_op.LEQ duration_op.EQ duration_op.GEQ
  At_Start At_End Over_All
  map_atom Domain Problem
  term.CONST term.VAR
  PNE ConstantExpr DurationExpr FunctionExpr DurationConstraint ActionHead SimpleActionSchema DurativeActionSchema SimpleActionBody DurativeActionBody
  Assign ScaleUp ScaleDown Increase Decrease NumericEffect
  ContinuousIncrease ContinuousDecrease ContinuousEffect
  map_numeric_effect map_numeric_expression
  String.explode String.implode
  \<comment> \<open>--- numeric entries (this session) ---\<close>
  check_and_cert_numeric_pddl_problem_no_return
  check_and_make_numeric_network_opt
  check_numeric_admission_diag_opt
  check_gbounds_opt
  numeric_ground_ast_problem_defs.numeric_draft_actions
  numeric_ground_ast_problem_defs.is_gbound_inv_exec
  GCmp_i Ceq Cle Cge Clt Cgt
  EC EV EAdd ESub EMul EDiv
  in Eval module_name Converter file_prefix Check_Unsolvability

end

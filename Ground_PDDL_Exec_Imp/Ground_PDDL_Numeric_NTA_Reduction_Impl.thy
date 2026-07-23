theory Ground_PDDL_Numeric_NTA_Reduction_Impl
  imports
    Ground_PDDL_Numeric_NTA_Reduction_Correctness
    Ground_PDDL_NTA_Reduction_Impl
begin

text \<open>\<^bold>\<open>NUMERIC_EXEC_PLAN WP-C\<close> -- the \<^emph>\<open>executable\<close> numeric net and its refinement to the abstract
  numeric net @{text num_net_impl} (WP-A). The numeric twin of @{text make_network_impl} /
  @{text model_checking_problem_refine} (theory @{text Ground_PDDL_NTA_Reduction_Impl}), but the numeric
  net is a thin \<^emph>\<open>augmentation\<close> of the propositional net (@{text augment_edge}: conjoin a numeric
  @{typ \<open>(String.literal, int) bexp\<close>} guard + append numeric @{typ \<open>(String.literal, int) exp\<close>} updates
  to each propositional edge; @{text \<open>num_all_vars = all_vars @ num_fluent_vars\<close>}), so the refinement
  lifts the existing propositional @{text \<open>*_refine\<close>} lemmas through the augmentation. Only the
  boundedness parameters @{text fluent_lo}/@{text fluent_hi} (the WP-E plug) are carried as inputs; the
  fluent encoding is the DEFINED @{const numeric_ground_ast_problem_defs.fluent_to_var_spec}, proved
  equal to the abstract @{text ndefs.fluent_to_var} by @{text fluent_to_var_spec_eq}.\<close>

subsection \<open>Executable numeric constructors\<close>

text \<open>The numeric net is a thin augmentation of the propositional executable net: conjoin a
  computable numeric guard and append computable numeric updates to each propositional edge, and
  append one bounded @{typ int} variable per declared numeric fluent to the variable bounds. All the
  numeric data (@{const numeric_ground_ast_problem_defs.n_pre} / @{const numeric_ground_ast_problem_defs.upds}
  / @{const numeric_ground_ast_problem_defs.num_goal} / @{const numeric_ground_ast_problem_defs.num_init}
  / @{const numeric_ground_ast_problem_defs.nfluents} / @{const numeric_ground_ast_problem_defs.const_to_int})
  is DEFINED from @{term P} in @{locale numeric_ground_ast_problem_defs} -- including the fluent naming
  @{const numeric_ground_ast_problem_defs.fluent_to_var_spec}; only the bounds
  @{text fluent_lo}/@{text fluent_hi} stay explicit definition arguments.\<close>

text \<open>The augmentation operation is a pure global function, so it is code-exportable and can be
  proved equal to the abstract, locale-local @{text numeric_tp_nta_reduction_defs.augment_edge}.\<close>
definition augment_edge_impl where
"augment_edge_impl g u e =
  (let (src, b, ac, act, upd, rst, tgt) = e in (src, bexp.and b g, ac, act, upd @ u, rst, tgt))"

text \<open>Executable integrality test on @{typ rat}: a rational in lowest terms is an integer iff its
  denominator is @{term 1}.  @{const quotient_of} yields the coprime-normalised @{term \<open>(num, den)\<close>}
  pair, so @{term \<open>snd (quotient_of r) = 1\<close>} is a decidable, code-generatable stand-in for the
  non-constructive @{term \<open>r \<in> \<int>\<close>}.\<close>
definition is_int_rat :: "rat \<Rightarrow> bool" where
  "is_int_rat r \<longleftrightarrow> snd (quotient_of r) = 1"

lemma is_int_rat_iff_Ints: "is_int_rat r \<longleftrightarrow> r \<in> \<int>"
proof
  assume "is_int_rat r"
  then have sd: "snd (quotient_of r) = 1" unfolding is_int_rat_def .
  obtain a b where ab: "quotient_of r = (a, b)" by (cases "quotient_of r")
  have "r = of_int a / of_int b" using quotient_of_div[OF ab] by simp
  moreover have "b = 1" using ab sd by simp
  ultimately have "r = of_int a" by simp
  then show "r \<in> \<int>" by (simp add: Ints_of_int)
next
  assume "r \<in> \<int>"
  then obtain n where "r = rat_of_int n" by (auto elim: Ints_cases)
  thus "is_int_rat r" unfolding is_int_rat_def by (simp add: quotient_of_rat_of_int)
qed

context numeric_ground_ast_problem_defs
begin

definition "num_pre_guard' s =
  bexp_and_all (map (comp_to_bexp fluent_to_var_spec const_to_int) (n_pre s))"

definition "num_inv_guard' a =
  bexp_and_all (map (comp_to_bexp fluent_to_var_spec const_to_int) (n_inv a))"

definition "num_goal_guard' =
  bexp_and_all (map (comp_to_bexp fluent_to_var_spec const_to_int) num_goal)"

definition "num_upd' s =
  map (\<lambda>(f, e). (fluent_to_var_spec f, nexp_to_exp fluent_to_var_spec const_to_int e)) (upds s)"

definition "num_init_upd' =
  map (\<lambda>f. (fluent_to_var_spec f, exp.const (const_to_int (num_init f)))) nfluents"

definition "num_fluent_vars' lo hi =
  map (\<lambda>f. (fluent_to_var_spec f, lo f, hi f)) nfluents"

definition "num_start_edge' a =
  augment_edge_impl (num_pre_guard' (at_start_spec a)) (num_upd' (at_start_spec a)) (start_edge' a)"

definition "num_end_edge' a =
  augment_edge_impl (num_pre_guard' (at_end_spec a)) (num_upd' (at_end_spec a)) (end_edge' a)"

definition "num_edge_2' a = augment_edge_impl (num_inv_guard' a) [] (edge_2' a)"

definition "num_edge_3' a = augment_edge_impl (num_inv_guard' a) [] (edge_3' a)"

definition "num_action_to_automaton' a =
(let
  committed_locs = (Nil::nat list);
  urgent_locs = [starting_loc_impl, ending_loc_impl];
  edges = [num_start_edge' a, num_edge_2' a, num_edge_3' a, num_end_edge' a, instant_trans_edge' a];
  invs = []::(nat \<times> (String.literal, int) acconstraint list) list
in (committed_locs, urgent_locs, edges, invs))"

definition "num_main_auto_init_edge' = augment_edge_impl bexp.true num_init_upd' main_auto_init_edge'"

definition "num_main_auto_goal_edge' = augment_edge_impl num_goal_guard' [] main_auto_goal_edge'"

definition "num_main_auto' =
(let
  committed_locs = [];
  urgent_locs = [init_loc_impl, goal_loc_impl];
  edges = [num_main_auto_init_edge', num_main_auto_goal_edge', main_auto_loop_impl];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

definition "num_net_automata' =
  num_main_auto' # map num_action_to_automaton' actions_spec"

definition "num_net_bounds' lo hi = net_bounds' @ num_fluent_vars' lo hi"

definition "num_init_locs' = init_locs'"

definition "num_init_vars' lo hi = map (map_prod id fst) (num_net_bounds' lo hi)"

definition "num_reach_formula' = reach_formula'"

end

text \<open>Code equations for the numeric net constructors (numeric twin of the classical
  @{thm [source] ground_ast_problem_code}).  Isabelle does not auto-generate code equations for
  locale constants, so we wire the numeric-net constructor @{text \<open>_def\<close>}s (and the locale-local
  fluent naming @{const numeric_ground_ast_problem_defs.fluent_to_var_spec}) as @{text \<open>[code]\<close>}.
  All the propositional edge helpers they augment (@{text start_edge'}/@{text net_bounds'}/... ),
  the numeric ground-data accessors (@{text n_pre}/@{text upds}/... ), and the pure augmentation
  @{const augment_edge_impl} are already @{text \<open>[code]\<close>} (classical @{text ground_ast_problem_code}
  bundle / numeric @{text numeric_ground_data_code} bundle / top-level definition).\<close>

lemmas numeric_ground_net_code[code] =
  numeric_ground_ast_problem_defs.fluent_to_var_spec_def
  numeric_ground_ast_problem_defs.num_pre_guard'_def
  numeric_ground_ast_problem_defs.num_inv_guard'_def
  numeric_ground_ast_problem_defs.num_goal_guard'_def
  numeric_ground_ast_problem_defs.num_upd'_def
  numeric_ground_ast_problem_defs.num_init_upd'_def
  numeric_ground_ast_problem_defs.num_fluent_vars'_def
  numeric_ground_ast_problem_defs.num_start_edge'_def
  numeric_ground_ast_problem_defs.num_end_edge'_def
  numeric_ground_ast_problem_defs.num_edge_2'_def
  numeric_ground_ast_problem_defs.num_edge_3'_def
  numeric_ground_ast_problem_defs.num_action_to_automaton'_def
  numeric_ground_ast_problem_defs.num_main_auto_init_edge'_def
  numeric_ground_ast_problem_defs.num_main_auto_goal_edge'_def
  numeric_ground_ast_problem_defs.num_main_auto'_def
  numeric_ground_ast_problem_defs.num_net_automata'_def
  numeric_ground_ast_problem_defs.num_net_bounds'_def
  numeric_ground_ast_problem_defs.num_init_locs'_def
  numeric_ground_ast_problem_defs.num_init_vars'_def
  numeric_ground_ast_problem_defs.num_reach_formula'_def

declare numeric_ground_net_code[code]

subsection \<open>Structural (valuation-free) sufficient conditions for the encoding-faithfulness universals\<close>

text \<open>The numeric leaf's faithfulness assumptions are universals over ALL integer valuations
  (@{term \<open>\<forall>w. num_val_ok w \<longrightarrow> nexp_ok w e\<close>}); an executable admission check needs a DECIDABLE,
  valuation-free sufficient condition. @{const numeric_tp_nta_reduction_defs.nexp_ok} depends on
  @{term w} only through @{const NVar} (the read must be a declared, integer fluent -- guaranteed by
  @{const numeric_tp_nta_reduction_defs.num_val_ok}) and @{const NDiv} (exact division cannot be
  guaranteed structurally). So the structural condition is: constants integral, reads declared,
  arithmetic recurses, division rejected (fail-closed; the benchmark fragment has no @{const NDiv}).
  This gives only the FORWARD direction (@{text \<open>structural \<Longrightarrow> universal\<close>}), which is exactly what the
  soundness assembly needs.\<close>

fun nexp_struct_ok :: "'n list \<Rightarrow> ('n, 'r::ring_1) nexp \<Rightarrow> bool" where
  "nexp_struct_ok fs (NConst c) \<longleftrightarrow> c \<in> \<int>"
| "nexp_struct_ok fs (NVar f)   \<longleftrightarrow> f \<in> set fs"
| "nexp_struct_ok fs (NAdd a b) \<longleftrightarrow> nexp_struct_ok fs a \<and> nexp_struct_ok fs b"
| "nexp_struct_ok fs (NSub a b) \<longleftrightarrow> nexp_struct_ok fs a \<and> nexp_struct_ok fs b"
| "nexp_struct_ok fs (NMul a b) \<longleftrightarrow> nexp_struct_ok fs a \<and> nexp_struct_ok fs b"
| "nexp_struct_ok fs (NDiv a b) \<longleftrightarrow> False"

fun comp_struct_ok :: "'n list \<Rightarrow> ('n, 'r::ring_1) comp \<Rightarrow> bool" where
  "comp_struct_ok fs (Comp p a b) \<longleftrightarrow> nexp_struct_ok fs a \<and> nexp_struct_ok fs b"

text \<open>Executable @{typ rat} twins: @{const nexp_struct_ok}'s @{term \<open>NConst c\<close>} clause tests
  @{term \<open>c \<in> \<int>\<close>}, which does NOT code-generate (@{term \<open>\<int>\<close>} = @{term \<open>range of_int\<close>}, an
  @{const image} over @{const UNIV}) and forces the polymorphic @{class ring_1} form to abort at runtime.
  On the exported @{typ rat} fragment it is the decidable @{const is_int_rat}.  These monomorphic twins
  (used by \<open>check_numeric_ground_problem\<close> below, whose numeric data is @{typ rat}) code-generate
  totally; \<open>nexp_struct_ok_exec_eq\<close> / \<open>comp_struct_ok_exec_eq\<close> bridge them to
  the abstract predicates so the @{text return_iff}/soundness statements are unchanged.\<close>
fun nexp_struct_ok_exec :: "'n list \<Rightarrow> ('n, rat) nexp \<Rightarrow> bool" where
  "nexp_struct_ok_exec fs (NConst c) \<longleftrightarrow> is_int_rat c"
| "nexp_struct_ok_exec fs (NVar f)   \<longleftrightarrow> f \<in> set fs"
| "nexp_struct_ok_exec fs (NAdd a b) \<longleftrightarrow> nexp_struct_ok_exec fs a \<and> nexp_struct_ok_exec fs b"
| "nexp_struct_ok_exec fs (NSub a b) \<longleftrightarrow> nexp_struct_ok_exec fs a \<and> nexp_struct_ok_exec fs b"
| "nexp_struct_ok_exec fs (NMul a b) \<longleftrightarrow> nexp_struct_ok_exec fs a \<and> nexp_struct_ok_exec fs b"
| "nexp_struct_ok_exec fs (NDiv a b) \<longleftrightarrow> False"

fun comp_struct_ok_exec :: "'n list \<Rightarrow> ('n, rat) comp \<Rightarrow> bool" where
  "comp_struct_ok_exec fs (Comp p a b) \<longleftrightarrow> nexp_struct_ok_exec fs a \<and> nexp_struct_ok_exec fs b"

lemma nexp_struct_ok_exec_eq: "nexp_struct_ok_exec fs e = nexp_struct_ok fs e"
  by (induction e) (auto simp: is_int_rat_iff_Ints)

lemma comp_struct_ok_exec_eq: "comp_struct_ok_exec fs c = comp_struct_ok fs c"
  by (cases c) (simp add: nexp_struct_ok_exec_eq)

text \<open>Function-level (eta) forms, so \<open>simp\<close> rewrites the PARTIAL applications
  @{term \<open>comp_struct_ok_exec nfluents\<close>} / @{term \<open>nexp_struct_ok_exec nfluents\<close>} that appear under
  @{const list_all} in \<open>check_numeric_ground_problem\<close> back to the abstract predicates.\<close>
lemma nexp_struct_ok_exec_eq_fun: "nexp_struct_ok_exec fs = nexp_struct_ok fs"
  by (rule ext) (rule nexp_struct_ok_exec_eq)

lemma comp_struct_ok_exec_eq_fun: "comp_struct_ok_exec fs = comp_struct_ok fs"
  by (rule ext) (rule comp_struct_ok_exec_eq)

context numeric_tp_nta_reduction_defs
begin

text \<open>Soundness: the structural condition implies the leaf's valuation-quantified faithfulness.\<close>

lemma nexp_struct_ok_sound:
  "nexp_struct_ok nfluents e \<Longrightarrow> num_val_ok w \<Longrightarrow> nexp_ok w e"
  by (induction e) (auto simp: num_val_ok_def)

lemma comp_struct_ok_sound:
  "comp_struct_ok nfluents c \<Longrightarrow> num_val_ok w \<Longrightarrow> comp_ok w c"
  by (cases c) (auto intro: nexp_struct_ok_sound)

end

subsection \<open>The executable numeric admission check\<close>

text \<open>An @{const isOK}-form bridge for @{const check_all_list}: needed so the monadic \<open>do\<close>-block
  binds (whose intermediate results are discarded, collapsing to @{const isOK}) rewrite to the
  element-level universals under simp (mirror of @{thm [source] isOK_check_ground_problem_core}).\<close>
lemma isOK_check_all_list[simp]:
  "isOK (check_all_list P l msg msgf) \<longleftrightarrow> (\<forall>x\<in>set l. P x)"
proof -
  have "isOK (check_all_list P l msg msgf) \<longleftrightarrow> check_all_list P l msg msgf = Inr ()"
    by (cases "check_all_list P l msg msgf") (auto simp: isOK_def)
  thus ?thesis by (simp add: check_all_list_return_iff)
qed

text \<open>The numeric twin of the propositional @{const check_ground_problem}: run the propositional core
  admission check @{const check_ground_problem_core}, then one decidable @{const check} / @{const check_all_list} per
  numeric leaf assumption of @{locale numeric_ground_ast_problem}. The valuation-quantified
  encoding-faithfulness assumptions are discharged through the DECIDABLE, valuation-free structural
  sufficient conditions @{const nexp_struct_ok} / @{const comp_struct_ok} (soundness:
  @{thm [source] numeric_tp_nta_reduction_defs.nexp_struct_ok_sound} /
  @{thm [source] numeric_tp_nta_reduction_defs.comp_struct_ok_sound}). This gives the FORWARD direction
  (check succeeds \<Longrightarrow> the numeric leaf holds), which is exactly what the soundness assembly needs.\<close>

lemma list_all_notin_set_eq_disjoint:
  "list_all (\<lambda>x. x \<notin> set ys) xs \<longleftrightarrow> set xs \<inter> set ys = {}"
  by (auto simp: list_all_iff)

context numeric_ground_ast_problem_defs
begin

definition "check_numeric_ground_problem fluent_lo fluent_hi \<equiv> do {
  check_ground_problem_base P;
  check_all_list (\<lambda>a. upds_functional_list (upds (at_start_spec a))) actions_spec
    ''Start-snap numeric updates are not functional (a fluent is written twice)'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. upds_functional_list (upds (at_end_spec a))) actions_spec
    ''End-snap numeric updates are not functional (a fluent is written twice)'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. upds_no_cross_read_list (upds (at_start_spec a))) actions_spec
    ''Start-snap numeric updates cross-read a co-written fluent'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. upds_no_cross_read_list (upds (at_end_spec a))) actions_spec
    ''End-snap numeric updates cross-read a co-written fluent'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>f. fluent_lo f \<le> fluent_hi f) nfluents
    ''Numeric fluent has an empty bound interval (lo > hi)'' (shows o func.name);
  check_all_list (\<lambda>a. list_all (\<lambda>(f, e). nexp_struct_ok_exec nfluents e) (upds (at_start_spec a))) actions_spec
    ''Start-snap numeric update RHS is not structurally integer-faithful'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. list_all (\<lambda>(f, e). nexp_struct_ok_exec nfluents e) (upds (at_end_spec a))) actions_spec
    ''End-snap numeric update RHS is not structurally integer-faithful'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. list_all (comp_struct_ok_exec nfluents) (n_pre (at_start_spec a))) actions_spec
    ''Start-snap numeric precondition is not structurally integer-faithful'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. list_all (comp_struct_ok_exec nfluents) (n_pre (at_end_spec a))) actions_spec
    ''End-snap numeric precondition is not structurally integer-faithful'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. list_all (comp_struct_ok_exec nfluents) (n_inv a)) actions_spec
    ''Numeric over-all invariant is not structurally integer-faithful'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>f. is_int_rat (num_init f)) nfluents
    ''Numeric fluent has a non-integer initial value'' (shows o func.name);
  check_all_list (\<lambda>a. list_all (\<lambda>(f, e). f \<in> set nfluents) (upds (at_start_spec a))) actions_spec
    ''Start-snap numeric update writes an undeclared fluent'' (shows o ast_temporal_action_schema_name);
  check_all_list (\<lambda>a. list_all (\<lambda>(f, e). f \<in> set nfluents) (upds (at_end_spec a))) actions_spec
    ''End-snap numeric update writes an undeclared fluent'' (shows o ast_temporal_action_schema_name);
  check (list_all (comp_struct_ok_exec nfluents) num_goal)
    (ERRS ''Numeric goal is not structurally integer-faithful'')
}"

text \<open>DIAGNOSTIC (temporary): 1-based index of the FIRST failing structural check in
  \<open>check_numeric_ground_problem\<close> (0 = all pass), so the SML glue can report which
  admission clause rejects a problem instead of a coarse NONE.\<close>
definition "check_numeric_ground_problem_diag (fluent_lo :: func \<Rightarrow> int) (fluent_hi :: func \<Rightarrow> int) \<equiv> (
  if \<not> isOK (check_ground_problem_base P) then (1::nat)
  else if \<not> list_all (\<lambda>a. upds_functional_list (upds (at_start_spec a))) actions_spec then 2
  else if \<not> list_all (\<lambda>a. upds_functional_list (upds (at_end_spec a))) actions_spec then 3
  else if \<not> list_all (\<lambda>a. upds_no_cross_read_list (upds (at_start_spec a))) actions_spec then 4
  else if \<not> list_all (\<lambda>a. upds_no_cross_read_list (upds (at_end_spec a))) actions_spec then 5
  else if \<not> list_all (\<lambda>f. fluent_lo f \<le> fluent_hi f) nfluents then 6
  else if \<not> list_all (\<lambda>a. list_all (\<lambda>(f, e). nexp_struct_ok_exec nfluents e) (upds (at_start_spec a))) actions_spec then 7
  else if \<not> list_all (\<lambda>a. list_all (\<lambda>(f, e). nexp_struct_ok_exec nfluents e) (upds (at_end_spec a))) actions_spec then 8
  else if \<not> list_all (\<lambda>a. list_all (comp_struct_ok_exec nfluents) (n_pre (at_start_spec a))) actions_spec then 9
  else if \<not> list_all (\<lambda>a. list_all (comp_struct_ok_exec nfluents) (n_pre (at_end_spec a))) actions_spec then 10
  else if \<not> list_all (\<lambda>a. list_all (comp_struct_ok_exec nfluents) (n_inv a)) actions_spec then 11
  else if \<not> list_all (\<lambda>f. is_int_rat (num_init f)) nfluents then 12
  else if \<not> list_all (\<lambda>a. list_all (\<lambda>(f, e). f \<in> set nfluents) (upds (at_start_spec a))) actions_spec then 13
  else if \<not> list_all (\<lambda>a. list_all (\<lambda>(f, e). f \<in> set nfluents) (upds (at_end_spec a))) actions_spec then 14
  else if \<not> list_all (comp_struct_ok_exec nfluents) num_goal then 15
  else 0)"

lemma check_numeric_ground_problem_return_iff:
  "check_numeric_ground_problem fluent_lo fluent_hi = Inr ()
   \<longleftrightarrow> ground_ast_problem_base P
     \<and> (\<forall>a\<in>set actions_spec. upds_functional_list (upds (at_start_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. upds_functional_list (upds (at_end_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. upds_no_cross_read_list (upds (at_start_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. upds_no_cross_read_list (upds (at_end_spec a)))
     \<and> (\<forall>f\<in>set nfluents. fluent_lo f \<le> fluent_hi f)
     \<and> (\<forall>a\<in>set actions_spec. list_all (\<lambda>(f, e). nexp_struct_ok nfluents e) (upds (at_start_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. list_all (\<lambda>(f, e). nexp_struct_ok nfluents e) (upds (at_end_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. list_all (comp_struct_ok nfluents) (n_pre (at_start_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. list_all (comp_struct_ok nfluents) (n_pre (at_end_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. list_all (comp_struct_ok nfluents) (n_inv a))
     \<and> (\<forall>f\<in>set nfluents. num_init f \<in> \<int>)
     \<and> (\<forall>a\<in>set actions_spec. list_all (\<lambda>(f, e). f \<in> set nfluents) (upds (at_start_spec a)))
     \<and> (\<forall>a\<in>set actions_spec. list_all (\<lambda>(f, e). f \<in> set nfluents) (upds (at_end_spec a)))
     \<and> list_all (comp_struct_ok nfluents) num_goal"
  unfolding check_numeric_ground_problem_def
  by (simp add: return_iff isOK_check_ground_problem_base check_ground_problem_base_return_iff
                is_int_rat_iff_Ints nexp_struct_ok_exec_eq_fun comp_struct_ok_exec_eq_fun)

end

text \<open>FORWARD soundness: the executable numeric admission check succeeding implies the numeric
  admission leaf @{locale numeric_ground_ast_problem} holds. This is the numeric twin of
  @{thm [source] check_ground_problem_return_iff} (forward half only). The decidable side-conditions
  transfer verbatim; the valuation-quantified faithfulness assumptions follow from the structural
  checks by @{thm [source] numeric_tp_nta_reduction_defs.nexp_struct_ok_sound} /
  @{thm [source] numeric_tp_nta_reduction_defs.comp_struct_ok_sound}.\<close>

lemma check_numeric_ground_problem_sound:
  "numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi = Inr ()
     \<Longrightarrow> numeric_ground_ast_problem P fluent_lo fluent_hi"
proof -
  assume h: "numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi = Inr ()"
  interpret D: numeric_ground_ast_problem_defs P .
  from h have "D.check_numeric_ground_problem fluent_lo fluent_hi = Inr ()" by simp
  note C = this[unfolded D.check_numeric_ground_problem_return_iff]
  from C have core: "ground_ast_problem_base P" by simp
  from C have
      uf_s: "\<forall>a\<in>set D.actions_spec. upds_functional_list (D.upds (D.at_start_spec a))"
      and uf_e: "\<forall>a\<in>set D.actions_spec. upds_functional_list (D.upds (D.at_end_spec a))"
      and ncr_s: "\<forall>a\<in>set D.actions_spec. upds_no_cross_read_list (D.upds (D.at_start_spec a))"
      and ncr_e: "\<forall>a\<in>set D.actions_spec. upds_no_cross_read_list (D.upds (D.at_end_spec a))"
      and fb: "\<forall>f\<in>set D.nfluents. fluent_lo f \<le> fluent_hi f"
      and ne_s: "\<forall>a\<in>set D.actions_spec. list_all (\<lambda>(f, e). nexp_struct_ok D.nfluents e) (D.upds (D.at_start_spec a))"
      and ne_e: "\<forall>a\<in>set D.actions_spec. list_all (\<lambda>(f, e). nexp_struct_ok D.nfluents e) (D.upds (D.at_end_spec a))"
      and cp_s: "\<forall>a\<in>set D.actions_spec. list_all (comp_struct_ok D.nfluents) (D.n_pre (D.at_start_spec a))"
      and cp_e: "\<forall>a\<in>set D.actions_spec. list_all (comp_struct_ok D.nfluents) (D.n_pre (D.at_end_spec a))"
      and ci: "\<forall>a\<in>set D.actions_spec. list_all (comp_struct_ok D.nfluents) (D.n_inv a)"
      and niv: "\<forall>f\<in>set D.nfluents. D.num_init f \<in> \<int>"
      and sw_s: "\<forall>a\<in>set D.actions_spec. list_all (\<lambda>(f, e). f \<in> set D.nfluents) (D.upds (D.at_start_spec a))"
      and sw_e: "\<forall>a\<in>set D.actions_spec. list_all (\<lambda>(f, e). f \<in> set D.nfluents) (D.upds (D.at_end_spec a))"
      and cg: "list_all (comp_struct_ok D.nfluents) D.num_goal"
    by simp+
  interpret core: ground_ast_problem_base P by (rule core)
  \<comment> \<open>Primed base: the numeric reduction is built over the injective @{const AtStart}/@{const AtEnd}
      snaps, so the leaf needs NO snap-distinctness.  Its @{locale temp_planning_problem_list_impl_int'}
      obligations are exactly the ones @{locale ground_ast_problem_base} already discharges via its
      @{text abstr_model_checking} sublocale (@{theory_text \<open>Ground_PDDL_Problem_Reduction\<close>}).\<close>
  interpret ndefs: numeric_tp_nta_reduction_defs'
    D.init_spec D.goal_spec D.at_start_spec D.at_end_spec D.over_all_spec
    D.lower_spec D.upper_spec D.pre_spec D.adds_spec D.dels_spec 0
    D.props_spec D.actions_spec D.act_to_name_spec D.prop_to_name_spec
    D.n_pre D.n_inv D.upds D.num_init D.num_goal D.nfluents D.fluent_to_name_spec
    fluent_lo fluent_hi D.const_to_int
    by unfold_locales
       (fact core.abstr_model_checking.distinct_props
             core.abstr_model_checking.distinct_actions
             core.abstr_model_checking.distinct_over_all
             core.abstr_model_checking.goal_consts_in_init_consts
             core.abstr_model_checking.domain_acts_mod_props
             core.abstr_model_checking.act_consts_in_init_consts)+
  have ne_ok: "\<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>(f, e)\<in>set us. ndefs.nexp_ok w e)"
    if "list_all (\<lambda>(f, e). nexp_struct_ok D.nfluents e) us" for us :: "(func \<times> (func, rat) nexp) list"
    using that by (auto simp: list_all_iff intro: ndefs.reduction_ref_impl.nexp_struct_ok_sound)
  have cp_ok: "\<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>c\<in>set cs. ndefs.comp_ok w c)"
    if "list_all (comp_struct_ok D.nfluents) cs" for cs :: "(func, rat) comp list"
    using that by (auto simp: list_all_iff intro: ndefs.reduction_ref_impl.comp_struct_ok_sound)
  show "numeric_ground_ast_problem P fluent_lo fluent_hi"
    apply unfold_locales
    subgoal using uf_s .
    subgoal using uf_e .
    subgoal using ncr_s .
    subgoal using ncr_e .
    subgoal using fb .
    subgoal by (rule ballI, rule ne_ok) (rule bspec[OF ne_s])
    subgoal by (rule ballI, rule ne_ok) (rule bspec[OF ne_e])
    subgoal by (rule ballI, rule cp_ok) (rule bspec[OF cp_s])
    subgoal by (rule ballI, rule cp_ok) (rule bspec[OF cp_e])
    subgoal by (rule ballI, rule cp_ok) (rule bspec[OF ci])
    subgoal using niv .
    subgoal using sw_s by (fastforce simp: list_all_iff)
    subgoal using sw_e by (fastforce simp: list_all_iff)
    subgoal using cp_ok[OF cg] by blast
    done
qed

subsection \<open>Refinement of the numeric constructors to the abstract numeric net\<close>

context numeric_ground_ast_problem
begin

text \<open>The pure augmentation operation coincides with the abstract, locale-local one.\<close>
lemma augment_edge_impl_eq: "augment_edge_impl = ndefs.augment_edge"
  unfolding augment_edge_impl_def ndefs.augment_edge_def ..

text \<open>The computable ground-level fluent-var map coincides with the abstract @{text ndefs.fluent_to_var}:
  both prefix @{text \<open>''fluent_''\<close>} onto the fluent name @{term \<open>func.name\<close>} (@{text ndefs}'s
  @{text fluent_to_name} slot is instantiated by @{const fluent_to_name_spec}).\<close>
lemma fluent_to_var_spec_eq: "fluent_to_var_spec = ndefs.fluent_to_var"
  unfolding fluent_to_var_spec_def ndefs.fluent_to_var_def ..

text \<open>The computable numeric guards/updates coincide with the abstract @{text ndefs} ones: same numeric
  data, same encoders.\<close>
lemma num_pre_guard_refine_start: "num_pre_guard' (at_start_spec a) = ndefs.num_pre_guard (AtStart a)"
  unfolding num_pre_guard'_def ndefs.num_pre_guard_def fluent_to_var_spec_eq
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps ..

lemma num_pre_guard_refine_end: "num_pre_guard' (at_end_spec a) = ndefs.num_pre_guard (AtEnd a)"
  unfolding num_pre_guard'_def ndefs.num_pre_guard_def fluent_to_var_spec_eq
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps ..

lemma num_inv_guard_refine: "num_inv_guard' a = ndefs.num_inv_guard a"
  unfolding num_inv_guard'_def ndefs.num_inv_guard_def fluent_to_var_spec_eq ..

lemma num_goal_guard_refine: "num_goal_guard' = ndefs.num_goal_guard"
  unfolding num_goal_guard'_def ndefs.num_goal_guard_def fluent_to_var_spec_eq ..

lemma num_upd_refine_start: "num_upd' (at_start_spec a) = ndefs.num_upd (AtStart a)"
  unfolding num_upd'_def ndefs.num_upd_def fluent_to_var_spec_eq
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps ..

lemma num_upd_refine_end: "num_upd' (at_end_spec a) = ndefs.num_upd (AtEnd a)"
  unfolding num_upd'_def ndefs.num_upd_def fluent_to_var_spec_eq
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps ..

lemma num_init_upd_refine: "num_init_upd' = ndefs.num_init_upd"
  unfolding num_init_upd'_def ndefs.num_init_upd_def fluent_to_var_spec_eq ..

lemma num_fluent_vars_refine: "num_fluent_vars' fluent_lo fluent_hi = ndefs.num_fluent_vars"
  unfolding num_fluent_vars'_def ndefs.num_fluent_vars_def fluent_to_var_spec_eq ..

text \<open>Atomic refines: the abstract @{text ndefs} propositional constants coincide with the executable
  impl constants. (Same proofs as the propositional @{text ground_ast_problem} atomic refines, but for
  the RAW @{text ndefs} interpretation, which is the one the numeric net is built over.)\<close>

lemma ndefs_prop_to_var: "ndefs.prop_to_var = prop_to_var_impl predicate.name"
  by (fold prop_to_name_spec_def) (rule ext, simp add: ndefs.prop_to_var_def prop_to_var_impl_def)

lemma ndefs_prop_to_lock: "ndefs.prop_to_lock = prop_to_lock_impl predicate.name"
  by (fold prop_to_name_spec_def) (rule ext, simp add: ndefs.prop_to_lock_def prop_to_lock_impl_def)

lemma ndefs_acts_active: "ndefs.acts_active = acts_active_impl"
  unfolding ndefs.acts_active_def acts_active_impl_def ..

lemma ndefs_planning_lock: "ndefs.planning_lock = planning_lock_impl"
  unfolding ndefs.planning_lock_def planning_lock_impl_def ..

lemma ndefs_act_to_start_clock: "ndefs.act_to_start_clock = act_to_start_clock_impl ast_temporal_action_schema_name"
  by (fold act_to_name_spec_def) (rule ext, simp add: ndefs.act_to_start_clock_def act_to_start_clock_impl_def)

lemma ndefs_act_to_end_clock: "ndefs.act_to_end_clock = act_to_end_clock_impl ast_temporal_action_schema_name"
  by (fold act_to_name_spec_def) (rule ext, simp add: ndefs.act_to_end_clock_def act_to_end_clock_impl_def)

lemma ndefs_off_loc: "ndefs.off_loc = off_loc_impl"
  unfolding ndefs.off_loc_def off_loc_impl_def ..

lemma ndefs_starting_loc: "ndefs.starting_loc = starting_loc_impl"
  unfolding ndefs.starting_loc_def starting_loc_impl_def ..

lemma ndefs_running_loc: "ndefs.running_loc = running_loc_impl"
  unfolding ndefs.running_loc_def running_loc_impl_def ..

lemma ndefs_ending_loc: "ndefs.ending_loc = ending_loc_impl"
  unfolding ndefs.ending_loc_def ending_loc_impl_def ..

lemma ndefs_init_loc: "ndefs.init_loc = init_loc_impl"
  unfolding ndefs.init_loc_def init_loc_impl_def ..

lemma ndefs_planning_loc: "ndefs.planning_loc = planning_loc_impl"
  unfolding ndefs.planning_loc_def planning_loc_impl_def ..

lemma ndefs_goal_loc: "ndefs.goal_loc = goal_loc_impl"
  unfolding ndefs.goal_loc_def goal_loc_impl_def ..

lemma ndefs_is_prop_ab: "ndefs.is_prop_ab n = (var_is n) o (prop_to_var_impl predicate.name)"
  unfolding ndefs.is_prop_ab_def ndefs_prop_to_var ..

lemma ndefs_set_prop_ab: "ndefs.set_prop_ab n = (set_var n) o (prop_to_var_impl predicate.name)"
  unfolding ndefs.set_prop_ab_def ndefs_prop_to_var ..

lemma ndefs_inc_prop_ab: "ndefs.inc_prop_ab n = (inc_var n) o (prop_to_var_impl predicate.name)"
  unfolding ndefs.inc_prop_ab_def ndefs_prop_to_var ..

lemma ndefs_is_prop_lock_ab: "ndefs.is_prop_lock_ab n = (var_is n) o (prop_to_lock_impl predicate.name)"
  unfolding ndefs.is_prop_lock_ab_def ndefs_prop_to_lock ..

lemma ndefs_set_prop_lock_ab: "ndefs.set_prop_lock_ab n = (set_var n) o (prop_to_lock_impl predicate.name)"
  unfolding ndefs.set_prop_lock_ab_def ndefs_prop_to_lock ..

lemma ndefs_inc_prop_lock_ab: "ndefs.inc_prop_lock_ab n = (inc_var n) o (prop_to_lock_impl predicate.name)"
  unfolding ndefs.inc_prop_lock_ab_def ndefs_prop_to_lock ..

lemma ndefs_pl_is_1: "ndefs.pl_is_1 = var_is 1 planning_lock_impl"
  unfolding ndefs.pl_is_1_def ndefs_planning_lock ..

text \<open>The primed @{text ndefs} net is built over the RESTRICTED @{text pre_imp_restr_list} /
  @{text over_all_restr_list}; on the reachable snap/action set (@{const AtStart}/@{const AtEnd} of
  @{const actions_spec}) the restriction is the identity, because ground actions only reference
  propositions.  These are the RAW analogues of the propositional @{text ground_ast_problem}
  equivalences (@{text pre_imp_restr_equiv_pre_imp} / @{text over_all_restr_equiv_over_all}), re-proved
  here off the @{locale ground_ast_problem_base} in-props facts.\<close>
lemma pre_imp_restr_equiv_pre_imp:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "imp_defs.rat_impl.pre_imp_restr_list a = imp_defs.rat_impl.pre_imp_list a"
proof -
  have "set (imp_defs.rat_impl.pre_imp_list a) \<subseteq> set props_spec"
  proof (intro subsetI)
    fix x
    assume "x \<in> set (imp_defs.rat_impl.pre_imp_list a)"
    thus "x \<in> set props_spec"
      using assms
      apply (induction a)
      unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.set_impl.app_snap.simps
      using start_pre_in_props end_pre_in_props by blast+
  qed
  thus ?thesis
    unfolding imp_defs.rat_impl.pre_imp_restr_list_def
    by (force simp: filter_id_conv)
qed

lemma over_all_restr_equiv_over_all:
  assumes "a \<in> set actions_spec"
  shows "imp_defs.rat_impl.over_all_restr_list a = over_all_spec a"
proof -
  have "set (over_all_spec a) \<subseteq> set props_spec"
    using over_all_in_props assms by simp
  thus ?thesis unfolding imp_defs.rat_impl.over_all_restr_list_def
    by (force simp: filter_id_conv)
qed

text \<open>The abstract @{text ndefs} mutex test on LABELLED snaps coincides with the executable
  @{const mutex_snap_action'}; the primed net's @{text pre_imp_restr_list} collapses to
  @{text pre_imp_list} on the reachable snaps via @{thm pre_imp_restr_equiv_pre_imp}.\<close>
lemma ndefs_mutex_snap_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
      and "b \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "ndefs.mutex_effects a b = mutex_snap_action' a b"
  unfolding mutex_snap_action'_def
  apply (subst abstr_model_checking.rat_imp'.prob_list_impl.set_impl.mutex_snap_action_def)
  unfolding comp_def apply (subst pre_imp_restr_equiv_pre_imp, use assms in blast)+
  apply (subst action_defs.mutex_snap_action_def[symmetric])
  by simp

lemma ndefs_net_int_clocks_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "ndefs.net_int_clocks a = net_int_clocks' a"
proof -
  have 1: "filter (\<lambda>aa. ndefs.mutex_effects a (AtStart aa)) actions_spec = filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec"
    apply (rule filter_eq_conv)
    using ndefs_mutex_snap_refine[OF assms] by simp
  have 2: "filter (\<lambda>aa. ndefs.mutex_effects a (AtEnd aa)) actions_spec = filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec"
    apply (rule filter_eq_conv)
    using ndefs_mutex_snap_refine[OF assms] by simp
  show ?thesis
    unfolding ndefs.net_int_clocks_def Let_def
    unfolding 1 2 net_int_clocks'_def
    unfolding ndefs_act_to_start_clock ndefs_act_to_end_clock
    by blast
qed

text \<open>Each RAW abstract propositional edge (the @{text ndefs} interpretation, over @{const at_start_spec}
  / @{const pre_spec} / ...) coincides with the executable propositional edge (over @{const AtStart} /
  @{const imp_defs.rat_impl.pre_imp_list} / ...), bridged pointwise through @{text app_snap} and the atomic
  refines above.  These are the RAW analogues of the propositional @{text ground_ast_problem} @{text
  \<open>*_refine\<close>} lemmas, re-proved here because the numeric net is built over the RAW net.\<close>

lemma ndefs_start_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "ndefs.start_edge a = start_edge' a"
  unfolding ndefs.start_edge_def start_edge'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_is_prop_lock_ab ndefs_set_prop_ab
  unfolding ndefs_pl_is_1 ndefs_acts_active ndefs_off_loc ndefs_starting_loc
  unfolding ndefs_act_to_start_clock
  using ndefs_net_int_clocks_refine assms pre_imp_restr_equiv_pre_imp
  by simp

lemma ndefs_end_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "ndefs.end_edge a = end_edge' a"
  unfolding ndefs.end_edge_def end_edge'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_is_prop_lock_ab ndefs_set_prop_ab
  unfolding ndefs_pl_is_1 ndefs_acts_active ndefs_off_loc ndefs_ending_loc
  using pre_imp_restr_equiv_pre_imp assms
  by auto

lemma ndefs_edge_2_refine:
  assumes "a \<in> set actions_spec"
  shows "ndefs.edge_2 a = edge_2' a"
  unfolding ndefs.edge_2_def edge_2'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_inc_prop_lock_ab
  unfolding ndefs_pl_is_1 ndefs_starting_loc ndefs_running_loc
  using over_all_restr_equiv_over_all assms
  by simp

lemma ndefs_lower_spec_refine: "lower_spec = lower_spec_impl"
  apply (intro ext)
  subgoal for x by (cases x rule: ast_temporal_action_schema_cases_unfold) simp+
  done

lemma ndefs_upper_spec_refine: "upper_spec = upper_spec_impl"
  apply (intro ext)
  subgoal for x by (cases x rule: ast_temporal_action_schema_cases_unfold) simp+
  done

lemma ndefs_l_dur_refine: "ndefs.l_dur a = l_dur_impl a"
  unfolding ndefs.l_dur_def l_dur_impl_def
  unfolding ndefs_lower_spec_refine ndefs_act_to_start_clock ..

lemma ndefs_u_dur_refine: "ndefs.u_dur a = u_dur_impl a"
  unfolding ndefs.u_dur_def u_dur_impl_def
  unfolding ndefs_upper_spec_refine ndefs_act_to_start_clock ..

lemma ndefs_edge_3_refine:
  assumes "a \<in> set actions_spec"
  shows "ndefs.edge_3 a = edge_3' a"
  unfolding ndefs.edge_3_def edge_3'_def Let_def
  unfolding ndefs_inc_prop_lock_ab ndefs_pl_is_1
  unfolding ndefs_running_loc ndefs_ending_loc ndefs_act_to_end_clock
  unfolding ndefs_l_dur_refine ndefs_u_dur_refine
  using ndefs_net_int_clocks_refine over_all_restr_equiv_over_all assms
  by simp

lemma ndefs_instant_trans_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "ndefs.instant_trans_edge a = instant_trans_edge' a"
  unfolding ndefs.instant_trans_edge_def instant_trans_edge'_def Let_def
  unfolding ndefs_pl_is_1 ndefs_starting_loc ndefs_ending_loc ndefs_act_to_end_clock
  unfolding ndefs_l_dur_refine ndefs_u_dur_refine
  using ndefs_net_int_clocks_refine assms
  by simp

text \<open>The (unfiltered) @{const init_spec} coincides with the executable @{const init_spec'}: the
  underlying predAtom list is distinct (init is distinct and @{const to_predicate} is injective on the
  no-args predAtoms), so the @{const remdups} in @{const init_spec} is the identity.  (Core-level: uses
  @{text init_no_args} and problem distinctness only, no @{text no_functions}.)\<close>
lemma ndefs_init_spec_eq: "init_spec = init_spec'"
  unfolding init_spec_def init_spec'_def
  apply (rule distinct_remdups_id)
  apply (rule distinct_inj_on_map)
  using wf_temporal_problem unfolding wf_temporal_problem_def apply simp
  apply (rule inj_on_subset)
   apply (rule inj_on_to_predicate)
  using init_preds_no_args unfolding list_all_iff by auto

text \<open>The primed main automaton reads @{const init_spec} / @{const goal_spec} through the
  props-restriction @{text \<open>list_inter props\<close>}; both lists are already @{text \<open>\<subseteq> props_spec\<close>}, so the
  restriction is the identity (RAW analogues of the propositional @{text filter_props_init} /
  @{text filter_props_goal}).\<close>
lemma init_spec_in_props: "set init_spec \<subseteq> set props_spec"
proof (rule subsetI)
  fix x assume "x \<in> set init_spec"
  then obtain y where y: "y \<in> set (init P)" "is_predAtom y" "x = to_predicate y"
    unfolding init_spec_def by auto
  have nfa: "\<not> wf_func_assign y"
    using y(2) by (cases y rule: wf_func_assign.cases) auto
  have "wf_fmla_atom objT y \<or> wf_func_assign y"
    using y(1) wf_temporal_problem unfolding wf_temporal_problem_def by blast
  hence "wf_fmla_atom objT y" using nfa by blast
  thus "x \<in> set props_spec"
    using wf_fmla_atom_in_props y(3) by simp
qed

lemma filter_props_init: "filter (\<lambda>p. p \<in> set props_spec) init_spec = init_spec'"
  using init_spec_in_props ndefs_init_spec_eq by (simp add: filter_id_conv subset_eq)

lemma filter_props_goal: "filter (\<lambda>p. p \<in> set props_spec) goal_spec = goal_spec"
  using goal_in_props filter_id_conv by fast

lemma ndefs_main_auto_init_edge_refine: "ndefs.main_auto_init_edge = main_auto_init_edge'"
  unfolding ndefs.main_auto_init_edge_def main_auto_init_edge'_def Let_def
  unfolding ndefs_set_prop_ab ndefs_planning_lock ndefs_acts_active ndefs_init_loc ndefs_planning_loc
  unfolding filter_props_init
  by simp

lemma ndefs_main_auto_goal_edge_refine: "ndefs.main_auto_goal_edge = main_auto_goal_edge'"
  unfolding ndefs.main_auto_goal_edge_def main_auto_goal_edge'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_planning_lock ndefs_acts_active ndefs_planning_loc ndefs_goal_loc
  unfolding filter_props_goal
  by simp

lemma ndefs_main_auto_loop_refine: "ndefs.main_auto_loop = main_auto_loop_impl"
  unfolding ndefs.main_auto_loop_def main_auto_loop_impl_def
  unfolding ndefs_goal_loc ..

subsection \<open>Refinement of the numeric edges, automata and net\<close>

text \<open>Each executable numeric edge = the abstract @{text ndefs} numeric edge: same augmentation
  (@{thm augment_edge_impl_eq}), same numeric guard/update (the guard/update refines above), and the
  underlying executable propositional edge equals the abstract one (the propositional edge refines).\<close>

lemma num_start_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "num_start_edge' a = ndefs.num_start_edge a"
  unfolding num_start_edge'_def ndefs.num_start_edge_def
  unfolding augment_edge_impl_eq num_pre_guard_refine_start num_upd_refine_start ndefs_start_edge_refine[OF assms] ..

lemma num_end_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "num_end_edge' a = ndefs.num_end_edge a"
  unfolding num_end_edge'_def ndefs.num_end_edge_def
  unfolding augment_edge_impl_eq num_pre_guard_refine_end num_upd_refine_end ndefs_end_edge_refine[OF assms] ..

lemma num_edge_2_refine:
  assumes "a \<in> set actions_spec"
  shows "num_edge_2' a = ndefs.num_edge_2 a"
  unfolding num_edge_2'_def ndefs.num_edge_2_def
  unfolding augment_edge_impl_eq num_inv_guard_refine ndefs_edge_2_refine[OF assms] ..

lemma num_edge_3_refine:
  assumes "a \<in> set actions_spec"
  shows "num_edge_3' a = ndefs.num_edge_3 a"
  unfolding num_edge_3'_def ndefs.num_edge_3_def
  unfolding augment_edge_impl_eq num_inv_guard_refine ndefs_edge_3_refine[OF assms] ..

lemma num_action_to_automaton_refine:
  assumes "a \<in> set actions_spec"
  shows "num_action_to_automaton' a = ndefs.num_action_to_automaton a"
  unfolding num_action_to_automaton'_def ndefs.num_action_to_automaton_def Let_def
  unfolding num_start_edge_refine[OF assms] num_edge_2_refine[OF assms] num_edge_3_refine[OF assms] num_end_edge_refine[OF assms]
  unfolding ndefs_instant_trans_edge_refine[OF assms]
  unfolding ndefs_starting_loc ndefs_ending_loc ..

lemma num_main_auto_init_edge_refine:
  "num_main_auto_init_edge' = ndefs.num_main_auto_init_edge"
  unfolding num_main_auto_init_edge'_def ndefs.num_main_auto_init_edge_def
  unfolding augment_edge_impl_eq num_init_upd_refine ndefs_main_auto_init_edge_refine ..

lemma num_main_auto_goal_edge_refine:
  "num_main_auto_goal_edge' = ndefs.num_main_auto_goal_edge"
  unfolding num_main_auto_goal_edge'_def ndefs.num_main_auto_goal_edge_def
  unfolding augment_edge_impl_eq num_goal_guard_refine ndefs_main_auto_goal_edge_refine ..

lemma num_main_auto_refine: "num_main_auto' = ndefs.num_main_auto"
  unfolding num_main_auto'_def ndefs.num_main_auto_def Let_def
  unfolding num_main_auto_init_edge_refine num_main_auto_goal_edge_refine
  unfolding ndefs_main_auto_loop_refine
  unfolding ndefs_init_loc ndefs_goal_loc ..

lemma num_net_automata_refine:
  "num_net_automata' = ndefs.num_timed_automaton_net"
  unfolding num_net_automata'_def ndefs.num_timed_automaton_net_def
  unfolding num_main_auto_refine
  using num_action_to_automaton_refine by simp

text \<open>The variable bounds / initial locations / reachability formula also coincide (RAW analogues of the
  propositional @{text ground_ast_problem} refines: @{text net_bounds}/@{text init_locs}/@{text
  reach_formula}), using the same @{text app_snap} bridge for the snap var-sets.\<close>

lemma ndefs_inv_vars_refine: "ndefs.inv_vars invs = inv_vars' invs"
  unfolding ndefs.inv_vars_def inv_vars'_def Let_def
  unfolding ndefs_prop_to_lock ndefs_prop_to_var
  by (simp add: image_Un)

lemma ndefs_snap_vars_refine:
  assumes "snap \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "ndefs.snap_vars snap = snap_vars' snap"
  unfolding ndefs.snap_vars_def
  unfolding pre_imp_restr_equiv_pre_imp[OF assms]
  unfolding ndefs_prop_to_var ndefs_prop_to_lock
  unfolding snap_vars'_def
  by presburger

lemma ndefs_action_vars_refine:
  assumes "a \<in> set actions_spec"
  shows "ndefs.action_vars a = action_vars' a"
  unfolding ndefs.action_vars_def
  unfolding ndefs_inv_vars_refine
  using assms ndefs_snap_vars_refine over_all_restr_equiv_over_all
  unfolding action_vars'_def
  by auto

lemma ndefs_net_bounds_refine: "net_bounds' = ndefs.net_bounds"
  unfolding ndefs.all_vars_def net_bounds'_def Let_def
  unfolding ndefs_prop_to_lock ndefs_prop_to_var ndefs_acts_active ndefs_planning_lock
  unfolding filter_props_init filter_props_goal
  unfolding fold_union' set_map
  using ndefs_action_vars_refine
  by auto

lemma ndefs_init_locs_refine: "init_locs' = ndefs.init_locs"
  unfolding ndefs.init_locs_def init_locs'_def
  unfolding ndefs_init_loc ndefs_off_loc ..

lemma ndefs_reach_formula_refine: "reach_formula' = ndefs.reach_formula"
  unfolding ndefs.reach_formula_def reach_formula'_def
  unfolding ndefs_goal_loc ..

text \<open>The numeric variable bounds, initial locations/variables and reachability formula coincide with the
  abstract @{text ndefs} numeric net: the numeric bounds append one bounded @{typ int} variable per fluent
  to the propositional bounds, and the locations/formula are unchanged.\<close>

lemma num_net_bounds_refine:
  "num_net_bounds' fluent_lo fluent_hi = ndefs.num_net_bounds"
  unfolding num_net_bounds'_def ndefs.num_all_vars_def
  unfolding ndefs_net_bounds_refine num_fluent_vars_refine ..

lemma num_init_locs_refine: "num_init_locs' = ndefs.init_locs"
  unfolding num_init_locs'_def ndefs_init_locs_refine ..

lemma num_init_vars_refine:
  "num_init_vars' fluent_lo fluent_hi = ndefs.num_init_vars"
  unfolding num_init_vars'_def ndefs.num_init_vars_def
  unfolding num_net_bounds_refine ..

lemma num_reach_formula_refine: "num_reach_formula' = ndefs.reach_formula"
  unfolding num_reach_formula'_def ndefs_reach_formula_refine ..

subsection \<open>The executable numeric model-checking problem\<close>

text \<open>The numeric twin of @{thm [source] ground_ast_problem.model_checking_problem_refine}: if the
  Munta semantics of the \<^emph>\<open>executable\<close> numeric net does not reach the (numeric) goal formula from the
  executable initial configuration, then the ground problem has no valid, bounded numeric plan.  Proved
  by rewriting the executable numeric net / bounds / initial configuration / formula to the abstract
  @{text ndefs} numeric net via the refines above, and firing the WP-A soundness capstone
  @{thm [source] num_net_form_not_sat_imp_no_valid_ground_plan}.\<close>

lemma num_model_checking_problem_refine:
  "\<not> Simple_Network_Impl.sem num_net_automata' ndefs.net_broadcast
        (num_net_bounds' fluent_lo fluent_hi),
      (num_init_locs', map_of (num_init_vars' fluent_lo fluent_hi), (\<lambda>_. 0))
      \<Turnstile> num_reach_formula'
   \<Longrightarrow> \<not>(\<exists>\<pi>. numeric_valid_ground_plan P fluent_lo fluent_hi \<pi>)"
  using num_net_form_not_sat_imp_no_valid_ground_plan
  unfolding num_net_automata_refine num_net_bounds_refine
  unfolding num_init_locs_refine num_init_vars_refine num_reach_formula_refine
  unfolding num_a\<^sub>0_def[symmetric]
  by blast

end


section \<open>WP-D: the numeric network assembly\<close>

text \<open>The numeric twin of @{const make_network_impl} / @{const check_and_make_network} (theory
  @{text Ground_PDDL_NTA_Reduction_Impl}): the pure builder assembles the concrete Munta NTA from the
  executable numeric constructors, and @{term check_and_make_numeric_network} runs the numeric admission
  check @{const numeric_ground_ast_problem_defs.check_numeric_ground_problem} first.  Soundness fires the
  WP-C capstone @{thm [source] numeric_ground_ast_problem.num_model_checking_problem_refine} at the
  admitted leaf: if the executable numeric net cannot reach the goal, the ground problem has no valid,
  bounded numeric plan.\<close>

definition "num_make_network_impl P fluent_lo fluent_hi \<equiv> do {
  let automata = numeric_ground_ast_problem_defs.num_net_automata' P;
  let broadcast = ground_ast_problem_defs.net_broadcast';
  let bounds = numeric_ground_ast_problem_defs.num_net_bounds' P fluent_lo fluent_hi;
  let init_locs = numeric_ground_ast_problem_defs.num_init_locs' P;
  let init_vars = numeric_ground_ast_problem_defs.num_init_vars' P fluent_lo fluent_hi;
  let formula = numeric_ground_ast_problem_defs.num_reach_formula';
  let clock_names = ground_ast_problem_defs.clock_names P;
  let auto_names = ground_ast_problem_defs.auto_names P;
  let ids_to_names = ground_ast_problem_defs.auto_loc_ids_to_names;
  let process_names_to_index = ground_ast_problem_defs.auto_names_to_index P;
  Error_Monad.return (clock_names, auto_names, ids_to_names, process_names_to_index,
     broadcast, automata, bounds, formula, init_locs, init_vars)
}"

lemma num_make_network_impl_return_iff[return_iff]:
  "num_make_network_impl P fluent_lo fluent_hi = Inr (
    ground_ast_problem_defs.clock_names P,
    ground_ast_problem_defs.auto_names P,
    ground_ast_problem_defs.auto_loc_ids_to_names,
    ground_ast_problem_defs.auto_names_to_index P,
    ground_ast_problem_defs.net_broadcast',
    numeric_ground_ast_problem_defs.num_net_automata' P,
    numeric_ground_ast_problem_defs.num_net_bounds' P fluent_lo fluent_hi,
    numeric_ground_ast_problem_defs.num_reach_formula',
    numeric_ground_ast_problem_defs.num_init_locs' P,
    numeric_ground_ast_problem_defs.num_init_vars' P fluent_lo fluent_hi)"
  unfolding num_make_network_impl_def by (simp add: return_iff)

definition "check_and_make_numeric_network P fluent_lo fluent_hi \<equiv> do {
  numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi;
  num_make_network_impl P fluent_lo fluent_hi
}"

lemma check_and_make_numeric_network_and_plan:
  assumes A: "check_and_make_numeric_network P fluent_lo fluent_hi
       = Inr (clocks, autos, ids_to_names, process_names_to_index,
              broadcast, automata, bounds, formula, init_locs, init_vars)"
  shows "\<not> (Simple_Network_Impl.sem automata broadcast bounds,
             (init_locs, map_of init_vars, (\<lambda>_. 0)) \<Turnstile> formula)
         \<longrightarrow> \<not>(\<exists>\<pi>. numeric_valid_ground_plan P fluent_lo fluent_hi \<pi>)"
proof -
  have chk: "numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi = Inr ()"
  proof (cases "numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi")
    case (Inl e)
    hence "check_and_make_numeric_network P fluent_lo fluent_hi = Inl e"
      unfolding check_and_make_numeric_network_def by simp
    thus ?thesis using A by simp
  next
    case (Inr u) thus ?thesis by simp
  qed
  have leaf: "numeric_ground_ast_problem P fluent_lo fluent_hi"
    using chk by (rule check_numeric_ground_problem_sound)
  have cdef: "check_and_make_numeric_network P fluent_lo fluent_hi = num_make_network_impl P fluent_lo fluent_hi"
    unfolding check_and_make_numeric_network_def chk by simp
  note mk = A[unfolded cdef]
  have eqs: "automata = numeric_ground_ast_problem_defs.num_net_automata' P"
      "broadcast = ground_ast_problem_defs.net_broadcast'"
      "bounds = numeric_ground_ast_problem_defs.num_net_bounds' P fluent_lo fluent_hi"
      "formula = numeric_ground_ast_problem_defs.num_reach_formula'"
      "init_locs = numeric_ground_ast_problem_defs.num_init_locs' P"
      "init_vars = numeric_ground_ast_problem_defs.num_init_vars' P fluent_lo fluent_hi"
    using mk by (simp_all add: num_make_network_impl_return_iff)
  interpret leaf_i: numeric_ground_ast_problem P fluent_lo fluent_hi by (rule leaf)
  have bc: "ground_ast_problem_defs.net_broadcast' = tp_nta_reduction_defs.net_broadcast"
    unfolding ground_ast_problem_defs.net_broadcast'_def leaf_i.ndefs.net_broadcast_def ..
  show ?thesis
    unfolding eqs bc
    using numeric_ground_ast_problem.num_model_checking_problem_refine[OF leaf]
    by blast
qed

end

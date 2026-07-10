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
lemma num_pre_guard_refine: "num_pre_guard' s = ndefs.num_pre_guard s"
  unfolding num_pre_guard'_def ndefs.num_pre_guard_def fluent_to_var_spec_eq ..

lemma num_inv_guard_refine: "num_inv_guard' a = ndefs.num_inv_guard a"
  unfolding num_inv_guard'_def ndefs.num_inv_guard_def fluent_to_var_spec_eq ..

lemma num_goal_guard_refine: "num_goal_guard' = ndefs.num_goal_guard"
  unfolding num_goal_guard'_def ndefs.num_goal_guard_def fluent_to_var_spec_eq ..

lemma num_upd_refine: "num_upd' s = ndefs.num_upd s"
  unfolding num_upd'_def ndefs.num_upd_def fluent_to_var_spec_eq ..

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

text \<open>The abstract @{text ndefs} mutex test on RAW snaps coincides with the executable
  @{const mutex_snap_action'} on the corresponding LABELLED snaps (bridged through @{text app_snap}).\<close>
lemma ndefs_mutex_snap_ss:
  "ndefs.mutex_effects (at_start_spec a) (at_start_spec b) = mutex_snap_action' (AtStart a) (AtStart b)"
  "ndefs.mutex_effects (at_start_spec a) (at_end_spec b) = mutex_snap_action' (AtStart a) (AtEnd b)"
  "ndefs.mutex_effects (at_end_spec a) (at_start_spec b) = mutex_snap_action' (AtEnd a) (AtStart b)"
  "ndefs.mutex_effects (at_end_spec a) (at_end_spec b) = mutex_snap_action' (AtEnd a) (AtEnd b)"
  unfolding mutex_snap_action'_def
  unfolding action_defs.mutex_snap_action_def
  unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.add_imp_list_def imp_defs.rat_impl.del_imp_list_def
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps
  by simp+

lemma ndefs_net_int_clocks_start:
  "ndefs.net_int_clocks (at_start_spec a) = net_int_clocks' (AtStart a)"
  unfolding ndefs.net_int_clocks_def net_int_clocks'_def Let_def
  unfolding ndefs_act_to_start_clock ndefs_act_to_end_clock
  by (simp add: ndefs_mutex_snap_ss cong: filter_cong)

lemma ndefs_net_int_clocks_end:
  "ndefs.net_int_clocks (at_end_spec a) = net_int_clocks' (AtEnd a)"
  unfolding ndefs.net_int_clocks_def net_int_clocks'_def Let_def
  unfolding ndefs_act_to_start_clock ndefs_act_to_end_clock
  by (simp add: ndefs_mutex_snap_ss cong: filter_cong)

text \<open>Each RAW abstract propositional edge (the @{text ndefs} interpretation, over @{const at_start_spec}
  / @{const pre_spec} / ...) coincides with the executable propositional edge (over @{const AtStart} /
  @{const imp_defs.rat_impl.pre_imp_list} / ...), bridged pointwise through @{text app_snap} and the atomic
  refines above.  These are the RAW analogues of the propositional @{text ground_ast_problem} @{text
  \<open>*_refine\<close>} lemmas, re-proved here because the numeric net is built over the RAW net.\<close>

lemma ndefs_start_edge_refine: "ndefs.start_edge a = start_edge' a"
  unfolding ndefs.start_edge_def start_edge'_def Let_def
  unfolding ndefs_net_int_clocks_start
  unfolding ndefs_is_prop_ab ndefs_is_prop_lock_ab ndefs_set_prop_ab
  unfolding ndefs_pl_is_1 ndefs_acts_active ndefs_off_loc ndefs_starting_loc
  unfolding ndefs_act_to_start_clock
  unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.add_imp_list_def imp_defs.rat_impl.del_imp_list_def
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps
  by simp

lemma ndefs_end_edge_refine: "ndefs.end_edge a = end_edge' a"
  unfolding ndefs.end_edge_def end_edge'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_is_prop_lock_ab ndefs_set_prop_ab
  unfolding ndefs_pl_is_1 ndefs_acts_active ndefs_off_loc ndefs_ending_loc
  unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.add_imp_list_def imp_defs.rat_impl.del_imp_list_def
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps
  by simp

lemma ndefs_edge_2_refine: "ndefs.edge_2 a = edge_2' a"
  unfolding ndefs.edge_2_def edge_2'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_inc_prop_lock_ab
  unfolding ndefs_pl_is_1 ndefs_starting_loc ndefs_running_loc
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

lemma ndefs_edge_3_refine: "ndefs.edge_3 a = edge_3' a"
  unfolding ndefs.edge_3_def edge_3'_def Let_def
  unfolding ndefs_net_int_clocks_end
  unfolding ndefs_inc_prop_lock_ab ndefs_pl_is_1
  unfolding ndefs_running_loc ndefs_ending_loc ndefs_act_to_end_clock
  unfolding ndefs_l_dur_refine ndefs_u_dur_refine
  by simp

lemma ndefs_instant_trans_edge_refine: "ndefs.instant_trans_edge a = instant_trans_edge' a"
  unfolding ndefs.instant_trans_edge_def instant_trans_edge'_def Let_def
  unfolding ndefs_net_int_clocks_end
  unfolding ndefs_pl_is_1 ndefs_starting_loc ndefs_ending_loc ndefs_act_to_end_clock
  unfolding ndefs_l_dur_refine ndefs_u_dur_refine
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
  using init_no_args unfolding list_all_iff by auto

lemma ndefs_main_auto_init_edge_refine: "ndefs.main_auto_init_edge = main_auto_init_edge'"
  unfolding ndefs.main_auto_init_edge_def main_auto_init_edge'_def Let_def
  unfolding ndefs_set_prop_ab ndefs_planning_lock ndefs_acts_active ndefs_init_loc ndefs_planning_loc
  unfolding ndefs_init_spec_eq
  by simp

lemma ndefs_main_auto_goal_edge_refine: "ndefs.main_auto_goal_edge = main_auto_goal_edge'"
  unfolding ndefs.main_auto_goal_edge_def main_auto_goal_edge'_def Let_def
  unfolding ndefs_is_prop_ab ndefs_planning_lock ndefs_acts_active ndefs_planning_loc ndefs_goal_loc
  by simp

lemma ndefs_main_auto_loop_refine: "ndefs.main_auto_loop = main_auto_loop_impl"
  unfolding ndefs.main_auto_loop_def main_auto_loop_impl_def
  unfolding ndefs_goal_loc ..

subsection \<open>Refinement of the numeric edges, automata and net\<close>

text \<open>Each executable numeric edge = the abstract @{text ndefs} numeric edge: same augmentation
  (@{thm augment_edge_impl_eq}), same numeric guard/update (the guard/update refines above), and the
  underlying executable propositional edge equals the abstract one (the propositional edge refines).\<close>

lemma num_start_edge_refine: "num_start_edge' a = ndefs.num_start_edge a"
  unfolding num_start_edge'_def ndefs.num_start_edge_def
  unfolding augment_edge_impl_eq num_pre_guard_refine num_upd_refine ndefs_start_edge_refine ..

lemma num_end_edge_refine: "num_end_edge' a = ndefs.num_end_edge a"
  unfolding num_end_edge'_def ndefs.num_end_edge_def
  unfolding augment_edge_impl_eq num_pre_guard_refine num_upd_refine ndefs_end_edge_refine ..

lemma num_edge_2_refine: "num_edge_2' a = ndefs.num_edge_2 a"
  unfolding num_edge_2'_def ndefs.num_edge_2_def
  unfolding augment_edge_impl_eq num_inv_guard_refine ndefs_edge_2_refine ..

lemma num_edge_3_refine: "num_edge_3' a = ndefs.num_edge_3 a"
  unfolding num_edge_3'_def ndefs.num_edge_3_def
  unfolding augment_edge_impl_eq num_inv_guard_refine ndefs_edge_3_refine ..

lemma num_action_to_automaton_refine:
  "num_action_to_automaton' a = ndefs.num_action_to_automaton a"
  unfolding num_action_to_automaton'_def ndefs.num_action_to_automaton_def Let_def
  unfolding num_start_edge_refine num_edge_2_refine num_edge_3_refine num_end_edge_refine
  unfolding ndefs_instant_trans_edge_refine
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

lemma ndefs_snap_vars_start_refine: "ndefs.snap_vars (at_start_spec a) = snap_vars' (AtStart a)"
  unfolding ndefs.snap_vars_def snap_vars'_def Let_def
  unfolding ndefs_prop_to_var ndefs_prop_to_lock
  unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.add_imp_list_def imp_defs.rat_impl.del_imp_list_def
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps
  by simp

lemma ndefs_snap_vars_end_refine: "ndefs.snap_vars (at_end_spec a) = snap_vars' (AtEnd a)"
  unfolding ndefs.snap_vars_def snap_vars'_def Let_def
  unfolding ndefs_prop_to_var ndefs_prop_to_lock
  unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.add_imp_list_def imp_defs.rat_impl.del_imp_list_def
  unfolding imp_defs.rat_impl.set_impl.app_snap.simps
  by simp

lemma ndefs_action_vars_refine: "ndefs.action_vars a = action_vars' a"
  unfolding ndefs.action_vars_def action_vars'_def Let_def
  unfolding ndefs_inv_vars_refine ndefs_snap_vars_start_refine ndefs_snap_vars_end_refine
  by (simp add: sup_commute sup_left_commute)

lemma ndefs_net_bounds_refine: "net_bounds' = ndefs.net_bounds"
  unfolding ndefs.all_vars_def net_bounds'_def Let_def
  unfolding ndefs_prop_to_lock ndefs_prop_to_var ndefs_acts_active ndefs_planning_lock
  unfolding ndefs_action_vars_refine ndefs_init_spec_eq
  by (simp add: fold_union')

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

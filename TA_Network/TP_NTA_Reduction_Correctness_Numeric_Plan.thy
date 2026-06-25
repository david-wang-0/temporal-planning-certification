theory TP_NTA_Reduction_Correctness_Numeric_Plan
  imports TP_NTA_Reduction_Correctness_Numeric_Happening
begin

context numeric_tp_nta_reduction_correctness
begin

text \<open>The propositional invariant transfers between consecutive happenings, extracted (config-generic)
from @{thm [source] plan_steps_possible}'s cases. They thread the @{text planning_sem} bookkeeping
across the index boundary; the numeric run-lifting reuses them verbatim and only adds the (identity)
tracking transfer.\<close>
lemma pp_post_imp_pre_pre_delay_Suc:
  assumes ib: "i < length planning_sem.htpl - 1"
      and post: "happening_post i (L, v, c)"
  shows "happening_pre_pre_delay (Suc i) (L, v, c)"
proof -
  have ib1: "i < length planning_sem.htpl"
    and ib2: "Suc i < length planning_sem.htpl" using ib by linarith+
  note D = happening_post_dests[OF post HOL.refl]
  have c2: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ (Suc i) p)"
    using D(1) ib1 ib2 by (auto simp: prop_state_after_happ_def prop_state_before_happ_def planning_sem.state_seq_Suc_is_upd_state)
  have c3: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index (Suc i)) p))"
    using D(2) ib1 ib2 by (auto simp: planning_sem.locked_after_indexed_timepoint_is_locked_before_Suc[symmetric])
  have c4: "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index (Suc i))))"
    using D(3) ib1 ib2 by (auto simp: planning_sem.active_after_indexed_timepoint_is_active_before_Suc[symmetric])
  have c5: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 0 \<longrightarrow> L ! Suc j = off_loc"
    using D(4) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c6: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 1 \<longrightarrow> L ! Suc j = running_loc"
    using D(5) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c7: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_start_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(6) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  have c8: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_end_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(7) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  show ?thesis by (rule happening_pre_pre_delayI[OF HOL.refl c2 c3 c4 c5 c6 c7 c8])
qed

lemma pp_init_imp_pre_pre_delay_0:
  assumes hlen: "0 < length planning_sem.htpl"
      and props': "init_planning_state_props' x"
  shows "happening_pre_pre_delay 0 x"
proof (rule init_planning_state_props'E[OF props'])
  fix L v c
  assume s: "x = (L, v, c)"
    and va: "v acts_active = Some 0"
    and Leq: "L = planning_loc # map (\<lambda>x. off_loc) actions"
    and pv: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p)"
    and pl: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    and cs: "\<forall>i<length actions. c (act_to_start_clock (actions ! i)) = 0"
    and ce: "\<forall>i<length actions. c (act_to_end_clock (actions ! i)) = 0"
  have c2: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ 0 p)"
    using pv hlen by (auto simp: planning_sem.plan_state_seq_props prop_state_before_happ_def)
  have c3: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index 0) p))"
    using pl by (auto simp: int_of_nat_def planning_sem.locked_before_initial_is_0)
  have c4: "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index 0)))"
    using va by (auto simp: int_of_nat_def planning_sem.active_before_initial_is_0)
  have c5: "\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index 0) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc"
    using Leq by (auto simp: planning_sem.open_active_count_initial_is_0)
  have c6: "\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index 0) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc"
    using Leq by (auto simp: planning_sem.open_active_count_initial_is_0)
  have c7: "\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay 0) act_to_start_clock (actions ! i) (planning_sem.time_index 0)"
    using cs hlen by (subst act_clock_pre_happ_simps cval_add_def planning_sem.exec_time_at_init)+
      (auto simp: get_delay_def planning_sem.card_htps_len_htpl of_rat_add Rat.of_int_def)
  have c8: "\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay 0) act_to_end_clock (actions ! i) (planning_sem.time_index 0)"
    using ce hlen by (subst act_clock_pre_happ_simps cval_add_def planning_sem.exec_time_at_init)+
      (auto simp: get_delay_def planning_sem.card_htps_len_htpl of_rat_add Rat.of_int_def)
  show "happening_pre_pre_delay 0 x" by (rule happening_pre_pre_delayI[OF s c2 c3 c4 c5 c6 c7 c8])
qed

lemma pp_post_last_imp_goal_trans_pre:
  assumes hlen: "0 < length planning_sem.htpl"
      and lvp: "LvP x"
      and post: "happening_post (length planning_sem.htpl - 1) x"
  shows "goal_trans_pre x"
proof -
  obtain L v c where s: "x = (L, v, c)" by (rule prod_cases3)
  have lv: "Lv_conds L v" using lvp unfolding s by simp
  note D = happening_post_dests[OF post s]
  have c3: "v acts_active = Some 0"
    using D(3) by (subst (asm) planning_sem.active_after_final_is_0) simp
  have c4: "L = planning_loc # map (\<lambda>x. off_loc) actions"
  proof (subst list_eq_iff_nth_eq, intro conjI allI impI)
    show "length L = length (planning_loc # map (\<lambda>x. off_loc) actions)"
      using Lv_conds_dests(1)[OF lv] by simp
  next
    fix i assume i: "i < length L"
    show "L ! i = (planning_loc # map (\<lambda>x. off_loc) actions) ! i"
    proof (cases i)
      case 0
      thus ?thesis using Lv_conds_dests(2)[OF lv] by simp
    next
      case (Suc i')
      hence i': "i' < length actions" using i Lv_conds_dests(1)[OF lv] by simp
      have "planning_sem.closed_active_count (planning_sem.time_index (length planning_sem.htpl - 1)) (actions ! i') = 0"
        by (rule planning_sem.closed_active_count_final_is_0[OF nth_mem[OF i']])
      hence "L ! Suc i' = off_loc" using D(4) i' by blast
      thus ?thesis using Suc i' by simp
    qed
  qed
  have c5: "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p))"
    apply (rule exI[of _ "planning_sem.upd_state (length planning_sem.htpl - 1)"])
    using D(1) hlen
    apply (subst planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    apply (rule conjI)
    using planning_sem.plan_state_seq_valid apply fastforce
    apply (subst (asm) prop_state_after_happ_def, simp)
    apply (subst (asm) planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    by blast
  have c6: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    using D(2) unfolding planning_sem.locked_after_final_is_0 int_of_nat_def by simp
  show ?thesis by (rule goal_trans_preI[OF s c3 c4 c5 c6])
qed

lemma pp_init_imp_goal_trans_pre:
  assumes hlen: "0 = length planning_sem.htpl"
      and props': "init_planning_state_props' x"
  shows "goal_trans_pre x"
proof -
  have init_is_goal: "set goal \<subseteq> set init"
    using hlen planning_sem.valid_plan_state_seq by auto
  show ?thesis
    apply (rule init_planning_state_props'E[OF props'])
    apply (rule goal_trans_preI)
    using init_is_goal by auto
qed

text \<open>The numeric twins of the four transfers: each is its propositional counterpart plus the
(essentially identity) tracking transfer at the matching index.\<close>
lemma num_post_imp_pre_pre_delay_Suc:
  assumes ib: "i < length planning_sem.htpl - 1"
      and lvp: "num_LvP cfg"
      and post: "num_happening_post M i cfg"
  shows "num_happening_pre_pre_delay M (Suc i) cfg \<and> num_LvP cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "happening_post i (L, v |` dom (map_of net_bounds), c)" using post[unfolded cfg] by (rule num_happening_post_propD)
  have t: "num_tracks v (snd (M (Suc i)))" using post[unfolded cfg] by (rule num_happening_post_trackD)
  have "num_happening_pre_pre_delay M (Suc i) cfg" unfolding cfg
    by (rule num_happening_pre_pre_delayI[where M = M and i = "Suc i", OF pp_post_imp_pre_pre_delay_Suc[OF ib p] t])
  thus ?thesis using lvp by blast
qed

lemma num_init_imp_pre_pre_delay_0:
  assumes hlen: "0 < length planning_sem.htpl"
      and lvp: "num_LvP cfg"
      and props': "num_init_planning_state_props' M cfg"
  shows "num_happening_pre_pre_delay M 0 cfg \<and> num_LvP cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" using props'[unfolded cfg] by (rule num_init_planning_state_props'_propD)
  have t: "num_tracks v (snd (M 0))" using props'[unfolded cfg] by (rule num_init_planning_state_props'_trackD)
  have "num_happening_pre_pre_delay M 0 cfg" unfolding cfg
    by (rule num_happening_pre_pre_delayI[where M = M and i = 0, OF pp_init_imp_pre_pre_delay_0[OF hlen p] t])
  thus ?thesis using lvp by blast
qed

lemma num_post_last_imp_goal_trans_pre:
  assumes hlen: "0 < length planning_sem.htpl"
      and lvp: "num_LvP cfg"
      and post: "num_happening_post M (length planning_sem.htpl - 1) cfg"
  shows "num_goal_trans_pre M cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have lvpr: "LvP (L, v |` dom (map_of net_bounds), c)" using lvp[unfolded cfg] by (rule num_LvP_imp_LvP)
  have p: "happening_post (length planning_sem.htpl - 1) (L, v |` dom (map_of net_bounds), c)" using post[unfolded cfg] by (rule num_happening_post_propD)
  have t0: "num_tracks v (snd (M (Suc (length planning_sem.htpl - 1))))" using post[unfolded cfg] by (rule num_happening_post_trackD)
  have suc_eq: "Suc (length planning_sem.htpl - 1) = length planning_sem.htpl" using hlen by simp
  have t: "num_tracks v (snd (M (length planning_sem.htpl)))" using t0 unfolding suc_eq .
  show ?thesis unfolding cfg
    by (rule num_goal_trans_preI[where M = M, OF pp_post_last_imp_goal_trans_pre[OF hlen lvpr p] t])
qed

lemma num_init_imp_goal_trans_pre:
  assumes hlen: "0 = length planning_sem.htpl"
      and props': "num_init_planning_state_props' M cfg"
  shows "num_goal_trans_pre M cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" using props'[unfolded cfg] by (rule num_init_planning_state_props'_propD)
  have t0: "num_tracks v (snd (M 0))" using props'[unfolded cfg] by (rule num_init_planning_state_props'_trackD)
  have t: "num_tracks v (snd (M (length planning_sem.htpl)))" using t0 by (simp add: hlen[symmetric])
  show ?thesis unfolding cfg
    by (rule num_goal_trans_preI[where M = M, OF pp_init_imp_goal_trans_pre[OF hlen p] t])
qed

text \<open>The numeric plan run, existentially: from a combined initial config (propositional
@{const init_planning_state_props'} plus tracking of @{term \<open>snd (M 0)\<close>}), the numeric net has a run
reaching a @{const num_goal_trans_pre} config. Mirrors @{thm [source] plan_steps_possible} but threads
the existential numeric run happening-by-happening (rather than via the @{const ext_seq'} combinator,
since the numeric configs differ from the propositional ones): the inner @{text chain} runs happenings
@{term j}..@{term \<open>length htpl - 1\<close>}, extending the run by @{thm [source] num_happening_steps_possible}
and carrying @{const num_happening_post} to the next happening's @{const num_happening_pre_pre_delay}.\<close>
lemma num_plan_steps_possible:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and lvp: "num_LvP cfg"
      and pres: "num_init_planning_state_props' M cfg"
  shows "\<exists>ms. num_graph_impl.steps (cfg # ms) \<and> num_goal_trans_pre M (last (cfg # ms))"
proof (cases "length planning_sem.htpl = 0")
  case True
  have g: "num_goal_trans_pre M cfg" by (rule num_init_imp_goal_trans_pre[OF True[symmetric] pres])
  show ?thesis
  proof (intro exI[of _ "[]"] conjI)
    show "num_graph_impl.steps (cfg # [])" by (rule num_graph_impl.steps.Single)
    show "num_goal_trans_pre M (last (cfg # []))" using g by simp
  qed
next
  case False
  hence hlen: "0 < length planning_sem.htpl" by simp
  \<comment> \<open>@{const num_LvP} is threaded as a SEPARATE conjunct through the run, mirroring @{const LvP} in
     @{thm [source] plan_steps_possible}: each step's @{thm [source] num_happening_steps_possible} both
     consumes and re-produces it, and the transfer to the next happening passes it through unchanged
     (same store).\<close>
  have chain: "\<exists>ms. num_graph_impl.steps (cfg' # ms)
                   \<and> num_happening_post M (length planning_sem.htpl - 1) (last (cfg' # ms))
                   \<and> num_LvP (last (cfg' # ms))"
    if "num_happening_pre_pre_delay M j cfg'" "num_LvP cfg'" "j < length planning_sem.htpl" for j cfg'
    using that
  proof (induction "length planning_sem.htpl - 1 - j" arbitrary: j cfg')
    case 0
    hence jeq: "j = length planning_sem.htpl - 1" using "0.prems"(3) by linarith
    obtain ms where ms: "num_graph_impl.steps (cfg' # ms)"
                        "num_happening_post M j (last (cfg' # ms))"
                        "num_LvP (last (cfg' # ms))"
      using num_happening_steps_possible[OF "0.prems"(3) vss m0 "0.prems"(2) "0.prems"(1)] by blast
    show ?case using ms jeq by blast
  next
    case (Suc d)
    have jlt1: "j < length planning_sem.htpl - 1" using Suc.hyps(2) by linarith
    obtain ms1 where ms1: "num_graph_impl.steps (cfg' # ms1)"
                          "num_happening_post M j (last (cfg' # ms1))"
                          "num_LvP (last (cfg' # ms1))"
      using num_happening_steps_possible[OF Suc.prems(3) vss m0 Suc.prems(2) Suc.prems(1)] by blast
    have preSuc: "num_happening_pre_pre_delay M (Suc j) (last (cfg' # ms1))"
      and lvpSuc: "num_LvP (last (cfg' # ms1))"
      using num_post_imp_pre_pre_delay_Suc[OF jlt1 ms1(3) ms1(2)] by blast+
    have meas: "d = length planning_sem.htpl - 1 - Suc j" using Suc.hyps(2) by linarith
    have sucjlt: "Suc j < length planning_sem.htpl" using jlt1 by linarith
    obtain ms2 where ms2: "num_graph_impl.steps (last (cfg' # ms1) # ms2)"
                          "num_happening_post M (length planning_sem.htpl - 1) (last (last (cfg' # ms1) # ms2))"
                          "num_LvP (last (last (cfg' # ms1) # ms2))"
      using Suc.hyps(1)[OF meas preSuc lvpSuc sucjlt] by blast
    have steps: "num_graph_impl.steps (cfg' # ms1 @ ms2)"
      using num_graph_impl.steps_append[OF ms1(1) ms2(1)] by simp
    have lasteq: "last (cfg' # ms1 @ ms2) = last (last (cfg' # ms1) # ms2)"
      by (cases ms2) auto
    have "num_happening_post M (length planning_sem.htpl - 1) (last (cfg' # ms1 @ ms2))"
      and "num_LvP (last (cfg' # ms1 @ ms2))"
      using ms2(2) ms2(3) lasteq by simp_all
    thus ?case using steps by blast
  qed
  have pre0: "num_happening_pre_pre_delay M 0 cfg"
    and lvp0: "num_LvP cfg"
    using num_init_imp_pre_pre_delay_0[OF hlen lvp pres] by blast+
  obtain ms where ms: "num_graph_impl.steps (cfg # ms)"
                      "num_happening_post M (length planning_sem.htpl - 1) (last (cfg # ms))"
                      "num_LvP (last (cfg # ms))"
    using chain[OF pre0 lvp0 hlen] by blast
  have "num_goal_trans_pre M (last (cfg # ms))"
    by (rule num_post_last_imp_goal_trans_pre[OF hlen ms(3) ms(2)])
  thus ?thesis using ms(1) by blast
qed



end

end

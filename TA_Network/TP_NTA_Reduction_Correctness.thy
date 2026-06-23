theory TP_NTA_Reduction_Correctness
  imports TP_NTA_Reduction_Correctness_Steps
begin
context tp_nta_reduction_correctness
begin
lemma happening_steps_possible:
  assumes i: "i < length planning_sem.htpl" 
      and pres: "happening_pre_pre_delay i s"
  shows "graph_impl.steps (s#delay_and_apply i s) \<and> happening_post i (last (delay_and_apply i s))" 
proof -
  let ?seq = "((ext_seq \<circ> seq_apply) (map edge_2_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
             ((ext_seq \<circ> seq_apply) (map end_edge_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions]))
               ((ext_seq \<circ> seq_apply) (map start_edge_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
                 (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (planning_sem.time_index i)) [0..<length actions])) 
                  ((ext_seq \<circ> seq_apply) (map edge_3_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions])) [delay (get_delay i) s])))))"
  presume p: "graph_impl.steps ?seq \<and> happening_post i (last ?seq)"

  have delay_non_negative: "0 \<le> get_delay i" 
    unfolding get_delay_def
    apply (cases "i = 0")
     apply (subst if_P, simp)
    using eps_ran apply simp
    apply (subst if_not_P, simp)
    using planning_sem.time_index_sorted_list[of "i - 1" "i"] assms(1)
    unfolding planning_sem.time_index_def by auto

  obtain L v c where
    s: "s = (L, v, c)" using prod_cases3 by blast

  obtain c' where
    c': "c' = c \<oplus> get_delay i" 
    and Lvc': "(L, v, c') = delay (get_delay i) (L, v, c)"
    unfolding delay_def by simp

  from pres[simplified s happening_pre_pre_delay_def Let_def happening_pre_def]
  have Lv_con: "Lv_conds L v" by fastforce
  
  have no_urgent: "\<forall>p<length (fst (snd net_impl.sem)). fst (L, v, c) ! p \<notin> urgent (fst (snd net_impl.sem) ! p)"
  proof (intro allI impI)
    have len_L: "length L = Suc (length actions)" using Lv_con unfolding Lv_conds_def by blast

    fix p
    assume "p <length (fst (snd net_impl.sem))"
    hence pl: "p < Suc (length actions)"
          "p < length L"
      using length_net_impl
      using len_L by simp+
    
    show "fst (L, v, c) ! p \<notin> urgent (fst (snd net_impl.sem) ! p)"
    proof (cases p)
      case 0
      then have 1: "L ! p = planning_loc" using Lv_con unfolding Lv_conds_def by blast
      
      have 2: "urgent (fst (snd net_impl.sem) ! p) = {init_loc, goal_loc}"
        unfolding sem_alt_def fst_conv snd_conv
        apply (subst nth_map, simp add: pl)
        apply (subst 0)
        apply (subst nth_Cons_0)
        unfolding comp_def main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
          urgent_def fst_conv by auto
      
      show ?thesis unfolding 2 fst_conv 1 
        using locations_unique 
        by blast
    next
      case (Suc n)
      hence a: "actions ! n \<in> set actions" using pl by simp
      consider "L ! p = off_loc" | "L ! p = running_loc"
        using pres unfolding s happening_pre_pre_delay_def Let_def happening_pre_def prod.case
        using pl unfolding Suc
        apply (cases rule: planning_sem.open_active_count_cases[OF a])
        by blast+
      note c = this
      have "urgent (fst (snd net_impl.sem) ! p) = {starting_loc, ending_loc} "
        apply (subst sem_alt_def)
        unfolding fst_conv snd_conv
        apply (subst nth_map, simp add: pl)
        unfolding Suc
        apply (subst nth_Cons_Suc) 
        apply (subst nth_map)
        using Suc pl apply blast
        apply (subst action_auto_urg)
        ..
      then
      show ?thesis 
        unfolding fst_conv
        apply (cases rule: c; elim ssubst)
        using locations_unique by blast+
    qed
  qed
    
  have tl_not_Nil: "1 < length xs \<Longrightarrow> tl xs \<noteq> []" for xs apply (cases xs) by auto
  have last_tl_eq_last: "last(tl ?seq)= last ?seq"
  proof - 
    have 1: "0 < sum_list (map length (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (planning_sem.time_index i)) [0..<length actions]))) +
        length (map end_edge_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions])) +
        length (map edge_2_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))"
      unfolding add_gr_0
      apply (rule time_index_action_index_happening_cases[OF i])
      by (fastforce intro!: length_pos_if_in_set sum_list_pos_if_ex_pos)+
    show ?thesis 
      apply (rule tl_last[symmetric], rule tl_not_Nil, (subst length_ext_seq_comp_seq_apply | subst length_fold_ext_seq_comp_seq_apply)+)
      apply (subst length_Cons)
      apply (subst length_nth_simps(1))
      using 1 by linarith
  qed

  show "graph_impl.steps (s#delay_and_apply i s) \<and> happening_post i (last (delay_and_apply i s))" 
    apply (rule conjI)
    subgoal
      unfolding delay_and_apply_def Let_def
      unfolding s
      apply (subst apply_nth_happening_def)
      unfolding Let_def
      unfolding apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def apply_instant_actions_alt
      unfolding comp_apply[of ext_seq seq_apply, symmetric]
      apply ((subst ext_seq_seq_apply_append_distrib | subst fold_ext_seq_comp_conv_foldl_append), (intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil)?, simp)+
      apply (rule steps_delay_replace[OF _ delay_non_negative no_urgent])
      apply (subst comp_def)
      apply (subst Cons_tl_ext_seq)
      apply (subst comp_apply[of ext_seq seq_apply, symmetric])
      apply ((subst ext_seq_seq_apply_append_distrib[symmetric] | subst fold_ext_seq_comp_conv_foldl_append[symmetric]), (intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil)?, simp)+
      using p s by blast
    unfolding delay_and_apply_def Let_def
    apply (subst apply_nth_happening_def)
    unfolding Let_def apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def  apply_instant_actions_alt
    unfolding comp_apply[of ext_seq seq_apply, symmetric]
    apply (subst last_tl_eq_last)
    using p by blast
  
next
let ?seq = "((ext_seq \<circ> seq_apply) (map edge_2_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
             ((ext_seq \<circ> seq_apply) (map end_edge_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions]))
               ((ext_seq \<circ> seq_apply) (map start_edge_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
                 (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (planning_sem.time_index i)) [0..<length actions])) 
                  ((ext_seq \<circ> seq_apply) (map edge_3_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions])) [delay (get_delay i) s])))))"

  have pres': "happening_pre_end_starts i (delay (get_delay i) s)"
  proof -
    obtain L v c where
      s': "delay (get_delay i) s = (L, v, c)" by (rule prod_cases3)
    have "happening_pre_post_delay i (delay (get_delay i) s)" 
      apply (insert pres)
      apply (induction s)
      unfolding delay_def map_prod_simp id_def 
      unfolding happening_pre_pre_delay_def happening_pre_post_delay_def 
      by simp
    thus ?thesis
      apply -
      unfolding s'
      apply (rule happening_pre_end_startsI, simp)
         apply (rule end_start_invsI, simp)
                apply (rule happening_invsI, simp)
      using happening_pre_post_delay_dests apply auto[5]
      subgoal by (auto 
            simp: planning_sem.open_active_count_eq_closed_active_count_if_only_instant_acts
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(5))
      subgoal by (auto 
            simp: planning_sem.open_active_count_eq_closed_active_count_if_only_instant_acts
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(6))
      using happening_pre_post_delay_dests apply auto[5]
      subgoal by (auto 
            simp: planning_sem.open_active_count_0_if_start_scheduled 
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(5))
      subgoal by (auto 
            simp: planning_sem.open_active_count_0_if_start_scheduled 
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(5))
      subgoal using happening_pre_post_delay_dests by auto
      subgoal by (auto 
            simp: planning_sem.open_active_count_1_if_ending
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(6))
      subgoal by (auto dest!: happening_pre_post_delay_dests(8))
      done
  qed
  show "graph_impl.steps ?seq \<and> happening_post i (last ?seq)"
      apply (rule start_ends_possible)
        apply (rule end_ends_possible)
          apply (rule start_starts_possible)
            apply (rule instant_actions_possible)
              apply (rule end_starts_possible)
    by (auto intro!: i graph_impl.steps.intros pres')
qed


lemma set_foldl_append: "set (foldl (@) ys xs) = \<Union> (set ` (set xs)) \<union> (set ys)"
  apply (induction xs arbitrary: ys)
  by auto

lemma plan_steps_possible: 
  assumes "graph_impl.steps xs \<and> init_planning_state_props' (last xs)"
  shows "graph_impl.steps (ext_seq' (map delay_and_apply [0..<length planning_sem.htpl]) xs) \<and> goal_trans_pre (last (ext_seq' (map delay_and_apply [0..<length planning_sem.htpl]) xs))"
proof (rule steps_seq.ext_seq'_induct_list_prop_and_post[
      where P = happening_pre_pre_delay 
        and Q = happening_post 
        and R = init_planning_state_props' 
        and fs = "map delay_and_apply [0..<length planning_sem.htpl]" 
        and S = goal_trans_pre, 
        OF assms,
        simplified length_map set_map length_upt minus_nat.diff_0 set_upt], 
        goal_cases)
  case (1 f x)
  have x: "delay_and_apply i x' \<noteq> []" if "i < length planning_sem.htpl" for i x'
  proof -
    have 1: "\<exists>x. x \<in> set xs \<Longrightarrow> xs \<noteq> []" for xs by auto
    show ?thesis
      unfolding delay_and_apply_def 
      unfolding apply_nth_happening_def Let_def
      unfolding apply_edge_2_effects_def apply_end_edge_effects_def apply_start_edge_effects_def apply_instant_actions_alt apply_edge_3_effects_def
      unfolding comp_apply[of ext_seq seq_apply, symmetric]
      apply (subst fold_ext_seq_comp_conv_foldl_append, intro ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst ext_seq_seq_apply_append_distrib, intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)+
      apply (subst ext_seq_seq_apply_append_distrib, simp)
      apply (subst comp_apply)
      apply (subst tl_ext_seq_not_Nil, simp)
      apply (subst list.sel)
      apply (subst append_Nil)
      apply (rule seq_apply_not_Nil)
      apply (rule 1)
      by (auto intro: planning_sem.time_index_action_happening_cases[OF that] dest!: mem_nth simp: is_starting_index_def is_ending_index_def is_instant_index_def set_foldl_append)
  qed
  show ?case
    apply (rule imageE[OF 1])
    using x by simp
next
  case (2 i s)
  then show ?case using happening_steps_possible by simp
next
  case (3 i s)
  hence ib: "i < length planning_sem.htpl - 1"
    and post: "happening_post i s" by blast+
  have ib1: "i < length planning_sem.htpl"
    and ib2: "Suc i < length planning_sem.htpl"
    using ib by linarith+
  obtain L v c where s: "s = (L, v, c)" by (rule prod_cases3)
  note D = happening_post_dests[OF post s]
  \<comment> \<open>The post-state of happening \<open>i\<close> is the pre-state of happening \<open>Suc i\<close>: transfer each
      invariant conjunct from \<open>after (time_index i)\<close> to \<open>before (time_index (Suc i))\<close>
      (the transfer lemmas and the index-guarded \<open>prop_state\<close> defs need the bounds \<open>ib1\<close>/\<open>ib2\<close>).\<close>
  have c2: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ (Suc i) p)"
    using D(2) ib1 ib2 by (auto simp: prop_state_after_happ_def prop_state_before_happ_def planning_sem.state_seq_Suc_is_upd_state)
  have c3: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index (Suc i)) p))"
    using D(3) ib1 ib2 by (auto simp: planning_sem.locked_after_indexed_timepoint_is_locked_before_Suc[symmetric])
  have c4: "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index (Suc i))))"
    using D(4) ib1 ib2 by (auto simp: planning_sem.active_after_indexed_timepoint_is_active_before_Suc[symmetric])
  have c5: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 0 \<longrightarrow> L ! Suc j = off_loc"
    using D(5) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c6: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 1 \<longrightarrow> L ! Suc j = running_loc"
    using D(6) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c7: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_start_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(7) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  have c8: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_end_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(8) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  show ?case by (rule happening_pre_pre_delayI[OF s D(1) c2 c3 c4 c5 c6 c7 c8])
next
  case (4 x)
  hence init_is_goal: "set goal \<subseteq> set init" using planning_sem.valid_plan_state_seq by auto
  show ?case 
    apply (insert 4)
    apply (erule init_planning_state_props'E)
    apply (rule goal_trans_preI)
    using init_is_goal by auto
next
  case (5 x)
  hence hlen: "0 < length planning_sem.htpl"
    and props': "init_planning_state_props' x" by blast+
  show ?case
  proof (rule init_planning_state_props'E[OF props'])
    fix L v c
    assume s: "x = (L, v, c)"
      and lv: "Lv_conds L v"
      and va: "v acts_active = Some 0"
      and Leq: "L = planning_loc # map (\<lambda>x. off_loc) actions"
      and pv: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p)"
      and pl: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
      and cs: "\<forall>i<length actions. c (act_to_start_clock (actions ! i)) = 0"
      and ce: "\<forall>i<length actions. c (act_to_end_clock (actions ! i)) = 0"
    \<comment> \<open>The very first happening is preceded by the initial state: every \<open>happening_pre_pre_delay 0\<close>
        conjunct follows from \<open>init_planning_state_props'\<close> by collapsing the
        \<open>before (time_index 0)\<close> quantities to their initial values.\<close>
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
    show "happening_pre_pre_delay 0 x" by (rule happening_pre_pre_delayI[OF s lv c2 c3 c4 c5 c6 c7 c8])
  qed
next
  case (6 x)
  hence hlen: "0 < length planning_sem.htpl"
    and post: "happening_post (length planning_sem.htpl - 1) x" by blast+
  obtain L v c where s: "x = (L, v, c)" by (rule prod_cases3)
  note D = happening_post_dests[OF post s]
  \<comment> \<open>The post-state of the final happening already satisfies the goal-transition pre-state: every
      invariant conjunct collapses to its final value (active and locks back to \<open>0\<close>, every action
      location back to \<open>off_loc\<close>, and \<open>prop_state\<close> witnessed by the final state sequence entry).\<close>
  have c3: "v acts_active = Some 0"
    using D(4) by (subst (asm) planning_sem.active_after_final_is_0) simp
  have c4: "L = planning_loc # map (\<lambda>x. off_loc) actions"
  proof (subst list_eq_iff_nth_eq, intro conjI allI impI)
    show "length L = length (planning_loc # map (\<lambda>x. off_loc) actions)"
      using Lv_conds_dests(1)[OF D(1)] by simp
  next
    fix i assume i: "i < length L"
    show "L ! i = (planning_loc # map (\<lambda>x. off_loc) actions) ! i"
    proof (cases i)
      case 0
      thus ?thesis using Lv_conds_dests(2)[OF D(1)] by simp
    next
      case (Suc i')
      hence i': "i' < length actions" using i Lv_conds_dests(1)[OF D(1)] by simp
      have "planning_sem.closed_active_count (planning_sem.time_index (length planning_sem.htpl - 1)) (actions ! i') = 0"
        by (rule planning_sem.closed_active_count_final_is_0[OF nth_mem[OF i']])
      hence "L ! Suc i' = off_loc" using D(5) i' by blast
      thus ?thesis using Suc i' by simp
    qed
  qed
  have c5: "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p))"
    apply (rule exI[of _ "planning_sem.upd_state (length planning_sem.htpl - 1)"])
    using D(2) hlen
    apply (subst planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    apply (rule conjI)
    using planning_sem.plan_state_seq_valid apply fastforce
    apply (subst (asm) prop_state_after_happ_def, simp)
    apply (subst (asm) planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    by blast
  have c6: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    using D(3) unfolding planning_sem.locked_after_final_is_0 int_of_nat_def by simp
  show ?case by (rule goal_trans_preI[OF s D(1) c3 c4 c5 c6])
qed

lemma final_step_possible: 
  assumes "graph_impl.steps xs \<and> goal_trans_pre (last xs)"
  shows "graph_impl.steps ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] xs) \<and> goal_state_conds (last ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] xs))"
proof (rule steps_seq.ext_seq_comp_seq_apply_single_list_prop_and_post[where R = goal_trans_pre, OF assms], rule conjI)
  fix x::"nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)"
  assume a: "goal_trans_pre x"
  show "goal_state_conds (main_auto_goal_edge_effect x)" 
    apply (insert a)
    apply (erule goal_trans_preE)
    subgoal for L v c
      apply (rule ssubst[of x], assumption)
      unfolding main_auto_goal_edge_effect_alt
      apply (rule goal_state_condsI, rule HOL.refl)
      by (auto elim: Lv_condsE intro!: single_upd_bounded map_of_net_bounds_planning_lock simp: variables_unique)
    done
  show "graph_impl.steps [x, main_auto_goal_edge_effect x]"
    apply (rule single_step_intro)
    apply (cases x)
    subgoal for L v c
      apply (rule ssubst, assumption)
      unfolding main_auto_goal_edge_effect_alt prod.case
      apply (insert a)
      apply (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
       apply (subst net_impl.sem_def)
       apply (rule step_u.step_int[where p = 0])
      unfolding TAG_def
                 apply (subst conv_trans)
      using length_net_automata apply simp
                 apply (subst main_auto_trans)
                 apply (rule image_eqI)
                  prefer 2
                  apply (rule insertI2)
                  apply (rule insertI1)
                 apply (simp add: main_auto_goal_edge_def)
      subgoal by (intro disjI2 strip) (subst no_committed conv_committed | simp)+
      subgoal
        apply (subst check_bexp_simps)+
        apply (intro exI conjI)
                prefer 9
                apply (rule check_bexp_all)
                apply (erule goal_trans_preE)
                apply simp
                apply (erule exE)
                apply (erule conjE)
                apply (rule ballI)
                apply (frule set_mp)
                 apply assumption
                apply (subst is_prop_ab_def)
                apply (subst comp_apply)
                apply (subst check_bexp_simps)
                apply (subst is_val_simps)+
                apply (intro exI conjI)
                  prefer 3
                  apply (rule HOL.refl)
                 apply simp
        subgoal for _ S b
          apply (subst prop_state_simps(1)[symmetric, where S = S], assumption)
          apply (elim allE)
          apply (erule mp)
          using map_of_net_bounds_init_goal goal_in_props
          by auto
               apply simp
              prefer 2
              apply (subst is_val_simps)
              apply (erule goal_trans_preE)
              apply (erule Lv_condsE)
              apply simp
             apply simp
            apply rule
           apply simp
          apply simp
         apply (subst is_val_simps)
         apply (erule goal_trans_preE)
         apply simp
        by (rule check_bexp_is_val.intros)
              apply simp
      using no_invs apply simp
            apply (erule goal_trans_preE)
            apply fastforce
           apply (erule goal_trans_preE)
           apply fastforce
          apply simp
         apply simp
        apply (rule is_upds.intros)
         apply (subst is_upd_def)
         apply (intro conjI exI)
           apply simp
          apply (rule check_bexp_is_val.intros)
         apply simp
        apply (rule is_upds.intros)
       apply (rule single_upd_bounded)
      by (auto elim: goal_trans_preE Lv_condsE simp: map_of_net_bounds_planning_lock)
    done
qed


lemma all_steps_possible: "graph_impl.steps plan_steps \<and> goal_state_conds (last plan_steps)" 
    unfolding plan_steps_def 
    unfolding comp_apply[of ext_seq seq_apply, symmetric]         
    apply (rule final_step_possible)
     apply (rule plan_steps_possible)
    by (rule initial_step_possible)


lemma goal_run_is_run: "graph_impl.run (goal_run (last plan_steps))"
proof -
  have x: "goal_state_conds (shd (goal_run (last plan_steps)))"  using all_steps_possible by simp
  
  show ?thesis
  proof (rule graph_impl.run.coinduct[where X = "\<lambda>x. goal_state_conds (shd x) \<and> x = goal_run (shd x)"], goal_cases)
    case 1
    then show ?case using x by auto
  next
    case (2 x)
    hence "goal_state_conds (shd x)" "x = goal_run (shd x)" by auto

    have ctr: "x = shd x ## shd x ## (goal_run (shd x))" 
    proof -
      have 1: "shd x ## (goal_run (shd x)) = (goal_run (shd x))"
        apply (subst (2) goal_run.ctr)
        by simp
      with \<open>x = goal_run (shd x)\<close>
      show ?thesis by auto
    qed
    obtain L v c where
      Lvc: "shd x = (L, v, c)" using prod_cases3 by blast
    hence conds: "goal_state_conds (L, v, c)" using 2 by auto

    have trans: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L, v, c\<rangle>"
      apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
      unfolding net_impl.sem_def
        apply (rule step_int[where p = 0])
      unfolding TAG_def
                  apply (subst conv_trans)
      using length_net_automata apply simp
                  apply (subst main_auto_trans)
                  apply (rule image_eqI[where x = main_auto_loop])
                   apply (subst main_auto_loop_def)
                   apply simp
                  apply simp
      subgoal by (intro disjI2 strip) (subst conv_committed no_committed | simp)+
      subgoal by (simp add: check_bexp_simps)
      subgoal by simp
      subgoal using conv_invs no_invs by simp
      subgoal using conds goal_state_condsE by fastforce
      subgoal using conds goal_state_condsE by fastforce
      subgoal using conds goal_state_condsE by fastforce
      subgoal using conds goal_state_condsE by fastforce
      subgoal by rule
      subgoal using conds goal_state_condsE by fastforce
      subgoal using conds goal_state_condsE by fastforce
      by auto
    have conds': "goal_state_conds (shd (shd x ## goal_run (shd x)))" 
      apply (subst stream.sel) using 2 by auto

    have ctr': "shd x ## (goal_run (shd x)) = goal_run (shd ((shd x) ## (goal_run (shd x))))"
      using goal_run.ctr stream.sel
      by simp
    show ?case
      apply (intro exI conjI)
        apply (rule ctr)
       apply (subst Lvc)+
      unfolding prod.case
      using trans ctr' conds' by simp+
  qed
qed

lemma valid_plan_imp_form_holds: "net_impl.sem, a\<^sub>0 \<Turnstile> reach_formula"
proof -
  have plan_steps_not_Nil: "plan_steps \<noteq> []" unfolding plan_steps_def 
    apply (rule ext_seq_not_Nil(2))
    apply (rule seq_apply_not_Nil)
    by simp

  have plan_steps_alt: "a\<^sub>0 # (tl plan_steps) = plan_steps"
  proof -
     have "a\<^sub>0 = hd plan_steps" unfolding plan_steps_def 
      apply (subst hd_ext_seq)
       apply (rule ext_seq'_not_Nil)
       apply simp
      apply (subst hd_ext_seq')
       apply simp
      apply (subst hd_ext_seq)
       by simp+
     thus ?thesis using hd_Cons_tl plan_steps_not_Nil by auto
   qed

  have run_alt: "a\<^sub>0 ## (stl (plan_steps @- (goal_run (last plan_steps)))) = (plan_steps @- (goal_run (last plan_steps)))"
    apply (subst shift_simps(2))
    apply (subst if_not_P)
     apply (rule plan_steps_not_Nil)
    apply (subst shift.simps(2)[symmetric])
    apply (subst plan_steps_alt)
    by blast

  have steps: "graph_impl.steps plan_steps" using all_steps_possible by blast

  have run: "graph_impl.run (plan_steps @- (goal_run (last plan_steps)))"
  proof (rule graph_impl.extend_run')
    show "graph_impl.steps plan_steps" using all_steps_possible by blast
    show "graph_impl.run (goal_run (last plan_steps))" using goal_run_is_run by blast
    show "last plan_steps = shd (goal_run (last plan_steps))" using goal_run.ctr by simp
    show "plan_steps @- stl (goal_run (last plan_steps)) = plan_steps @- goal_run (last plan_steps)" using goal_run.ctr by simp
  qed
  hence run': "graph_impl.run (a\<^sub>0 ## (stl (plan_steps @- (goal_run (last plan_steps)))))" using run_alt by auto

  have form_holds: "holds (\<lambda>(L, v, _). check_sexp (sexp.loc 0 goal_loc) L (the \<circ> v)) (goal_run (last plan_steps))"
  proof -
    obtain L v c where
      Lvc: "shd (goal_run (last plan_steps)) = (L, v, c)" using prod_cases3 by blast
    hence  "last (plan_steps) = (L, v, c)" using goal_run.sel by auto
    hence "goal_state_conds (L, v, c)" using all_steps_possible by auto
    hence "L ! 0 = goal_loc" using goal_state_condsE by force
    hence "check_sexp (sexp.loc 0 goal_loc) L (the \<circ> v)" by auto
    thus ?thesis using holds.simps Lvc by fastforce
  qed
  show "?thesis" 
    unfolding reach_formula_def 
    unfolding models_def 
    unfolding formula.case
    unfolding graph_impl.Ex_ev_def
    unfolding Sequence_LTL.ev_alt_def
    using run' run_alt form_holds by blast
qed
end

context tp_nta_reduction_correctness'
begin
lemmas valid_plan_imp_form_holds = ref_correctness.valid_plan_imp_form_holds
end

context tp_nta_reduction_model_checking'
begin
find_theorems name: "ref_model_checking"

lemma valid_temp_plan_imp_form_holds:
  assumes "\<exists>\<pi>::(nat, 'action, int) temp_plan. temp_plan_for_problem_list_impl_int' at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>"
  shows "ref_model_checking.net_impl.sem,ref_model_checking.a\<^sub>0 \<Turnstile> reduction_ref_impl.reach_formula"
proof -
  obtain \<pi>::"(nat, 'action, int) temp_plan" where
    plan: "temp_plan_for_problem_list_impl_int' at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>" 
    using assms by auto
  interpret x: tp_nta_reduction_correctness' init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name
    using valid_plan_imp_locale_inst plan by blast
  show ?thesis using x.valid_plan_imp_form_holds by auto
qed

text \<open>**Numeric collapse at the capstone.** The reduction's existence-form capstone applies
unchanged to an (empty-)numeric problem: a @{const numeric_temp_plan_for_problem_list_impl_int'}
problem is a @{const temp_plan_for_problem_list_impl_int'} problem (the numeric fixes carry no
@{theory_text \<open>assumes\<close>}; @{thm [source] numeric_temp_plan_for_problem_list_impl_int'_imp_prop}),
so plan-existence at the numeric twin discharges @{thm [source] valid_temp_plan_imp_form_holds}'s
hypothesis. Inside that numeric locale the empty-numeric collapse
@{thm [source] numeric_temp_plan_for_problem_list_defs.collapse_num_valid_plan} identifies its
@{term num_valid_plan} with this propositional @{term valid_plan}.\<close>
lemma numeric_valid_temp_plan_imp_form_holds:
  assumes "\<exists>\<pi>::(nat, 'action, int) temp_plan.
    numeric_temp_plan_for_problem_list_impl_int' at_start at_end over_all lower upper pre adds dels
      init goal \<epsilon> props actions \<pi>"
  shows "ref_model_checking.net_impl.sem,ref_model_checking.a\<^sub>0 \<Turnstile> reduction_ref_impl.reach_formula"
  using assms valid_temp_plan_imp_form_holds
    numeric_temp_plan_for_problem_list_impl_int'_imp_prop
  by blast

end


section \<open>Numeric reduction correctness (Layer B)\<close>

text \<open>The numeric correctness locale merges three layers at the @{emph \<open>same\<close>} propositional
parameters: the propositional reduction correctness @{locale tp_nta_reduction_correctness} (which
gives the @{emph \<open>forward\<close>} direction -- a valid plan induces a goal-reaching run via @{text plan_steps}
and the step lemmas, i.e. the soundness-of-certification direction, @{emph \<open>not\<close>} a full bisimulation),
the numeric net @{locale numeric_tp_nta_reduction} (list-valued numeric data, the numeric automata
@{text num_timed_automaton_net}, and the grounder-match well-formedness), and the abstract numeric
plan layer @{locale numeric_temp_plan_for_problem_list_impl_int} instantiated at the @{text \<open>set o _\<close>}
projection of the list numeric data (so its @{text num_rat_impl} interprets @{locale
numeric_temp_plan_defs} at the rat-refined parameters, where @{text num_valid_plan} lives). The one
genuinely new assumption -- everything else is @{emph \<open>fixes\<close>}-only over shared ancestors -- is that
the numeric plan is valid (@{text num_rat_impl.num_valid_plan}), strengthening the propositional
@{text valid_plan} the reduction already assumes.\<close>
locale numeric_tp_nta_reduction_correctness =
  tp_nta_reduction_correctness
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name +
  numeric_tp_nta_reduction
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
    n_pre n_inv upds num_init num_goal nfluents fluent_to_var fluent_lo fluent_hi const_to_int +
  num_plan: numeric_temp_plan_for_problem_list_impl_int
    at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>
    "set o n_pre" "set o n_inv" "set o upds"
    "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and \<pi> :: "('i, 'action, int) temp_plan"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
    and n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_var :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int" +
  assumes num_valid: "num_plan.num_rat_impl.num_valid_plan"
      and const_to_int_of_int: "const_to_int (Int.of_int m) = m"
begin

text \<open>The numeric network's Munta semantics, mirroring the propositional @{text net_impl}/@{text
graph_impl}: same broadcast channels (none), the augmented automata @{const num_timed_automaton_net},
and the augmented variable bounds @{const num_net_bounds}. @{locale Simple_Network_Impl} is
assumption-free, so this is a bare interpretation.\<close>
sublocale num_net_impl: Simple_Network_Impl num_timed_automaton_net net_broadcast num_net_bounds .
sublocale num_graph_impl: Graph_Defs
  "\<lambda>(L, s, u) (L', s', u'). step_u' num_net_impl.sem L s u L' s' u'" .

text \<open>Sanity: both nets and the numeric plan-validity are in scope at the shared parameters.\<close>
lemma num_net_in_scope: "num_timed_automaton_net = num_main_auto # map num_action_to_automaton actions"
  by (simp add: num_timed_automaton_net_def)

subsection \<open>Tracking the abstract numeric valuation in the integer variable store\<close>

text \<open>The integer variable store @{term v} TRACKS the abstract numeric valuation @{term w} when every
declared fluent is defined in @{term w} and its variable holds the integer encoding of that value.
Numeric fluents are FRESH (disjoint from the propositional variables, @{thm fluent_vars_fresh}), so
tracking constrains only the numeric sub-store and is preserved by every propositional update.\<close>
definition num_tracks :: "(String.literal \<rightharpoonup> int) \<Rightarrow> ('n \<rightharpoonup> 'r) \<Rightarrow> bool" where
"num_tracks v w \<longleftrightarrow> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> v (fluent_to_var f) = Some (const_to_int r))"

lemma num_tracksI:
  assumes "\<And>f. f \<in> set nfluents \<Longrightarrow> \<exists>r. w f = Some r \<and> v (fluent_to_var f) = Some (const_to_int r)"
  shows "num_tracks v w"
  using assms unfolding num_tracks_def by blast

lemma num_tracks_definedD:
  assumes "num_tracks v w" and "f \<in> set nfluents"
  shows "\<exists>r. w f = Some r"
  using assms unfolding num_tracks_def by blast

lemma num_tracks_varD:
  assumes "num_tracks v w" and "f \<in> set nfluents" and "w f = Some r"
  shows "v (fluent_to_var f) = Some (const_to_int r)"
  using assms unfolding num_tracks_def by force

subsection \<open>Faithfulness of the integer encoding on the discrete fragment\<close>

text \<open>On integer-valued operands @{term const_to_int} commutes with the arithmetic that
@{const nexp_to_exp} emits (@{const Int.of_int} round-trips through @{thm const_to_int_of_int}). For
division this needs the operand to divide exactly -- the documented @{text \<open>NDiv \<mapsto> div\<close>} gap, where
the truncating @{const divide_int_inst.divide_int} agrees with the field quotient only on exact
divisions.\<close>
lemma const_to_int_add:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "const_to_int (a + b) = const_to_int a + const_to_int b"
  using assms by (auto simp flip: of_int_add simp: const_to_int_of_int elim!: Ints_cases)

lemma const_to_int_diff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "const_to_int (a - b) = const_to_int a - const_to_int b"
  using assms by (auto simp flip: of_int_diff simp: const_to_int_of_int elim!: Ints_cases)

lemma const_to_int_mult:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "const_to_int (a * b) = const_to_int a * const_to_int b"
  using assms by (auto simp flip: of_int_mult simp: const_to_int_of_int elim!: Ints_cases)

lemma const_to_int_div:
  assumes "a \<in> \<int>" and "b \<in> \<int>" and "b \<noteq> 0"
      and "const_to_int b dvd const_to_int a"
    shows "const_to_int (a / b) = const_to_int a div const_to_int b"
proof -
  obtain ma where a: "a = Int.of_int ma" using assms(1) by (auto elim: Ints_cases)
  obtain mb where b: "b = Int.of_int mb" using assms(2) by (auto elim: Ints_cases)
  have mb0: "mb \<noteq> 0" using assms(3) b by auto
  have "mb dvd ma" using assms(4) a b const_to_int_of_int by simp
  then obtain q where q: "ma = mb * q" by blast
  have ab: "a / b = Int.of_int q"
    using a b mb0 q by (simp add: of_int_mult)
  have "const_to_int a div const_to_int b = q"
  proof -
    have ca: "const_to_int a = ma" using a const_to_int_of_int by simp
    have cb: "const_to_int b = mb" using b const_to_int_of_int by simp
    show ?thesis unfolding ca cb using q mb0 by (simp add: nonzero_mult_div_cancel_left)
  qed
  thus ?thesis using ab const_to_int_of_int by simp
qed

lemma Ints_div_exact:
  assumes "a \<in> \<int>" and "b \<in> \<int>" and "b \<noteq> 0"
      and "const_to_int b dvd const_to_int a"
    shows "a / b \<in> \<int>"
proof -
  obtain ma where a: "a = Int.of_int ma" using assms(1) by (auto elim: Ints_cases)
  obtain mb where b: "b = Int.of_int mb" using assms(2) by (auto elim: Ints_cases)
  have mb0: "mb \<noteq> 0" using assms(3) b by auto
  have "mb dvd ma" using assms(4) a b const_to_int_of_int by simp
  then obtain q where "ma = mb * q" by blast
  hence "a / b = Int.of_int q" using a b mb0 by (simp add: of_int_mult)
  thus ?thesis by (simp add: Ints_of_int)
qed

text \<open>@{term \<open>nexp_ok w e\<close>}: the encoder is FAITHFUL on @{term e} at valuation @{term w} -- every leaf
reads a declared, integer-valued fluent or an integer constant, and every @{term NDiv} divides exactly.
This is the precise discrete-fragment side-condition under which the truncating Munta integer arithmetic
agrees with the abstract field arithmetic.\<close>
fun nexp_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> bool" where
  "nexp_ok w (NConst c) \<longleftrightarrow> c \<in> \<int>"
| "nexp_ok w (NVar f)   \<longleftrightarrow> f \<in> set nfluents \<and> (\<exists>r. w f = Some r \<and> r \<in> \<int>)"
| "nexp_ok w (NAdd a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NSub a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NMul a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NDiv a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b
     \<and> the (eval_nexp w b) \<noteq> 0
     \<and> const_to_int (the (eval_nexp w b)) dvd const_to_int (the (eval_nexp w a))"

text \<open>The load-bearing correspondence: under a tracking store, a faithful numeric expression evaluates
abstractly to an integer-valued field element whose integer encoding is exactly what Munta computes for
the translated @{const nexp_to_exp}. A single induction gives evaluability, integer-valuedness and the
@{const is_val} agreement at once.\<close>
lemma nexp_ok_is_val:
  assumes "num_tracks v w" and "nexp_ok w e"
  shows "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
           \<and> is_val v (nexp_to_exp fluent_to_var const_to_int e) (const_to_int r)"
  using assms(2)
proof (induction e)
  case (NConst c)
  thus ?case by (auto simp: is_val_simps)
next
  case (NVar f)
  then obtain r where f: "f \<in> set nfluents" and wf: "w f = Some r" and ri: "r \<in> \<int>" by auto
  have "v (fluent_to_var f) = Some (const_to_int r)" by (rule num_tracks_varD[OF assms(1) f wf])
  thus ?case using wf ri by (auto simp: is_val_simps)
next
  case (NAdd a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NAdd a b)) (const_to_int ra + const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NAdd a b)) (const_to_int (ra + rb))"
    using const_to_int_add[OF a(2) b(2)] by simp
  thus ?case using a(1,2) b(1,2) by (auto simp: Ints_add)
next
  case (NSub a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NSub a b)) (const_to_int ra - const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NSub a b)) (const_to_int (ra - rb))"
    using const_to_int_diff[OF a(2) b(2)] by simp
  thus ?case using a(1,2) b(1,2) by (auto simp: Ints_diff)
next
  case (NMul a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NMul a b)) (const_to_int ra * const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NMul a b)) (const_to_int (ra * rb))"
    using const_to_int_mult[OF a(2) b(2)] by simp
  thus ?case using a(1,2) b(1,2) by (auto simp: Ints_mult)
next
  case (NDiv a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have nz: "rb \<noteq> 0" and dvd: "const_to_int rb dvd const_to_int ra"
    using NDiv.prems a(1) b(1) by auto
  have ev: "eval_nexp w (NDiv a b) = Some (ra / rb)" using a(1) b(1) nz by simp
  have iv: "ra / rb \<in> \<int>" by (rule Ints_div_exact[OF a(2) b(2) nz dvd])
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NDiv a b)) (const_to_int ra div const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NDiv a b)) (const_to_int (ra / rb))"
    using const_to_int_div[OF a(2) b(2) nz dvd] by simp
  thus ?case using ev iv by blast
qed

text \<open>On integer-valued operands the encoding @{term const_to_int} preserves equality and order (it
inverts the monotone @{const Int.of_int}), so each abstract comparison transfers to its Munta
@{const check_bexp} counterpart.\<close>
lemma const_to_int_eq_iff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "(const_to_int a = const_to_int b) = (a = b)"
  using assms by (auto elim!: Ints_cases simp: const_to_int_of_int)

lemma const_to_int_le_iff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "(const_to_int a \<le> const_to_int b) = (a \<le> b)"
  using assms by (auto elim!: Ints_cases simp: const_to_int_of_int)

lemma const_to_int_lt_iff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "(const_to_int a < const_to_int b) = (a < b)"
  using assms by (auto elim!: Ints_cases simp: const_to_int_of_int)

text \<open>@{term \<open>comp_ok w c\<close>}: both sides of the comparison are faithful numeric expressions.\<close>
fun comp_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n, 'r) comp \<Rightarrow> bool" where
  "comp_ok w (Comp p a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"

text \<open>A satisfied, faithful abstract comparison transfers to the translated Munta guard holding True.\<close>
lemma check_bexp_comp_to_bexp:
  assumes "num_tracks v w" and "comp_ok w c" and "sat_comp w c"
  shows "check_bexp v (comp_to_bexp fluent_to_var const_to_int c) True"
proof -
  obtain p a b where c: "c = Comp p a b" by (cases c) auto
  have oka: "nexp_ok w a" and okb: "nexp_ok w b" using assms(2) c by auto
  obtain x where x: "eval_nexp w a = Some x" "x \<in> \<int>"
    "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int x)"
    using nexp_ok_is_val[OF assms(1) oka] by blast
  obtain y where y: "eval_nexp w b = Some y" "y \<in> \<int>"
    "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int y)"
    using nexp_ok_is_val[OF assms(1) okb] by blast
  have rel: "cmp_op_rel p x y" using assms(3) c x(1) y(1) by (simp add: sat_comp_def)
  let ?ea = "nexp_to_exp fluent_to_var const_to_int a"
  let ?eb = "nexp_to_exp fluent_to_var const_to_int b"
  show ?thesis
  proof (cases p)
    case Ceq
    have "(const_to_int y = const_to_int x) = True"
      using rel Ceq const_to_int_eq_iff[OF x(2) y(2)] by auto
    moreover have "check_bexp v (bexp.eq ?ea ?eb) (const_to_int y = const_to_int x)"
      by (rule check_bexp_is_val.intros(6)[OF x(3) y(3)])
    ultimately show ?thesis using c Ceq by simp
  next
    case Cle
    have "(const_to_int x \<le> const_to_int y) = True"
      using rel Cle const_to_int_le_iff[OF x(2) y(2)] by simp
    moreover have "check_bexp v (bexp.le ?ea ?eb) (const_to_int x \<le> const_to_int y)"
      by (rule check_bexp_is_val.intros(7)[OF x(3) y(3)])
    ultimately show ?thesis using c Cle by simp
  next
    case Cge
    have "(const_to_int y \<le> const_to_int x) = True"
      using rel Cge const_to_int_le_iff[OF y(2) x(2)] by simp
    moreover have "check_bexp v (bexp.ge ?ea ?eb) (const_to_int x \<ge> const_to_int y)"
      by (rule check_bexp_is_val.intros(9)[OF x(3) y(3)])
    ultimately show ?thesis using c Cge by simp
  next
    case Clt
    have "(const_to_int x < const_to_int y) = True"
      using rel Clt const_to_int_lt_iff[OF x(2) y(2)] by simp
    moreover have "check_bexp v (bexp.lt ?ea ?eb) (const_to_int x < const_to_int y)"
      by (rule check_bexp_is_val.intros(8)[OF x(3) y(3)])
    ultimately show ?thesis using c Clt by simp
  next
    case Cgt
    have "(const_to_int y < const_to_int x) = True"
      using rel Cgt const_to_int_lt_iff[OF y(2) x(2)] by simp
    moreover have "check_bexp v (bexp.gt ?ea ?eb) (const_to_int x > const_to_int y)"
      by (rule check_bexp_is_val.intros(10)[OF x(3) y(3)])
    ultimately show ?thesis using c Cgt by simp
  qed
qed

text \<open>Lifted to a guard list: a conjunction of satisfied faithful comparisons makes the
@{const bexp_and_all} of their translations hold True. This is the shape of every numeric guard
(@{const num_pre_guard} / @{const num_inv_guard} / @{const num_goal_guard}).\<close>
lemma check_bexp_comps_guard:
  assumes "num_tracks v w" and "\<forall>c \<in> set cs. comp_ok w c" and "sat_comps w (set cs)"
  shows "check_bexp v (bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) cs)) True"
proof (rule check_bexp_all, intro ballI)
  fix b assume "b \<in> set (map (comp_to_bexp fluent_to_var const_to_int) cs)"
  then obtain c where c: "c \<in> set cs" "b = comp_to_bexp fluent_to_var const_to_int c" by auto
  have "comp_ok w c" using assms(2) c(1) by blast
  moreover have "sat_comp w c" using assms(3) c(1) by (simp add: sat_comps_def)
  ultimately show "check_bexp v b True"
    using check_bexp_comp_to_bexp[OF assms(1)] c(2) by blast
qed

subsection \<open>Tracking is preserved by the numeric updates\<close>

text \<open>A translated numeric expression's Munta value depends only on the store at the fluent variables
it reads, so a store change away from those variables leaves the value unchanged. This is the Munta
counterpart of @{thm [source] eval_nexp_cong}, and it is what makes the sequential Munta update fold
agree with the simultaneous abstract @{const apply_upds} under @{const upds_no_cross_read_list}.\<close>
lemma is_val_nexp_to_exp_cong:
  assumes "is_val v (nexp_to_exp fluent_to_var const_to_int e) k"
      and "\<And>f. f \<in> nexp_fluents e \<Longrightarrow> v' (fluent_to_var f) = v (fluent_to_var f)"
    shows "is_val v' (nexp_to_exp fluent_to_var const_to_int e) k"
  using assms by (induction e arbitrary: k) (auto simp: is_val_simps)

lemma nexp_ok_fluents:
  assumes "nexp_ok w e"
  shows "nexp_fluents e \<subseteq> set nfluents"
  using assms by (induction e) auto

lemma upds_functional_set:
  assumes "distinct (map fst us)"
  shows "upds_functional (set us)"
proof -
  have "e = e'" if "(f, e) \<in> set us" and "(f, e') \<in> set us" for f e e'
    using that assms by (metis map_of_is_SomeI option.inject)
  thus ?thesis unfolding upds_functional_def by auto
qed

text \<open>The sequential Munta update fold reaches the simultaneous override target: each fluent variable
ends holding the value its update's RHS evaluates to @{emph \<open>against the pre-state\<close>} @{term v}, and all
other variables are untouched. The @{const upds_no_cross_read_list} side-condition is exactly what lets
a later update's RHS ignore the earlier writes (via @{thm [source] is_val_nexp_to_exp_cong}).\<close>
lemma is_upds_num_upd_aux:
  assumes "distinct (map fst us)"
      and "\<And>f e. (f, e) \<in> set us \<Longrightarrow> nexp_fluents e \<inter> (fst ` set us - {f}) = {}"
      and "\<And>f e. (f, e) \<in> set us \<Longrightarrow> is_val v (nexp_to_exp fluent_to_var const_to_int e) (kv f)"
      and "inj_on fluent_to_var (fst ` set us \<union> (\<Union>(f, e)\<in>set us. nexp_fluents e))"
    shows "\<exists>v'. is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us) v'
             \<and> (\<forall>x. x \<notin> fluent_to_var ` fst ` set us \<longrightarrow> v' x = v x)
             \<and> (\<forall>(f,e) \<in> set us. v' (fluent_to_var f) = Some (kv f))"
  using assms
proof (induction us arbitrary: v)
  case Nil
  show ?case by (auto intro: is_upds.intros(1))
next
  case (Cons fe us')
  obtain f0 e0 where fe: "fe = (f0, e0)" by (cases fe)
  have f0_notin: "f0 \<notin> fst ` set us'" using Cons.prems(1) fe by auto
  have val0: "is_val v (nexp_to_exp fluent_to_var const_to_int e0) (kv f0)"
    using Cons.prems(3) fe by simp
  let ?v1 = "v(fluent_to_var f0 \<mapsto> kv f0)"
  have upd0: "is_upd v (fluent_to_var f0, nexp_to_exp fluent_to_var const_to_int e0) ?v1"
    unfolding is_upd_def using val0 by blast
  have dist': "distinct (map fst us')" using Cons.prems(1) fe by simp
  have nocross': "nexp_fluents e \<inter> (fst ` set us' - {f}) = {}" if "(f, e) \<in> set us'" for f e
    using Cons.prems(2)[of f e] fe that by auto
  have inj': "inj_on fluent_to_var (fst ` set us' \<union> (\<Union>(f, e)\<in>set us'. nexp_fluents e))"
    using Cons.prems(4) fe by (auto elim!: inj_on_subset)
  have val': "is_val ?v1 (nexp_to_exp fluent_to_var const_to_int e) (kv f)" if fe': "(f, e) \<in> set us'" for f e
  proof -
    have base: "is_val v (nexp_to_exp fluent_to_var const_to_int e) (kv f)"
      using Cons.prems(3) fe fe' by simp
    have "f \<noteq> f0" using f0_notin fe' by (metis image_eqI fst_conv)
    hence f0e: "f0 \<in> fst ` set (fe # us') - {f}" using fe by simp
    hence f0nr: "f0 \<notin> nexp_fluents e" using Cons.prems(2)[of f e] fe fe' by auto
    have agree: "?v1 (fluent_to_var g) = v (fluent_to_var g)" if "g \<in> nexp_fluents e" for g
    proof -
      have "g \<noteq> f0" using f0nr that by auto
      moreover have "g \<in> fst ` set (fe # us') \<union> (\<Union>(f, e)\<in>set (fe # us'). nexp_fluents e)"
        using that fe' by force
      moreover have "f0 \<in> fst ` set (fe # us') \<union> (\<Union>(f, e)\<in>set (fe # us'). nexp_fluents e)"
        using fe by simp
      ultimately have "fluent_to_var g \<noteq> fluent_to_var f0"
        by (rule inj_on_contraD[OF Cons.prems(4)])
      thus ?thesis by simp
    qed
    show ?thesis by (rule is_val_nexp_to_exp_cong[OF base agree])
  qed
  obtain v' where v':
      "is_upds ?v1 (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us') v'"
      "\<forall>x. x \<notin> fluent_to_var ` fst ` set us' \<longrightarrow> v' x = ?v1 x"
      "\<forall>(f,e) \<in> set us'. v' (fluent_to_var f) = Some (kv f)"
    using Cons.IH[OF dist' nocross' val' inj'] by blast
  have notin': "fluent_to_var f0 \<notin> fluent_to_var ` fst ` set us'"
    using f0_notin Cons.prems(4) fe by (auto simp: inj_on_def)
  show ?case
  proof (intro exI[of _ v'] conjI)
    show "is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) (fe # us')) v'"
      using is_upds.intros(2)[OF upd0 v'(1)] fe by simp
  next
    show "\<forall>x. x \<notin> fluent_to_var ` fst ` set (fe # us') \<longrightarrow> v' x = v x"
    proof (intro allI impI)
      fix x assume "x \<notin> fluent_to_var ` fst ` set (fe # us')"
      hence "x \<notin> fluent_to_var ` fst ` set us'" and "x \<noteq> fluent_to_var f0" using fe by auto
      thus "v' x = v x" using v'(2) by auto
    qed
  next
    show "\<forall>(f,e) \<in> set (fe # us'). v' (fluent_to_var f) = Some (kv f)"
    proof safe
      fix f e assume mem: "(f, e) \<in> set (fe # us')"
      show "v' (fluent_to_var f) = Some (kv f)"
      proof (cases "(f, e) \<in> set us'")
        case True thus ?thesis using v'(3) by auto
      next
        case False
        hence "f = f0" using mem fe by auto
        thus ?thesis using v'(2) notin' by simp
      qed
    qed
  qed
qed

text \<open>Per-snap interface: applying a well-formed snap's numeric updates via Munta @{const is_upds}
preserves tracking, landing on the abstract simultaneous update @{const apply_upds} of that snap's
@{term upds} (this is @{text snap_num_update} in the abstract set view). The propositional variables
are untouched, so a propositional transition lifts to the numeric net exactly when this fires.\<close>
lemma is_upds_num_upd:
  assumes tr: "num_tracks v w"
      and fn: "upds_functional_list us"
      and nc: "upds_no_cross_read_list us"
      and ok: "\<And>f e. (f, e) \<in> set us \<Longrightarrow> f \<in> set nfluents \<and> nexp_ok w e"
  obtains v' where
      "is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us) v'"
      and "num_tracks v' (apply_upds (set us) w)"
      and "\<And>x. x \<notin> fluent_to_var ` fst ` set us \<Longrightarrow> v' x = v x"
proof -
  have dist: "distinct (map fst us)" using fn by (simp add: upds_functional_list_def)
  have ufun: "upds_functional (set us)" by (rule upds_functional_set[OF dist])
  have fst_sub: "fst ` set us \<subseteq> set nfluents" using ok by auto
  have rd_sub: "(\<Union>(f, e)\<in>set us. nexp_fluents e) \<subseteq> set nfluents"
    using ok nexp_ok_fluents by fastforce
  let ?kv = "\<lambda>f. const_to_int (the (apply_upds (set us) w f))"
  have val: "is_val v (nexp_to_exp fluent_to_var const_to_int e) (?kv f)" if mem: "(f, e) \<in> set us" for f e
  proof -
    have "nexp_ok w e" using ok mem by blast
    then obtain r where r: "eval_nexp w e = Some r"
        and isv: "is_val v (nexp_to_exp fluent_to_var const_to_int e) (const_to_int r)"
      using nexp_ok_is_val[OF tr] by blast
    have "apply_upds (set us) w f = eval_nexp w e" by (rule apply_upds_in[OF ufun mem])
    hence "?kv f = const_to_int r" using r by simp
    thus ?thesis using isv by simp
  qed
  have ncr: "nexp_fluents e \<inter> (fst ` set us - {f}) = {}" if "(f, e) \<in> set us" for f e
  proof -
    have "\<forall>(f, e)\<in>set us. nexp_fluents e \<inter> (fst ` set us - {f}) = {}"
      using nc by (simp add: upds_no_cross_read_list_def)
    thus ?thesis using that by blast
  qed
  have inj: "inj_on fluent_to_var (fst ` set us \<union> (\<Union>(f, e)\<in>set us. nexp_fluents e))"
    by (rule inj_on_subset[OF fluent_to_var_inj]) (use fst_sub rd_sub in blast)
  obtain v' where v':
      "is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us) v'"
      "\<forall>x. x \<notin> fluent_to_var ` fst ` set us \<longrightarrow> v' x = v x"
      "\<forall>(f,e) \<in> set us. v' (fluent_to_var f) = Some (?kv f)"
    using is_upds_num_upd_aux[where kv = "\<lambda>f. const_to_int (the (apply_upds (set us) w f))",
                              OF dist ncr val inj] by blast
  have track: "num_tracks v' (apply_upds (set us) w)"
  proof (rule num_tracksI)
    fix g assume g: "g \<in> set nfluents"
    show "\<exists>r. apply_upds (set us) w g = Some r \<and> v' (fluent_to_var g) = Some (const_to_int r)"
    proof (cases "g \<in> fst ` set us")
      case True
      then obtain e where e: "(g, e) \<in> set us" by auto
      have "nexp_ok w e" using ok e by blast
      then obtain r where r: "eval_nexp w e = Some r" using nexp_ok_is_val[OF tr] by blast
      have au: "apply_upds (set us) w g = Some r" using apply_upds_in[OF ufun e] r by simp
      have "v' (fluent_to_var g) = Some (?kv g)" using v'(3) e by auto
      hence "v' (fluent_to_var g) = Some (const_to_int r)" using au by simp
      thus ?thesis using au by blast
    next
      case False
      have au: "apply_upds (set us) w g = w g" by (rule apply_upds_notin[OF False])
      obtain r where r: "w g = Some r" using num_tracks_definedD[OF tr g] by blast
      have "fluent_to_var g \<notin> fluent_to_var ` fst ` set us"
      proof
        assume "fluent_to_var g \<in> fluent_to_var ` fst ` set us"
        then obtain h where h: "h \<in> fst ` set us" "fluent_to_var g = fluent_to_var h" by auto
        have "g = h" using fluent_to_var_inj g fst_sub h by (auto dest: inj_onD)
        thus False using False h(1) by auto
      qed
      hence "v' (fluent_to_var g) = v (fluent_to_var g)" using v'(2) by auto
      hence "v' (fluent_to_var g) = Some (const_to_int r)" using num_tracks_varD[OF tr g r] by simp
      thus ?thesis using au r by simp
    qed
  qed
  have outside: "v' x = v x" if "x \<notin> fluent_to_var ` fst ` set us" for x
    using v'(2) that by blast
  show ?thesis by (rule that[OF v'(1) track outside])
qed

subsection \<open>Stronger numeric invariants (the propositional ones plus correct numeric tracking)\<close>

text \<open>The per-step invariants of the propositional bisimulation, strengthened with the requirement that
the integer variable store @{emph \<open>also\<close>} tracks the abstract numeric valuation at the matching index
(NUMERIC_PLAN A.6 / 5.5). @{term M} is the abstract numeric state sequence supplied by
@{text num_valid_plan}: @{term \<open>snd (M i)\<close>} is the valuation @{emph \<open>before\<close>} happening @{term i} and
@{term \<open>snd (M (Suc i))\<close>} the valuation after it. Each twin implies its propositional original, so the
projection direction reuses the existing proof verbatim; the extra @{const num_tracks} conjunct is the
new numeric content threaded through the run.\<close>

definition "num_happening_pre M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_pre i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M i)) \<and> Simple_Network_Language.bounded (map_of num_net_bounds) v)"

definition "num_happening_pre_pre_delay M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M i)) \<and> Simple_Network_Language.bounded (map_of num_net_bounds) v)"

definition "num_happening_post M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_post i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M (Suc i))) \<and> Simple_Network_Language.bounded (map_of num_net_bounds) v)"

definition "num_init_planning_state_props' M Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> init_planning_state_props' (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M 0)) \<and> Simple_Network_Language.bounded (map_of num_net_bounds) v)"

definition "num_goal_trans_pre M Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> goal_trans_pre (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M (length planning_sem.htpl))) \<and> Simple_Network_Language.bounded (map_of num_net_bounds) v)"

lemma num_happening_preI:
  assumes "happening_pre i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M i))"
      and "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "num_happening_pre M i (L, v, c)"
  using assms by (simp add: num_happening_pre_def)

lemma num_happening_pre_propD: "num_happening_pre M i (L, v, c) \<Longrightarrow> happening_pre i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_trackD: "num_happening_pre M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M i))"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_boundD: "num_happening_pre M i (L, v, c) \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_pre_delayI:
  assumes "happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M i))"
      and "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "num_happening_pre_pre_delay M i (L, v, c)"
  using assms by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_propD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_trackD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M i))"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_boundD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_postI:
  assumes "happening_post i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M (Suc i)))"
      and "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "num_happening_post M i (L, v, c)"
  using assms by (simp add: num_happening_post_def)

lemma num_happening_post_propD: "num_happening_post M i (L, v, c) \<Longrightarrow> happening_post i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_post_def)

lemma num_happening_post_trackD: "num_happening_post M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M (Suc i)))"
  by (simp add: num_happening_post_def)

lemma num_happening_post_boundD: "num_happening_post M i (L, v, c) \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v"
  by (simp add: num_happening_post_def)

lemma num_init_planning_state_props'I:
  assumes "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M 0))"
      and "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "num_init_planning_state_props' M (L, v, c)"
  using assms by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_propD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> init_planning_state_props' (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_trackD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> num_tracks v (snd (M 0))"
  by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_boundD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v"
  by (simp add: num_init_planning_state_props'_def)

lemma num_goal_trans_preI:
  assumes "goal_trans_pre (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M (length planning_sem.htpl)))"
      and "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "num_goal_trans_pre M (L, v, c)"
  using assms by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_propD: "num_goal_trans_pre M (L, v, c) \<Longrightarrow> goal_trans_pre (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_trackD:
  "num_goal_trans_pre M (L, v, c) \<Longrightarrow> num_tracks v (snd (M (length planning_sem.htpl)))"
  by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_boundD:
  "num_goal_trans_pre M (L, v, c) \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v"
  by (simp add: num_goal_trans_pre_def)

subsection \<open>Numeric network step infrastructure (mirroring the propositional Edges layer)\<close>

text \<open>The numeric automata carry no committed locations and no location invariants -- @{const
augment_edge} only conjoins a guard and appends updates -- so the structural facts the @{text
num_net_impl} step relation needs mirror the propositional @{text no_committed}/@{text no_invs}/@{text
step_t_possible} on @{const num_timed_automaton_net}. @{thm [source] conv_trans} and @{thm [source]
conv_committed} are already stated generically over the automata list, so they apply to the numeric
net unchanged.\<close>

lemma num_no_committed:
  assumes "p < length num_timed_automaton_net"
  shows "committed (map automaton_of num_timed_automaton_net ! p) = {}"
  using assms
  unfolding num_timed_automaton_net_def automaton_of_def committed_def num_main_auto_def Let_def
    num_action_to_automaton_def
  apply (cases p)
  by simp+

lemma num_no_invs': assumes "p < length num_timed_automaton_net"
  shows "inv (automaton_of (num_timed_automaton_net ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding num_timed_automaton_net_def Let_def prod.case
    by simp+
  show ?thesis
    unfolding num_timed_automaton_net_def Let_def prod.case
  unfolding num_main_auto_def Let_def num_action_to_automaton_def
  unfolding comp_apply
  unfolding inv_def
  apply (cases p)
   apply simp
   apply (subst automaton_of_def)
   apply (subst prod.case)+
   apply (subst snd_conv)+
   apply (subst default_map_of_def) apply simp
  subgoal for p'
    apply (rule ssubst[of p])
     apply assumption
    apply (subst nth_Cons_Suc)
    apply (drule 1)
    apply (subst nth_map)
     apply assumption
    unfolding automaton_of_def prod.case snd_conv
    apply (subst default_map_of_def)
    by simp
  done
qed

lemma num_conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of num_timed_automaton_net ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "num_timed_automaton_net ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(num_timed_automaton_net ! p)"])
    apply (subst comp_apply)
    apply (subst conv_automaton_def)
    apply (subst prod.case)+
    apply (subst automaton_of_def)
    apply (subst prod.case)+
    apply (subst snd_conv)+
    apply (subst automaton_of_def)
    apply (subst prod.case)+
    apply (subst snd_conv)+
    apply (induction d)
     apply (subst list.map)
    unfolding default_map_of_def
     apply simp
    subgoal for d ds
      apply (induction d)
      subgoal for i c
        apply (rule ext)
        subgoal for x
          apply (subst list.map)
          apply (subst prod.case)+
          unfolding map_of_Cons_code
          apply (subst map_default_def)+
          apply (cases "i = x")
           apply (subst if_P, assumption)+
           apply simp
          apply (subst if_not_P, assumption)+
          apply (subst (asm) map_default_def)
          apply (rule subst[of "FinFun.map_default [] (map_of (map (\<lambda>(s, cc). (s, map conv_ac cc)) ds)) x" "map conv_ac (case map_of ds x of None \<Rightarrow> [] | Some b' \<Rightarrow> b')"])
           apply simp
          apply (subst map_default_def)
          by blast
        done
      done
    done
  done

lemma num_no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)"
  shows "inv (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net ! p) = (\<lambda>x. [])"
  apply (subst num_conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using num_no_invs'
  apply (subst num_no_invs')
  using assms by auto

text \<open>A delay step of length 0 is always available (no invariants to block it), and the
single-step/internal-step intros for the numeric graph -- the numeric counterparts of @{text
step_t_possible} / @{text single_step_intro} / @{text non_t_step_intro}.\<close>
lemma num_step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of num_net_bounds) y"
  shows "num_net_impl.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding num_net_impl.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using num_no_invs by auto
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by auto
  done

lemmas num_single_step_intro = num_graph_impl.steps.Cons[OF _ num_graph_impl.steps.Single]
lemmas num_non_t_step_intro = num_step_t_possible[THEN step_u'.intros, rotated, rotated]

text \<open>Per-automaton transition/urgency characterisations of the numeric net, the inputs to a
@{text step_u.step_int} edge-firing (mirroring @{thm [source] main_auto_trans} / @{thm [source]
action_auto_urg}; action-automaton transitions are reached via the generic @{thm [source] conv_trans}
at the action's index, then @{text num_action_auto_trans}).\<close>
schematic_goal num_main_auto_trans:
  shows "trans (automaton_of (num_timed_automaton_net ! 0)) = ?x"
  apply (subst num_timed_automaton_net_def)
  apply (subst nth_Cons_0)
  unfolding num_main_auto_def Let_def comp_def snd_conv trans_def automaton_of_def
    prod.case fst_conv list.set ..

schematic_goal num_action_auto_trans:
  shows "trans (automaton_of (num_action_to_automaton a)) = ?x"
  unfolding num_action_to_automaton_def Let_def comp_def snd_conv trans_def automaton_of_def
    prod.case fst_conv list.set ..

schematic_goal num_action_auto_urg:
  shows "urgent ((automaton_of \<circ> conv_automaton) (num_action_to_automaton a)) = ?x"
  unfolding urgent_def num_action_to_automaton_def Let_def comp_apply fst_conv snd_conv
    conv_automaton_def prod.case automaton_of_def list.set ..

text \<open>The numeric edge-effect config transformers reuse the @{emph \<open>generic\<close>} @{const edge_effect}
(it applies an edge's updates/location/reset, with no guard check) at the @{const augment_edge}'d
edges, so each fires the propositional @{emph \<open>and\<close>} the numeric updates. The duration edge
@{const edge_3} and the instant edge @{const instant_trans_edge} carry no numeric data, so their
propositional effects @{const edge_3_effect} / @{const instant_trans_edge_effect} are reused unchanged.\<close>
definition "num_start_edge_effect n = edge_effect (Suc n) (num_start_edge (actions ! n))"
definition "num_end_edge_effect n = edge_effect (Suc n) (num_end_edge (actions ! n))"
definition "num_edge_2_effect n = edge_effect (Suc n) (num_edge_2 (actions ! n))"
definition "num_main_auto_init_edge_effect = edge_effect 0 num_main_auto_init_edge"
definition "num_main_auto_goal_edge_effect = edge_effect 0 num_main_auto_goal_edge"

text \<open>@{const augment_edge} only conjoins a guard and appends numeric updates -- it keeps the target
location and the clock resets -- so applying it via @{const edge_effect} yields the @{emph \<open>same\<close>}
location and clock valuation as the un-augmented edge; only the variable store differs (by the appended
numeric updates, which touch the fresh fluent variables). These two generic facts are load-bearing for
the run-lifting: the numeric run's locations and clocks coincide with the propositional run's.\<close>
lemma edge_effect_augment_loc:
  "fst (edge_effect n (augment_edge gn fn e) Lvc) = fst (edge_effect n e Lvc)"
  by (simp add: augment_edge_def edge_effect_def Let_def case_prod_beta split: prod.splits)

lemma edge_effect_augment_clk:
  "snd (snd (edge_effect n (augment_edge gn fn e) Lvc)) = snd (snd (edge_effect n e Lvc))"
  by (simp add: augment_edge_def edge_effect_def Let_def case_prod_beta split: prod.splits)

text \<open>Per-edge corollaries: each numeric edge-effect agrees with its propositional counterpart on the
location and clock components (only the variable store -- the fluent vars -- differs).\<close>
lemmas num_edge_effect_defs =
  num_start_edge_effect_def num_end_edge_effect_def num_edge_2_effect_def
  num_main_auto_init_edge_effect_def num_main_auto_goal_edge_effect_def
  start_edge_effect_def end_edge_effect_def edge_2_effect_def
  main_auto_init_edge_effect_def main_auto_goal_edge_effect_def
  num_start_edge_def num_end_edge_def num_edge_2_def
  num_main_auto_init_edge_def num_main_auto_goal_edge_def

lemma num_start_edge_effect_loc: "fst (num_start_edge_effect n Lvc) = fst (start_edge_effect n Lvc)"
  and num_start_edge_effect_clk: "snd (snd (num_start_edge_effect n Lvc)) = snd (snd (start_edge_effect n Lvc))"
  and num_end_edge_effect_loc: "fst (num_end_edge_effect n Lvc) = fst (end_edge_effect n Lvc)"
  and num_end_edge_effect_clk: "snd (snd (num_end_edge_effect n Lvc)) = snd (snd (end_edge_effect n Lvc))"
  and num_edge_2_effect_loc: "fst (num_edge_2_effect n Lvc) = fst (edge_2_effect n Lvc)"
  and num_edge_2_effect_clk: "snd (snd (num_edge_2_effect n Lvc)) = snd (snd (edge_2_effect n Lvc))"
  and num_main_auto_init_edge_effect_loc: "fst (num_main_auto_init_edge_effect Lvc) = fst (main_auto_init_edge_effect Lvc)"
  and num_main_auto_init_edge_effect_clk: "snd (snd (num_main_auto_init_edge_effect Lvc)) = snd (snd (main_auto_init_edge_effect Lvc))"
  and num_main_auto_goal_edge_effect_loc: "fst (num_main_auto_goal_edge_effect Lvc) = fst (main_auto_goal_edge_effect Lvc)"
  and num_main_auto_goal_edge_effect_clk: "snd (snd (num_main_auto_goal_edge_effect Lvc)) = snd (snd (main_auto_goal_edge_effect Lvc))"
  by (simp_all add: num_edge_effect_defs edge_effect_augment_loc edge_effect_augment_clk)

lemma length_num_net_automata: "length num_timed_automaton_net = Suc (length actions)"
  by (simp add: num_timed_automaton_net_def)

text \<open>Monotonicity of Munta evaluation under store extension: extending the variable store (here with
the fresh fluent variables) preserves every @{const check_bexp}/@{const is_val} judgement. This is how a
propositional guard or update value transfers verbatim to the numeric store, which agrees with the
propositional one on the propositional variables and only adds fluent variables (so @{term \<open>v \<subseteq>\<^sub>m vn\<close>}).\<close>
lemma check_bexp_is_val_mono:
  shows "check_bexp v b bv \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> check_bexp v' b bv"
    and "is_val v e k \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> is_val v' e k"
proof -
  have "check_bexp v b bv \<Longrightarrow> (\<forall>v'. v \<subseteq>\<^sub>m v' \<longrightarrow> check_bexp v' b bv)"
    and "is_val v e k \<Longrightarrow> (\<forall>v'. v \<subseteq>\<^sub>m v' \<longrightarrow> is_val v' e k)"
    by (induction rule: check_bexp_is_val.inducts)
       (fastforce intro: check_bexp_is_val.intros simp: map_le_def dom_def)+
  thus "check_bexp v b bv \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> check_bexp v' b bv"
    and "is_val v e k \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> is_val v' e k"
    by blast+
qed

text \<open>A propositional update sequence lifts to any store extension: it can fire on @{term vn} (which
extends @{term v} with the fresh fluent variables), leaving the extension untouched outside the written
variables and producing a result that again extends the propositional result. This is the update-side
counterpart of @{thm [source] check_bexp_is_val_mono}, the second half of the per-step lifting glue.\<close>
lemma is_upds_map_le:
  assumes "is_upds v f v'" and "v \<subseteq>\<^sub>m vn"
  shows "\<exists>vn'. is_upds vn f vn' \<and> v' \<subseteq>\<^sub>m vn' \<and> (\<forall>x. x \<notin> fst ` set f \<longrightarrow> vn' x = vn x)"
  using assms
proof (induction f arbitrary: v vn)
  case Nil
  hence "v' = v" by (auto simp: is_upds_Nil_iff)
  thus ?case using Nil.prems(2) by (auto intro: is_upds.intros)
next
  case (Cons fe f)
  obtain x e where fe: "fe = (x, e)" by (cases fe)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 f v'"
    using Cons.prems(1) fe by (auto simp: is_upds_Cons_iff)
  obtain k where k: "is_val v e k" and v1_eq: "v1 = v(x \<mapsto> k)"
    using v1 by (auto simp: is_upd_def)
  have "is_val vn e k" by (rule check_bexp_is_val_mono(2)[OF k Cons.prems(2)])
  hence upd_vn: "is_upd vn (x, e) (vn(x \<mapsto> k))" by (auto simp: is_upd_def)
  have "v1 \<subseteq>\<^sub>m vn(x \<mapsto> k)" using Cons.prems(2) v1_eq by (auto simp: map_le_def)
  then obtain vn' where vn':
      "is_upds (vn(x \<mapsto> k)) f vn'"
      "v' \<subseteq>\<^sub>m vn'"
      "\<forall>y. y \<notin> fst ` set f \<longrightarrow> vn' y = (vn(x \<mapsto> k)) y"
    using Cons.IH[OF rest] by blast
  have "is_upds vn (fe # f) vn'" using upd_vn vn'(1) fe by (auto intro: is_upds.intros)
  moreover have "\<forall>y. y \<notin> fst ` set (fe # f) \<longrightarrow> vn' y = vn y"
    using vn'(3) fe by auto
  ultimately show ?case using vn'(2) by blast
qed

text \<open>The keystone generic per-step lifting: an internal transition of the numeric network firing any
edge of @{const num_timed_automaton_net} -- assembled directly from @{thm [source] step_u.step_int}, with
its committed/invariant side-conditions discharged by @{thm [source] num_no_committed}/@{thm [source]
num_no_invs} and the transition-membership by the generic @{thm [source] conv_trans}. The caller supplies
the augmented edge, the (combined) guard @{term \<open>check_bexp vn bg True\<close>}, the clock guard, the update
@{term \<open>is_upds vn fu vn'\<close>}, and numeric boundedness; the guard/update are split into propositional and
numeric halves at the call site (via @{thm [source] check_bexp_is_val_mono} / @{thm [source] is_upds_map_le}
and @{thm [source] check_bexp_comps_guard} / @{thm [source] is_upds_num_upd}).\<close>
lemma num_step_int_lift:
  assumes p_len: "p < length num_timed_automaton_net"
      and edge: "(l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
      and bexp: "check_bexp vn bg True"
      and guard: "c \<turnstile> conv_cc g"
      and loc: "L ! p = l"
      and L_len: "length L = length num_timed_automaton_net"
      and isupds: "is_upds vn fu vn'"
      and bounded: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    shows "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0]c\<rangle>"
proof -
  have p_len': "p < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)"
    using p_len by simp
  have conv_edge:
    "(l, bg, conv_cc g, Sil a, fu, r, l')
       \<in> trans ((map (automaton_of \<circ> conv_automaton) num_timed_automaton_net) ! p)"
    apply (subst conv_trans[OF p_len'])
    using edge by (force intro: image_eqI[where x = "(l, bg, g, Sil a, fu, r, l')"])
  have committed_empty:
    "committed (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net ! q) = {}"
    if q: "q < length num_timed_automaton_net" for q
  proof -
    have q': "q < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)" using q by simp
    show ?thesis using conv_committed[OF q'] num_no_committed[OF q] by simp
  qed
  show ?thesis
    unfolding num_net_impl.sem_def
    apply (rule step_u.step_int[where p = p])
    unfolding TAG_def
              apply (rule conv_edge)
             apply (rule disjI2, rule allI, rule impI)
             apply (subst committed_empty)
              apply simp
             apply simp
            apply (rule bexp)
           apply (rule guard)
          apply (rule allI, rule impI, subst num_no_invs, assumption, simp)
         apply (rule loc)
        using L_len p_len apply simp
       apply (rule HOL.refl)
      apply (rule HOL.refl)
     apply (rule isupds)
    apply (rule bounded)
    done
qed

text \<open>Inversion workhorse: invert a propositional internal Munta step to recover the fired edge,
its (combined) guard and updates. The dual of @{thm [source] num_step_int_lift} for the propositional
net: @{thm [source] step_u_elims'} peels off the @{term step_u} (@{text step_int}) premises -- the
fired edge in the @{emph \<open>conv\<close>} net, the bexp/clock guards, and the location/update side-conditions --
then @{thm [source] conv_trans} un-@{const conv_automaton}s the edge back to a plain
@{const net_automata} edge with @{term \<open>g'' = conv_cc g\<close>}.\<close>
lemma prop_int_step_invert:
  assumes "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', v', c'\<rangle>"
      and "length L = length net_automata"
  obtains p l b g f r l' where
    "p < length net_automata"
    "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    "check_bexp v b True"
    "c \<turnstile> conv_cc g"
    "L ! p = l"
    "L' = L[p := l']"
    "c' = [r\<rightarrow>0]c"
    "is_upds v f v'"
proof -
  note step = assms(1)[unfolded net_impl.sem_def]
  show thesis
    apply (rule step_u_elims'(2)[OF step])
    apply (unfold TAG_def)
    subgoal premises prems for l b g'' f r l' p
    proof -
      have plen: "p < length net_automata"
        using prems(7) assms(2) by simp
      have plen': "p < length (map (automaton_of \<circ> conv_automaton) net_automata)"
        using plen by simp
      have "(l, b, g'', Sil a, f, r, l')
              \<in> (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) `
                  trans (automaton_of (net_automata ! p))"
        using prems(1) unfolding conv_trans[OF plen'] .
      then obtain g where
          edge: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
          and g''_eq: "g'' = conv_cc g"
        by auto
      show thesis
        using plen edge prems(3) prems(4)[unfolded g''_eq] prems(6) prems(8) prems(9) prems(10)
        by (rule that)
    qed
    done
qed

text \<open>The per-step internal lift, combining @{thm [source] prop_int_step_invert} (invert the
propositional step) with the keystone @{thm [source] num_step_int_lift} (reconstruct the numeric step).
The edge-dependent numeric data is supplied by the caller through @{term num_data}: for the inverted
fired edge it must exhibit the augmented numeric edge in @{const num_timed_automaton_net}, the numeric
guard holding on the extended store @{term vn}, the appended numeric update firing to some @{term vn'}
in @{const num_net_bounds}, that @{term vn'} still extends the propositional post-store @{term v'}, and
that @{term vn'} tracks the post-step numeric valuation @{term w'} (the valuation the abstract sequence
assigns after this snap). In the run-lifting the happening index fixes the snap and @{text
num_valid_state_sequence} discharges the guard/update; the source location @{term \<open>L ! p = l\<close>} pins down
which edge fired, and @{term w'} threads the numeric valuation config-by-config.\<close>
lemma num_int_step_lift:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', v', c'\<rangle>"
      and L_len: "length L = length net_automata"
      and num_data:
        "\<And>p l b g f r l'.
           p < length net_automata \<Longrightarrow>
           (l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p)) \<Longrightarrow>
           L ! p = l \<Longrightarrow> check_bexp v b True \<Longrightarrow> is_upds v f v' \<Longrightarrow>
           \<exists>bg fu vn'.
              (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
              \<and> check_bexp vn bg True
              \<and> is_upds vn fu vn'
              \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
              \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w'"
  shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', vn', c'\<rangle>
               \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w' \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
proof -
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp v b True"
    and G: "c \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0]c"
    and U: "is_upds v f v'"
    by (rule prop_int_step_invert[OF step L_len])
  obtain bg fu vn' where
      NE: "(l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    and NB: "check_bexp vn bg True"
    and NU: "is_upds vn fu vn'"
    and BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    and LE: "v' \<subseteq>\<^sub>m vn'"
    and TR: "num_tracks vn' w'"
    using num_data[OF P E LOC B U] by blast
  have len_eq: "length net_automata = length num_timed_automaton_net"
    by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have plen_num: "p < length num_timed_automaton_net" using P len_eq by simp
  have Llen_num: "length L = length num_timed_automaton_net" using L_len len_eq by simp
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0]c\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  thus ?thesis using L'eq c'eq LE TR BND by blast
qed

text \<open>A Munta update sequence leaves every variable it does not write unchanged.\<close>
lemma is_upds_unchanged:
  assumes "is_upds s us s'" and "x \<notin> fst ` set us"
  shows "s' x = s x"
  using assms by (induction rule: is_upds.induct) (auto simp: is_upd_def)

text \<open>Numeric tracking survives a propositional update sequence that writes no fluent variable. The
propositional edge updates touch only propositional variables, which are disjoint from the fresh fluent
variables (@{thm [source] fluent_vars_fresh}), so the integer encodings the fluent variables carry are
untouched.\<close>
lemma num_tracks_pres_unwritten:
  assumes tr: "num_tracks vn w"
      and upd: "is_upds vn f vn'"
      and fresh: "\<And>g. g \<in> set nfluents \<Longrightarrow> fluent_to_var g \<notin> fst ` set f"
    shows "num_tracks vn' w"
proof (rule num_tracksI)
  fix g assume g: "g \<in> set nfluents"
  obtain r where r: "w g = Some r" using num_tracks_definedD[OF tr g] by blast
  have v: "vn (fluent_to_var g) = Some (const_to_int r)" by (rule num_tracks_varD[OF tr g r])
  have "vn' (fluent_to_var g) = vn (fluent_to_var g)" by (rule is_upds_unchanged[OF upd fresh[OF g]])
  thus "\<exists>r. w g = Some r \<and> vn' (fluent_to_var g) = Some (const_to_int r)" using r v by auto
qed

text \<open>Discharging the @{term num_data} provider for an edge with @{emph \<open>no numeric update\<close>}
(@{term \<open>fu = f\<close>}): the unchanged edges that appear verbatim in @{const num_timed_automaton_net}
(@{const edge_3} / @{const instant_trans_edge} / @{const main_auto_loop}) and the guard-only augmented
edges (@{const num_edge_2} / @{const num_main_auto_goal_edge}, whose @{const augment_edge} appends the
empty update list). The propositional update sequence @{term f} fires on the extended store via @{thm
[source] is_upds_map_le}, and -- writing no fluent variable -- preserves tracking by @{thm [source]
num_tracks_pres_unwritten}. The caller supplies the assembled (combined) guard
@{term \<open>check_bexp vn bg True\<close>}, the numeric edge's membership, the freshness of @{term f}, and
boundedness of the result; no abstract numeric data beyond that is consumed.\<close>
lemma num_data_no_write_edge:
  assumes le: "v \<subseteq>\<^sub>m vn"
      and tr: "num_tracks vn w"
      and num_edge: "(l, bg, g, Sil a, f, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
      and NB: "check_bexp vn bg True"
      and U: "is_upds v f v'"
      and fresh: "\<And>h. h \<in> set nfluents \<Longrightarrow> fluent_to_var h \<notin> fst ` set f"
      and bnd: "\<And>vn'. is_upds vn f vn' \<Longrightarrow> v' \<subseteq>\<^sub>m vn'
                 \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    shows "\<exists>bg fu vn'.
             (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
             \<and> check_bexp vn bg True \<and> is_upds vn fu vn'
             \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
             \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w"
proof -
  obtain vn' where NU: "is_upds vn f vn'" and LE: "v' \<subseteq>\<^sub>m vn'"
    using is_upds_map_le[OF U le] by blast
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'" using bnd[OF NU LE] .
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  show ?thesis using num_edge NB NU BND LE TR by blast
qed

text \<open>Discharging the @{term num_data} provider for an edge that carries a numeric @{emph \<open>update\<close>}
(the @{const augment_edge} of a @{text start}/@{text end}/@{text init} edge, whose appended update list
is @{term \<open>num_upd s\<close>} for @{term \<open>us = upds s\<close>}). The combined update is @{term \<open>f @ num_upd s\<close>}: the
propositional half @{term f} fires on the extended store via @{thm [source] is_upds_map_le} (writing no
fluent variable, so tracking survives by @{thm [source] num_tracks_pres_unwritten}), then the numeric half
fires via @{thm [source] is_upds_num_upd}, landing on the abstract simultaneous update @{const apply_upds}
of @{term us}. The two phases compose by @{thm [source] is_upds_appendI}; @{term \<open>v' \<subseteq>\<^sub>m vn'\<close>}
survives because the fluent variables the numeric half writes are fresh for @{term v'}.\<close>
lemma num_data_upd_edge:
  assumes le: "v \<subseteq>\<^sub>m vn"
      and tr: "num_tracks vn w"
      and num_edge: "(l, bexp.and b gn, g, Sil a,
                       f @ map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) us, r, l')
                     \<in> trans (automaton_of (num_timed_automaton_net ! p))"
      and B: "check_bexp v b True"
      and gn: "check_bexp vn gn True"
      and U: "is_upds v f v'"
      and fresh: "\<And>h. h \<in> set nfluents \<Longrightarrow> fluent_to_var h \<notin> fst ` set f"
      and v'_fresh: "\<And>h. h \<in> set nfluents \<Longrightarrow> fluent_to_var h \<notin> dom v'"
      and fn_func: "upds_functional_list us"
      and fn_ncr: "upds_no_cross_read_list us"
      and fn_ok: "\<And>fl e. (fl, e) \<in> set us \<Longrightarrow> fl \<in> set nfluents \<and> nexp_ok w e"
      and bnd: "\<And>vn'. v' \<subseteq>\<^sub>m vn' \<Longrightarrow> num_tracks vn' (apply_upds (set us) w)
                  \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    shows "\<exists>bg fu vn'.
             (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
             \<and> check_bexp vn bg True \<and> is_upds vn fu vn'
             \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
             \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' (apply_upds (set us) w)"
proof -
  let ?fn = "map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) us"
  \<comment> \<open>Combined guard fires on @{term vn}.\<close>
  have bvn: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have NB: "check_bexp vn (bexp.and b gn) True"
    using check_bexp_is_val.intros(3)[OF bvn gn] by simp
  \<comment> \<open>Propositional updates fire on @{term vn}, preserving tracking.\<close>
  obtain vn_mid where
      NUmid: "is_upds vn f vn_mid"
    and LEmid: "v' \<subseteq>\<^sub>m vn_mid"
    and OFFmid: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn_mid x = vn x"
    using is_upds_map_le[OF U le] by blast
  have TRmid: "num_tracks vn_mid w" by (rule num_tracks_pres_unwritten[OF tr NUmid fresh])
  \<comment> \<open>Numeric updates fire on @{term vn_mid}.\<close>
  obtain vn' where
      NUnum: "is_upds vn_mid ?fn vn'"
    and TRnum: "num_tracks vn' (apply_upds (set us) w)"
    and OFFnum: "\<And>x. x \<notin> fluent_to_var ` fst ` set us \<Longrightarrow> vn' x = vn_mid x"
    using is_upds_num_upd[OF TRmid fn_func fn_ncr fn_ok] by metis
  \<comment> \<open>Compose the two update phases.\<close>
  have NU: "is_upds vn (f @ ?fn) vn'" by (rule is_upds_appendI[OF NUmid NUnum])
  \<comment> \<open>@{term v'} survives: the numeric half writes only fresh fluent variables.\<close>
  have LE: "v' \<subseteq>\<^sub>m vn'"
  proof (unfold map_le_def, intro ballI)
    fix x assume xdom: "x \<in> dom v'"
    have "x \<notin> fluent_to_var ` fst ` set us"
    proof
      assume "x \<in> fluent_to_var ` fst ` set us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set us" by auto
      obtain e where "(fl, e) \<in> set us" using flmem by auto
      hence "fl \<in> set nfluents" using fn_ok by blast
      hence "fluent_to_var fl \<notin> dom v'" by (rule v'_fresh)
      thus False using xfl xdom by simp
    qed
    hence "vn' x = vn_mid x" by (rule OFFnum)
    moreover have "v' x = vn_mid x" using LEmid xdom by (auto simp: map_le_def)
    ultimately show "v' x = vn' x" by simp
  qed
  \<comment> \<open>Boundedness from the caller's provider.\<close>
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    using bnd[OF LE TRnum] .
  show ?thesis using num_edge NB NU BND LE TRnum by blast
qed

subsection \<open>Numeric guards depend only on the fluents they read (the non-interference foundation)\<close>

text \<open>A comparison's truth depends only on the values at the fluents it reads (@{const comp_fluents}) --
@{thm [source] eval_nexp_cong} lifted to @{const sat_comp}. This is the foundation of the intra-happening
non-interference argument for the run-lifting: a snap's guard, evaluated against the @{emph \<open>partially
updated\<close>} valuation reached after earlier co-occurring snaps fire, still agrees with its value at the
pre-happening valuation, because those snaps write only fluents the guard does not read (numeric
non-interference, @{term num_mutex_snap_action}). NB these are general facts about @{const sat_comp};
they belong in the abstract @{theory_text Temporal_Plans} layer and should move there in the refactor.\<close>
lemma sat_comp_cong:
  assumes "\<And>f. f \<in> comp_fluents c \<Longrightarrow> w f = w' f"
  shows "sat_comp w c = sat_comp w' c"
proof (cases c)
  case (Comp p a b)
  have ea: "eval_nexp w a = eval_nexp w' a" by (rule eval_nexp_cong) (use assms Comp in auto)
  have eb: "eval_nexp w b = eval_nexp w' b" by (rule eval_nexp_cong) (use assms Comp in auto)
  show ?thesis unfolding sat_comp_def Comp by (simp only: comp.case ea eb)
qed

lemma sat_comps_cong:
  assumes "\<And>c f. c \<in> C \<Longrightarrow> f \<in> comp_fluents c \<Longrightarrow> w f = w' f"
  shows "sat_comps w C = sat_comps w' C"
proof -
  have "sat_comp w c = sat_comp w' c" if "c \<in> C" for c
    by (rule sat_comp_cong) (use assms that in blast)
  thus ?thesis unfolding sat_comps_def by blast
qed

text \<open>The set-level happening update agrees with the pre-happening valuation off the fluents the
happening writes: if @{term f} is written by no snap in the (functional, pairwise-non-interfering)
happening @{term S}, then applying @{term S}'s simultaneous numeric update leaves @{term f} unchanged.
Finite induction on @{term S} via the @{thm [source] num_plan.num_rat_impl.happening_num_update_set_insert}
recursion (each step peels one snap and the residual reads the running valuation, so @{term w} is
generalised); each peeled snap @{term a} leaves @{term f} alone by
@{thm [source] num_plan.num_rat_impl.snap_num_update_unwritten}.\<close>
lemma happening_num_update_set_unwritten:
  assumes fin: "finite S"
      and func: "\<And>x. x \<in> S \<Longrightarrow> upds_functional ((set \<circ> upds) x)"
      and noint: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      and unwr: "f \<notin> (\<Union>s\<in>S. num_plan.num_rat_impl.snap_writes s)"
    shows "num_plan.num_rat_impl.happening_num_update_set S w f = w f"
  using fin func noint unwr
proof (induction arbitrary: w rule: finite_induct)
  case empty
  show ?case by (simp add: num_plan.num_rat_impl.happening_num_update_set_empty[unfolded comp_def])
next
  case (insert a S)
  have fa: "f \<notin> num_plan.num_rat_impl.snap_writes a"
   and fS: "f \<notin> (\<Union>s\<in>S. num_plan.num_rat_impl.snap_writes s)"
    using insert.prems(3) by (auto simp: comp_def)
  have ins: "num_plan.num_rat_impl.happening_num_update_set (insert a S) w
               = num_plan.num_rat_impl.happening_num_update_set S (num_plan.num_rat_impl.snap_num_update a w)"
    by (rule num_plan.num_rat_impl.happening_num_update_set_insert[OF insert.hyps(1,2) insert.prems(1,2)])
  have step: "num_plan.num_rat_impl.happening_num_update_set S (num_plan.num_rat_impl.snap_num_update a w) f
                = num_plan.num_rat_impl.snap_num_update a w f"
    by (rule insert.IH) (use insert.prems(1,2) fS in \<open>auto simp: comp_def\<close>)
  have "num_plan.num_rat_impl.snap_num_update a w f = w f"
    by (rule num_plan.num_rat_impl.snap_num_update_unwritten[OF fa])
  thus ?case using ins step by (simp add: comp_def)
qed

text \<open>Guard invariance under a partial happening update by non-interfering snaps -- the heart of the
intra-happening numeric content. If a guard set @{term C} reads only fluents of @{term s} (its read
fluents lie in @{term \<open>snap_reads s\<close>}) and every snap in the co-occurring happening @{term S} does
@{emph \<open>not\<close>} numerically interfere with @{term s} (@{term \<open>\<not> num_mutex_snap_action s s'\<close>}), then
@{term S}'s simultaneous numeric update misses every fluent the guard reads, so the guard holds at the
partially-updated valuation @{term \<open>happening_num_update_set S w\<close>} iff it held at the pre-happening
@{term w}. Hence checking an intra-happening Munta guard at the running (partially-updated) store agrees
with the abstract guard at the pre-happening valuation. Proof: @{thm [source] sat_comps_cong} reduces to
the per-read-fluent agreement, and non-interference (third disjunct of
@{thm [source] num_plan.num_rat_impl.num_mutex_snap_action_def}) puts each read fluent outside @{term S}'s
writes, so @{thm [source] happening_num_update_set_unwritten} leaves it fixed.\<close>
lemma sat_comps_happening_num_update_set:
  assumes fin: "finite S"
      and func: "\<And>x. x \<in> S \<Longrightarrow> upds_functional ((set \<circ> upds) x)"
      and noint: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      and sint: "\<And>s'. s' \<in> S \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action s s'"
      and rd: "(\<Union>c\<in>C. comp_fluents c) \<subseteq> num_plan.num_rat_impl.snap_reads s"
    shows "sat_comps (num_plan.num_rat_impl.happening_num_update_set S w) C = sat_comps w C"
proof (rule sat_comps_cong)
  fix c f assume c: "c \<in> C" and f: "f \<in> comp_fluents c"
  have fr: "f \<in> num_plan.num_rat_impl.snap_reads s" using rd c f by blast
  have notin: "f \<notin> (\<Union>s'\<in>S. num_plan.num_rat_impl.snap_writes s')"
  proof
    assume "f \<in> (\<Union>s'\<in>S. num_plan.num_rat_impl.snap_writes s')"
    then obtain s' where s': "s' \<in> S"
      and fw: "f \<in> num_plan.num_rat_impl.snap_writes s'" by blast
    have "num_plan.num_rat_impl.snap_writes s' \<inter> num_plan.num_rat_impl.snap_reads s = {}"
      using sint[OF s'] unfolding num_plan.num_rat_impl.num_mutex_snap_action_def by blast
    thus False using fw fr by blast
  qed
  show "num_plan.num_rat_impl.happening_num_update_set S w f = w f"
    by (rule happening_num_update_set_unwritten[OF fin func noint notin])
qed

subsection \<open>Numeric delay primitives for the run-lifting\<close>

text \<open>Head-replacement for the numeric graph (the numeric mirror of @{thm [source] steps_replace_Cons_hd}):
a one-step run @{term \<open>[x, hd ys]\<close>} and a run @{term \<open>y # ys\<close>} splice to a run @{term \<open>x # ys\<close>}. Pure
@{locale Graph_Defs} plumbing on @{const num_graph_impl.steps}, identical to the propositional proof.\<close>
lemma num_steps_replace_Cons_hd:
  assumes "num_graph_impl.steps [x, hd ys]"
          "num_graph_impl.steps (y # ys)"
    shows "num_graph_impl.steps (x # ys)"
proof (cases ys)
  case Nil
  then show ?thesis using assms(1) by blast
next
  case (Cons a list)
  hence 1: "num_graph_impl.steps ys" using assms num_graph_impl.steps_ConsD by blast
  show ?thesis using num_graph_impl.steps_append[OF assms(1) 1] Cons by simp
qed

text \<open>Absorbing a leading delay on the numeric run (the numeric mirror of
@{thm [source] steps_delay_replace}): if @{term \<open>delay t x # xs\<close>} is a numeric run, @{term \<open>0 \<le> t\<close>}, and
no automaton sits on an urgent location at @{term x}, then @{term \<open>x # xs\<close>} is a numeric run -- the
leading length-@{term t} delay merges into the first delay step. Same proof as the propositional one:
invert the first @{const Simple_Network_Language.label.Del} step and re-issue a longer one via
@{thm [source] step_u.step_t}. The numeric net carries the SAME clocks/locations as the propositional one,
so the delay machinery transfers verbatim; @{term not_urgent} is supplied by the caller (the run-lifting,
where @{const num_happening_pre_pre_delay} pins the locations).\<close>
lemma num_steps_delay_replace:
  assumes "num_graph_impl.steps (delay t x # xs)"
      and t: "0 \<le> t"
      and not_urgent: "(\<forall>p < length (fst (snd num_net_impl.sem)). (fst x) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p))"
    shows "num_graph_impl.steps (x # xs)"
proof (cases rule: num_graph_impl.steps.cases[OF assms(1)])
  case 1
  then show ?thesis by blast
next
  fix tx y ys
  assume a: "delay t x # xs = tx # y # ys"
    "(case tx of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). num_net_impl.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) y"
    "num_graph_impl.steps (y # ys)"

  have xs: "xs = y # ys" using a by simp

  obtain Ly vy cy where
    y: "y = (Ly, vy, cy)" by (cases y; auto)

  obtain L v c where
    x: "x = (L, v, c)" by (cases x; auto)

  from a(1)
  have tx: "tx = (L, v, c \<oplus> t)" unfolding delay_def map_prod_def x prod.case id_def by simp

  from a(2)[simplified tx prod.case y, THEN step_u'_elims]
  obtain L' v' c' a where
    del: "num_net_impl.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>"
    and a: "a \<noteq> Simple_Network_Language.label.Del" "num_net_impl.sem \<turnstile> \<langle>L', v', c'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>Ly, vy, cy\<rangle>" by blast

  obtain broad N B where
    as: "num_net_impl.sem = (broad, N, B)" by (cases num_net_impl.sem) auto
  obtain t' where
    "c' = (c \<oplus> t) \<oplus> t'"
    and L': "L' = L"
    and v': "v' = v"
    and t': "0 \<le> t'"
    and other: "\<forall>p<length N. c' \<turnstile> Simple_Network_Language.inv (N ! p) (L ! p)"
      "(\<exists>p<length N. L ! p \<in> urgent (N ! p)) \<longrightarrow> t' = 0"
      "Simple_Network_Language.bounded B v"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as
    unfolding TAG_def
    by auto
  hence c': "c' = c \<oplus> (t + t')" unfolding cval_add_def by auto
  have del': "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>"
    unfolding as
    unfolding L' v' c'
    apply (rule step_u.step_t)
    unfolding TAG_def
    subgoal using other c' by blast
    subgoal using assms(2) t' by simp
    subgoal using other(2) t' assms(2) not_urgent unfolding x as fst_conv snd_conv by blast
    by (rule other(3))

  show ?thesis
    apply (rule num_steps_replace_Cons_hd[OF _ assms(1)])
    unfolding xs list.sel
    apply (rule num_single_step_intro)
    unfolding x y prod.case
    by (rule step_u'.intros[OF del' a])
qed

text \<open>Structure of the numeric network's Munta semantics (the numeric mirror of @{thm [source]
sem_alt_def}) and its automata-list length (mirror of @{thm [source] length_net_impl}). These unblock
the per-automaton urgency/location reasoning the run-lifting needs over @{const num_net_impl.sem}.\<close>
schematic_goal num_sem_alt_def: "num_net_impl.sem = ?x"
  unfolding num_net_impl.sem_def num_timed_automaton_net_def
  unfolding Simple_Network_Impl.sem_def fst_conv snd_conv ..

lemma length_num_net_impl: "length ((fst o snd) num_net_impl.sem) = Suc (length actions)"
  unfolding num_net_impl.sem_def
  using length_num_net_automata by auto

text \<open>No automaton sits on an urgent location at a @{const happening_pre_pre_delay} configuration of the
numeric net -- the @{term not_urgent} hypothesis @{thm [source] num_steps_delay_replace} needs. The numeric
net carries the SAME locations (from the shared @{const happening_pre_pre_delay}) and the SAME urgent sets
(@{const augment_edge} leaves the urgent component untouched: main automaton @{term \<open>{init_loc, goal_loc}\<close>},
action automata @{term \<open>{starting_loc, ending_loc}\<close>}) as the propositional net, so this is the inline
@{text no_urgent} block of @{thm [source] happening_steps_possible} with @{text num_} structure facts.\<close>
lemma num_no_urgent:
  assumes pres: "happening_pre_pre_delay i (L, v, c)"
  shows "\<forall>p<length (fst (snd num_net_impl.sem)). fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
proof (intro allI impI)
  from pres[simplified happening_pre_pre_delay_def Let_def happening_pre_def]
  have Lv_con: "Lv_conds L v" by fastforce
  have len_L: "length L = Suc (length actions)" using Lv_con unfolding Lv_conds_def by blast

  fix p
  assume "p < length (fst (snd num_net_impl.sem))"
  hence pl: "p < Suc (length actions)"
        "p < length L"
    using length_num_net_impl
    using len_L by simp+

  show "fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
  proof (cases p)
    case 0
    then have 1: "L ! p = planning_loc" using Lv_con unfolding Lv_conds_def by blast

    have 2: "urgent (fst (snd num_net_impl.sem) ! p) = {init_loc, goal_loc}"
      unfolding num_sem_alt_def fst_conv snd_conv
      apply (subst nth_map, simp add: pl)
      apply (subst 0)
      apply (subst nth_Cons_0)
      unfolding comp_def num_main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
        urgent_def fst_conv by auto

    show ?thesis unfolding 2 fst_conv 1
      using locations_unique
      by blast
  next
    case (Suc n)
    hence a: "actions ! n \<in> set actions" using pl by simp
    consider "L ! p = off_loc" | "L ! p = running_loc"
      using pres unfolding happening_pre_pre_delay_def Let_def happening_pre_def prod.case
      using pl unfolding Suc
      apply (cases rule: planning_sem.open_active_count_cases[OF a])
      by blast+
    note c = this
    have "urgent (fst (snd num_net_impl.sem) ! p) = {starting_loc, ending_loc} "
      apply (subst num_sem_alt_def)
      unfolding fst_conv snd_conv
      apply (subst nth_map, simp add: pl)
      unfolding Suc
      apply (subst nth_Cons_Suc)
      apply (subst nth_map)
      using Suc pl apply blast
      apply (subst num_action_auto_urg)
      ..
    then
    show ?thesis
      unfolding fst_conv
      apply (cases rule: c; elim ssubst)
      using locations_unique by blast+
  qed
qed

subsection \<open>Projection infrastructure for the relational lift (Option A)\<close>

text \<open>The numeric (combined) store @{term v} (@{const num_net_bounds}-bounded) splits into its
propositional projection @{term \<open>v |` dom (map_of net_bounds)\<close>} -- which is @{const net_bounds}-bounded,
so it satisfies the propositional invariants -- and its fluent part @{term \<open>v |` (fluent_to_var ` set nfluents)\<close>},
which carries @{const num_tracks}. The two domains are disjoint by @{thm [source] fluent_vars_fresh}, so
@{term v} is their @{const map_add}.\<close>

lemma dom_map_of_num_net_bounds:
  "dom (map_of num_net_bounds) = dom (map_of net_bounds) \<union> fluent_to_var ` set nfluents"
  by (auto simp: num_all_vars_def num_fluent_vars_def dom_map_of_conv_image_fst)

lemma fluent_var_notin_net_bounds:
  assumes "f \<in> set nfluents"
  shows "fluent_to_var f \<notin> dom (map_of net_bounds)"
  using fluent_vars_fresh assms by (simp add: dom_map_of_conv_image_fst)

lemma map_of_num_net_bounds_eq_on_props:
  assumes "x \<in> dom (map_of net_bounds)"
  shows "map_of num_net_bounds x = map_of net_bounds x"
  using assms by (simp add: num_all_vars_def map_of_append map_add_dom_app_simps(3))

lemma prop_proj_bounded:
  assumes "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "Simple_Network_Language.bounded (map_of net_bounds) (v |` dom (map_of net_bounds))"
proof -
  have domv: "dom v = dom (map_of num_net_bounds)"
    using assms unfolding Simple_Network_Language.bounded_def by blast
  have pv_sub: "dom (map_of net_bounds) \<subseteq> dom v"
    using domv dom_map_of_num_net_bounds by blast
  have dom_pv: "dom (v |` dom (map_of net_bounds)) = dom (map_of net_bounds)"
    using pv_sub by auto
  show ?thesis
    unfolding Simple_Network_Language.bounded_def
  proof (intro conjI)
    show "dom (v |` dom (map_of net_bounds)) = dom (map_of net_bounds)" by (rule dom_pv)
  next
    show "\<forall>x \<in> dom (v |` dom (map_of net_bounds)).
            fst (the (map_of net_bounds x)) \<le> the ((v |` dom (map_of net_bounds)) x)
            \<and> the ((v |` dom (map_of net_bounds)) x) \<le> snd (the (map_of net_bounds x))"
    proof (intro ballI)
      fix x assume "x \<in> dom (v |` dom (map_of net_bounds))"
      hence xpv: "x \<in> dom (map_of net_bounds)" using dom_pv by simp
      have r: "(v |` dom (map_of net_bounds)) x = v x" using xpv by (simp add: restrict_in)
      have b: "map_of num_net_bounds x = map_of net_bounds x" by (rule map_of_num_net_bounds_eq_on_props[OF xpv])
      have "fst (the (map_of num_net_bounds x)) \<le> the (v x) \<and> the (v x) \<le> snd (the (map_of num_net_bounds x))"
        using assms xpv pv_sub unfolding Simple_Network_Language.bounded_def by blast
      thus "fst (the (map_of net_bounds x)) \<le> the ((v |` dom (map_of net_bounds)) x)
            \<and> the ((v |` dom (map_of net_bounds)) x) \<le> snd (the (map_of net_bounds x))"
        unfolding r b by simp
    qed
  qed
qed

lemma store_decomp:
  assumes "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "v = (v |` dom (map_of net_bounds)) ++ (v |` (fluent_to_var ` set nfluents))"
proof (rule ext)
  fix x
  have domv: "dom v = dom (map_of net_bounds) \<union> fluent_to_var ` set nfluents"
    using assms dom_map_of_num_net_bounds unfolding Simple_Network_Language.bounded_def by simp
  show "v x = ((v |` dom (map_of net_bounds)) ++ (v |` (fluent_to_var ` set nfluents))) x"
  proof (cases "x \<in> fluent_to_var ` set nfluents")
    case True
    then obtain y where y: "v x = Some y" using domv by auto
    have "(v |` (fluent_to_var ` set nfluents)) x = Some y" using True y by (simp add: restrict_in)
    thus ?thesis using y by (simp add: map_add_def)
  next
    case nv_no: False
    hence nd: "x \<notin> dom (v |` (fluent_to_var ` set nfluents))" by (simp add: restrict_map_def domIff)
    have mp: "((v |` dom (map_of net_bounds)) ++ (v |` (fluent_to_var ` set nfluents))) x
                = (v |` dom (map_of net_bounds)) x"
      by (rule map_add_dom_app_simps(3)[OF nd])
    show ?thesis
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      then obtain y where y: "v x = Some y" using domv by auto
      have "(v |` dom (map_of net_bounds)) x = Some y" using True y by (simp add: restrict_in)
      thus ?thesis using y mp by simp
    next
      case False
      hence vn: "v x = None" using domv nv_no by (auto simp: domIff)
      have pp: "(v |` dom (map_of net_bounds)) x = None" using False by (simp add: restrict_map_def)
      show ?thesis by (simp only: vn mp pp)
    qed
  qed
qed

subsection \<open>Generic run-lift engine: combining the propositional and numeric nets\<close>

text \<open>The numeric net carries the SAME urgent sets as the propositional net at every automaton index:
@{const augment_edge} touches only edges, not the urgent component (main automaton @{term \<open>{init_loc,
goal_loc}\<close>}, action automata @{term \<open>{starting_loc, ending_loc}\<close>}). This is what lets a propositional
delay step be re-issued verbatim on the numeric net (the urgency side-condition of @{thm [source]
step_u.step_t} transfers).\<close>
lemma num_urgent_eq:
  assumes p: "p < Suc (length actions)"
  shows "urgent (fst (snd num_net_impl.sem) ! p) = urgent (fst (snd net_impl.sem) ! p)"
proof (cases p)
  case 0
  have n: "urgent (fst (snd num_net_impl.sem) ! p) = {init_loc, goal_loc}"
    unfolding num_sem_alt_def fst_conv snd_conv
    apply (subst nth_map, simp add: p length_num_net_automata)
    apply (subst 0) apply (subst nth_Cons_0)
    unfolding comp_def num_main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
      urgent_def fst_conv by auto
  have pr: "urgent (fst (snd net_impl.sem) ! p) = {init_loc, goal_loc}"
    unfolding sem_alt_def fst_conv snd_conv
    apply (subst nth_map, simp add: p length_net_automata)
    apply (subst 0) apply (subst nth_Cons_0)
    unfolding comp_def main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
      urgent_def fst_conv by auto
  show ?thesis using n pr by simp
next
  case (Suc n)
  have nn: "urgent (fst (snd num_net_impl.sem) ! p) = {starting_loc, ending_loc}"
    apply (subst num_sem_alt_def) unfolding fst_conv snd_conv
    apply (subst nth_map, simp add: p length_num_net_automata)
    unfolding Suc apply (subst nth_Cons_Suc) apply (subst nth_map) using Suc p apply simp
    apply (subst num_action_auto_urg) ..
  have pr: "urgent (fst (snd net_impl.sem) ! p) = {starting_loc, ending_loc}"
    apply (subst sem_alt_def) unfolding fst_conv snd_conv
    apply (subst nth_map, simp add: p length_net_automata)
    unfolding Suc apply (subst nth_Cons_Suc) apply (subst nth_map) using Suc p apply simp
    apply (subst action_auto_urg) ..
  show ?thesis using nn pr by simp
qed

text \<open>Lifting a propositional delay step to the numeric net: a @{const Simple_Network_Language.label.Del}
step of @{const net_impl.sem} re-issues verbatim on @{const num_net_impl.sem} (same locations, same delay,
store untouched -- delays only advance clocks). The numeric net has no invariants (@{thm [source]
num_no_invs}) and the same urgent sets (@{thm [source] num_urgent_eq}), so the only new obligation is the
numeric boundedness of the (unchanged) store, supplied by the caller.\<close>
lemma num_step_t_lift:
  assumes propdel: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vp, c'\<rangle>"
      and bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
    shows "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c'\<rangle>"
proof -
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where
      c': "c' = c \<oplus> t"
    and t: "0 \<le> t"
    and urgp: "(\<exists>p<length N. L ! p \<in> urgent (N ! p)) \<longrightarrow> t = 0"
    apply (cases rule: step_u_elims(1)[OF propdel])
    unfolding as unfolding TAG_def by auto
  have lp: "length N = Suc (length actions)" using as length_net_impl by (simp add: comp_def)
  have urgn: "(\<exists>p<length (fst (snd num_net_impl.sem)). L ! p \<in> urgent (fst (snd num_net_impl.sem) ! p)) \<longrightarrow> t = 0"
  proof -
    have ln: "length (fst (snd num_net_impl.sem)) = Suc (length actions)" using length_num_net_impl by (simp add: comp_def)
    have "urgent (fst (snd num_net_impl.sem) ! p) = urgent (N ! p)" if "p < Suc (length actions)" for p
      using num_urgent_eq[OF that] as by simp
    thus ?thesis using urgp lp ln by auto
  qed
  show ?thesis
    unfolding c' num_net_impl.sem_def
    apply (rule step_t)
    subgoal unfolding TAG_def using num_no_invs by auto
    subgoal unfolding TAG_def using t by simp
    subgoal unfolding TAG_def using urgn unfolding num_net_impl.sem_def by simp
    subgoal unfolding TAG_def using bnd by auto
    done
qed

subsection \<open>Run-lifting: the numeric happening and plan runs (forward direction)\<close>

text \<open>The numeric happening run, existentially: from a combined config @{term \<open>(L, vn, c)\<close>} whose store
both satisfies the propositional @{const happening_pre_pre_delay} and tracks the pre-happening numeric
valuation @{term \<open>snd (M i)\<close>}, there is a numeric run that ends in a config satisfying
@{const num_happening_post} (the propositional post-invariant plus tracking of @{term \<open>snd (M (Suc i))\<close>}).
The run shadows the propositional @{const delay_and_apply} run (same locations and clocks), threading the
fluent variables through @{thm [source] num_int_step_lift} per internal step.\<close>
lemma num_happening_steps_possible:
  assumes i: "i < length planning_sem.htpl"
      and vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and pres: "num_happening_pre_pre_delay M i cfg"
  shows "\<exists>ns. num_graph_impl.steps (cfg # ns)
              \<and> num_happening_post M i (last (cfg # ns))"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have ppd: "happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)"
    using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_propD)
  have tr: "num_tracks v (snd (M i))" using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_trackD)
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_boundD)
  \<comment> \<open>The propositional happening run over the net_bounds PROJECTION store v |` dom (map_of net_bounds),
     which num_happening_pre_pre_delay_propD certifies as a valid propositional pre-state.\<close>
  have prun: "graph_impl.steps ((L, v |` dom (map_of net_bounds), c) # delay_and_apply i (L, v |` dom (map_of net_bounds), c))"
    and ppost: "happening_post i (last (delay_and_apply i (L, v |` dom (map_of net_bounds), c)))"
    using happening_steps_possible[OF i ppd] by blast+
  \<comment> \<open>TODO (the run-lift core): lift prun to a numeric run over the FULL store v, threading num_tracks
     (the running happening_num_update_set partial fold) and the num_net_bounds bound via num_int_step_lift
     + num_data_no_write_edge / num_data_upd_edge per internal step (L ! p pins the fired edge) and
     num_steps_delay_replace for the leading delay; num_happening_post then follows from ppost since the
     numeric run's last store projects (prop_proj_bounded) to the prop run's last store.\<close>
  show "\<exists>ns. num_graph_impl.steps (cfg # ns) \<and> num_happening_post M i (last (cfg # ns))"
    unfolding cfg
    sorry
qed

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
    using D(2) ib1 ib2 by (auto simp: prop_state_after_happ_def prop_state_before_happ_def planning_sem.state_seq_Suc_is_upd_state)
  have c3: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index (Suc i)) p))"
    using D(3) ib1 ib2 by (auto simp: planning_sem.locked_after_indexed_timepoint_is_locked_before_Suc[symmetric])
  have c4: "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index (Suc i))))"
    using D(4) ib1 ib2 by (auto simp: planning_sem.active_after_indexed_timepoint_is_active_before_Suc[symmetric])
  have c5: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 0 \<longrightarrow> L ! Suc j = off_loc"
    using D(5) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c6: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 1 \<longrightarrow> L ! Suc j = running_loc"
    using D(6) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c7: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_start_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(7) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  have c8: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_end_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(8) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  show ?thesis by (rule happening_pre_pre_delayI[OF HOL.refl D(1) c2 c3 c4 c5 c6 c7 c8])
qed

lemma pp_init_imp_pre_pre_delay_0:
  assumes hlen: "0 < length planning_sem.htpl"
      and props': "init_planning_state_props' x"
  shows "happening_pre_pre_delay 0 x"
proof (rule init_planning_state_props'E[OF props'])
  fix L v c
  assume s: "x = (L, v, c)"
    and lv: "Lv_conds L v"
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
  show "happening_pre_pre_delay 0 x" by (rule happening_pre_pre_delayI[OF s lv c2 c3 c4 c5 c6 c7 c8])
qed

lemma pp_post_last_imp_goal_trans_pre:
  assumes hlen: "0 < length planning_sem.htpl"
      and post: "happening_post (length planning_sem.htpl - 1) x"
  shows "goal_trans_pre x"
proof -
  obtain L v c where s: "x = (L, v, c)" by (rule prod_cases3)
  note D = happening_post_dests[OF post s]
  have c3: "v acts_active = Some 0"
    using D(4) by (subst (asm) planning_sem.active_after_final_is_0) simp
  have c4: "L = planning_loc # map (\<lambda>x. off_loc) actions"
  proof (subst list_eq_iff_nth_eq, intro conjI allI impI)
    show "length L = length (planning_loc # map (\<lambda>x. off_loc) actions)"
      using Lv_conds_dests(1)[OF D(1)] by simp
  next
    fix i assume i: "i < length L"
    show "L ! i = (planning_loc # map (\<lambda>x. off_loc) actions) ! i"
    proof (cases i)
      case 0
      thus ?thesis using Lv_conds_dests(2)[OF D(1)] by simp
    next
      case (Suc i')
      hence i': "i' < length actions" using i Lv_conds_dests(1)[OF D(1)] by simp
      have "planning_sem.closed_active_count (planning_sem.time_index (length planning_sem.htpl - 1)) (actions ! i') = 0"
        by (rule planning_sem.closed_active_count_final_is_0[OF nth_mem[OF i']])
      hence "L ! Suc i' = off_loc" using D(5) i' by blast
      thus ?thesis using Suc i' by simp
    qed
  qed
  have c5: "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p))"
    apply (rule exI[of _ "planning_sem.upd_state (length planning_sem.htpl - 1)"])
    using D(2) hlen
    apply (subst planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    apply (rule conjI)
    using planning_sem.plan_state_seq_valid apply fastforce
    apply (subst (asm) prop_state_after_happ_def, simp)
    apply (subst (asm) planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    by blast
  have c6: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    using D(3) unfolding planning_sem.locked_after_final_is_0 int_of_nat_def by simp
  show ?thesis by (rule goal_trans_preI[OF s D(1) c3 c4 c5 c6])
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
      and post: "num_happening_post M i cfg"
  shows "num_happening_pre_pre_delay M (Suc i) cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "happening_post i (L, v |` dom (map_of net_bounds), c)" using post[unfolded cfg] by (rule num_happening_post_propD)
  have t: "num_tracks v (snd (M (Suc i)))" using post[unfolded cfg] by (rule num_happening_post_trackD)
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v" using post[unfolded cfg] by (rule num_happening_post_boundD)
  show ?thesis unfolding cfg
    by (rule num_happening_pre_pre_delayI[where M = M and i = "Suc i", OF pp_post_imp_pre_pre_delay_Suc[OF ib p] t bnd])
qed

lemma num_init_imp_pre_pre_delay_0:
  assumes hlen: "0 < length planning_sem.htpl"
      and props': "num_init_planning_state_props' M cfg"
  shows "num_happening_pre_pre_delay M 0 cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" using props'[unfolded cfg] by (rule num_init_planning_state_props'_propD)
  have t: "num_tracks v (snd (M 0))" using props'[unfolded cfg] by (rule num_init_planning_state_props'_trackD)
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v" using props'[unfolded cfg] by (rule num_init_planning_state_props'_boundD)
  show ?thesis unfolding cfg
    by (rule num_happening_pre_pre_delayI[where M = M and i = 0, OF pp_init_imp_pre_pre_delay_0[OF hlen p] t bnd])
qed

lemma num_post_last_imp_goal_trans_pre:
  assumes hlen: "0 < length planning_sem.htpl"
      and post: "num_happening_post M (length planning_sem.htpl - 1) cfg"
  shows "num_goal_trans_pre M cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "happening_post (length planning_sem.htpl - 1) (L, v |` dom (map_of net_bounds), c)" using post[unfolded cfg] by (rule num_happening_post_propD)
  have t0: "num_tracks v (snd (M (Suc (length planning_sem.htpl - 1))))" using post[unfolded cfg] by (rule num_happening_post_trackD)
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v" using post[unfolded cfg] by (rule num_happening_post_boundD)
  have suc_eq: "Suc (length planning_sem.htpl - 1) = length planning_sem.htpl" using hlen by simp
  have t: "num_tracks v (snd (M (length planning_sem.htpl)))" using t0 unfolding suc_eq .
  show ?thesis unfolding cfg
    by (rule num_goal_trans_preI[where M = M, OF pp_post_last_imp_goal_trans_pre[OF hlen p] t bnd])
qed

lemma num_init_imp_goal_trans_pre:
  assumes hlen: "0 = length planning_sem.htpl"
      and props': "num_init_planning_state_props' M cfg"
  shows "num_goal_trans_pre M cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" using props'[unfolded cfg] by (rule num_init_planning_state_props'_propD)
  have t0: "num_tracks v (snd (M 0))" using props'[unfolded cfg] by (rule num_init_planning_state_props'_trackD)
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v" using props'[unfolded cfg] by (rule num_init_planning_state_props'_boundD)
  have t: "num_tracks v (snd (M (length planning_sem.htpl)))" using t0 by (simp add: hlen[symmetric])
  show ?thesis unfolding cfg
    by (rule num_goal_trans_preI[where M = M, OF pp_init_imp_goal_trans_pre[OF hlen p] t bnd])
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
  have chain: "\<exists>ms. num_graph_impl.steps (cfg' # ms)
                   \<and> num_happening_post M (length planning_sem.htpl - 1) (last (cfg' # ms))"
    if "num_happening_pre_pre_delay M j cfg'" "j < length planning_sem.htpl" for j cfg'
    using that
  proof (induction "length planning_sem.htpl - 1 - j" arbitrary: j cfg')
    case 0
    hence jeq: "j = length planning_sem.htpl - 1" using "0.prems"(2) by linarith
    obtain ms where ms: "num_graph_impl.steps (cfg' # ms)"
                        "num_happening_post M j (last (cfg' # ms))"
      using num_happening_steps_possible[OF "0.prems"(2) vss "0.prems"(1)] by blast
    show ?case using ms jeq by blast
  next
    case (Suc d)
    have jlt1: "j < length planning_sem.htpl - 1" using Suc.hyps(2) by linarith
    obtain ms1 where ms1: "num_graph_impl.steps (cfg' # ms1)"
                          "num_happening_post M j (last (cfg' # ms1))"
      using num_happening_steps_possible[OF Suc.prems(2) vss Suc.prems(1)] by blast
    have preSuc: "num_happening_pre_pre_delay M (Suc j) (last (cfg' # ms1))"
      by (rule num_post_imp_pre_pre_delay_Suc[OF jlt1 ms1(2)])
    have meas: "d = length planning_sem.htpl - 1 - Suc j" using Suc.hyps(2) by linarith
    have sucjlt: "Suc j < length planning_sem.htpl" using jlt1 by linarith
    obtain ms2 where ms2: "num_graph_impl.steps (last (cfg' # ms1) # ms2)"
                          "num_happening_post M (length planning_sem.htpl - 1) (last (last (cfg' # ms1) # ms2))"
      using Suc.hyps(1)[OF meas preSuc sucjlt] by blast
    have steps: "num_graph_impl.steps (cfg' # ms1 @ ms2)"
      using num_graph_impl.steps_append[OF ms1(1) ms2(1)] by simp
    have lasteq: "last (cfg' # ms1 @ ms2) = last (last (cfg' # ms1) # ms2)"
      by (cases ms2) auto
    have "num_happening_post M (length planning_sem.htpl - 1) (last (cfg' # ms1 @ ms2))"
      using ms2(2) lasteq by simp
    thus ?case using steps by blast
  qed
  have pre0: "num_happening_pre_pre_delay M 0 cfg" by (rule num_init_imp_pre_pre_delay_0[OF hlen pres])
  obtain ms where ms: "num_graph_impl.steps (cfg # ms)"
                      "num_happening_post M (length planning_sem.htpl - 1) (last (cfg # ms))"
    using chain[OF pre0 hlen] by blast
  have "num_goal_trans_pre M (last (cfg # ms))"
    by (rule num_post_last_imp_goal_trans_pre[OF hlen ms(2)])
  thus ?thesis using ms(1) by blast
qed


end

end

theory TP_NTA_Reduction_Correctness
  imports TP_NTA_Reduction_Correctness_Steps
begin
context tp_nta_reduction_correctness
begin
lemma happening_steps_possible:
  assumes i: "i < length planning_sem.htpl" 
      and pres: "happening_pre_pre_delay i s"
      and lvp: "LvP s"
  shows "graph_impl.steps (s#delay_and_apply i s) \<and> happening_post i (last (delay_and_apply i s)) \<and> LvP (last (delay_and_apply i s))" 
proof -
  let ?seq = "((ext_seq \<circ> seq_apply) (map edge_2_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
             ((ext_seq \<circ> seq_apply) (map end_edge_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions]))
               ((ext_seq \<circ> seq_apply) (map start_edge_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
                 (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (planning_sem.time_index i)) [0..<length actions])) 
                  ((ext_seq \<circ> seq_apply) (map edge_3_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions])) [delay (get_delay i) s])))))"
  presume p: "graph_impl.steps ?seq \<and> happening_post i (last ?seq) \<and> LvP (last ?seq)"

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

  have Lv_con: "Lv_conds L v" using lvp unfolding s by simp
  
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

  show "graph_impl.steps (s#delay_and_apply i s) \<and> happening_post i (last (delay_and_apply i s)) \<and> LvP (last (delay_and_apply i s))" 
    apply (intro conjI)
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
    subgoal
      unfolding delay_and_apply_def Let_def
      apply (subst apply_nth_happening_def)
      unfolding Let_def apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def  apply_instant_actions_alt
      unfolding comp_apply[of ext_seq seq_apply, symmetric]
      apply (subst last_tl_eq_last)
      using p by blast
    subgoal
      unfolding delay_and_apply_def Let_def
      apply (subst apply_nth_happening_def)
      unfolding Let_def apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def  apply_instant_actions_alt
      unfolding comp_apply[of ext_seq seq_apply, symmetric]
      apply (subst last_tl_eq_last)
      using p by blast
    done
  
next
let ?seq = "((ext_seq \<circ> seq_apply) (map edge_2_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
             ((ext_seq \<circ> seq_apply) (map end_edge_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions]))
               ((ext_seq \<circ> seq_apply) (map start_edge_effect (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]))
                 (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (planning_sem.time_index i)) [0..<length actions])) 
                  ((ext_seq \<circ> seq_apply) (map edge_3_effect (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions])) [delay (get_delay i) s])))))"

  have seed: "LvP (delay (get_delay i) s)"
    using lvp by (cases s) (simp add: delay_def)

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
            dest!: happening_pre_post_delay_dests(4))
      subgoal by (auto 
            simp: planning_sem.open_active_count_eq_closed_active_count_if_only_instant_acts
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(5))
      using happening_pre_post_delay_dests apply auto[5]
      subgoal by (auto 
            simp: planning_sem.open_active_count_0_if_start_scheduled 
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(4))
      subgoal by (auto 
            simp: planning_sem.open_active_count_0_if_start_scheduled 
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(4))
      subgoal using happening_pre_post_delay_dests by auto
      subgoal by (auto 
            simp: planning_sem.open_active_count_1_if_ending
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(5))
      subgoal by (auto dest!: happening_pre_post_delay_dests(7))
      done
  qed
  show "graph_impl.steps ?seq \<and> happening_post i (last ?seq) \<and> LvP (last ?seq)"
      apply (rule start_ends_possible)
        apply (rule end_ends_possible)
          apply (rule start_starts_possible)
            apply (rule instant_actions_possible)
              apply (rule end_starts_possible)
    by (auto intro!: i graph_impl.steps.intros pres' seed)
qed


lemma set_foldl_append: "set (foldl (@) ys xs) = \<Union> (set ` (set xs)) \<union> (set ys)"
  apply (induction xs arbitrary: ys)
  by auto

lemma plan_steps_possible: 
  assumes "graph_impl.steps xs \<and> init_planning_state_props' (last xs) \<and> LvP (last xs)"
  shows "graph_impl.steps (ext_seq' (map delay_and_apply [0..<length planning_sem.htpl]) xs) \<and> goal_trans_pre (last (ext_seq' (map delay_and_apply [0..<length planning_sem.htpl]) xs)) \<and> LvP (last (ext_seq' (map delay_and_apply [0..<length planning_sem.htpl]) xs))"
proof (rule steps_seq.ext_seq'_induct_list_prop_and_post[
      where P = "\<lambda>i s. happening_pre_pre_delay i s \<and> LvP s" 
        and Q = "\<lambda>i s. happening_post i s \<and> LvP s" 
        and R = "\<lambda>x. init_planning_state_props' x \<and> LvP x" 
        and fs = "map delay_and_apply [0..<length planning_sem.htpl]" 
        and S = "\<lambda>x. goal_trans_pre x \<and> LvP x", 
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
  then have lt: "i < length planning_sem.htpl"
    and pre: "happening_pre_pre_delay i s"
    and lvp: "LvP s" by blast+
  have nth_eq: "(map delay_and_apply [0..<length planning_sem.htpl] ! i) = delay_and_apply i"
    using lt by simp
  show ?case unfolding nth_eq using happening_steps_possible[OF lt pre lvp] by blast
next
  case (3 i s)
  then have ib: "i < length planning_sem.htpl - 1"
    and post: "happening_post i s"
    and lvp: "LvP s" by blast+
  have ib1: "i < length planning_sem.htpl"
    and ib2: "Suc i < length planning_sem.htpl"
    using ib by linarith+
  obtain L v c where s: "s = (L, v, c)" by (rule prod_cases3)
  note D = happening_post_dests[OF post s]
  \<comment> \<open>The post-state of happening \<open>i\<close> is the pre-state of happening \<open>Suc i\<close>: transfer each
      invariant conjunct from \<open>after (time_index i)\<close> to \<open>before (time_index (Suc i))\<close>
      (the transfer lemmas and the index-guarded \<open>prop_state\<close> defs need the bounds \<open>ib1\<close>/\<open>ib2\<close>).
      \<open>Lv_conds\<close> is no longer a \<open>happening_post\<close> conjunct; it rides along in the threaded \<open>LvP s\<close>
      and passes through unchanged (same store \<open>s\<close>).\<close>
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
  have "happening_pre_pre_delay (Suc i) s" by (rule happening_pre_pre_delayI[OF s c2 c3 c4 c5 c6 c7 c8])
  thus ?case using lvp by blast
next
  case (4 x)
  then have hlen0: "0 = length planning_sem.htpl"
    and props': "init_planning_state_props' x"
    and lvp: "LvP x" by blast+
  have init_is_goal: "set goal \<subseteq> set init" using hlen0 planning_sem.valid_plan_state_seq by auto
  have "goal_trans_pre x"
    apply (rule init_planning_state_props'E[OF props'])
    apply (rule goal_trans_preI)
    using init_is_goal by auto
  thus ?case using lvp by blast
next
  case (5 x)
  then have hlen: "0 < length planning_sem.htpl"
    and props': "init_planning_state_props' x"
    and lvp: "LvP x" by blast+
  have "happening_pre_pre_delay 0 x"
  proof (rule init_planning_state_props'E[OF props'])
    fix L v c
    assume s: "x = (L, v, c)"
      and va: "v acts_active = Some 0"
      and Leq: "L = planning_loc # map (\<lambda>x. off_loc) actions"
      and pv: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p)"
      and pl: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
      and cs: "\<forall>i<length actions. c (act_to_start_clock (actions ! i)) = 0"
      and ce: "\<forall>i<length actions. c (act_to_end_clock (actions ! i)) = 0"
    \<comment> \<open>The very first happening is preceded by the initial state: every \<open>happening_pre_pre_delay 0\<close>
        conjunct follows from \<open>init_planning_state_props'\<close> by collapsing the
        \<open>before (time_index 0)\<close> quantities to their initial values. \<open>Lv_conds\<close> is no longer supplied
        by \<open>init_planning_state_props'E\<close>; it rides along in the threaded \<open>LvP x\<close>.\<close>
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
  thus ?case using lvp by blast
next
  case (6 x)
  then have hlen: "0 < length planning_sem.htpl"
    and post: "happening_post (length planning_sem.htpl - 1) x"
    and lvp: "LvP x" by blast+
  obtain L v c where s: "x = (L, v, c)" by (rule prod_cases3)
  have lv: "Lv_conds L v" using lvp unfolding s by simp
  note D = happening_post_dests[OF post s]
  \<comment> \<open>The post-state of the final happening already satisfies the goal-transition pre-state: every
      invariant conjunct collapses to its final value (active and locks back to \<open>0\<close>, every action
      location back to \<open>off_loc\<close>, and \<open>prop_state\<close> witnessed by the final state sequence entry).
      \<open>Lv_conds\<close> is no longer a \<open>happening_post\<close> conjunct; the length/loc facts come from the threaded
      \<open>LvP x\<close> via \<open>lv\<close>, and \<open>LvP x\<close> passes through to the conclusion unchanged.\<close>
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
  have "goal_trans_pre x" by (rule goal_trans_preI[OF s c3 c4 c5 c6])
  thus ?case using lvp by blast
qed

lemma final_step_possible: 
  assumes "graph_impl.steps xs \<and> goal_trans_pre (last xs) \<and> LvP (last xs)"
  shows "graph_impl.steps ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] xs) \<and> goal_state_conds (last ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] xs))"
proof (rule steps_seq.ext_seq_comp_seq_apply_single_list_prop_and_post[where R = "\<lambda>x. goal_trans_pre x \<and> LvP x", OF assms], rule conjI)
  fix x::"nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)"
  assume aL: "goal_trans_pre x \<and> LvP x"
  hence a: "goal_trans_pre x"
    and lvp: "LvP x" by simp_all
  \<comment> \<open>The goal edge fires from the goal-transition pre-state to the goal state: it only flips
      location 0 to \<open>goal_loc\<close> and \<open>planning_lock\<close> to 2. Every \<open>goal_state_conds\<close> conjunct comes from
      \<open>goal_trans_pre\<close> (value/lock/loc), except \<open>bounded\<close>, which is no longer a \<open>goal_trans_pre\<close>
      conjunct and is re-sourced from the threaded \<open>LvP x\<close> via \<open>lv\<close> (\<open>single_upd_bounded\<close> on the
      \<open>planning_lock \<mapsto> 2\<close> update, whose bound is \<open>(0, 2)\<close>).\<close>
  show "goal_state_conds (main_auto_goal_edge_effect x)"
  proof (rule goal_trans_preE[OF a])
    fix L v c
    assume s: "x = (L, v, c)"
      and va: "v acts_active = Some 0"
      and Leq: "L = planning_loc # map (\<lambda>x. off_loc) actions"
      and pv: "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p))"
      and pl: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    have lv: "Lv_conds L v" using lvp unfolding s by simp
    show "goal_state_conds (main_auto_goal_edge_effect x)"
      unfolding s main_auto_goal_edge_effect_alt
    proof (rule goal_state_condsI, rule HOL.refl)
      show "bounded (map_of net_bounds) (v(planning_lock \<mapsto> 2))"
        by (rule single_upd_bounded[OF Lv_conds_dests(3)[OF lv] map_of_net_bounds_planning_lock]; simp)
      show "(v(planning_lock \<mapsto> 2)) acts_active = Some 0" using va by (simp add: variables_unique)
      show "(v(planning_lock \<mapsto> 2)) planning_lock = Some 2" by simp
      show "L[0 := goal_loc] = goal_loc # map (\<lambda>x. off_loc) actions" unfolding Leq by simp
      show "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> (v(planning_lock \<mapsto> 2)) (prop_to_var p) = Some (prop_state S p))"
        using pv by (auto simp: variables_unique)
      show "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> (v(planning_lock \<mapsto> 2)) (prop_to_lock p) = Some 0"
        using pl by (auto simp: variables_unique)
    qed
  qed
  show "graph_impl.steps [x, main_auto_goal_edge_effect x]"
  proof -
    obtain L v c where s: "x = (L, v, c)" by (rule prod_cases3)
    have lv: "Lv_conds L v" using lvp unfolding s by simp
    show "graph_impl.steps [x, main_auto_goal_edge_effect x]"
      apply (rule single_step_intro)
      apply (rule ssubst[OF s])
      unfolding main_auto_goal_edge_effect_alt prod.case
      apply (insert a[unfolded s])
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
              apply (simp add: Lv_conds_dests(4)[OF lv])
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
      \<comment> \<open>The remaining \<open>step_int\<close> premises: the target-location facts (\<open>L ! 0 = planning_loc\<close>,
          \<open>0 < length L\<close>) come from \<open>lv\<close> (no longer from \<open>goal_trans_pre\<close>); the \<open>is_upds\<close> of the single
          \<open>planning_lock \<mapsto> 2\<close> update is structural; the two \<open>bounded\<close> goals reduce to \<open>bounded v\<close> from
          \<open>lv\<close> via \<open>single_upd_bounded\<close> (bound \<open>(0, 2)\<close>).\<close>
            apply (rule Lv_conds_dests(2)[OF lv])
           apply (insert Lv_conds_dests(1)[OF lv]; simp)
          apply simp
         apply simp
        apply (rule is_upds.intros)
         apply (subst is_upd_def)
         apply (intro conjI exI)
           apply simp
          apply (rule check_bexp_is_val.intros)
         apply simp
        apply (rule is_upds.intros)
       apply (rule single_upd_bounded[OF Lv_conds_dests(3)[OF lv] map_of_net_bounds_planning_lock]; simp)
      by (rule Lv_conds_dests(3)[OF lv])
  qed
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

end

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
      \<comment> \<open>The range-boundedness reachability invariant (grounder-match contract, complementing the
         static integrality assumptions in @{locale numeric_tp_nta_reduction}): along any valid numeric
         state sequence the per-happening valuations stay within the declared fluent variable bounds.
         A certifier checks this against the candidate plan's finite trace; PDDL supplies no bounds, and a
         global closure over all in-range valuations would be false for monotone effects. The intermediate
         partial-fold stores within a happening are derived in range from the @{term i}/@{term \<open>Suc i\<close>}
         endpoints (each fluent is written at most once, so a partial value is one of the two endpoints).
         Indexed by @{term \<open>rat_impl.htpl\<close>}, which the later \<open>rat_impl_htpl_eq\<close> equates with
         @{term \<open>planning_sem.htpl\<close>}.\<close>
      and num_seq_in_bounds:
            "\<And>M i. num_plan.num_rat_impl.num_valid_state_sequence M
               \<Longrightarrow> snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)
               \<Longrightarrow> i \<le> length rat_impl.htpl
               \<Longrightarrow> fluent_in_bounds (snd (M i))"
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

text \<open>The encoder-faithfulness side-conditions @{const nexp_ok} / @{const comp_ok} (every leaf reads a
declared, integer-valued fluent or an integer constant, and every @{term NDiv} divides exactly -- the
precise discrete-fragment condition under which the truncating Munta integer arithmetic agrees with the
abstract field arithmetic) are now defined in the @{locale numeric_tp_nta_reduction_defs} ancestor, so
the grounder-match well-formedness assumptions can reference them.\<close>

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

text \<open>The numeric structural invariant, the full-store analogue of @{const Lv_conds}: it is the
propositional @{const Lv_conds} content (length / head location / @{const planning_lock}) but with the
boundedness stated against the FULL numeric bounds @{const num_net_bounds}. It is factored OUT of the
numeric twins below and carried as a SEPARATE conjunct (@{text num_LvP}) throughout the numeric run,
exactly as @{const LvP} is carried through the propositional run.\<close>
definition "num_Lv_conds L v \<equiv>
  length L = Suc (length actions)
\<and> L ! 0 = planning_loc
\<and> Simple_Network_Language.bounded (map_of num_net_bounds) v
\<and> v planning_lock = Some 1"

fun num_LvP :: "(nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool" where
  "num_LvP (L, v, c) = num_Lv_conds L v"

lemma num_Lv_condsI:
  assumes "length L = Suc (length actions)"
    "L ! 0 = planning_loc"
    "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    "v planning_lock = Some 1"
  shows "num_Lv_conds L v"
  using assms unfolding num_Lv_conds_def by blast

lemma num_Lv_conds_dests:
  assumes "num_Lv_conds L v"
  shows "length L = Suc (length actions)"
    "L ! 0 = planning_loc"
    "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    "v planning_lock = Some 1"
  using assms unfolding num_Lv_conds_def by auto

lemma num_Lv_conds_maintained:
  assumes "num_Lv_conds L v"
    and "length L = length L'"
    and "L ! 0 = L' ! 0"
    and "v' planning_lock = v planning_lock"
    and "Simple_Network_Language.bounded (map_of num_net_bounds) v \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v'"
  shows "num_Lv_conds L' v'"
  using assms unfolding num_Lv_conds_def by simp

definition "num_happening_pre M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_pre i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M i)))"

definition "num_happening_pre_pre_delay M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M i)))"

definition "num_happening_post M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_post i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M (Suc i))))"

definition "num_init_planning_state_props' M Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> init_planning_state_props' (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M 0)))"

definition "num_goal_trans_pre M Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> goal_trans_pre (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M (length planning_sem.htpl))))"

lemma num_happening_preI:
  assumes "happening_pre i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M i))"
  shows "num_happening_pre M i (L, v, c)"
  using assms by (simp add: num_happening_pre_def)

lemma num_happening_pre_propD: "num_happening_pre M i (L, v, c) \<Longrightarrow> happening_pre i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_trackD: "num_happening_pre M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M i))"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_pre_delayI:
  assumes "happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M i))"
  shows "num_happening_pre_pre_delay M i (L, v, c)"
  using assms by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_propD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_trackD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M i))"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_postI:
  assumes "happening_post i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M (Suc i)))"
  shows "num_happening_post M i (L, v, c)"
  using assms by (simp add: num_happening_post_def)

lemma num_happening_post_propD: "num_happening_post M i (L, v, c) \<Longrightarrow> happening_post i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_post_def)

lemma num_happening_post_trackD: "num_happening_post M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M (Suc i)))"
  by (simp add: num_happening_post_def)

lemma num_init_planning_state_props'I:
  assumes "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M 0))"
  shows "num_init_planning_state_props' M (L, v, c)"
  using assms by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_propD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> init_planning_state_props' (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_trackD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> num_tracks v (snd (M 0))"
  by (simp add: num_init_planning_state_props'_def)

lemma num_goal_trans_preI:
  assumes "goal_trans_pre (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M (length planning_sem.htpl)))"
  shows "num_goal_trans_pre M (L, v, c)"
  using assms by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_propD: "num_goal_trans_pre M (L, v, c) \<Longrightarrow> goal_trans_pre (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_trackD:
  "num_goal_trans_pre M (L, v, c) \<Longrightarrow> num_tracks v (snd (M (length planning_sem.htpl)))"
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
  proof (induction rule: check_bexp_is_val.inducts)
    case (12 s x val)
    then show ?case by (auto simp: map_le_def dom_def intro: check_bexp_is_val.intros)
  qed (blast intro: check_bexp_is_val.intros)+
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

text \<open>The set-level happening update equals the list-level fold over any @{emph \<open>distinct\<close>}
enumeration of the happening, under the functional + pairwise-non-interference side conditions:
@{const Finite_Set.fold} collapses to a @{const fold} on a distinct list whose snaps pairwise commute.
This is the bridge that lets the run-order fold of the numeric edge updates (a list) be identified with
@{const num_plan.num_rat_impl.happening_num_update_set} (the order-independent set update that
@{const num_plan.num_rat_impl.num_valid_state_sequence} pins to @{term \<open>snd (M (Suc i))\<close>}).\<close>
lemma happening_num_update_set_eq_fold_list:
  assumes "distinct xs"
      and "\<And>a. a \<in> set xs \<Longrightarrow> upds_functional ((set \<circ> upds) a)"
      and "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action a b"
    shows "num_plan.num_rat_impl.happening_num_update_set (set xs) w = num_plan.num_rat_impl.happening_num_update xs w"
  using assms
proof (induction xs arbitrary: w)
  case Nil
  show ?case
    by (simp add: num_plan.num_rat_impl.happening_num_update_set_empty[unfolded comp_def]
                  num_plan.num_rat_impl.happening_num_update_Nil[unfolded comp_def])
next
  case (Cons x xs)
  have "num_plan.num_rat_impl.happening_num_update_set (insert x (set xs)) w
          = num_plan.num_rat_impl.happening_num_update_set (set xs) (num_plan.num_rat_impl.snap_num_update x w)"
    by (rule num_plan.num_rat_impl.happening_num_update_set_insert)
       (use Cons.prems in \<open>auto simp: comp_def\<close>)
  also have "\<dots> = num_plan.num_rat_impl.happening_num_update xs (num_plan.num_rat_impl.snap_num_update x w)"
    using Cons.IH Cons.prems by (auto simp: comp_def)
  also have "\<dots> = num_plan.num_rat_impl.happening_num_update (x # xs) w"
    by (simp add: num_plan.num_rat_impl.happening_num_update_Cons)
  finally show ?case by (simp add: comp_def)
qed

text \<open>FACT-1 of the numeric run-lift: re-express a single happening as a union over action
@{emph \<open>indices\<close>}. The abstract @{thm [source] planning_sem.happ_at_is_union_of_starting_ending_instant}
splits the happening into instant/ending/starting snap sets; regrouping the @{term at_start} and
@{term at_end} images and converting each @{term \<open>{a \<in> set actions. P a}\<close>} to its index form via
@{thm [source] set_conv_nth} (folding the @{term is_starting_index} / @{term is_ending_index} /
@{term is_instant_index} abbreviations) yields the index-indexed shape the run-order list consumes:
the at-start snaps of the starting-or-instant indices, unioned with the at-end snaps of the
ending-or-instant indices. Stated for an arbitrary time @{term t}; instantiate @{term \<open>t = planning_sem.time_index i\<close>}
for the @{term i}-th happening.\<close>
lemma happ_at_index_decomp:
  "planning_sem.happ_at planning_sem.plan_happ_seq t
     = at_start ` { actions ! j | j. j < length actions \<and> (is_starting_index t j \<or> is_instant_index t j) }
       \<union> at_end ` { actions ! j | j. j < length actions \<and> (is_ending_index t j \<or> is_instant_index t j) }"
proof -
  have start_set: "planning_sem.instant_actions_at t \<union> planning_sem.starting_actions_at t
                     = { actions ! j | j. j < length actions \<and> (is_starting_index t j \<or> is_instant_index t j) }"
    unfolding planning_sem.instant_actions_at_def planning_sem.starting_actions_at_def
              is_starting_index_def is_instant_index_def
    by (simp only: set_conv_nth) blast
  have end_set: "planning_sem.instant_actions_at t \<union> planning_sem.ending_actions_at t
                   = { actions ! j | j. j < length actions \<and> (is_ending_index t j \<or> is_instant_index t j) }"
    unfolding planning_sem.instant_actions_at_def planning_sem.ending_actions_at_def
              is_ending_index_def is_instant_index_def
    by (simp only: set_conv_nth) blast
  have "planning_sem.happ_at planning_sem.plan_happ_seq t
          = planning_sem.instant_snaps_at t \<union> planning_sem.ending_snaps_at t \<union> planning_sem.starting_snaps_at t"
    by (rule planning_sem.happ_at_is_union_of_starting_ending_instant)
  also have "\<dots> = at_start ` (planning_sem.instant_actions_at t \<union> planning_sem.starting_actions_at t)
                    \<union> at_end ` (planning_sem.instant_actions_at t \<union> planning_sem.ending_actions_at t)"
    unfolding planning_sem.instant_snaps_at_def planning_sem.ending_snaps_at_def planning_sem.starting_snaps_at_def
    by (auto simp: image_Un)
  finally show ?thesis
    by (simp only: start_set end_set)
qed

text \<open>S-property export (1): the @{term i}-th happening is finite. The whole happening sequence
@{const planning_sem.plan_happ_seq} is finite for a finite plan (@{thm [source]
planning_sem.finite_happ_seq}), and a single happening is the @{term snd}-image of the slice of
@{const planning_sem.plan_happ_seq} at @{term \<open>planning_sem.time_index i\<close>}.\<close>
lemma happening_finite:
  "finite (planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i))"
proof -
  have "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)
          = snd ` {p \<in> planning_sem.plan_happ_seq. fst p = planning_sem.time_index i}"
    by (force simp: image_iff)
  thus ?thesis by (simp add: planning_sem.finite_happ_seq)
qed

text \<open>S-property export (2): every snap in a happening has a functional update set. By
@{thm [source] happ_at_index_decomp} each snap is @{term \<open>at_start (actions ! j)\<close>} or
@{term \<open>at_end (actions ! j)\<close>} for some @{term \<open>j < length actions\<close>}, hence applied to an action in
@{term \<open>set actions\<close>}; the locale's @{thm [source] upds_functional_start} /
@{thm [source] upds_functional_end} give @{const upds_functional_list} of its updates, which
@{thm [source] upds_functional_set} lifts to @{const upds_functional} on the @{term set}.\<close>
lemma happening_upds_functional:
  assumes "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  shows "upds_functional ((set \<circ> upds) s)"
proof -
  have "s \<in> at_start ` { actions ! j | j. j < length actions
                            \<and> (is_starting_index (planning_sem.time_index i) j
                               \<or> is_instant_index (planning_sem.time_index i) j) }
          \<union> at_end ` { actions ! j | j. j < length actions
                          \<and> (is_ending_index (planning_sem.time_index i) j
                             \<or> is_instant_index (planning_sem.time_index i) j) }"
    using assms by (simp only: happ_at_index_decomp)
  then consider
      (starting) j where "j < length actions" and "s = at_start (actions ! j)"
    | (ending) j where "j < length actions" and "s = at_end (actions ! j)"
    by blast
  thus ?thesis
  proof cases
    case starting
    hence "actions ! j \<in> set actions" by simp
    hence "upds_functional_list (upds (at_start (actions ! j)))"
      using upds_functional_start by blast
    thus ?thesis
      using starting by (simp add: upds_functional_set upds_functional_list_def)
  next
    case ending
    hence "actions ! j \<in> set actions" by simp
    hence "upds_functional_list (upds (at_end (actions ! j)))"
      using upds_functional_end by blast
    thus ?thesis
      using ending by (simp add: upds_functional_set upds_functional_list_def)
  qed
qed

text \<open>The numeric mutex-validity of the plan is one conjunct of the numeric plan validity carried by
the @{thm [source] num_valid} locale assumption.\<close>
lemma num_mutex_valid_plan: "num_plan.num_rat_impl.num_mutex_valid_plan"
  using num_valid unfolding num_plan.num_rat_impl.num_valid_plan_def by blast

text \<open>S-property export (3): two distinct snaps that co-occur in one happening do not numerically
interfere. Both snaps live at the same time @{term \<open>planning_sem.time_index i\<close>}; unfolding
@{const planning_sem.plan_happ_seq} exposes their plan-entry witnesses in @{term \<open>ran \<pi>_sem\<close>}, lifted
to @{term \<open>dom \<pi>_sem\<close>}. From two @{emph \<open>distinct\<close>} plan entries, the first conjunct of
@{const num_plan.num_rat_impl.num_mutex_valid_plan} applies at equal times (\<epsilon>-distance @{term 0});
from the @{emph \<open>same\<close>} entry the two distinct co-occurring snaps must be the start/end pair of an
instantaneous (@{term \<open>d = 0\<close>}) action, discharged by its instant-action clause.
NB the numeric @{term num_mutex_snap_action} machinery resolves through @{text num_plan.num_rat_impl},
but the happening sequence is the shared @{const planning_sem.plan_happ_seq} (both interpretations are
instantiated at the same @{term \<open>\<pi>_sem\<close>} / @{term \<open>rat_of_int \<epsilon>\<close>}).\<close>
lemma happening_num_noninterfere:
  assumes "s1 \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and "s2 \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and "s1 \<noteq> s2"
    shows "\<not> num_plan.num_rat_impl.num_mutex_snap_action s1 s2"
proof -
  have h1: "(planning_sem.time_index i, s1) \<in> planning_sem.plan_happ_seq"
    using assms(1) by (rule planning_sem.in_happ_atD)
  have h2: "(planning_sem.time_index i, s2) \<in> planning_sem.plan_happ_seq"
    using assms(2) by (rule planning_sem.in_happ_atD)
  obtain a ta da where
    A: "(a, ta, da) \<in> ran \<pi>_sem"
    and as1: "at_start a = s1 \<and> planning_sem.time_index i = ta
                \<or> at_end a = s1 \<and> planning_sem.time_index i = ta + da"
    using planning_sem.in_happ_seq_exD[OF h1] by blast
  obtain b tb db where
    B: "(b, tb, db) \<in> ran \<pi>_sem"
    and bs2: "at_start b = s2 \<and> planning_sem.time_index i = tb
                \<or> at_end b = s2 \<and> planning_sem.time_index i = tb + db"
    using planning_sem.in_happ_seq_exD[OF h2] by blast
  obtain k where k: "\<pi>_sem k = Some (a, ta, da)" using A unfolding ran_def by blast
  obtain l where l: "\<pi>_sem l = Some (b, tb, db)" using B unfolding ran_def by blast
  have kdom: "k \<in> dom \<pi>_sem" using k by blast
  have ldom: "l \<in> dom \<pi>_sem" using l by blast
  note nmvp = num_mutex_valid_plan[unfolded num_plan.num_rat_impl.num_mutex_valid_plan_def, folded \<pi>_sem_def]
  have distinct_clause: "\<not> num_plan.num_rat_impl.num_mutex_snap_action sa sb"
    if "k' \<in> dom \<pi>_sem" and "l' \<in> dom \<pi>_sem" and "k' \<noteq> l'"
       and "\<pi>_sem k' = Some (a', ta', da')" and "\<pi>_sem l' = Some (b', tb', db')"
       and "sa = at_start a' \<and> tt = ta' \<or> sa = at_end a' \<and> tt = ta' + da'"
       and "sb = at_start b' \<and> u = tb' \<or> sb = at_end b' \<and> u = tb' + db'"
       and "tt - u < rat_of_int \<epsilon> \<and> u - tt < rat_of_int \<epsilon> \<or> tt = u"
     for k' l' a' ta' da' b' tb' db' sa sb tt u
    using nmvp that by blast
  have instant_clause: "\<not> num_plan.num_rat_impl.num_mutex_snap_action (at_start a') (at_end a')"
    if "(a', tt, d') \<in> ran \<pi>_sem" and "d' = 0 \<or> d' < rat_of_int \<epsilon>"
    for a' tt d'
    using nmvp that by blast
  consider (diff) "k \<noteq> l" | (same) "k = l" by blast
  thus ?thesis
  proof cases
    case diff
    show ?thesis
      by (rule distinct_clause[OF kdom ldom diff k l _ _ _])
         (use as1 bs2 in blast)+
  next
    case same
    hence eq: "a = b" "ta = tb" "da = db" using k l by auto
    have s12: "s1 = at_start a \<and> s2 = at_end a \<or> s1 = at_end a \<and> s2 = at_start a"
      using as1 bs2 assms(3) eq by auto
    have da0: "da = 0" using as1 bs2 assms(3) eq by auto
    have ni: "\<not> num_plan.num_rat_impl.num_mutex_snap_action (at_start a) (at_end a)"
      by (rule instant_clause[OF A]) (simp add: da0)
    thus ?thesis
      using s12 by (metis num_plan.num_rat_impl.num_mutex_snap_action_refl)
  qed
qed

text \<open>Bridge: the rat-level @{text rat_impl} interpretation (the ancestor that
@{const num_plan.num_rat_impl.num_valid_state_sequence} unfolds into) and the propositional
@{text planning_sem} interpretation are instantiated with the SAME plan -- @{text rat_impl}'s plan
@{term \<open>map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>\<close>} is exactly @{const \<pi>_sem} --
so all plan-derived constants (@{const planning_sem.htps}/@{const planning_sem.htpl}/
@{const planning_sem.time_index}/@{const planning_sem.plan_happ_seq}) coincide across the two. This lets
the @{const num_plan.num_rat_impl.num_valid_state_sequence} fold-conjunct (stated over @{text rat_impl}'s
happening) feed the @{text planning_sem}-keyed S-property exports.\<close>
lemma rat_impl_plan_happ_seq_eq: "rat_impl.plan_happ_seq = planning_sem.plan_happ_seq"
  unfolding rat_impl.plan_happ_seq_def planning_sem.plan_happ_seq_def \<pi>_sem_def by simp

lemma rat_impl_htps_eq: "rat_impl.htps = planning_sem.htps"
  unfolding rat_impl.htps_def planning_sem.htps_def \<pi>_sem_def by simp

lemma rat_impl_htpl_eq: "rat_impl.htpl = planning_sem.htpl"
  by (simp add: rat_impl.htpl_def planning_sem.htpl_def rat_impl_htps_eq)

lemma rat_impl_time_index_eq: "rat_impl.time_index = planning_sem.time_index"
  by (simp add: rat_impl.time_index_def planning_sem.time_index_def rat_impl_htpl_eq)

lemma rat_impl_happ_at_eq:
  "planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)
     = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  by (simp add: rat_impl_plan_happ_seq_eq rat_impl_time_index_eq)

text \<open>Item 3 (the heart of Part 1): the run-order list fold of the numeric snap updates over ANY distinct
enumeration @{term xs} of the @{term i}-th happening equals the abstract after-valuation
@{term \<open>snd (M (Suc i))\<close>}. The happening's snaps pairwise commute
(@{thm [source] happening_num_noninterfere}), so FACT-2 (@{thm [source] happening_num_update_set_eq_fold_list})
collapses the order-dependent list fold to the order-independent set update
@{const num_plan.num_rat_impl.happening_num_update_set}, which
@{const num_plan.num_rat_impl.num_valid_state_sequence} pins to @{term \<open>snd (M (Suc i))\<close>} (after the
@{thm [source] rat_impl_happ_at_eq} namespace bridge).\<close>
lemma run_order_fold_eq_happening_num_update_set:
  assumes i: "i < length planning_sem.htpl"
      and vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and dist: "distinct xs"
      and setxs: "set xs = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
    shows "num_plan.num_rat_impl.happening_num_update xs (snd (M i)) = snd (M (Suc i))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  have fold_eq: "num_plan.num_rat_impl.happening_num_update_set (set xs) (snd (M i))
                   = num_plan.num_rat_impl.happening_num_update xs (snd (M i))"
  proof (rule happening_num_update_set_eq_fold_list[OF dist])
    show "upds_functional ((set \<circ> upds) a)" if "a \<in> set xs" for a
    proof -
      have "a \<in> ?S" using that setxs by simp
      thus ?thesis by (rule happening_upds_functional)
    qed
  next
    show "\<not> num_plan.num_rat_impl.num_mutex_snap_action a b"
      if "a \<in> set xs" "b \<in> set xs" "a \<noteq> b" for a b
    proof -
      have "a \<in> ?S" and "b \<in> ?S" using that setxs by simp_all
      thus ?thesis using that(3) by (rule happening_num_noninterfere)
    qed
  qed
  have iH: "i < length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  have vss_i: "num_plan.num_rat_impl.happening_num_update_set ?S (snd (M i)) = snd (M (Suc i))"
  proof -
    have "num_plan.num_rat_impl.happening_num_update_set
            (planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)) (snd (M i))
          = snd (M (Suc i))"
      using vss iH unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def by blast
    thus ?thesis by (simp add: rat_impl_happ_at_eq)
  qed
  have "num_plan.num_rat_impl.happening_num_update xs (snd (M i))
          = num_plan.num_rat_impl.happening_num_update_set (set xs) (snd (M i))"
    by (rule fold_eq[symmetric])
  also have "\<dots> = num_plan.num_rat_impl.happening_num_update_set ?S (snd (M i))"
    by (simp only: setxs)
  also have "\<dots> = snd (M (Suc i))" by (rule vss_i)
  finally show ?thesis .
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
      and lvp: "num_LvP (L, v, c)"
  shows "\<forall>p<length (fst (snd num_net_impl.sem)). fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
proof (intro allI impI)
  have num_lv: "num_Lv_conds L v" using lvp by simp
  have len_L: "length L = Suc (length actions)" by (rule num_Lv_conds_dests(1)[OF num_lv])

  fix p
  assume "p < length (fst (snd num_net_impl.sem))"
  hence pl: "p < Suc (length actions)"
        "p < length L"
    using length_num_net_impl
    using len_L by simp+

  show "fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
  proof (cases p)
    case 0
    then have 1: "L ! p = planning_loc" using num_Lv_conds_dests(2)[OF num_lv] by simp

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

lemma map_of_map_inj_on:
  assumes "inj_on key (set xs)"
      and "a \<in> set xs"
    shows "map_of (map (\<lambda>x. (key x, vl x)) xs) (key a) = Some (vl a)"
  using assms
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "a = x")
    case True
    thus ?thesis by simp
  next
    case False
    hence ax: "a \<in> set xs" using Cons.prems(2) by simp
    have inj_xs: "inj_on key (set xs)" using Cons.prems(1) by (rule inj_on_subset) auto
    have xmem: "x \<in> set (x # xs)" by simp
    have "key a \<noteq> key x"
    proof
      assume eq: "key a = key x"
      have "a = x" by (rule inj_onD[OF Cons.prems(1) eq Cons.prems(2) xmem])
      thus False using False by simp
    qed
    thus ?thesis using Cons.IH[OF inj_xs ax] by simp
  qed
qed simp
lemma map_of_num_net_bounds_fluent:
  assumes "f \<in> set nfluents"
  shows "map_of num_net_bounds (fluent_to_var f) = Some (fluent_lo f, fluent_hi f)"
proof -
  have fresh: "fluent_to_var f \<notin> fst ` set all_vars" using fluent_vars_fresh assms by blast
  hence notdom: "fluent_to_var f \<notin> dom (map_of all_vars)" by (simp add: dom_map_of_conv_image_fst)
  have split: "map_of num_net_bounds (fluent_to_var f) = map_of num_fluent_vars (fluent_to_var f)"
    unfolding num_all_vars_def map_of_append using notdom by (simp add: map_add_dom_app_simps(3))
  have "map_of num_fluent_vars (fluent_to_var f) = Some (fluent_lo f, fluent_hi f)"
    unfolding num_fluent_vars_def
    by (rule map_of_map_inj_on[OF fluent_to_var_inj assms])
  thus ?thesis using split by simp
qed

lemma num_tracks_bounded:
  assumes domeq: "dom vn = dom (map_of num_net_bounds)"
      and prop_b: "Simple_Network_Language.bounded (map_of net_bounds) (vn |` dom (map_of net_bounds))"
      and tr: "num_tracks vn w"
      and inb: "fluent_in_bounds w"
    shows "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
  unfolding Simple_Network_Language.bounded_def
proof (intro conjI)
  show "dom vn = dom (map_of num_net_bounds)" by (rule domeq)
next
  show "\<forall>x \<in> dom vn. fst (the (map_of num_net_bounds x)) \<le> the (vn x)
          \<and> the (vn x) \<le> snd (the (map_of num_net_bounds x))"
  proof (intro ballI)
    fix x assume xdom: "x \<in> dom vn"
    have "x \<in> dom (map_of net_bounds) \<union> fluent_to_var ` set nfluents"
      using xdom domeq dom_map_of_num_net_bounds by simp
    thus "fst (the (map_of num_net_bounds x)) \<le> the (vn x)
          \<and> the (vn x) \<le> snd (the (map_of num_net_bounds x))"
    proof
      assume xp: "x \<in> dom (map_of net_bounds)"
      have xrp: "x \<in> dom (vn |` dom (map_of net_bounds))" using xdom xp by simp
      have r: "(vn |` dom (map_of net_bounds)) x = vn x" using xp by (simp add: restrict_in)
      have b: "map_of num_net_bounds x = map_of net_bounds x" by (rule map_of_num_net_bounds_eq_on_props[OF xp])
      have "fst (the (map_of net_bounds x)) \<le> the ((vn |` dom (map_of net_bounds)) x)
            \<and> the ((vn |` dom (map_of net_bounds)) x) \<le> snd (the (map_of net_bounds x))"
        using prop_b xrp unfolding Simple_Network_Language.bounded_def by blast
      thus ?thesis unfolding r b by simp
    next
      assume "x \<in> fluent_to_var ` set nfluents"
      then obtain f where f: "f \<in> set nfluents"
        and xf: "x = fluent_to_var f"
        by auto
      have bx: "map_of num_net_bounds x = Some (fluent_lo f, fluent_hi f)"
        unfolding xf by (rule map_of_num_net_bounds_fluent[OF f])
      obtain r where wf: "w f = Some r" using num_tracks_definedD[OF tr f] by blast
      have vx: "vn x = Some (const_to_int r)" unfolding xf by (rule num_tracks_varD[OF tr f wf])
      have "fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
        using inb f wf unfolding fluent_in_bounds_def by force
      thus ?thesis using bx vx by simp
    qed
  qed
qed

text \<open>The per-happening endpoint facts the run-lift consumes: along the init-anchored valid numeric
sequence every @{term \<open>snd (M i)\<close>} (for @{term \<open>i \<le> length planning_sem.htpl\<close>}) is in range -- hence
integer-valued -- by the @{thm [source] num_seq_in_bounds} reachability invariant (re-indexed from
@{term \<open>rat_impl.htpl\<close>} to @{term \<open>planning_sem.htpl\<close>} via @{thm [source] rat_impl_htpl_eq}).\<close>
lemma num_seq_fluent_in_bounds:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i \<le> length planning_sem.htpl"
    shows "fluent_in_bounds (snd (M i))"
proof -
  have "i \<le> length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  thus ?thesis by (rule num_seq_in_bounds[OF vss m0])
qed

lemma num_seq_val_ok:
  assumes "num_plan.num_rat_impl.num_valid_state_sequence M"
      and "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and "i \<le> length planning_sem.htpl"
    shows "num_val_ok (snd (M i))"
  by (rule fluent_in_bounds_imp_num_val_ok[OF num_seq_fluent_in_bounds[OF assms]])

text \<open>R1 (integrality \<Rightarrow> faithfulness) helpers for the numeric run-lift. First the eval/integrality
half of @{thm [source] nexp_ok_is_val}, factored out so it stands without the @{const num_tracks}
premise: an @{const nexp_ok} expression evaluates to a defined, integer-valued result. The arithmetic
cases close by @{thm [source] Ints_add} / @{thm [source] Ints_diff} / @{thm [source] Ints_mult}; the
@{term NDiv} case uses @{thm [source] Ints_div_exact} with the @{text \<open>\<noteq> 0\<close>} and @{text dvd}
side-conditions that @{const nexp_ok} already carries.\<close>
lemma nexp_ok_eval:
  assumes "nexp_ok w e"
  shows "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>"
  using assms
proof (induction e)
  case (NConst c)
  thus ?case by auto
next
  case (NVar f)
  thus ?case by auto
next
  case (NAdd a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by (auto simp: Ints_add)
next
  case (NSub a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by (auto simp: Ints_diff)
next
  case (NMul a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by (auto simp: Ints_mult)
next
  case (NDiv a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  have nz: "rb \<noteq> 0" and dvd: "const_to_int rb dvd const_to_int ra"
    using NDiv.prems a(1) b(1) by auto
  have ev: "eval_nexp w (NDiv a b) = Some (ra / rb)" using a(1) b(1) nz by simp
  have iv: "ra / rb \<in> \<int>" by (rule Ints_div_exact[OF a(2) b(2) nz dvd])
  thus ?case using ev by blast
qed

text \<open>A single snap update of a start/end snap of a plan action preserves @{const num_val_ok}: every
declared fluent stays defined and integer-valued. A written fluent gets @{term \<open>eval_nexp w e\<close>} for
its @{const nexp_ok} right-hand side (the snap's updates are @{const nexp_ok} over any @{const num_val_ok}
valuation by @{thm [source] snap_upds_nexp_ok_start} / @{thm [source] snap_upds_nexp_ok_end}), integer by
@{thm [source] nexp_ok_eval}; an unwritten fluent keeps its (integer) pre-value. The functional side
condition comes from @{thm [source] upds_functional_start} / @{thm [source] upds_functional_end}.\<close>
lemma snap_num_update_preserves_num_val_ok:
  assumes a: "a \<in> set actions"
      and s: "s = at_start a \<or> s = at_end a"
      and ok: "num_val_ok w"
    shows "num_val_ok (num_plan.num_rat_impl.snap_num_update s w)"
proof -
  have func: "upds_functional ((set \<circ> upds) s)"
    using a s upds_functional_start upds_functional_end
    by (auto simp: upds_functional_set upds_functional_list_def)
  have rhs_ok: "nexp_ok w e" if "(f, e) \<in> set (upds s)" for f e
    using s a ok snap_upds_nexp_ok_start snap_upds_nexp_ok_end that by fastforce
  have "\<exists>r. num_plan.num_rat_impl.snap_num_update s w g = Some r \<and> r \<in> \<int>"
    if g: "g \<in> set nfluents" for g
  proof (cases "g \<in> fst ` set (upds s)")
    case True
    then obtain e where e: "(g, e) \<in> set (upds s)" by auto
    have "num_plan.num_rat_impl.snap_num_update s w g = eval_nexp w e"
      using func e by (simp add: num_plan.num_rat_impl.snap_num_update_writes)
    moreover obtain r where "eval_nexp w e = Some r" and "r \<in> \<int>"
      using nexp_ok_eval[OF rhs_ok[OF e]] by blast
    ultimately show ?thesis by simp
  next
    case False
    hence "g \<notin> num_plan.num_rat_impl.snap_writes s"
      by (simp add: num_plan.num_rat_impl.snap_writes_def)
    hence "num_plan.num_rat_impl.snap_num_update s w g = w g"
      by (rule num_plan.num_rat_impl.snap_num_update_unwritten)
    thus ?thesis using ok g by (auto simp: num_val_ok_def)
  qed
  thus ?thesis by (simp add: num_val_ok_def)
qed

text \<open>Folding a list of start/end snaps (a happening, presented as a list) preserves @{const num_val_ok}:
each fold step is a single @{const num_plan.num_rat_impl.snap_num_update} of one start/end snap, handled by
@{thm [source] snap_num_update_preserves_num_val_ok}; induct on the list, generalising the running
valuation.\<close>
lemma happening_num_update_preserves_num_val_ok:
  assumes "num_val_ok w"
      and "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
    shows "num_val_ok (num_plan.num_rat_impl.happening_num_update ys w)"
  using assms
proof (induction ys arbitrary: w)
  case Nil
  thus ?case using Nil.prems(1)
    by (simp add: num_plan.num_rat_impl.happening_num_update_Nil[unfolded comp_def])
next
  case (Cons y ys)
  obtain a where a: "a \<in> set actions"
    and ay: "y = at_start a \<or> y = at_end a"
    using Cons.prems(2) by auto
  have sok: "num_val_ok (num_plan.num_rat_impl.snap_num_update y w)"
    by (rule snap_num_update_preserves_num_val_ok[OF a ay Cons.prems(1)])
  have step: "num_val_ok (num_plan.num_rat_impl.happening_num_update ys
            (num_plan.num_rat_impl.snap_num_update y w))"
    by (rule Cons.IH[OF sok]) (use Cons.prems(2) in auto)
  show ?case
    by (subst num_plan.num_rat_impl.happening_num_update_Cons) (rule step)
qed

text \<open>The payload R1 fact: every right-hand side of a snap occurring in happening @{term i} is
@{const nexp_ok} over any @{const num_val_ok} valuation. By @{thm [source] happ_at_index_decomp} each
happening snap is @{term \<open>at_start (actions ! j)\<close>} or @{term \<open>at_end (actions ! j)\<close>} for some
@{term \<open>j < length actions\<close>} (so @{term \<open>actions ! j \<in> set actions\<close>}); the locale assumptions
@{thm [source] snap_upds_nexp_ok_start} / @{thm [source] snap_upds_nexp_ok_end} then give
@{const nexp_ok} of each update's right-hand side. Same case-split as
@{thm [source] happening_upds_functional}.\<close>
lemma happening_snap_nexp_ok:
  assumes mem: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and upd: "(f, e) \<in> set (upds s)"
      and ok: "num_val_ok w"
    shows "nexp_ok w e"
proof -
  have "s \<in> at_start ` { actions ! j | j. j < length actions
                            \<and> (is_starting_index (planning_sem.time_index i) j
                               \<or> is_instant_index (planning_sem.time_index i) j) }
          \<union> at_end ` { actions ! j | j. j < length actions
                          \<and> (is_ending_index (planning_sem.time_index i) j
                             \<or> is_instant_index (planning_sem.time_index i) j) }"
    using mem by (simp only: happ_at_index_decomp)
  then consider
      (starting) j where "j < length actions" and "s = at_start (actions ! j)"
    | (ending) j where "j < length actions" and "s = at_end (actions ! j)"
    by blast
  thus ?thesis
  proof cases
    case starting
    hence "actions ! j \<in> set actions" by simp
    thus ?thesis using snap_upds_nexp_ok_start ok upd starting by fastforce
  next
    case ending
    hence "actions ! j \<in> set actions" by simp
    thus ?thesis using snap_upds_nexp_ok_end ok upd ending by fastforce
  qed
qed

text \<open>A happening fold leaves a fluent untouched if no snap in the list writes it: each fold step is
a single @{const num_plan.num_rat_impl.snap_num_update} of an unwritten fluent, which is the identity on
that fluent by @{thm [source] num_plan.num_rat_impl.snap_num_update_unwritten}. Induct on the list,
generalising the running valuation. (The locale write set @{term \<open>num_plan.num_rat_impl.snap_writes s\<close>}
unfolds to @{term \<open>fst ` (set \<circ> upds) s\<close>}.)\<close>
lemma happening_num_update_unwritten:
  assumes "\<And>s. s \<in> set qs \<Longrightarrow> g \<notin> fst ` (set \<circ> upds) s"
  shows "num_plan.num_rat_impl.happening_num_update qs v g = v g"
  using assms
proof (induction qs arbitrary: v)
  case Nil
  show ?case
    by (simp add: num_plan.num_rat_impl.happening_num_update_Nil[unfolded comp_def])
next
  case (Cons q qs)
  have qw: "g \<notin> num_plan.num_rat_impl.snap_writes q"
    using Cons.prems[of q] by (simp add: num_plan.num_rat_impl.snap_writes_def)
  have step: "num_plan.num_rat_impl.happening_num_update qs
                (num_plan.num_rat_impl.snap_num_update q v) g
              = num_plan.num_rat_impl.snap_num_update q v g"
    by (rule Cons.IH) (use Cons.prems in auto)
  have "num_plan.num_rat_impl.snap_num_update q v g = v g"
    by (rule num_plan.num_rat_impl.snap_num_update_unwritten[OF qw])
  thus ?case
    using step by (subst num_plan.num_rat_impl.happening_num_update_Cons) simp
qed

text \<open>The running partial snap-fold over a @{emph \<open>prefix\<close>} @{term ys} of the @{term i}-th happening
stays within the declared fluent bounds. Both endpoints @{term \<open>snd (M i)\<close>} and @{term \<open>snd (M (Suc i))\<close>}
are in bounds (@{thm [source] num_seq_fluent_in_bounds}), and the full fold over the whole happening
@{term \<open>ys @ zs\<close>} equals the after-endpoint (@{thm [source] run_order_fold_eq_happening_num_update_set}).
For a declared fluent @{term g}: if no snap in @{term ys} writes it, the prefix fold leaves it at the
pre-endpoint value; if some @{term ys}-snap writes it, then -- since two snaps of one happening that
both write @{term g} would interfere (@{thm [source] happening_num_noninterfere} contradicted via the
write/write disjunct of @{const num_plan.num_rat_impl.num_mutex_snap_action}) -- no @{term zs}-snap
writes @{term g}, so the @{term zs}-tail of the full fold leaves it untouched, pinning the prefix value
to the after-endpoint value. Either way @{term g} lands in its declared bounds.\<close>
lemma running_prefix_in_bounds:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
      and dist: "distinct (ys @ zs)"
      and full: "set (ys @ zs) = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
    shows "fluent_in_bounds (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
proof -
  let ?w0 = "snd (M i)"
  let ?wpost = "snd (M (Suc i))"
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  have b0: "fluent_in_bounds ?w0"
    using i by (intro num_seq_fluent_in_bounds[OF vss m0]) simp
  have bpost: "fluent_in_bounds ?wpost"
    using i by (intro num_seq_fluent_in_bounds[OF vss m0]) simp
  have full_fold: "num_plan.num_rat_impl.happening_num_update (ys @ zs) ?w0 = ?wpost"
    by (rule run_order_fold_eq_happening_num_update_set[OF i vss dist full])
  have fold_app: "num_plan.num_rat_impl.happening_num_update (ys @ zs) v
                    = num_plan.num_rat_impl.happening_num_update zs
                        (num_plan.num_rat_impl.happening_num_update ys v)" for v
    unfolding num_plan.num_rat_impl.happening_num_update_def
    by (subst fold_append) (rule o_apply)
  have disj: "set ys \<inter> set zs = {}" using dist by auto
  have bound_g: "\<exists>r. num_plan.num_rat_impl.happening_num_update ys ?w0 g = Some r \<and> r \<in> \<int>
                   \<and> fluent_lo g \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi g"
    if g: "g \<in> set nfluents" for g
  proof (cases "\<exists>s \<in> set ys. g \<in> fst ` (set \<circ> upds) s")
    case False
    hence "num_plan.num_rat_impl.happening_num_update ys ?w0 g = ?w0 g"
      by (intro happening_num_update_unwritten) blast
    thus ?thesis using b0 g unfolding fluent_in_bounds_def by simp
  next
    case True
    then obtain s1 where s1: "s1 \<in> set ys" and g1: "g \<in> fst ` (set \<circ> upds) s1" by blast
    have unwr_zs: "g \<notin> fst ` (set \<circ> upds) s2" if s2: "s2 \<in> set zs" for s2
    proof
      assume g2: "g \<in> fst ` (set \<circ> upds) s2"
      have ne: "s1 \<noteq> s2" using s1 s2 disj by blast
      have m1: "s1 \<in> ?S" using s1 full by auto
      have m2: "s2 \<in> ?S" using s2 full by auto
      have "\<not> num_plan.num_rat_impl.num_mutex_snap_action s1 s2"
        by (rule happening_num_noninterfere[OF m1 m2 ne])
      moreover have "num_plan.num_rat_impl.num_mutex_snap_action s1 s2"
        using g1 g2 unfolding num_plan.num_rat_impl.num_mutex_snap_action_def
                              num_plan.num_rat_impl.snap_writes_def by blast
      ultimately show False by simp
    qed
    have "num_plan.num_rat_impl.happening_num_update zs
            (num_plan.num_rat_impl.happening_num_update ys ?w0) g
          = num_plan.num_rat_impl.happening_num_update ys ?w0 g"
      by (intro happening_num_update_unwritten) (rule unwr_zs)
    hence "num_plan.num_rat_impl.happening_num_update ys ?w0 g = ?wpost g"
      using full_fold by (simp add: fold_app)
    thus ?thesis using bpost g unfolding fluent_in_bounds_def by simp
  qed
  show ?thesis unfolding fluent_in_bounds_def using bound_g by blast
qed

text \<open>Per-snap numeric precondition satisfaction extracted from numeric-plan validity: along a valid
numeric state sequence, every snap @{term s} of the @{term i}-th happening has its numeric precondition
@{term \<open>n_pre s\<close>} satisfied at the pre-happening valuation @{term \<open>snd (M i)\<close>}. This is the precondition
conjunct of @{thm [source] num_plan.num_rat_impl.num_valid_state_sequence_def} (where @{term \<open>num_plan\<close>}'s
@{term n_pre} is @{term \<open>set \<circ> n_pre\<close>}, so the comparison set is @{term \<open>set (n_pre s)\<close>}); the happening
membership is bridged from the @{term rat_impl} form by @{thm [source] rat_impl_happ_at_eq}. Same
extraction shape as @{thm [source] run_order_fold_eq_happening_num_update_set} /
@{thm [source] happening_upds_functional}.\<close>
lemma happening_snap_pre_sat:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and i: "i < length planning_sem.htpl"
      and s: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
    shows "sat_comps (snd (M i)) (set (n_pre s))"
proof -
  have iH: "i < length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  have sH: "s \<in> planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)"
    using s by (simp add: rat_impl_happ_at_eq)
  have "\<forall>s \<in> planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i).
          sat_comps (snd (M i)) ((set \<circ> n_pre) s)"
    using vss iH unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def by blast
  thus ?thesis using sH by simp
qed

text \<open>Guard invariance under a @{emph \<open>partial\<close>} (prefix-list) happening fold -- the list-prefix twin of
@{thm [source] sat_comps_happening_num_update_set}. If @{term s} co-occurs in the @{term i}-th happening,
@{term ys} is a @{term s}-free subset of that happening, then folding @{term ys}'s numeric updates over
@{term \<open>snd (M i)\<close>} leaves @{term s}'s numeric precondition satisfaction unchanged: each @{term ys}-snap
@{term s'} is distinct from @{term s} and co-occurs, so does not numerically interfere
(@{thm [source] happening_num_noninterfere}), hence misses every fluent @{term s} reads; the precondition's
read fluents lie in @{term \<open>snap_reads s\<close>} (definitionally), so @{thm [source] happening_num_update_unwritten}
pins them. @{thm [source] sat_comps_cong} reduces to the per-read-fluent agreement. (The @{term rd}
read-containment is derived inline from @{thm [source] num_plan.num_rat_impl.snap_reads_def}, so it is not a
hypothesis.)\<close>
lemma sat_comps_running_prefix:
  assumes s: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and s_notin: "s \<notin> set ys"
    shows "sat_comps (num_plan.num_rat_impl.happening_num_update ys (snd (M i))) (set (n_pre s))
             = sat_comps (snd (M i)) (set (n_pre s))"
proof (rule sat_comps_cong)
  fix c f assume c: "c \<in> set (n_pre s)" and f: "f \<in> comp_fluents c"
  have fr: "f \<in> num_plan.num_rat_impl.snap_reads s"
    using c f unfolding num_plan.num_rat_impl.snap_reads_def by auto
  have unwr: "f \<notin> fst ` (set \<circ> upds) s'" if s': "s' \<in> set ys" for s'
  proof -
    have m': "s' \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      using s' ys_sub by blast
    have ne: "s' \<noteq> s" using s' s_notin by blast
    have "\<not> num_plan.num_rat_impl.num_mutex_snap_action s' s"
      by (rule happening_num_noninterfere[OF m' s ne])
    hence "num_plan.num_rat_impl.snap_writes s' \<inter> num_plan.num_rat_impl.snap_reads s = {}"
      unfolding num_plan.num_rat_impl.num_mutex_snap_action_def by blast
    hence "f \<notin> num_plan.num_rat_impl.snap_writes s'" using fr by blast
    thus ?thesis unfolding num_plan.num_rat_impl.snap_writes_def .
  qed
  show "num_plan.num_rat_impl.happening_num_update ys (snd (M i)) f = snd (M i) f"
    by (rule happening_num_update_unwritten) (rule unwr)
qed

lemma happening_num_update_inv_unchanged:
  assumes g: "g \<in> (\<Union>a \<in> set actions. \<Union>c \<in> set (n_inv a). comp_fluents c)"
      and ys: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
    shows "num_plan.num_rat_impl.happening_num_update ys w g = w g"
proof (rule happening_num_update_unwritten)
  fix s assume s: "s \<in> set ys"
  obtain b c where b: "b \<in> set actions" and c: "c \<in> set (n_inv b)" and gc: "g \<in> comp_fluents c"
    using g by blast
  have ginv_b: "g \<in> (\<Union>c \<in> set (n_inv b). comp_fluents c)" using c gc by blast
  obtain a where a: "a \<in> set actions" and sa: "s = at_start a \<or> s = at_end a"
    using ys[OF s] by blast
  have "(fst ` set (upds (at_start a)) \<union> fst ` set (upds (at_end a)))
          \<inter> (\<Union>c \<in> set (n_inv b). comp_fluents c) = {}"
    using n_inv_readonly a b by blast
  hence "g \<notin> fst ` set (upds (at_start a))" and "g \<notin> fst ` set (upds (at_end a))"
    using ginv_b by auto
  thus "g \<notin> fst ` (set \<circ> upds) s" using sa by (auto simp: comp_def)
qed

lemma num_seq_inv_const:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and i: "i \<le> length planning_sem.htpl"
      and g: "g \<in> (\<Union>a \<in> set actions. \<Union>c \<in> set (n_inv a). comp_fluents c)"
    shows "snd (M i) g = snd (M 0) g"
  using i
proof (induction i)
  case 0
  show ?case by simp
next
  case (Suc i')
  have i'H: "i' < length planning_sem.htpl" using Suc.prems by simp
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i')"
  obtain xs where dist: "distinct xs" and setxs: "set xs = ?S"
    using finite_distinct_list[OF happening_finite] by blast
  have fold_post: "num_plan.num_rat_impl.happening_num_update xs (snd (M i')) = snd (M (Suc i'))"
    by (rule run_order_fold_eq_happening_num_update_set[OF i'H vss dist setxs])
  have ys: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if s: "s \<in> set xs" for s
  proof -
    have "s \<in> at_start ` { actions ! j | j. j < length actions
              \<and> (is_starting_index (planning_sem.time_index i') j \<or> is_instant_index (planning_sem.time_index i') j) }
            \<union> at_end ` { actions ! j | j. j < length actions
              \<and> (is_ending_index (planning_sem.time_index i') j \<or> is_instant_index (planning_sem.time_index i') j) }"
      using s setxs by (simp only: happ_at_index_decomp)
    thus ?thesis by (auto simp: set_nthI)
  qed
  have "num_plan.num_rat_impl.happening_num_update xs (snd (M i')) g = snd (M i') g"
    by (rule happening_num_update_inv_unchanged[OF g ys])
  hence "snd (M (Suc i')) g = snd (M i') g" using fold_post by simp
  thus ?case using Suc.IH Suc.prems by simp
qed

lemma active_action_inv_sat:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and i: "i < length planning_sem.htpl"
      and a: "a \<in> num_plan.num_rat_impl.active_actions (rat_impl.time_index i)"
    shows "sat_comps (snd (M i)) (set (n_inv a))"
proof -
  have iH: "i < length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  have "\<forall>a \<in> num_plan.num_rat_impl.active_actions (rat_impl.time_index i).
          sat_comps (snd (M i)) ((set \<circ> n_inv) a)"
    using vss iH unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def by blast
  thus ?thesis using a by simp
qed

lemma num_inv_guard_sat_at:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and a: "a \<in> set actions"
      and aact: "a \<in> num_plan.num_rat_impl.active_actions (rat_impl.time_index i')"
      and i': "i' < length planning_sem.htpl"
      and wagree: "\<And>g. g \<in> (\<Union>c \<in> set (n_inv a). comp_fluents c) \<Longrightarrow> w g = snd (M i') g"
    shows "sat_comps w (set (n_inv a))"
proof -
  have sat: "sat_comps (snd (M i')) (set (n_inv a))"
    by (rule active_action_inv_sat[OF vss i' aact])
  have "sat_comps w (set (n_inv a)) = sat_comps (snd (M i')) (set (n_inv a))"
  proof (rule sat_comps_cong)
    fix c f assume c: "c \<in> set (n_inv a)" and f: "f \<in> comp_fluents c"
    have "f \<in> (\<Union>c \<in> set (n_inv a). comp_fluents c)" using c f by blast
    thus "w f = snd (M i') f" by (rule wagree)
  qed
  thus ?thesis using sat by simp
qed

text \<open>The bridge to the propositional structural invariant: the projection of a
@{const num_Lv_conds}-store to the propositional bounds domain satisfies @{const Lv_conds}. The
boundedness comes from @{thm [source] prop_proj_bounded}; @{const planning_lock} survives the
restriction because it is a propositional variable (@{thm [source] map_of_net_bounds_planning_lock}
puts it in @{term \<open>dom (map_of net_bounds)\<close>}); length / head location are about @{term L} directly.
This is what supplies the propositional @{const LvP} premise on the projection store when the numeric
run invokes the propositional @{thm [source] happening_steps_possible}.\<close>
lemma num_Lv_conds_imp_Lv_conds:
  assumes "num_Lv_conds L v"
  shows "Lv_conds L (v |` dom (map_of net_bounds))"
proof (rule Lv_condsI)
  show "length L = Suc (length actions)" by (rule num_Lv_conds_dests(1)[OF assms])
  show "L ! 0 = planning_loc" by (rule num_Lv_conds_dests(2)[OF assms])
  show "Simple_Network_Language.bounded (map_of net_bounds) (v |` dom (map_of net_bounds))"
    by (rule prop_proj_bounded[OF num_Lv_conds_dests(3)[OF assms]])
  have "planning_lock \<in> dom (map_of net_bounds)" using map_of_net_bounds_planning_lock by blast
  hence "(v |` dom (map_of net_bounds)) planning_lock = v planning_lock" by (simp add: restrict_in)
  thus "(v |` dom (map_of net_bounds)) planning_lock = Some 1"
    using num_Lv_conds_dests(4)[OF assms] by simp
qed

lemma num_LvP_imp_LvP:
  assumes "num_LvP (L, v, c)"
  shows "LvP (L, v |` dom (map_of net_bounds), c)"
  using assms num_Lv_conds_imp_Lv_conds by simp

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

text \<open>Every edge of @{const net_automata} carries a @{const Sil} action (all edge definitions ---
@{const main_auto_init_edge} / @{const main_auto_goal_edge} / @{const main_auto_loop} on the main
automaton and @{const start_edge} / @{const edge_2} / @{const edge_3} / @{const end_edge} /
@{const instant_trans_edge} on the action automata --- are @{term \<open>Sil (STR '''')\<close>}), so no @{const In}
or @{const Out} synchronisation edge exists anywhere in the propositional net.\<close>
lemma net_automata_no_in:
  assumes "p < length net_automata"
  shows "(l, b, g, In aa, f, r, l') \<notin> trans (automaton_of (net_automata ! p))"
proof (cases p)
  case 0
  show ?thesis unfolding 0 main_auto_trans
    unfolding main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def Let_def by simp
next
  case (Suc n)
  have nlt: "n < length actions" using assms unfolding Suc length_net_automata by simp
  show ?thesis unfolding Suc nth_auto_trans[OF nlt]
    unfolding start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def Let_def by simp
qed

lemma net_automata_no_out:
  assumes "p < length net_automata"
  shows "(l, b, g, Out aa, f, r, l') \<notin> trans (automaton_of (net_automata ! p))"
proof (cases p)
  case 0
  show ?thesis unfolding 0 main_auto_trans
    unfolding main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def Let_def by simp
next
  case (Suc n)
  have nlt: "n < length actions" using assms unfolding Suc length_net_automata by simp
  show ?thesis unfolding Suc nth_auto_trans[OF nlt]
    unfolding start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def Let_def by simp
qed

text \<open>The same on the @{emph \<open>conv\<close>}-elaborated automata that @{const net_impl.sem} actually steps over:
@{const conv_automaton} only rewrites the clock guard (@{thm [source] conv_trans}), so it preserves the
@{const In}/@{const Out} action labels and hence introduces no synchronisation edge either.\<close>
lemma conv_net_no_in:
  assumes "p < length net_automata"
  shows "(l, b, g, In aa, f, r, l') \<notin> trans (automaton_of (conv_automaton (net_automata ! p)))"
proof -
  have plen: "p < length (map (automaton_of \<circ> conv_automaton) net_automata)" using assms by simp
  have rw: "automaton_of (conv_automaton (net_automata ! p)) = map (automaton_of \<circ> conv_automaton) net_automata ! p"
    using assms by (simp add: comp_def)
  show ?thesis unfolding rw conv_trans[OF plen] using net_automata_no_in[OF assms] by auto
qed

lemma conv_net_no_out:
  assumes "p < length net_automata"
  shows "(l, b, g, Out aa, f, r, l') \<notin> trans (automaton_of (conv_automaton (net_automata ! p)))"
proof -
  have plen: "p < length (map (automaton_of \<circ> conv_automaton) net_automata)" using assms by simp
  have rw: "automaton_of (conv_automaton (net_automata ! p)) = map (automaton_of \<circ> conv_automaton) net_automata ! p"
    using assms by (simp add: comp_def)
  show ?thesis unfolding rw conv_trans[OF plen] using net_automata_no_out[OF assms] by auto
qed

text \<open>A non-@{const Del} step of @{const net_impl.sem} is necessarily an @{const Internal} step: the
empty broadcast set (@{thm [source] net_broadcast_def}) rules out a @{const Broad} step, and the
absence of any @{const In}/@{const Out} edge (@{thm [source] conv_net_no_in} /
@{thm [source] conv_net_no_out}) rules out a @{const Bin} step.\<close>
lemma prop_non_del_step_internal:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', v', c'\<rangle>"
      and aD: "a \<noteq> Simple_Network_Language.label.Del"
      and L_len: "length L = length net_automata"
  shows "\<exists>aa. a = Internal aa"
proof (cases a)
  case Del
  then show ?thesis using aD by simp
next
  case (Internal aa)
  then show ?thesis by blast
next
  case (Bin aa)
  have F: False
    apply (rule step_u_elims'(3)[OF step[unfolded Bin net_impl.sem_def]])
    unfolding TAG_def
    using L_len by (auto dest: conv_net_no_in)
  then show ?thesis by simp
next
  case (Broad aa)
  have F: False
    apply (rule step_u_elims'(4)[OF step[unfolded Broad net_impl.sem_def]])
    unfolding TAG_def
    using net_broadcast_def by simp
  then show ?thesis by simp
qed

lemma num_step'_lift:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L', v', c'\<rangle>"
      and L_len: "length L = length net_automata"
      and bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
      and num_data:
        "\<And>a p l b g f r l'.
           p < length net_automata \<Longrightarrow>
           (l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p)) \<Longrightarrow>
           L ! p = l \<Longrightarrow> check_bexp v b True \<Longrightarrow> is_upds v f v' \<Longrightarrow>
           \<exists>bg fu vn'.
              (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
              \<and> check_bexp vn bg True
              \<and> is_upds vn fu vn'
              \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
              \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w'"
  shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>
               \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w' \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
proof -
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "a \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', v', c'\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where
      Lieq: "Li = L"
    and vieq: "vi = v"
    and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', v', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain aa where aInt: "a = Internal aa"
    using prop_non_del_step_internal[OF actI aD L_len] by blast
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have nd: "\<exists>bg fu vn'.
              (l, bg, g, Sil aa, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
              \<and> check_bexp vn bg True
              \<and> is_upds vn fu vn'
              \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
              \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w'"
    if "p < length net_automata"
       "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
       "L ! p = l" "check_bexp v b True" "is_upds v f v'"
    for p l b g f r l'
    using num_data that by blast
  have ex: "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal aa\<^esub> \<langle>L', vn', c'\<rangle>
                 \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w' \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    apply (rule num_int_step_lift[OF actI[unfolded aInt] L_len])
    using nd by blast
  obtain vn' where
      numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal aa\<^esub> \<langle>L', vn', c'\<rangle>"
    and le': "v' \<subseteq>\<^sub>m vn'"
    and tr': "num_tracks vn' w'"
    and bnd': "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    using ex by blast
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using le' tr' bnd' by blast
qed

definition run_order_snaps :: "nat \<Rightarrow> 'snap_action list" where
"run_order_snaps i \<equiv>
  (let t = planning_sem.time_index i; acts = [0..<length actions];
       start_indices = filter (is_starting_index t) acts;
       end_indices   = filter (is_ending_index t) acts;
       both          = filter (is_instant_index t) acts
   in concat (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) both)
      @ map (\<lambda>n. at_start (actions!n)) start_indices
      @ map (\<lambda>n. at_end (actions!n)) end_indices)"

lemma set_run_order_snaps:
  "set (run_order_snaps i) = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
proof -
  let ?t = "planning_sem.time_index i"
  have setS: "set (filter (is_starting_index ?t) [0..<length actions])
                = {j. j < length actions \<and> is_starting_index ?t j}"
    by (simp add: set_filter)
  have setE: "set (filter (is_ending_index ?t) [0..<length actions])
                = {j. j < length actions \<and> is_ending_index ?t j}"
    by (simp add: set_filter)
  have setB: "set (filter (is_instant_index ?t) [0..<length actions])
                = {j. j < length actions \<and> is_instant_index ?t j}"
    by (simp add: set_filter)
  show ?thesis
    unfolding run_order_snaps_def Let_def happ_at_index_decomp
    apply (simp only: set_append set_concat set_map setS setE setB)
    by auto
qed

lemma distinct_run_order_snaps:
  "distinct (run_order_snaps i)"
proof -
  let ?t = "planning_sem.time_index i"
  define SI where "SI = filter (is_instant_index ?t) [0..<length actions]"
  define SS where "SS = filter (is_starting_index ?t) [0..<length actions]"
  define SE where "SE = filter (is_ending_index ?t) [0..<length actions]"
  \<comment> \<open>Membership in each index list: the index is below @{term \<open>length actions\<close>} and has the case.\<close>
  have memSI: "n < length actions" "is_instant_index ?t n" if "n \<in> set SI" for n
    using that unfolding SI_def by auto
  have memSS: "n < length actions" "is_starting_index ?t n" if "n \<in> set SS" for n
    using that unfolding SS_def by auto
  have memSE: "n < length actions" "is_ending_index ?t n" if "n \<in> set SE" for n
    using that unfolding SE_def by auto
  \<comment> \<open>Each index list is distinct (a filter of the distinct @{term \<open>[0..<length actions]\<close>}).\<close>
  have distSI: "distinct SI" unfolding SI_def by simp
  have distSS: "distinct SS" unfolding SS_def by simp
  have distSE: "distinct SE" unfolding SE_def by simp
  \<comment> \<open>The three index-cases are mutually exclusive at a fixed time-point.\<close>
  have excl_IS: "\<not> is_starting_index ?t n" if "is_instant_index ?t n" for n
    using that by (simp add: index_case_defs planning_sem.is_instant_action_def
                              planning_sem.is_starting_action_def)
  have excl_IE: "\<not> is_ending_index ?t n" if "is_instant_index ?t n" for n
    using that by (simp add: index_case_defs planning_sem.is_instant_action_def
                              planning_sem.is_ending_action_def)
  have excl_SE: "\<not> is_ending_index ?t n" if "is_starting_index ?t n" for n
    using that by (simp add: index_case_defs planning_sem.is_starting_action_def
                              planning_sem.is_ending_action_def)
  \<comment> \<open>Hence the index lists are pairwise disjoint as sets.\<close>
  have disj_SI_SS: "set SI \<inter> set SS = {}"
    using memSI(2) memSS(2) excl_IS by blast
  have disj_SI_SE: "set SI \<inter> set SE = {}"
    using memSI(2) memSE(2) excl_IE by blast
  have disj_SS_SE: "set SS \<inter> set SE = {}"
    using memSS(2) memSE(2) excl_SE by blast
  \<comment> \<open>Snap-distinctness within and across the index lists.\<close>
  have ne_se: "at_start (actions ! n) \<noteq> at_end (actions ! m)"
    if "n < length actions" "m < length actions" for n m
    using nth_start_end_disj[OF set_nthI[OF that(2)] that(1)] .
  have ne_es: "at_end (actions ! n) \<noteq> at_start (actions ! m)"
    if "n < length actions" "m < length actions" for n m
    using nth_end_start_disj[OF set_nthI[OF that(2)] that(1)] .
  \<comment> \<open>The three component lists.\<close>
  let ?A = "concat (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
  let ?B = "map (\<lambda>n. at_start (actions!n)) SS"
  let ?C = "map (\<lambda>n. at_end (actions!n)) SE"
  \<comment> \<open>@{term ?A} is distinct: distinct outer index list, each 2-element block distinct
     (start \<noteq> end), and distinct blocks are disjoint (action-injectivity + start/end-disjointness).\<close>
  have dA: "distinct ?A"
  proof (rule distinct_concat)
    have inj_SI: "x = y"
      if "x \<in> set SI" "y \<in> set SI"
         "[at_start (actions!x), at_end (actions!x)] = [at_start (actions!y), at_end (actions!y)]"
      for x y
      using that nth_starts_unique[OF memSI(1)[OF that(1)] memSI(1)[OF that(2)]] by force
    show "distinct (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
      unfolding distinct_map using distSI by (auto intro!: inj_onI simp: inj_SI)
  next
    fix ys
    assume "ys \<in> set (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
    then obtain n where n: "n \<in> set SI" "ys = [at_start (actions!n), at_end (actions!n)]" by auto
    show "distinct ys" using n ne_se[OF memSI(1)[OF n(1)] memSI(1)[OF n(1)]] by auto
  next
    fix ys zs
    assume "ys \<in> set (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
       and "zs \<in> set (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
       and yz: "ys \<noteq> zs"
    then obtain n m where
        nm: "n \<in> set SI"
            "m \<in> set SI"
            "ys = [at_start (actions!n), at_end (actions!n)]"
            "zs = [at_start (actions!m), at_end (actions!m)]"
      by auto
    have "n \<noteq> m" using nm yz by auto
    hence "actions ! n \<noteq> actions ! m"
      using nth_actions_unique[OF memSI(1)[OF nm(1)] memSI(1)[OF nm(2)]] by blast
    thus "set ys \<inter> set zs = {}"
      using nm memSI(1)[OF nm(1)] memSI(1)[OF nm(2)]
            nth_starts_unique nth_ends_unique ne_se ne_es by auto
  qed
  have dB: "distinct ?B"
  proof -
    have "x = y" if "x \<in> set SS" "y \<in> set SS" "at_start (actions!x) = at_start (actions!y)" for x y
      using that nth_starts_unique[OF memSS(1)[OF that(1)] memSS(1)[OF that(2)]] by force
    thus ?thesis unfolding distinct_map using distSS by (auto intro!: inj_onI)
  qed
  have dC: "distinct ?C"
  proof -
    have "x = y" if "x \<in> set SE" "y \<in> set SE" "at_end (actions!x) = at_end (actions!y)" for x y
      using that nth_ends_unique[OF memSE(1)[OF that(1)] memSE(1)[OF that(2)]] by force
    thus ?thesis unfolding distinct_map using distSE by (auto intro!: inj_onI)
  qed
  \<comment> \<open>@{term ?A} disjoint from @{term ?B}: a @{term at_start} from @{term SI} vs @{term SS}
     differs by action-injectivity (disjoint index sets); an @{term at_end} vs @{term at_start}
     by start/end-disjointness.\<close>
  have dAB: "set ?A \<inter> set ?B = {}"
  proof -
    have "x \<noteq> y" if "x \<in> set ?A" "y \<in> set ?B" for x y
    proof -
      from that(2) obtain m where m: "m \<in> set SS" "y = at_start (actions!m)" by auto
      from that(1) obtain n where
          n: "n \<in> set SI" "x = at_start (actions!n) \<or> x = at_end (actions!n)" by auto
      have nm: "n \<noteq> m" using n(1) m(1) disj_SI_SS by blast
      have nlen: "n < length actions" using memSI(1)[OF n(1)] .
      have mlen: "m < length actions" using memSS(1)[OF m(1)] .
      show ?thesis using n(2)
      proof
        assume "x = at_start (actions!n)"
        thus ?thesis using m(2) nm nth_starts_unique[OF nlen mlen] by simp
      next
        assume "x = at_end (actions!n)"
        thus ?thesis using m(2) ne_es[OF nlen mlen] by simp
      qed
    qed
    thus ?thesis by blast
  qed
  \<comment> \<open>@{term ?A} disjoint from @{term ?C}: an @{term at_start} vs @{term at_end} by start/end-disjointness;
     an @{term at_end} from @{term SI} vs @{term SE} by action-injectivity (disjoint index sets).\<close>
  have dAC: "set ?A \<inter> set ?C = {}"
  proof -
    have "x \<noteq> y" if "x \<in> set ?A" "y \<in> set ?C" for x y
    proof -
      from that(2) obtain m where m: "m \<in> set SE" "y = at_end (actions!m)" by auto
      from that(1) obtain n where
          n: "n \<in> set SI" "x = at_start (actions!n) \<or> x = at_end (actions!n)" by auto
      have nm: "n \<noteq> m" using n(1) m(1) disj_SI_SE by blast
      have nlen: "n < length actions" using memSI(1)[OF n(1)] .
      have mlen: "m < length actions" using memSE(1)[OF m(1)] .
      show ?thesis using n(2)
      proof
        assume "x = at_start (actions!n)"
        thus ?thesis using m(2) ne_se[OF nlen mlen] by simp
      next
        assume "x = at_end (actions!n)"
        thus ?thesis using m(2) nm nth_ends_unique[OF nlen mlen] by simp
      qed
    qed
    thus ?thesis by blast
  qed
  \<comment> \<open>@{term ?B} disjoint from @{term ?C}: an @{term at_start} vs @{term at_end}, by start/end-disjointness.\<close>
  have dBC: "set ?B \<inter> set ?C = {}"
  proof -
    have "x \<noteq> y" if "x \<in> set ?B" "y \<in> set ?C" for x y
    proof -
      from that(1) obtain n where n: "n \<in> set SS" "x = at_start (actions!n)" by auto
      from that(2) obtain m where m: "m \<in> set SE" "y = at_end (actions!m)" by auto
      show ?thesis using n m ne_se[OF memSS(1)[OF n(1)] memSE(1)[OF m(1)]] by auto
    qed
    thus ?thesis by blast
  qed
  have "distinct (?A @ ?B @ ?C)"
    using dA dB dC dAB dAC dBC by (simp add: Int_Un_distrib)
  thus ?thesis
    unfolding run_order_snaps_def Let_def SI_def SS_def SE_def .
qed

text \<open>The numeric graph satisfies the @{locale sequence_rules} composition laws (the numeric mirror of
the propositional \<open>steps_seq\<close> interpretation, proved identically: @{const num_graph_impl.steps} is a
@{locale Graph_Defs} step relation, so its singleton intro and the \<open>num_steps_extend\<close> splice
discharge @{text base}/@{text step}). This is the structural combinator the numeric run-lifting
reuses to walk the @{const delay_and_apply} phase decomposition.\<close>
lemma num_steps_extend:
  "num_graph_impl.steps xs
  \<Longrightarrow> num_graph_impl.steps (last xs # ys)
  \<Longrightarrow> num_graph_impl.steps (xs @ ys)"
  by (rule num_graph_impl.steps_append'[where as = xs and bs = "last xs # ys"]) simp+

sublocale num_steps_seq: sequence_rules num_graph_impl.steps
  apply standard
  using num_graph_impl.steps.intros(1) num_steps_extend .

subsection \<open>Numeric per-phase run-lift: the \<open>edge_3\<close> (ending-duration) phase\<close>

text \<open>The relational invariant carried by the numeric run-lift: the numeric (combined) store
@{term vn} EXTENDS the propositional store @{term vp} (so the propositional run's facts transfer
verbatim by @{thm [source] check_bexp_is_val_mono} / @{thm [source] is_upds_map_le}), it TRACKS the
abstract numeric valuation @{term w} (@{const num_tracks}), and it is @{const num_net_bounds}-bounded.
The locations and clocks are shared (both runs fire the same @{const edge_3} edge), so they are not
part of \<open>REL\<close>; they coincide config-for-config.\<close>
definition REL where
"REL vp vn w \<longleftrightarrow> vp \<subseteq>\<^sub>m vn \<and> num_tracks vn w \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn"

lemma RELI:
  assumes "vp \<subseteq>\<^sub>m vn"
    and "num_tracks vn w"
    and "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
  shows "REL vp vn w"
  using assms unfolding REL_def by blast

lemma REL_leD: "REL vp vn w \<Longrightarrow> vp \<subseteq>\<^sub>m vn"
  and REL_trD: "REL vp vn w \<Longrightarrow> num_tracks vn w"
  and REL_bndD: "REL vp vn w \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn"
  unfolding REL_def by blast+

text \<open>Re-establishing the @{const num_net_bounds} bound on the numeric post-store of a no-fluent-write
edge: the numeric store @{term vn'} extends the propositional post-store @{term vp'} (so on the
propositional variables it equals @{term vp'}, which the propositional run keeps
@{const net_bounds}-bounded), it tracks @{term w} (so the fluent variables are in their fluent bounds
because @{term w} is @{const fluent_in_bounds}), and these two halves cover @{const num_net_bounds}.\<close>
lemma REL_bnd_from_proj:
  assumes le: "vp' \<subseteq>\<^sub>m vn'"
      and vp'_dom: "dom vp' = dom (map_of net_bounds)"
      and pbnd: "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and tr: "num_tracks vn' w"
      and fin: "fluent_in_bounds w"
      and vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    shows "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
proof (rule num_tracks_bounded[OF vn'_dom _ tr fin])
  have "(vn' |` dom (map_of net_bounds)) = vp'"
  proof (rule ext)
    fix x
    show "(vn' |` dom (map_of net_bounds)) x = vp' x"
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      hence "x \<in> dom vp'" using vp'_dom by simp
      then obtain y where y: "vp' x = Some y" by auto
      have "vn' x = Some y" using le y unfolding map_le_def by (metis domI)
      thus ?thesis using True y by (simp add: restrict_in)
    next
      case False
      hence "x \<notin> dom vp'" using vp'_dom by simp
      thus ?thesis using False by (simp add: restrict_map_def domIff)
    qed
  qed
  thus "Simple_Network_Language.bounded (map_of net_bounds) (vn' |` dom (map_of net_bounds))"
    using pbnd by simp
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const edge_3} VERBATIM (third in
the edge list of @{const num_action_to_automaton}), so the numeric net contains the same
@{const edge_3} transition as the propositional net.\<close>
lemma num_nth_auto_edge_3:
  assumes n: "n < length actions"
  shows "edge_3 (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const num_start_edge} (first in the
edge list of @{const num_action_to_automaton}) and @{const num_end_edge} (fourth), so the numeric net
contains the AUGMENTED start/end transitions.\<close>
lemma num_nth_auto_num_start_edge:
  assumes n: "n < length actions"
  shows "num_start_edge (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

lemma num_nth_auto_num_end_edge:
  assumes n: "n < length actions"
  shows "num_end_edge (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const num_edge_2} (second in the
edge list of @{const num_action_to_automaton}), so the numeric net contains the AUGMENTED running-entry
edge -- @{const edge_2} with the numeric @{const num_inv_guard} conjoined (and no extra update).\<close>
lemma num_nth_auto_num_edge_2:
  assumes n: "n < length actions"
  shows "num_edge_2 (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>Among the five edges of an action automaton only @{const edge_3} leaves the @{const running_loc}
location (start: @{const off_loc}, edge_2: @{const starting_loc}, end: @{const ending_loc}, instant:
@{const starting_loc}). So a propositional internal step from a config whose @{term \<open>Suc n\<close>}-th location
is @{const running_loc} must have fired @{const edge_3} at automaton @{term \<open>Suc n\<close>}: the source
location pins the fired edge.\<close>
lemma prop_edge_3_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and run: "L ! Suc n = running_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = edge_3 (actions ! n)"
proof -
  have l_run: "l = running_loc" using Lp run pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_run
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel: lifting ONE propositional @{const edge_3} step (the no-fluent-write
ending-duration edge) to a numeric @{const num_graph_impl.steps} step, preserving @{const REL}. The
propositional step is GIVEN (extracted from the propositional happening run); the numeric guard and
update fire on the extended store @{term vn} by monotonicity, tracking survives because @{const edge_3}
writes only the propositional @{const prop_to_lock} variables (fresh of the fluent variables), and the
@{const num_net_bounds} bound is re-established from the propositional post-bound (@{thm [source]
REL_bnd_from_proj}). The locations and clocks are those of the propositional step.\<close>
lemma num_edge_3_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and run: "L ! Suc n = running_loc"
      and n: "n < length actions"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (edge_3_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and fin: "fluent_in_bounds w"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle> \<and> REL vp' vn' w"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have L'_eq: "L' = L[Suc n := ending_loc]"
    using L'eq by (simp add: edge_3_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const edge_3}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}.\<close>
  have running_ne_ending: "running_loc \<noteq> ending_loc" by (simp add: locations_unique)
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    moreover have "L[Suc n := ending_loc] ! Suc n = ending_loc" using Sn_lt by simp
    ultimately show False using L'eq2 L'_eq run running_ne_ending by simp
  qed
  have edge3: "(l, b, g, Sil a, f, r, l') = edge_3 (actions ! n)"
    by (rule prop_edge_3_pinned[OF P E LOC run n pSuc])
  \<comment> \<open>The fired edge's components, read off @{const edge_3}.\<close>
  note edge_parts = edge3[unfolded edge_3_def Let_def, simplified prod.inject]
  \<comment> \<open>The numeric edge: @{const edge_3} verbatim, with the same guard and update.\<close>
  have NE: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc edge3 by (rule num_nth_auto_edge_3[OF n])
  \<comment> \<open>The numeric guard fires on the extended store; the update fires, preserving tracking.\<close>
  have NB: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  obtain vn' where
      NU: "is_upds vn f vn'"
    and LE: "vp' \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn' x = vn x"
    using is_upds_map_le[OF U le] by blast
  \<comment> \<open>@{const edge_3} writes only @{const prop_to_lock} variables, fresh of the fluents, so tracking
     survives.\<close>
  have f_eq: "f = map (inc_prop_lock_ab (- 1)) (over_all (actions ! n))"
    using edge3 by (simp add: edge_3_def Let_def)
  have fst_f: "fst ` set f = prop_to_lock ` set (over_all (actions ! n))"
    unfolding f_eq set_map image_image inc_prop_lock_ab_def by (simp add: comp_def)
  have aMem: "actions ! n \<in> set actions" using n by simp
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
  proof
    assume "fluent_to_var h \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and ph: "fluent_to_var h = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus False using ph fluent_var_notin_net_bounds[OF h] by simp
  qed
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound from the propositional post-bound and tracking.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  have fset_sub: "fst ` set f \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and xp: "x = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus "x \<in> dom vn" using xp dom_vn dom_map_of_num_net_bounds by auto
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
  proof -
    have "dom vn' = dom vn"
    proof (rule set_eqI)
      fix x
      show "x \<in> dom vn' \<longleftrightarrow> x \<in> dom vn"
      proof (cases "x \<in> fst ` set f")
        case True
        have "x \<in> dom vn" using True fset_sub by blast
        moreover have "x \<in> dom vn'"
          using NU True
        proof (induction f arbitrary: vn)
          case (Cons fe f)
          obtain y e where fe: "fe = (y, e)" by (cases fe)
          obtain v1 where v1: "is_upd vn (y, e) v1" and rest: "is_upds v1 f vn'"
            using Cons.prems(1) fe by (auto simp: is_upds_Cons_iff)
          obtain kk where v1_eq: "v1 = vn(y \<mapsto> kk)" using v1 by (auto simp: is_upd_def)
          show ?case
          proof (cases "x \<in> fst ` set f")
            case True
            show ?thesis using Cons.IH[OF rest True] .
          next
            case False
            hence xy: "x = y" using Cons.prems(2) fe by auto
            have "vn' x = v1 x" using is_upds_unchanged[OF rest] False by blast
            also have "\<dots> = Some kk" using v1_eq xy by simp
            finally show ?thesis by blast
          qed
        qed simp
        ultimately show ?thesis by blast
      next
        case False
        thus ?thesis using OFF[OF False] by (auto simp: domIff)
      qed
    qed
    thus ?thesis using dom_vn by simp
  qed
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TR fin vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TR BND by (auto intro: RELI)
qed

text \<open>A Munta update sequence whose written variables are all already in the store's domain leaves the
domain unchanged: each @{const is_upd} is a point override @{term \<open>v(x \<mapsto> k)\<close>}, which only adds @{term x}
to the domain, and here @{term x} is already present. This is the upper half of the domain-preservation
argument the run-lift needs when re-establishing the @{const num_net_bounds} bound on the numeric
post-store (the lower half is @{const num_tracks} / the propositional projection).\<close>
lemma is_upds_dom_eq:
  assumes "is_upds v us v'"
      and "fst ` set us \<subseteq> dom v"
    shows "dom v' = dom v"
  using assms
proof (induction us arbitrary: v)
  case Nil
  thus ?case by (auto elim: is_upds.cases)
next
  case (Cons u us)
  obtain x e where u: "u = (x, e)" by (cases u)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 us v'"
    using Cons.prems(1) u by (auto simp: is_upds_Cons_iff)
  obtain k where v1_eq: "v1 = v(x \<mapsto> k)" using v1 by (auto simp: is_upd_def)
  have xdom: "x \<in> dom v" using Cons.prems(2) u by simp
  have dom_v1: "dom v1 = dom v" using v1_eq xdom by auto
  have "fst ` set us \<subseteq> dom v1" using Cons.prems(2) dom_v1 by auto
  thus ?case using Cons.IH[OF rest] dom_v1 by simp
qed

text \<open>A Munta update sequence only ever grows the store's domain: each @{const is_upd} point-overrides
its variable, which can add a binding but never deletes one.\<close>
lemma is_upds_dom_mono:
  assumes "is_upds v us v'"
  shows "dom v \<subseteq> dom v'"
  using assms
proof (induction us arbitrary: v)
  case Nil
  thus ?case by (auto elim: is_upds.cases)
next
  case (Cons u us)
  obtain x e where u: "u = (x, e)" by (cases u)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 us v'"
    using Cons.prems u by (auto simp: is_upds_Cons_iff)
  obtain k where v1_eq: "v1 = v(x \<mapsto> k)" using v1 by (auto simp: is_upd_def)
  have "dom v \<subseteq> dom v1" using v1_eq by auto
  thus ?case using Cons.IH[OF rest] by blast
qed

text \<open>Every variable a Munta update sequence writes ends up in the domain of the resulting store:
each @{const is_upd} point-overrides its variable to a defined value, and later updates never delete
it (@{thm [source] is_upds_dom_mono}). Used to place the written propositional/fluent variables inside
the numeric store's domain.\<close>
lemma is_upds_writes_dom:
  assumes "is_upds v us v'"
  shows "fst ` set us \<subseteq> dom v'"
  using assms
proof (induction us arbitrary: v)
  case Nil
  thus ?case by simp
next
  case (Cons u us)
  obtain x e where u: "u = (x, e)" by (cases u)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 us v'"
    using Cons.prems u by (auto simp: is_upds_Cons_iff)
  obtain k where v1_eq: "v1 = v(x \<mapsto> k)" using v1 by (auto simp: is_upd_def)
  have "x \<in> dom v1" using v1_eq by auto
  hence "x \<in> dom v'" using is_upds_dom_mono[OF rest] by blast
  thus ?case using Cons.IH[OF rest] u by auto
qed

text \<open>The @{const off_loc} source location pins the fired edge to @{const start_edge}: among the five
edges of an action automaton only @{const start_edge} leaves @{const off_loc} (edge_2: @{const
starting_loc}, edge_3: @{const running_loc}, end: @{const ending_loc}, instant: @{const starting_loc}).
So a propositional internal step from a config whose @{term \<open>Suc n\<close>}-th location is @{const off_loc} must
have fired @{const start_edge} at automaton @{term \<open>Suc n\<close>}.\<close>
lemma prop_start_edge_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and off: "L ! Suc n = off_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = start_edge (actions ! n)"
proof -
  have l_off: "l = off_loc" using Lp off pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_off
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel for a fluent-WRITING happening edge: lifting ONE propositional
@{const start_edge} step (the @{text at_start} snap of @{term \<open>actions ! n\<close>}) to a numeric
@{const num_graph_impl.steps} step whose numeric edge is the AUGMENTED @{const num_start_edge}, carrying
the numeric guard @{const num_pre_guard} and the appended numeric update @{const num_upd}. Unlike
@{thm [source] num_edge_3_step_lift} this CHANGES the abstract valuation: the numeric post-store tracks
@{term \<open>num_plan.num_rat_impl.snap_num_update s w = apply_upds (set (upds s)) w\<close>}. The numeric guard
holds by @{thm [source] check_bexp_comps_guard} (the snap's @{term n_pre} comparisons are satisfied at
@{term w} and faithful), the numeric update fires by @{thm [source] is_upds_num_upd} landing on
@{const apply_upds}, the two update phases compose by @{thm [source] is_upds_appendI}, and the
@{const num_net_bounds} bound on the post-store is re-established from the propositional post-bound and
the post-fold being @{const fluent_in_bounds} (@{thm [source] REL_bnd_from_proj}). Edge-pinning is by
@{thm [source] prop_start_edge_pinned} (source location @{const off_loc}).\<close>
lemma num_edge_upd_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and off: "L ! Suc n = off_loc"
      and n: "n < length actions"
      and s_eq: "s = at_start (actions ! n)"
      and mem: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (start_edge_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and wok: "num_val_ok w"
      and fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update s w)"
      and sat: "sat_comps w (set (n_pre s))"
      and upd_lhs: "fst ` set (upds s) \<subseteq> set nfluents"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>
                 \<and> REL vp' vn' (num_plan.num_rat_impl.snap_num_update s w)"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have aMem: "actions ! n \<in> set actions" using n by simp
  let ?us = "upds s"
  let ?fn = "num_upd s"
  have fn_eq: "?fn = map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) ?us"
    by (simp add: num_upd_def)
  have w'_eq: "num_plan.num_rat_impl.snap_num_update s w = apply_upds (set ?us) w"
    by (simp add: num_plan.num_rat_impl.snap_num_update_def)
  \<comment> \<open>The numeric post-fold bound, restated in @{const apply_upds} form for @{thm [source] is_upds_num_upd}.\<close>
  have fin': "fluent_in_bounds (apply_upds (set ?us) w)" using fin w'_eq by simp
  \<comment> \<open>The contract facts for the @{text at_start} snap, instantiated at @{term w}.\<close>
  have us_func: "upds_functional_list ?us"
    using upds_functional_start aMem s_eq by blast
  have us_ncr: "upds_no_cross_read_list ?us"
    using upds_no_cross_read_start aMem s_eq by blast
  have us_ok: "fl \<in> set nfluents \<and> nexp_ok w e" if "(fl, e) \<in> set ?us" for fl e
  proof -
    have "nexp_ok w e" using happening_snap_nexp_ok[OF mem _ wok] that by blast
    moreover have "fl \<in> set nfluents" using upd_lhs that by blast
    ultimately show ?thesis by blast
  qed
  have pre_ok: "\<forall>cc \<in> set (n_pre s). comp_ok w cc"
    using snap_pre_comp_ok_start aMem s_eq wok by blast
  \<comment> \<open>The numeric pre-guard holds on the extended store.\<close>
  have guard_ok: "check_bexp vn (num_pre_guard s) True"
    unfolding num_pre_guard_def by (rule check_bexp_comps_guard[OF tr pre_ok sat])
  have L'_eq: "L' = L[Suc n := starting_loc]"
    using L'eq by (simp add: start_edge_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const start_edge}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}, which goes to
     @{const starting_loc} \<noteq> @{const off_loc}.\<close>
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    hence "L' ! Suc n = off_loc" using L'eq2 off by simp
    moreover have "L' ! Suc n = starting_loc" using L'_eq Sn_lt by simp
    ultimately show False by (simp add: locations_unique)
  qed
  have edge_se: "(l, b, g, Sil a, f, r, l') = start_edge (actions ! n)"
    by (rule prop_start_edge_pinned[OF P E LOC off n pSuc])
  \<comment> \<open>The numeric edge: the AUGMENTED @{const num_start_edge}, in the numeric net at @{term \<open>Suc n\<close>}.\<close>
  have NE: "(l, bexp.and b (num_pre_guard s), g, Sil a, f @ ?fn, r, l')
              \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc
    using num_nth_auto_num_start_edge[OF n]
    unfolding num_start_edge_def augment_edge_def edge_se[symmetric] s_eq[symmetric] Let_def
    by (simp add: prod.case)
  \<comment> \<open>Combined guard fires on @{term vn}.\<close>
  have bvn: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have NB: "check_bexp vn (bexp.and b (num_pre_guard s)) True"
    using check_bexp_is_val.intros(3)[OF bvn guard_ok] by simp
  \<comment> \<open>Fluent variables are fresh of the propositional update @{term f}.\<close>
  have f_in_vp': "fst ` set f \<subseteq> dom vp'" by (rule is_upds_writes_dom[OF U])
  have v'_fresh: "fluent_to_var h \<notin> dom vp'" if h: "h \<in> set nfluents" for h
  proof -
    have "dom vp' = dom (map_of net_bounds)"
      using pbnd' unfolding Simple_Network_Language.bounded_def by blast
    thus ?thesis using fluent_var_notin_net_bounds[OF h] by simp
  qed
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
    using f_in_vp' v'_fresh[OF h] by blast
  \<comment> \<open>Propositional updates fire on @{term vn}, preserving tracking.\<close>
  obtain vn_mid where
      NUmid: "is_upds vn f vn_mid"
    and LEmid: "vp' \<subseteq>\<^sub>m vn_mid"
    and OFFmid: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn_mid x = vn x"
    using is_upds_map_le[OF U le] by blast
  have TRmid: "num_tracks vn_mid w" by (rule num_tracks_pres_unwritten[OF tr NUmid fresh])
  \<comment> \<open>Numeric updates fire on @{term vn_mid}, landing on the abstract simultaneous override.\<close>
  obtain vn' where
      NUnum: "is_upds vn_mid ?fn vn'"
    and TRnum: "num_tracks vn' (apply_upds (set ?us) w)"
    and OFFnum: "\<And>x. x \<notin> fluent_to_var ` fst ` set ?us \<Longrightarrow> vn' x = vn_mid x"
    using is_upds_num_upd[OF TRmid us_func us_ncr us_ok, folded fn_eq] by metis
  have NU: "is_upds vn (f @ ?fn) vn'" by (rule is_upds_appendI[OF NUmid NUnum])
  \<comment> \<open>@{term vp'} survives: the numeric half writes only fresh fluent variables.\<close>
  have LE: "vp' \<subseteq>\<^sub>m vn'"
  proof (unfold map_le_def, intro ballI)
    fix x assume xdom: "x \<in> dom vp'"
    have "x \<notin> fluent_to_var ` fst ` set ?us"
    proof
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      hence "fluent_to_var fl \<notin> dom vp'" by (rule v'_fresh)
      thus False using xfl xdom by simp
    qed
    hence "vn' x = vn_mid x" by (rule OFFnum)
    moreover have "vp' x = vn_mid x" using LEmid xdom by (auto simp: map_le_def)
    ultimately show "vp' x = vn' x" by simp
  qed
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound on the post-store.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  \<comment> \<open>The combined update writes only variables already present in @{term vn}: props (net_bounds) and
     fluent variables, both inside @{const num_net_bounds}.\<close>
  have fset_sub: "fst ` set (f @ ?fn) \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set (f @ ?fn)"
    hence "x \<in> fst ` set f \<union> fluent_to_var ` fst ` set ?us" by (auto simp: fn_eq)
    thus "x \<in> dom vn"
    proof
      assume "x \<in> fst ` set f"
      hence "x \<in> dom vp'" using f_in_vp' by blast
      thus "x \<in> dom vn" using vp'_dom dom_vn dom_map_of_num_net_bounds by auto
    next
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      thus "x \<in> dom vn" using xfl dom_vn dom_map_of_num_net_bounds by auto
    qed
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TRnum fin' vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TRnum BND w'_eq by (auto intro: RELI)
qed

text \<open>The configuration-level relation between a propositional config and a numeric config: same
locations, same clocks, and the stores related by @{const REL}.\<close>
definition RELC where
"RELC cp cn w \<longleftrightarrow> (case cp of (Lp, vp, cup) \<Rightarrow> case cn of (Ln, vn, cun) \<Rightarrow>
   Lp = Ln \<and> cup = cun \<and> REL vp vn w)"

lemma RELCI:
  assumes "REL vp vn w"
  shows "RELC (L, vp, c) (L, vn, c) w"
  using assms unfolding RELC_def by simp

lemma RELC_locD: "RELC (Lp, vp, cup) (Ln, vn, cun) w \<Longrightarrow> Lp = Ln"
  and RELC_clkD: "RELC (Lp, vp, cup) (Ln, vn, cun) w \<Longrightarrow> cup = cun"
  and RELC_relD: "RELC (Lp, vp, cup) (Ln, vn, cun) w \<Longrightarrow> REL vp vn w"
  unfolding RELC_def by auto

text \<open>The START phase run-lift, a FOLD-EVOLVING analogue of the \<open>RLP\<close> edge_3 phase-lift: each
@{const start_edge_effect} step both fires a numeric edge AND advances the abstract numeric fold by the
fired snap @{term \<open>at_start (actions ! n)\<close>}. By induction on the index suffix @{term ns}, threading the
running propositional config @{term sp}, the running numeric store @{term vn}, and the accumulated snap
prefix @{term ys} (a distinct sublist of happening @{term i}). The per-step kernel @{thm [source]
num_edge_upd_step_lift} is discharged from the running fold @{term \<open>num_plan.num_rat_impl.happening_num_update ys (snd (M i))\<close>}:
@{const num_val_ok} via @{thm [source] happening_num_update_preserves_num_val_ok}, the post-fold bound via
@{thm [source] running_prefix_in_bounds}, the precondition satisfaction via @{thm [source] happening_snap_pre_sat}
+ @{thm [source] sat_comps_running_prefix}, and the write-set/membership facts from the locale and
@{thm [source] happ_at_index_decomp}. The propositional per-step structural facts (the @{const off_loc} source
location, the length, the projection bound on the post-store) are supplied per run-position by the
caller hypothesis @{text struct}.\<close>
lemma num_start_phase_lift:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
  assumes ns_start: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions
                            \<and> is_starting_index (planning_sem.time_index i) n"
      and ys_act: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and zs_dist: "distinct (ys @ map (\<lambda>n. at_start (actions ! n)) ns @ zs)"
      and zs_full: "set (ys @ map (\<lambda>n. at_start (actions ! n)) ns @ zs)
                      = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and prun: "graph_impl.steps (sp # seq_apply (map start_edge_effect ns) sp)"
      and struct: "\<And>k. k < length ns \<Longrightarrow>
                     fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k) ! Suc (ns ! k) = off_loc
                     \<and> length (fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k)) = length net_automata
                     \<and> Simple_Network_Language.bounded (map_of net_bounds)
                           (fst (snd (start_edge_effect (ns ! k)
                                       ((sp # seq_apply (map start_edge_effect ns) sp) ! k))))"
      and rel0: "RELC sp cn (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
    shows "\<exists>nss. num_graph_impl.steps (cn # nss)
                 \<and> length nss = length ns
                 \<and> RELC (last (sp # seq_apply (map start_edge_effect ns) sp)) (last (cn # nss))
                        (num_plan.num_rat_impl.happening_num_update
                           (ys @ map (\<lambda>n. at_start (actions ! n)) ns) (snd (M i)))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  have base_val_ok: "num_val_ok (snd (M i))"
    using i by (intro num_seq_val_ok[OF vss m0]) simp
  \<comment> \<open>The generalized inductive claim: over any starting-index suffix @{term as}, running config
     @{term s}, accumulated snap-prefix @{term bs} (a distinct happening-sublist), residual @{term cs}.\<close>
  have gen: "\<exists>nss. num_graph_impl.steps (dn # nss)
                   \<and> length nss = length as
                   \<and> RELC (last (s # seq_apply (map start_edge_effect as) s)) (last (dn # nss))
                          (?w (bs @ map (\<lambda>n. at_start (actions ! n)) as))"
    if as_start: "\<And>n. n \<in> set as \<Longrightarrow> n < length actions
                          \<and> is_starting_index (planning_sem.time_index i) n"
       and bs_act: "\<And>t. t \<in> set bs \<Longrightarrow> \<exists>a \<in> set actions. t = at_start a \<or> t = at_end a"
       and bs_sub: "set bs \<subseteq> ?S"
       and cs_dist: "distinct (bs @ map (\<lambda>n. at_start (actions ! n)) as @ cs)"
       and cs_full: "set (bs @ map (\<lambda>n. at_start (actions ! n)) as @ cs) = ?S"
       and srun: "graph_impl.steps (s # seq_apply (map start_edge_effect as) s)"
       and sstruct: "\<And>k. k < length as \<Longrightarrow>
                       fst ((s # seq_apply (map start_edge_effect as) s) ! k) ! Suc (as ! k) = off_loc
                       \<and> length (fst ((s # seq_apply (map start_edge_effect as) s) ! k)) = length net_automata
                       \<and> Simple_Network_Language.bounded (map_of net_bounds)
                             (fst (snd (start_edge_effect (as ! k)
                                         ((s # seq_apply (map start_edge_effect as) s) ! k))))"
       and srel: "RELC s dn (?w bs)"
     for as s dn bs cs
    using that
  proof (induction as arbitrary: s dn bs cs)
    case Nil
    show ?case
    proof (intro exI[where x = "[]"] conjI)
      show "num_graph_impl.steps (dn # [])" by (rule num_graph_impl.steps.intros(1))
    next
      show "length [] = length []" by simp
    next
      show "RELC (last (s # seq_apply (map start_edge_effect []) s)) (last (dn # []))
                 (?w (bs @ map (\<lambda>n. at_start (actions ! n)) []))"
        by (simp only: list.map seq_apply_Nil append_Nil2 last_ConsL) (rule Nil.prems(8))
    qed
  next
    case (Cons n as')
    let ?sn = "at_start (actions ! n)"
    let ?s' = "start_edge_effect n s"
    \<comment> \<open>Decompose the running config and the @{const RELC}-related numeric start.\<close>
    obtain L vp c where s: "s = (L, vp, c)" by (cases s)
    obtain Ln dvn cn0 where dn: "dn = (Ln, dvn, cn0)" by (cases dn)
    have Leq: "Ln = L" by (rule RELC_locD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have ceq: "cn0 = c" by (rule RELC_clkD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have relS: "REL vp dvn (?w bs)" by (rule RELC_relD[OF Cons.prems(8)[unfolded s dn]])
    \<comment> \<open>Head index facts.\<close>
    have nmem: "n \<in> set (n # as')" by simp
    have n_lt: "n < length actions"
      and n_start: "is_starting_index (planning_sem.time_index i) n"
      using Cons.prems(1)[OF nmem] by blast+
    have aMem: "actions ! n \<in> set actions" using n_lt by simp
    \<comment> \<open>The fired start-snap is in happening @{term i}.\<close>
    have sn_mem: "?sn \<in> ?S"
      unfolding happ_at_index_decomp
      using n_lt n_start by blast
    \<comment> \<open>Run decomposition: the first edge and the tail run over @{term \<open>?s'\<close>}.\<close>
    have run_unfold: "s # seq_apply (map start_edge_effect (n # as')) s
                        = s # ?s' # seq_apply (map start_edge_effect as') ?s'"
      by (simp only: list.map seq_apply_Cons_Cons)
    have run_dec: "graph_impl.steps (s # ?s' # seq_apply (map start_edge_effect as') ?s')"
      using Cons.prems(6) run_unfold by simp
    \<comment> \<open>The propositional first edge and the tail run.\<close>
    have pstep0: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst ?s', fst (snd ?s'), snd (snd ?s')\<rangle>"
      using run_dec unfolding s by (cases ?s') (auto elim: graph_impl.steps.cases simp: prod.case)
    have tailrun: "graph_impl.steps (?s' # seq_apply (map start_edge_effect as') ?s')"
      using run_dec by (rule graph_impl.steps_ConsD) simp
    \<comment> \<open>The structural facts at run-position 0 (the head step on @{term s}).\<close>
    have off0: "L ! Suc n = off_loc"
      and Llen0: "length L = length net_automata"
      and pbnd0: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s'))"
      using Cons.prems(7)[of 0] unfolding s by simp_all
    \<comment> \<open>The new accumulated snap-prefix and the list-shape rearrangement that re-targets the
       distinctness/fullness premises of the IH.\<close>
    define bs' where "bs' = bs @ [?sn]"
    have list_rearr: "bs @ map (\<lambda>m. at_start (actions ! m)) (n # as') @ cs
                        = bs' @ map (\<lambda>m. at_start (actions ! m)) as' @ cs"
      unfolding bs'_def by simp
    have cs_dist': "distinct (bs' @ map (\<lambda>m. at_start (actions ! m)) as' @ cs)"
      using Cons.prems(4)[unfolded list_rearr] .
    have cs_full': "set (bs' @ map (\<lambda>m. at_start (actions ! m)) as' @ cs) = ?S"
      using Cons.prems(5)[unfolded list_rearr] .
    \<comment> \<open>@{term \<open>?sn\<close>} is fresh of the already-folded prefix @{term bs}.\<close>
    have sn_notin_bs: "?sn \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr[symmetric])
    \<comment> \<open>The fold-append identity: snapping @{term \<open>?sn\<close>} onto the @{term bs}-fold IS the @{term bs'}-fold
       (the @{const fold} LANDMINE: rewrite via @{thm [source] fold_append}, not @{text simp}).\<close>
    have foldapp: "num_plan.num_rat_impl.snap_num_update ?sn (?w bs) = ?w bs'"
      unfolding bs'_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append) (simp add: comp_def)
    \<comment> \<open>The four numeric-fold kernel hypotheses for the @{term \<open>?sn\<close>} step at @{term \<open>?w bs\<close>}.\<close>
    have wok: "num_val_ok (?w bs)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok Cons.prems(2)])
    have fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      unfolding foldapp by (rule running_prefix_in_bounds[OF vss m0 i cs_dist' cs_full'])
    have sat_eq: "sat_comps (?w bs) (set (n_pre ?sn)) = sat_comps (snd (M i)) (set (n_pre ?sn))"
      by (rule sat_comps_running_prefix[OF sn_mem Cons.prems(3) sn_notin_bs])
    have sat: "sat_comps (?w bs) (set (n_pre ?sn))"
      unfolding sat_eq by (rule happening_snap_pre_sat[OF vss i sn_mem])
    have upd_lhs: "fst ` set (upds ?sn) \<subseteq> set nfluents"
      using snap_writes_nfluents_start aMem by blast
    \<comment> \<open>Apply the per-step kernel: the @{term \<open>?sn\<close>} edge lifts to a numeric step from @{term dn}.\<close>
    have L'eq: "fst ?s' = fst (start_edge_effect n (L, vp, c))" unfolding s by simp
    obtain vn' where
        numstep: "num_net_impl.sem \<turnstile> \<langle>L, dvn, c\<rangle> \<rightarrow> \<langle>fst ?s', vn', snd (snd ?s')\<rangle>"
      and relE: "REL (fst (snd ?s')) vn' (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      using num_edge_upd_step_lift[OF relS Llen0 off0 n_lt HOL.refl sn_mem
              pstep0 L'eq pbnd0 wok fin sat upd_lhs] by blast
    \<comment> \<open>Package the numeric post-config and its @{const RELC}-relation at the advanced fold @{term \<open>?w bs'\<close>}.\<close>
    obtain L' vp' c' where s'eq: "?s' = (L', vp', c')" by (cases ?s')
    define dn' where "dn' = (L', vn', c')"
    have relC': "RELC ?s' dn' (?w bs')"
      unfolding dn'_def s'eq
      using RELCI[OF relE[unfolded foldapp]] unfolding s'eq by simp
    \<comment> \<open>The IH premises for the tail suffix @{term as'} from @{term \<open>?s'\<close>}, @{term dn'}, @{term bs'}.\<close>
    have as'_start: "m < length actions \<and> is_starting_index (planning_sem.time_index i) m"
      if "m \<in> set as'" for m
      using Cons.prems(1) that by simp
    have bs'_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs'" for t
      using that aMem Cons.prems(2) unfolding bs'_def by auto
    have bs'_sub: "set bs' \<subseteq> ?S"
      using Cons.prems(3) sn_mem unfolding bs'_def by auto
    \<comment> \<open>Re-index the per-run-position structural premise: position @{term k} of the tail run is
       position @{term \<open>Suc k\<close>} of the full run.\<close>
    have sstruct': "fst ((?s' # seq_apply (map start_edge_effect as') ?s') ! k) ! Suc (as' ! k) = off_loc
                    \<and> length (fst ((?s' # seq_apply (map start_edge_effect as') ?s') ! k)) = length net_automata
                    \<and> Simple_Network_Language.bounded (map_of net_bounds)
                          (fst (snd (start_edge_effect (as' ! k)
                                      ((?s' # seq_apply (map start_edge_effect as') ?s') ! k))))"
      if k: "k < length as'" for k
    proof -
      have Sk: "Suc k < length (n # as')" using k by simp
      have idx: "(s # seq_apply (map start_edge_effect (n # as')) s) ! Suc k
                   = (?s' # seq_apply (map start_edge_effect as') ?s') ! k"
        unfolding run_unfold by simp
      show ?thesis using Cons.prems(7)[OF Sk] unfolding idx by simp
    qed
    have ih: "\<exists>nss. num_graph_impl.steps (dn' # nss)
                   \<and> length nss = length as'
                   \<and> RELC (last (?s' # seq_apply (map start_edge_effect as') ?s')) (last (dn' # nss))
                          (?w (bs' @ map (\<lambda>m. at_start (actions ! m)) as'))"
      by (rule Cons.IH[OF as'_start bs'_act bs'_sub cs_dist' cs_full' tailrun sstruct' relC'])
    obtain nss' where
        nrun': "num_graph_impl.steps (dn' # nss')"
      and lnss': "length nss' = length as'"
      and rlast': "RELC (last (?s' # seq_apply (map start_edge_effect as') ?s')) (last (dn' # nss'))
                        (?w (bs' @ map (\<lambda>m. at_start (actions ! m)) as'))"
      using ih by (elim exE conjE)
    \<comment> \<open>Splice: the head numeric step from @{term dn} to @{term dn'} in front of the tail numeric run.\<close>
    have headstep: "num_graph_impl.steps [dn, dn']"
      unfolding dn dn'_def Leq ceq s'eq
      by (rule num_single_step_intro) (use numstep s'eq in \<open>simp add: prod.case\<close>)
    have spliced: "num_graph_impl.steps (dn # dn' # nss')"
      using num_steps_extend[OF headstep] nrun' by simp
    show ?case
    proof (intro exI[where x = "dn' # nss'"] conjI)
      show "num_graph_impl.steps (dn # dn' # nss')" by (rule spliced)
    next
      show "length (dn' # nss') = length (n # as')" using lnss' by simp
    next
      have bsrew: "bs' @ map (\<lambda>m. at_start (actions ! m)) as'
                     = bs @ map (\<lambda>m. at_start (actions ! m)) (n # as')"
        unfolding bs'_def by simp
      have lastrew: "last (s # seq_apply (map start_edge_effect (n # as')) s)
                       = last (?s' # seq_apply (map start_edge_effect as') ?s')"
        unfolding run_unfold by simp
      show "RELC (last (s # seq_apply (map start_edge_effect (n # as')) s)) (last (dn # dn' # nss'))
                 (?w (bs @ map (\<lambda>m. at_start (actions ! m)) (n # as')))"
        using rlast' unfolding lastrew bsrew by simp
    qed
  qed
  show ?thesis
    by (rule gen[OF ns_start ys_act ys_sub zs_dist zs_full prun struct rel0])
qed

text \<open>The @{const ending_loc} source location pins the fired edge to @{const end_edge}: among the five
edges of an action automaton only @{const end_edge} leaves @{const ending_loc} (start: @{const off_loc},
edge_2: @{const starting_loc}, edge_3: @{const running_loc}, instant: @{const starting_loc}). So a
propositional internal step from a config whose @{term \<open>Suc n\<close>}-th location is @{const ending_loc} must
have fired @{const end_edge} at automaton @{term \<open>Suc n\<close>}.\<close>
lemma prop_end_edge_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and end0: "L ! Suc n = ending_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = end_edge (actions ! n)"
proof -
  have l_end: "l = ending_loc" using Lp end0 pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_end
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The END analogue of @{thm [source] num_edge_upd_step_lift}: the reusable per-step kernel for a
fluent-WRITING happening edge, lifting ONE propositional @{const end_edge} step (the @{text at_end} snap
of @{term \<open>actions ! n\<close>}) to a numeric @{const num_graph_impl.steps} step whose numeric edge is the
AUGMENTED @{const num_end_edge}. The numeric post-store tracks
@{term \<open>num_plan.num_rat_impl.snap_num_update s w = apply_upds (set (upds s)) w\<close>}; everything is the
START kernel with start swapped to end, the source location pinned to @{const ending_loc} (via
@{thm [source] prop_end_edge_pinned}) and the post location at @{const off_loc}.\<close>
lemma num_edge_upd_step_lift_end:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and end0: "L ! Suc n = ending_loc"
      and n: "n < length actions"
      and s_eq: "s = at_end (actions ! n)"
      and mem: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (end_edge_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and wok: "num_val_ok w"
      and fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update s w)"
      and sat: "sat_comps w (set (n_pre s))"
      and upd_lhs: "fst ` set (upds s) \<subseteq> set nfluents"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>
                 \<and> REL vp' vn' (num_plan.num_rat_impl.snap_num_update s w)"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have aMem: "actions ! n \<in> set actions" using n by simp
  let ?us = "upds s"
  let ?fn = "num_upd s"
  have fn_eq: "?fn = map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) ?us"
    by (simp add: num_upd_def)
  have w'_eq: "num_plan.num_rat_impl.snap_num_update s w = apply_upds (set ?us) w"
    by (simp add: num_plan.num_rat_impl.snap_num_update_def)
  \<comment> \<open>The numeric post-fold bound, restated in @{const apply_upds} form for @{thm [source] is_upds_num_upd}.\<close>
  have fin': "fluent_in_bounds (apply_upds (set ?us) w)" using fin w'_eq by simp
  \<comment> \<open>The contract facts for the @{text at_end} snap, instantiated at @{term w}.\<close>
  have us_func: "upds_functional_list ?us"
    using upds_functional_end aMem s_eq by blast
  have us_ncr: "upds_no_cross_read_list ?us"
    using upds_no_cross_read_end aMem s_eq by blast
  have us_ok: "fl \<in> set nfluents \<and> nexp_ok w e" if "(fl, e) \<in> set ?us" for fl e
  proof -
    have "nexp_ok w e" using happening_snap_nexp_ok[OF mem _ wok] that by blast
    moreover have "fl \<in> set nfluents" using upd_lhs that by blast
    ultimately show ?thesis by blast
  qed
  have pre_ok: "\<forall>cc \<in> set (n_pre s). comp_ok w cc"
    using snap_pre_comp_ok_end aMem s_eq wok by blast
  \<comment> \<open>The numeric pre-guard holds on the extended store.\<close>
  have guard_ok: "check_bexp vn (num_pre_guard s) True"
    unfolding num_pre_guard_def by (rule check_bexp_comps_guard[OF tr pre_ok sat])
  have L'_eq: "L' = L[Suc n := off_loc]"
    using L'eq by (simp add: end_edge_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const end_edge}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}, which goes to
     @{const off_loc} \<noteq> @{const ending_loc}.\<close>
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    hence "L' ! Suc n = ending_loc" using L'eq2 end0 by simp
    moreover have "L' ! Suc n = off_loc" using L'_eq Sn_lt by simp
    ultimately show False by (simp add: locations_unique)
  qed
  have edge_se: "(l, b, g, Sil a, f, r, l') = end_edge (actions ! n)"
    by (rule prop_end_edge_pinned[OF P E LOC end0 n pSuc])
  \<comment> \<open>The numeric edge: the AUGMENTED @{const num_end_edge}, in the numeric net at @{term \<open>Suc n\<close>}.\<close>
  have NE: "(l, bexp.and b (num_pre_guard s), g, Sil a, f @ ?fn, r, l')
              \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc
    using num_nth_auto_num_end_edge[OF n]
    unfolding num_end_edge_def augment_edge_def edge_se[symmetric] s_eq[symmetric] Let_def
    by (simp add: prod.case)
  \<comment> \<open>Combined guard fires on @{term vn}.\<close>
  have bvn: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have NB: "check_bexp vn (bexp.and b (num_pre_guard s)) True"
    using check_bexp_is_val.intros(3)[OF bvn guard_ok] by simp
  \<comment> \<open>Fluent variables are fresh of the propositional update @{term f}.\<close>
  have f_in_vp': "fst ` set f \<subseteq> dom vp'" by (rule is_upds_writes_dom[OF U])
  have v'_fresh: "fluent_to_var h \<notin> dom vp'" if h: "h \<in> set nfluents" for h
  proof -
    have "dom vp' = dom (map_of net_bounds)"
      using pbnd' unfolding Simple_Network_Language.bounded_def by blast
    thus ?thesis using fluent_var_notin_net_bounds[OF h] by simp
  qed
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
    using f_in_vp' v'_fresh[OF h] by blast
  \<comment> \<open>Propositional updates fire on @{term vn}, preserving tracking.\<close>
  obtain vn_mid where
      NUmid: "is_upds vn f vn_mid"
    and LEmid: "vp' \<subseteq>\<^sub>m vn_mid"
    and OFFmid: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn_mid x = vn x"
    using is_upds_map_le[OF U le] by blast
  have TRmid: "num_tracks vn_mid w" by (rule num_tracks_pres_unwritten[OF tr NUmid fresh])
  \<comment> \<open>Numeric updates fire on @{term vn_mid}, landing on the abstract simultaneous override.\<close>
  obtain vn' where
      NUnum: "is_upds vn_mid ?fn vn'"
    and TRnum: "num_tracks vn' (apply_upds (set ?us) w)"
    and OFFnum: "\<And>x. x \<notin> fluent_to_var ` fst ` set ?us \<Longrightarrow> vn' x = vn_mid x"
    using is_upds_num_upd[OF TRmid us_func us_ncr us_ok, folded fn_eq] by metis
  have NU: "is_upds vn (f @ ?fn) vn'" by (rule is_upds_appendI[OF NUmid NUnum])
  \<comment> \<open>@{term vp'} survives: the numeric half writes only fresh fluent variables.\<close>
  have LE: "vp' \<subseteq>\<^sub>m vn'"
  proof (unfold map_le_def, intro ballI)
    fix x assume xdom: "x \<in> dom vp'"
    have "x \<notin> fluent_to_var ` fst ` set ?us"
    proof
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      hence "fluent_to_var fl \<notin> dom vp'" by (rule v'_fresh)
      thus False using xfl xdom by simp
    qed
    hence "vn' x = vn_mid x" by (rule OFFnum)
    moreover have "vp' x = vn_mid x" using LEmid xdom by (auto simp: map_le_def)
    ultimately show "vp' x = vn' x" by simp
  qed
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound on the post-store.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  \<comment> \<open>The combined update writes only variables already present in @{term vn}: props (net_bounds) and
     fluent variables, both inside @{const num_net_bounds}.\<close>
  have fset_sub: "fst ` set (f @ ?fn) \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set (f @ ?fn)"
    hence "x \<in> fst ` set f \<union> fluent_to_var ` fst ` set ?us" by (auto simp: fn_eq)
    thus "x \<in> dom vn"
    proof
      assume "x \<in> fst ` set f"
      hence "x \<in> dom vp'" using f_in_vp' by blast
      thus "x \<in> dom vn" using vp'_dom dom_vn dom_map_of_num_net_bounds by auto
    next
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      thus "x \<in> dom vn" using xfl dom_vn dom_map_of_num_net_bounds by auto
    qed
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TRnum fin' vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TRnum BND w'_eq by (auto intro: RELI)
qed


text \<open>The END phase run-lift, the END analogue of @{thm [source] num_start_phase_lift}: each
@{const end_edge_effect} step both fires a numeric edge AND advances the abstract numeric fold by the
fired snap @{term \<open>at_end (actions ! n)\<close>}. By induction on the index suffix @{term ns}, threading the
running propositional config @{term sp}, the running numeric store @{term vn}, and the accumulated snap
prefix @{term ys} (a distinct sublist of happening @{term i}). The per-step kernel @{thm [source]
num_edge_upd_step_lift_end} is discharged from the running fold exactly as in the START phase:
@{const num_val_ok} via @{thm [source] happening_num_update_preserves_num_val_ok}, the post-fold bound
via @{thm [source] running_prefix_in_bounds}, the precondition satisfaction via
@{thm [source] happening_snap_pre_sat} + @{thm [source] sat_comps_running_prefix}, and the
write-set/membership facts from the locale and @{thm [source] happ_at_index_decomp} (ENDING indices land
in the @{text at_end}-image). The propositional per-step structural facts (the @{const ending_loc} source
location, the length, the projection bound on the post-store) are supplied per run-position by the caller
hypothesis @{text struct}.\<close>
lemma num_end_phase_lift:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
  assumes ns_end: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions
                          \<and> is_ending_index (planning_sem.time_index i) n"
      and ys_act: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and zs_dist: "distinct (ys @ map (\<lambda>n. at_end (actions ! n)) ns @ zs)"
      and zs_full: "set (ys @ map (\<lambda>n. at_end (actions ! n)) ns @ zs)
                      = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and prun: "graph_impl.steps (sp # seq_apply (map end_edge_effect ns) sp)"
      and struct: "\<And>k. k < length ns \<Longrightarrow>
                     fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k) ! Suc (ns ! k) = ending_loc
                     \<and> length (fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k)) = length net_automata
                     \<and> Simple_Network_Language.bounded (map_of net_bounds)
                           (fst (snd (end_edge_effect (ns ! k)
                                       ((sp # seq_apply (map end_edge_effect ns) sp) ! k))))"
      and rel0: "RELC sp cn (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
    shows "\<exists>nss. num_graph_impl.steps (cn # nss)
                 \<and> length nss = length ns
                 \<and> RELC (last (sp # seq_apply (map end_edge_effect ns) sp)) (last (cn # nss))
                        (num_plan.num_rat_impl.happening_num_update
                           (ys @ map (\<lambda>n. at_end (actions ! n)) ns) (snd (M i)))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  have base_val_ok: "num_val_ok (snd (M i))"
    using i by (intro num_seq_val_ok[OF vss m0]) simp
  \<comment> \<open>The generalized inductive claim: over any ending-index suffix @{term as}, running config
     @{term s}, accumulated snap-prefix @{term bs} (a distinct happening-sublist), residual @{term cs}.\<close>
  have gen: "\<exists>nss. num_graph_impl.steps (dn # nss)
                   \<and> length nss = length as
                   \<and> RELC (last (s # seq_apply (map end_edge_effect as) s)) (last (dn # nss))
                          (?w (bs @ map (\<lambda>n. at_end (actions ! n)) as))"
    if as_end: "\<And>n. n \<in> set as \<Longrightarrow> n < length actions
                          \<and> is_ending_index (planning_sem.time_index i) n"
       and bs_act: "\<And>t. t \<in> set bs \<Longrightarrow> \<exists>a \<in> set actions. t = at_start a \<or> t = at_end a"
       and bs_sub: "set bs \<subseteq> ?S"
       and cs_dist: "distinct (bs @ map (\<lambda>n. at_end (actions ! n)) as @ cs)"
       and cs_full: "set (bs @ map (\<lambda>n. at_end (actions ! n)) as @ cs) = ?S"
       and srun: "graph_impl.steps (s # seq_apply (map end_edge_effect as) s)"
       and sstruct: "\<And>k. k < length as \<Longrightarrow>
                       fst ((s # seq_apply (map end_edge_effect as) s) ! k) ! Suc (as ! k) = ending_loc
                       \<and> length (fst ((s # seq_apply (map end_edge_effect as) s) ! k)) = length net_automata
                       \<and> Simple_Network_Language.bounded (map_of net_bounds)
                             (fst (snd (end_edge_effect (as ! k)
                                         ((s # seq_apply (map end_edge_effect as) s) ! k))))"
       and srel: "RELC s dn (?w bs)"
     for as s dn bs cs
    using that
  proof (induction as arbitrary: s dn bs cs)
    case Nil
    show ?case
    proof (intro exI[where x = "[]"] conjI)
      show "num_graph_impl.steps (dn # [])" by (rule num_graph_impl.steps.intros(1))
    next
      show "length [] = length []" by simp
    next
      show "RELC (last (s # seq_apply (map end_edge_effect []) s)) (last (dn # []))
                 (?w (bs @ map (\<lambda>n. at_end (actions ! n)) []))"
        by (simp only: list.map seq_apply_Nil append_Nil2 last_ConsL) (rule Nil.prems(8))
    qed
  next
    case (Cons n as')
    let ?sn = "at_end (actions ! n)"
    let ?s' = "end_edge_effect n s"
    \<comment> \<open>Decompose the running config and the @{const RELC}-related numeric start.\<close>
    obtain L vp c where s: "s = (L, vp, c)" by (cases s)
    obtain Ln dvn cn0 where dn: "dn = (Ln, dvn, cn0)" by (cases dn)
    have Leq: "Ln = L" by (rule RELC_locD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have ceq: "cn0 = c" by (rule RELC_clkD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have relS: "REL vp dvn (?w bs)" by (rule RELC_relD[OF Cons.prems(8)[unfolded s dn]])
    \<comment> \<open>Head index facts.\<close>
    have nmem: "n \<in> set (n # as')" by simp
    have n_lt: "n < length actions"
      and n_end: "is_ending_index (planning_sem.time_index i) n"
      using Cons.prems(1)[OF nmem] by blast+
    have aMem: "actions ! n \<in> set actions" using n_lt by simp
    \<comment> \<open>The fired end-snap is in happening @{term i}.\<close>
    have sn_mem: "?sn \<in> ?S"
      unfolding happ_at_index_decomp
      using n_lt n_end by blast
    \<comment> \<open>Run decomposition: the first edge and the tail run over @{term \<open>?s'\<close>}.\<close>
    have run_unfold: "s # seq_apply (map end_edge_effect (n # as')) s
                        = s # ?s' # seq_apply (map end_edge_effect as') ?s'"
      by (simp only: list.map seq_apply_Cons_Cons)
    have run_dec: "graph_impl.steps (s # ?s' # seq_apply (map end_edge_effect as') ?s')"
      using Cons.prems(6) run_unfold by simp
    \<comment> \<open>The propositional first edge and the tail run.\<close>
    have pstep0: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst ?s', fst (snd ?s'), snd (snd ?s')\<rangle>"
      using run_dec unfolding s by (cases ?s') (auto elim: graph_impl.steps.cases simp: prod.case)
    have tailrun: "graph_impl.steps (?s' # seq_apply (map end_edge_effect as') ?s')"
      using run_dec by (rule graph_impl.steps_ConsD) simp
    \<comment> \<open>The structural facts at run-position 0 (the head step on @{term s}).\<close>
    have end0: "L ! Suc n = ending_loc"
      and Llen0: "length L = length net_automata"
      and pbnd0: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s'))"
      using Cons.prems(7)[of 0] unfolding s by simp_all
    \<comment> \<open>The new accumulated snap-prefix and the list-shape rearrangement that re-targets the
       distinctness/fullness premises of the IH.\<close>
    define bs' where "bs' = bs @ [?sn]"
    have list_rearr: "bs @ map (\<lambda>m. at_end (actions ! m)) (n # as') @ cs
                        = bs' @ map (\<lambda>m. at_end (actions ! m)) as' @ cs"
      unfolding bs'_def by simp
    have cs_dist': "distinct (bs' @ map (\<lambda>m. at_end (actions ! m)) as' @ cs)"
      using Cons.prems(4)[unfolded list_rearr] .
    have cs_full': "set (bs' @ map (\<lambda>m. at_end (actions ! m)) as' @ cs) = ?S"
      using Cons.prems(5)[unfolded list_rearr] .
    \<comment> \<open>@{term \<open>?sn\<close>} is fresh of the already-folded prefix @{term bs}.\<close>
    have sn_notin_bs: "?sn \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr[symmetric])
    \<comment> \<open>The fold-append identity: snapping @{term \<open>?sn\<close>} onto the @{term bs}-fold IS the @{term bs'}-fold
       (the @{const fold} LANDMINE: rewrite via @{thm [source] fold_append}, not @{text simp}).\<close>
    have foldapp: "num_plan.num_rat_impl.snap_num_update ?sn (?w bs) = ?w bs'"
      unfolding bs'_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append) (simp add: comp_def)
    \<comment> \<open>The four numeric-fold kernel hypotheses for the @{term \<open>?sn\<close>} step at @{term \<open>?w bs\<close>}.\<close>
    have wok: "num_val_ok (?w bs)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok Cons.prems(2)])
    have fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      unfolding foldapp by (rule running_prefix_in_bounds[OF vss m0 i cs_dist' cs_full'])
    have sat_eq: "sat_comps (?w bs) (set (n_pre ?sn)) = sat_comps (snd (M i)) (set (n_pre ?sn))"
      by (rule sat_comps_running_prefix[OF sn_mem Cons.prems(3) sn_notin_bs])
    have sat: "sat_comps (?w bs) (set (n_pre ?sn))"
      unfolding sat_eq by (rule happening_snap_pre_sat[OF vss i sn_mem])
    have upd_lhs: "fst ` set (upds ?sn) \<subseteq> set nfluents"
      using snap_writes_nfluents_end aMem by blast
    \<comment> \<open>Apply the per-step kernel: the @{term \<open>?sn\<close>} edge lifts to a numeric step from @{term dn}.\<close>
    have L'eq: "fst ?s' = fst (end_edge_effect n (L, vp, c))" unfolding s by simp
    obtain vn' where
        numstep: "num_net_impl.sem \<turnstile> \<langle>L, dvn, c\<rangle> \<rightarrow> \<langle>fst ?s', vn', snd (snd ?s')\<rangle>"
      and relE: "REL (fst (snd ?s')) vn' (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      using num_edge_upd_step_lift_end[OF relS Llen0 end0 n_lt HOL.refl sn_mem
              pstep0 L'eq pbnd0 wok fin sat upd_lhs] by blast
    \<comment> \<open>Package the numeric post-config and its @{const RELC}-relation at the advanced fold @{term \<open>?w bs'\<close>}.\<close>
    obtain L' vp' c' where s'eq: "?s' = (L', vp', c')" by (cases ?s')
    define dn' where "dn' = (L', vn', c')"
    have relC': "RELC ?s' dn' (?w bs')"
      unfolding dn'_def s'eq
      using RELCI[OF relE[unfolded foldapp]] unfolding s'eq by simp
    \<comment> \<open>The IH premises for the tail suffix @{term as'} from @{term \<open>?s'\<close>}, @{term dn'}, @{term bs'}.\<close>
    have as'_end: "m < length actions \<and> is_ending_index (planning_sem.time_index i) m"
      if "m \<in> set as'" for m
      using Cons.prems(1) that by simp
    have bs'_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs'" for t
      using that aMem Cons.prems(2) unfolding bs'_def by auto
    have bs'_sub: "set bs' \<subseteq> ?S"
      using Cons.prems(3) sn_mem unfolding bs'_def by auto
    \<comment> \<open>Re-index the per-run-position structural premise: position @{term k} of the tail run is
       position @{term \<open>Suc k\<close>} of the full run.\<close>
    have sstruct': "fst ((?s' # seq_apply (map end_edge_effect as') ?s') ! k) ! Suc (as' ! k) = ending_loc
                    \<and> length (fst ((?s' # seq_apply (map end_edge_effect as') ?s') ! k)) = length net_automata
                    \<and> Simple_Network_Language.bounded (map_of net_bounds)
                          (fst (snd (end_edge_effect (as' ! k)
                                      ((?s' # seq_apply (map end_edge_effect as') ?s') ! k))))"
      if k: "k < length as'" for k
    proof -
      have Sk: "Suc k < length (n # as')" using k by simp
      have idx: "(s # seq_apply (map end_edge_effect (n # as')) s) ! Suc k
                   = (?s' # seq_apply (map end_edge_effect as') ?s') ! k"
        unfolding run_unfold by simp
      show ?thesis using Cons.prems(7)[OF Sk] unfolding idx by simp
    qed
    have ih: "\<exists>nss. num_graph_impl.steps (dn' # nss)
                   \<and> length nss = length as'
                   \<and> RELC (last (?s' # seq_apply (map end_edge_effect as') ?s')) (last (dn' # nss))
                          (?w (bs' @ map (\<lambda>m. at_end (actions ! m)) as'))"
      by (rule Cons.IH[OF as'_end bs'_act bs'_sub cs_dist' cs_full' tailrun sstruct' relC'])
    obtain nss' where
        nrun': "num_graph_impl.steps (dn' # nss')"
      and lnss': "length nss' = length as'"
      and rlast': "RELC (last (?s' # seq_apply (map end_edge_effect as') ?s')) (last (dn' # nss'))
                        (?w (bs' @ map (\<lambda>m. at_end (actions ! m)) as'))"
      using ih by (elim exE conjE)
    \<comment> \<open>Splice: the head numeric step from @{term dn} to @{term dn'} in front of the tail numeric run.\<close>
    have headstep: "num_graph_impl.steps [dn, dn']"
      unfolding dn dn'_def Leq ceq s'eq
      by (rule num_single_step_intro) (use numstep s'eq in \<open>simp add: prod.case\<close>)
    have spliced: "num_graph_impl.steps (dn # dn' # nss')"
      using num_steps_extend[OF headstep] nrun' by simp
    show ?case
    proof (intro exI[where x = "dn' # nss'"] conjI)
      show "num_graph_impl.steps (dn # dn' # nss')" by (rule spliced)
    next
      show "length (dn' # nss') = length (n # as')" using lnss' by simp
    next
      have bsrew: "bs' @ map (\<lambda>m. at_end (actions ! m)) as'
                     = bs @ map (\<lambda>m. at_end (actions ! m)) (n # as')"
        unfolding bs'_def by simp
      have lastrew: "last (s # seq_apply (map end_edge_effect (n # as')) s)
                       = last (?s' # seq_apply (map end_edge_effect as') ?s')"
        unfolding run_unfold by simp
      show "RELC (last (s # seq_apply (map end_edge_effect (n # as')) s)) (last (dn # dn' # nss'))
                 (?w (bs @ map (\<lambda>m. at_end (actions ! m)) (n # as')))"
        using rlast' unfolding lastrew bsrew by simp
    qed
  qed
  show ?thesis
    by (rule gen[OF ns_end ys_act ys_sub zs_dist zs_full prun struct rel0])
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const instant_trans_edge} VERBATIM
(fifth in the edge list of @{const num_action_to_automaton}), so the numeric net contains the same
@{const instant_trans_edge} transition as the propositional net.\<close>
lemma num_nth_auto_instant_trans_edge:
  assumes n: "n < length actions"
  shows "instant_trans_edge (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>The @{const starting_loc} source location is shared by @{const edge_2} (target @{const running_loc})
and @{const instant_trans_edge} (target @{const ending_loc}); among the five edges of an action automaton
these are the only two leaving @{const starting_loc}. So a propositional internal step from a config whose
@{term \<open>Suc n\<close>}-th location is @{const starting_loc} AND whose fired edge targets @{const ending_loc} must
have fired @{const instant_trans_edge} at automaton @{term \<open>Suc n\<close>} (the target distinguishes it from
@{const edge_2}).\<close>
lemma prop_instant_trans_edge_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and start0: "L ! Suc n = starting_loc"
      and tgt: "l' = ending_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = instant_trans_edge (actions ! n)"
proof -
  have l_start: "l = starting_loc" using Lp start0 pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_start tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel for the INSTANT internal step: lifting ONE propositional
@{const instant_trans_edge} step (the no-fluent-write start-to-end duration edge of an instant action) to
a numeric @{const num_graph_impl.steps} step, preserving @{const REL}. The structure mirrors
@{thm [source] num_edge_3_step_lift}: the numeric edge is @{const instant_trans_edge} VERBATIM (reused in
@{const num_action_to_automaton} with no augment, no numeric update), so the abstract valuation @{term w}
is UNCHANGED. The only differences are the source location (@{const starting_loc} rather than
@{const running_loc}) and the edge-pinning (@{thm [source] prop_instant_trans_edge_pinned}, distinguishing
@{const instant_trans_edge} from @{const edge_2} by the @{const ending_loc} target).\<close>
lemma num_instant_trans_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and start0: "L ! Suc n = starting_loc"
      and n: "n < length actions"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (instant_trans_edge_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and fin: "fluent_in_bounds w"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle> \<and> REL vp' vn' w"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have L'_eq: "L' = L[Suc n := ending_loc]"
    using L'eq by (simp add: instant_trans_edge_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const instant_trans_edge}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}.\<close>
  have starting_ne_ending: "starting_loc \<noteq> ending_loc" by (simp add: locations_unique)
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    moreover have "L[Suc n := ending_loc] ! Suc n = ending_loc" using Sn_lt by simp
    ultimately show False using L'eq2 L'_eq start0 starting_ne_ending by simp
  qed
  \<comment> \<open>The fired edge targets @{const ending_loc}: position @{term \<open>Suc n\<close>} of the post locations.\<close>
  have tgt: "l' = ending_loc"
  proof -
    have "L[p := l'] ! Suc n = l'" using pSuc Sn_lt by simp
    moreover have "L[Suc n := ending_loc] ! Suc n = ending_loc" using Sn_lt by simp
    ultimately show ?thesis using L'eq2 L'_eq by simp
  qed
  have edgeit: "(l, b, g, Sil a, f, r, l') = instant_trans_edge (actions ! n)"
    by (rule prop_instant_trans_edge_pinned[OF P E LOC start0 tgt n pSuc])
  \<comment> \<open>The numeric edge: @{const instant_trans_edge} verbatim, with the same (empty) update.\<close>
  have NE: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc edgeit by (rule num_nth_auto_instant_trans_edge[OF n])
  \<comment> \<open>The numeric guard fires on the extended store; the (empty) update fires, preserving tracking.\<close>
  have NB: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  obtain vn' where
      NU: "is_upds vn f vn'"
    and LE: "vp' \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn' x = vn x"
    using is_upds_map_le[OF U le] by blast
  \<comment> \<open>@{const instant_trans_edge} writes nothing (empty update), so tracking survives trivially.\<close>
  have f_eq: "f = []" using edgeit by (simp add: instant_trans_edge_def Let_def)
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
    using f_eq by simp
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound from the propositional post-bound and tracking.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  have fset_sub: "fst ` set f \<subseteq> dom vn" using f_eq by simp
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TR fin vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TR BND by (auto intro: RELI)
qed

text \<open>The three configs produced by one @{const apply_snap_action} block: the @{const start_edge_effect}
post-config @{term s1}, the @{const instant_trans_edge_effect} post-config @{term s2}, and the
@{const end_edge_effect} post-config @{term s3} (the snap block of an instant action runs start, then the
internal start-to-end transition, then end).\<close>
lemma apply_snap_action_unfold:
  "apply_snap_action n s
     = [start_edge_effect n s,
        instant_trans_edge_effect n (start_edge_effect n s),
        end_edge_effect n (instant_trans_edge_effect n (start_edge_effect n s))]"
  unfolding apply_snap_action_def
  by (simp add: seq_apply_def upt_rec)

text \<open>Head-split of @{const apply_instant_actions}: the leading instant index @{term n} contributes its
@{const apply_snap_action} block, and the rest of the run continues from that block's last config.\<close>
lemma apply_instant_actions_Cons:
  "apply_instant_actions (n # ns) s
     = apply_snap_action n s @ apply_instant_actions ns (last (apply_snap_action n s))"
proof -
  have ne: "apply_snap_action n s \<noteq> []" by (simp add: apply_snap_action_unfold)
  have "apply_instant_actions (n # ns) s
          = seq_apply' (apply_snap_action n # map apply_snap_action ns) s"
    by (simp add: apply_instant_actions_def)
  also have "\<dots> = ext_seq' (map apply_snap_action ns) (apply_snap_action n s)"
    by (rule seq_apply'_as_ext_seq'[where f = "apply_snap_action n" and x = s, OF ne])
  also have "\<dots> = apply_snap_action n s @ seq_apply' (map apply_snap_action ns) (last (apply_snap_action n s))"
    by (rule ext_seq'_as_seq_apply')
  also have "\<dots> = apply_snap_action n s @ apply_instant_actions ns (last (apply_snap_action n s))"
    by (simp add: apply_instant_actions_def)
  finally show ?thesis .
qed

text \<open>The propositional per-block structural bundle the instant phase-lift consumes at each
@{const apply_snap_action} block: from the block-entry config @{term c} at action index @{term m}, the
three sub-step source locations (@{const off_loc} at @{term c}, @{const starting_loc} at the
@{const start_edge_effect} post-config, @{const ending_loc} at the @{const instant_trans_edge_effect}
post-config), the lengths, and the @{const net_bounds} bounds of the three post-stores. Bundling it as a
single predicate keeps the kernel-instantiation FIRST-ORDER (the induction matches the predicate symbol,
not a @{text let}-body).\<close>
definition instant_block_struct where
"instant_block_struct c m \<longleftrightarrow>
   (let s1 = start_edge_effect m c;
        s2 = instant_trans_edge_effect m s1;
        s3 = end_edge_effect m s2 in
      fst c ! Suc m = off_loc
      \<and> length (fst c) = length net_automata
      \<and> Simple_Network_Language.bounded (map_of net_bounds) (fst (snd s1))
      \<and> fst s1 ! Suc m = starting_loc
      \<and> length (fst s1) = length net_automata
      \<and> Simple_Network_Language.bounded (map_of net_bounds) (fst (snd s2))
      \<and> fst s2 ! Suc m = ending_loc
      \<and> length (fst s2) = length net_automata
      \<and> Simple_Network_Language.bounded (map_of net_bounds) (fst (snd s3)))"

lemma instant_block_structD:
  assumes "instant_block_struct c m"
  shows "fst c ! Suc m = off_loc"
    and "length (fst c) = length net_automata"
    and "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (start_edge_effect m c)))"
    and "fst (start_edge_effect m c) ! Suc m = starting_loc"
    and "length (fst (start_edge_effect m c)) = length net_automata"
    and "Simple_Network_Language.bounded (map_of net_bounds)
            (fst (snd (instant_trans_edge_effect m (start_edge_effect m c))))"
    and "fst (instant_trans_edge_effect m (start_edge_effect m c)) ! Suc m = ending_loc"
    and "length (fst (instant_trans_edge_effect m (start_edge_effect m c))) = length net_automata"
    and "Simple_Network_Language.bounded (map_of net_bounds)
            (fst (snd (end_edge_effect m (instant_trans_edge_effect m (start_edge_effect m c)))))"
  using assms unfolding instant_block_struct_def Let_def by simp_all
text \<open>The INSTANT phase run-lift, the most complex of the four phase-lifts: each
@{const apply_snap_action} block both fires THREE numeric edges (start, the internal start-to-end
duration transition, end) AND advances the abstract numeric fold by TWO snaps, @{term \<open>at_start (actions ! n)\<close>}
then @{term \<open>at_end (actions ! n)\<close>} (the internal duration transition writes nothing). By induction on the
index suffix @{term ns}, threading the running propositional config @{term sp}, the running numeric store,
and the accumulated snap prefix @{term ys}. The three per-block kernels are
@{thm [source] num_edge_upd_step_lift} (start, fold += @{term \<open>at_start (actions ! n)\<close>}),
@{thm [source] num_instant_trans_step_lift} (the no-write internal step, fold unchanged), and
@{thm [source] num_edge_upd_step_lift_end} (end, fold += @{term \<open>at_end (actions ! n)\<close>}). For an INSTANT
index @{term n} BOTH @{term \<open>at_start (actions ! n)\<close>} and @{term \<open>at_end (actions ! n)\<close>} are in happening
@{term i} (it satisfies @{const is_instant_index}, which @{thm [source] happ_at_index_decomp} places in the
starting-or-instant image AND the ending-or-instant image). The propositional per-block structural facts
(the @{const off_loc} / @{const starting_loc} / @{const ending_loc} source locations at the three
sub-configs, the lengths, the projection bounds on the three post-stores) are supplied per run-position by
the caller hypothesis @{text struct}.\<close>
lemma num_instant_phase_lift:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
  assumes ns_inst: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions
                            \<and> is_instant_index (planning_sem.time_index i) n"
      and ys_act: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and zs_dist: "distinct (ys @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns) @ zs)"
      and zs_full: "set (ys @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns) @ zs)
                      = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and prun: "graph_impl.steps (sp # apply_instant_actions ns sp)"
      and struct: "\<And>k. k < length ns \<Longrightarrow>
                     instant_block_struct ((sp # apply_instant_actions ns sp) ! (3 * k)) (ns ! k)"
      and rel0: "RELC sp cn (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
    shows "\<exists>nss. num_graph_impl.steps (cn # nss)
                 \<and> length nss = length (apply_instant_actions ns sp)
                 \<and> RELC (last (sp # apply_instant_actions ns sp)) (last (cn # nss))
                        (num_plan.num_rat_impl.happening_num_update
                           (ys @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns)) (snd (M i)))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  let ?snaps = "\<lambda>ns. concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns)"
  have base_val_ok: "num_val_ok (snd (M i))"
    using i by (intro num_seq_val_ok[OF vss m0]) simp
  \<comment> \<open>The generalized inductive claim over any instant-index suffix @{term as}, running config @{term s},
     accumulated snap-prefix @{term bs} (a distinct happening-sublist), residual @{term cs}.\<close>
  have gen: "\<exists>nss. num_graph_impl.steps (dn # nss)
                   \<and> length nss = length (apply_instant_actions as s)
                   \<and> RELC (last (s # apply_instant_actions as s)) (last (dn # nss))
                          (?w (bs @ ?snaps as))"
    if as_inst: "\<And>n. n \<in> set as \<Longrightarrow> n < length actions
                          \<and> is_instant_index (planning_sem.time_index i) n"
       and bs_act: "\<And>t. t \<in> set bs \<Longrightarrow> \<exists>a \<in> set actions. t = at_start a \<or> t = at_end a"
       and bs_sub: "set bs \<subseteq> ?S"
       and cs_dist: "distinct (bs @ ?snaps as @ cs)"
       and cs_full: "set (bs @ ?snaps as @ cs) = ?S"
       and srun: "graph_impl.steps (s # apply_instant_actions as s)"
       and sstruct: "\<And>k. k < length as \<Longrightarrow>
                       instant_block_struct ((s # apply_instant_actions as s) ! (3 * k)) (as ! k)"
       and srel: "RELC s dn (?w bs)"
     for as s dn bs cs
    using that
  proof (induction as arbitrary: s dn bs cs)
    case Nil
    show ?case
    proof (intro exI[where x = "[]"] conjI)
      show "num_graph_impl.steps (dn # [])" by (rule num_graph_impl.steps.intros(1))
    next
      show "length [] = length (apply_instant_actions [] s)"
        by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil)
    next
      show "RELC (last (s # apply_instant_actions [] s)) (last (dn # []))
                 (?w (bs @ ?snaps []))"
        by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil) (rule Nil.prems(8))
    qed
  next
    case (Cons n as')
    let ?sst = "at_start (actions ! n)"
    let ?sen = "at_end (actions ! n)"
    \<comment> \<open>The block configs.\<close>
    let ?s1 = "start_edge_effect n s"
    let ?s2 = "instant_trans_edge_effect n ?s1"
    let ?s3 = "end_edge_effect n ?s2"
    \<comment> \<open>Decompose the running config and the @{const RELC}-related numeric start.\<close>
    obtain L vp c where s: "s = (L, vp, c)" by (cases s)
    obtain Ln dvn cn0 where dn: "dn = (Ln, dvn, cn0)" by (cases dn)
    have Leq: "Ln = L" by (rule RELC_locD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have ceq: "cn0 = c" by (rule RELC_clkD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have relS: "REL vp dvn (?w bs)" by (rule RELC_relD[OF Cons.prems(8)[unfolded s dn]])
    \<comment> \<open>Head index facts.\<close>
    have nmem: "n \<in> set (n # as')" by simp
    have n_lt: "n < length actions"
      and n_inst: "is_instant_index (planning_sem.time_index i) n"
      using Cons.prems(1)[OF nmem] by blast+
    have aMem: "actions ! n \<in> set actions" using n_lt by simp
    \<comment> \<open>An INSTANT index lands in BOTH images: at-start and at-end snaps are both in happening @{term i}.\<close>
    have sst_mem: "?sst \<in> ?S"
      unfolding happ_at_index_decomp using n_lt n_inst by blast
    have sen_mem: "?sen \<in> ?S"
      unfolding happ_at_index_decomp using n_lt n_inst by blast
    \<comment> \<open>Run decomposition: the block and the tail run.\<close>
    have last_snap: "last (apply_snap_action n s) = ?s3"
      by (simp add: apply_snap_action_unfold)
    have run_unfold: "s # apply_instant_actions (n # as') s
                        = s # ?s1 # ?s2 # ?s3 # apply_instant_actions as' ?s3"
      apply (subst apply_instant_actions_Cons)
      apply (subst last_snap)
      apply (subst apply_snap_action_unfold)
      by simp
    have run_dec: "graph_impl.steps (s # ?s1 # ?s2 # ?s3 # apply_instant_actions as' ?s3)"
      using Cons.prems(6) run_unfold by simp
    have tail1: "graph_impl.steps (?s1 # ?s2 # ?s3 # apply_instant_actions as' ?s3)"
      using run_dec by (rule graph_impl.steps_ConsD) simp
    have tail2: "graph_impl.steps (?s2 # ?s3 # apply_instant_actions as' ?s3)"
      using tail1 by (rule graph_impl.steps_ConsD) simp
    have tailrun: "graph_impl.steps (?s3 # apply_instant_actions as' ?s3)"
      using tail2 by (rule graph_impl.steps_ConsD) simp
    \<comment> \<open>The three propositional sub-steps of the block.\<close>
    have pstep0: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst ?s1, fst (snd ?s1), snd (snd ?s1)\<rangle>"
      using run_dec unfolding s by (cases ?s1) (auto elim: graph_impl.steps.cases simp: prod.case)
    have pstep1: "net_impl.sem \<turnstile> \<langle>fst ?s1, fst (snd ?s1), snd (snd ?s1)\<rangle> \<rightarrow> \<langle>fst ?s2, fst (snd ?s2), snd (snd ?s2)\<rangle>"
      using run_dec by (cases ?s1; cases ?s2) (auto elim: graph_impl.steps.cases simp: prod.case)
    have pstep2: "net_impl.sem \<turnstile> \<langle>fst ?s2, fst (snd ?s2), snd (snd ?s2)\<rangle> \<rightarrow> \<langle>fst ?s3, fst (snd ?s3), snd (snd ?s3)\<rangle>"
      using run_dec by (cases ?s2; cases ?s3) (auto elim: graph_impl.steps.cases simp: prod.case)
    \<comment> \<open>The structural facts at run-position 0 (block 0 entry config @{term s}).\<close>
    have ibs0: "instant_block_struct s n"
      using Cons.prems(7)[of 0] by simp
    note struct0 = instant_block_structD[OF ibs0]
    have off0: "L ! Suc n = off_loc" using struct0(1) unfolding s by simp
    have Llen0: "length L = length net_automata" using struct0(2) unfolding s by simp
    \<comment> \<open>The new accumulated snap-prefixes and the list-shape rearrangement re-targeting the IH premises.\<close>
    define bs1 where "bs1 = bs @ [?sst]"
    define bs2 where "bs2 = bs @ [?sst, ?sen]"
    have snaps_Cons: "?snaps (n # as') = ?sst # ?sen # ?snaps as'" by simp
    have list_rearr: "bs @ ?snaps (n # as') @ cs = bs2 @ ?snaps as' @ cs"
      unfolding bs2_def snaps_Cons by simp
    have cs_dist': "distinct (bs2 @ ?snaps as' @ cs)"
      using Cons.prems(4)[unfolded list_rearr] .
    have cs_full': "set (bs2 @ ?snaps as' @ cs) = ?S"
      using Cons.prems(5)[unfolded list_rearr] .
    \<comment> \<open>The intermediate prefix @{term bs1} fullness/distinctness, with @{term \<open>?sen # ?snaps as'\<close>} residual.\<close>
    have list_rearr1: "bs @ ?snaps (n # as') @ cs = bs1 @ (?sen # ?snaps as' @ cs)"
      unfolding bs1_def snaps_Cons by simp
    have cs_dist1: "distinct (bs1 @ (?sen # ?snaps as' @ cs))"
      using Cons.prems(4)[unfolded list_rearr1] .
    have cs_full1: "set (bs1 @ (?sen # ?snaps as' @ cs)) = ?S"
      using Cons.prems(5)[unfolded list_rearr1] .
    \<comment> \<open>The snaps are fresh of the already-folded prefixes.\<close>
    have sst_notin_bs: "?sst \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr1[symmetric] snaps_Cons)
    have sen_notin_bs: "?sen \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr1[symmetric] snaps_Cons)
    have sen_ne_sst: "?sen \<noteq> ?sst"
      using Cons.prems(4) by (auto simp add: list_rearr1[symmetric] snaps_Cons)
    have sen_notin_bs1: "?sen \<notin> set bs1"
      using sen_notin_bs sen_ne_sst unfolding bs1_def by simp
    \<comment> \<open>The fold-append identities (the @{const fold} LANDMINE: rewrite via @{thm [source] fold_append}).\<close>
    have foldapp_st: "num_plan.num_rat_impl.snap_num_update ?sst (?w bs) = ?w bs1"
      unfolding bs1_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append) (simp add: comp_def)
    have foldapp_en: "num_plan.num_rat_impl.snap_num_update ?sen (?w bs1) = ?w bs2"
      unfolding bs2_def bs1_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append)+ (simp add: comp_def)
    \<comment> \<open>The kernel hypotheses for the START snap at @{term \<open>?w bs\<close>}.\<close>
    have wok: "num_val_ok (?w bs)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok Cons.prems(2)])
    have fin_st: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sst (?w bs))"
      unfolding foldapp_st by (rule running_prefix_in_bounds[OF vss m0 i cs_dist1 cs_full1])
    have sat_st_eq: "sat_comps (?w bs) (set (n_pre ?sst)) = sat_comps (snd (M i)) (set (n_pre ?sst))"
      by (rule sat_comps_running_prefix[OF sst_mem Cons.prems(3) sst_notin_bs])
    have sat_st: "sat_comps (?w bs) (set (n_pre ?sst))"
      unfolding sat_st_eq by (rule happening_snap_pre_sat[OF vss i sst_mem])
    have upd_lhs_st: "fst ` set (upds ?sst) \<subseteq> set nfluents"
      using snap_writes_nfluents_start aMem by blast
    \<comment> \<open>Apply the START kernel: @{term ?sst} edge lifts to a numeric step from @{term dn} to @{term d1}.\<close>
    have L'eq0: "fst ?s1 = fst (start_edge_effect n (L, vp, c))" unfolding s by simp
    obtain vn1 where
        numstep0: "num_net_impl.sem \<turnstile> \<langle>L, dvn, c\<rangle> \<rightarrow> \<langle>fst ?s1, vn1, snd (snd ?s1)\<rangle>"
      and relE0: "REL (fst (snd ?s1)) vn1 (num_plan.num_rat_impl.snap_num_update ?sst (?w bs))"
      using num_edge_upd_step_lift[OF relS Llen0 off0 n_lt HOL.refl sst_mem
              pstep0 L'eq0 struct0(3) wok fin_st sat_st upd_lhs_st]
      by blast
    have rel1: "REL (fst (snd ?s1)) vn1 (?w bs1)" using relE0[unfolded foldapp_st] .
    \<comment> \<open>Apply the INSTANT-TRANS kernel: @{term ?s1} to @{term ?s2}, fold UNCHANGED.\<close>
    have starting1: "fst ?s1 ! Suc n = starting_loc" using struct0(4) .
    have Llen1: "length (fst ?s1) = length net_automata" using struct0(5) .
    have fin1: "fluent_in_bounds (?w bs1)"
      using fin_st[unfolded foldapp_st] .
    have L'eq1: "fst ?s2 = fst (instant_trans_edge_effect n (fst ?s1, fst (snd ?s1), snd (snd ?s1)))"
      by simp
    obtain vn2 where
        numstep1: "num_net_impl.sem \<turnstile> \<langle>fst ?s1, vn1, snd (snd ?s1)\<rangle> \<rightarrow> \<langle>fst ?s2, vn2, snd (snd ?s2)\<rangle>"
      and rel2: "REL (fst (snd ?s2)) vn2 (?w bs1)"
      using num_instant_trans_step_lift[OF rel1 Llen1 starting1 n_lt pstep1 L'eq1 struct0(6) fin1]
      by blast
    \<comment> \<open>Kernel hypotheses for the END snap at @{term \<open>?w bs1\<close>}.\<close>
    have bs1_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs1" for t
      using that aMem Cons.prems(2) unfolding bs1_def by auto
    have wok1: "num_val_ok (?w bs1)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok bs1_act])
    have fin_en: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sen (?w bs1))"
      unfolding foldapp_en by (rule running_prefix_in_bounds[OF vss m0 i cs_dist' cs_full'])
    have bs1_sub: "set bs1 \<subseteq> ?S" using Cons.prems(3) sst_mem unfolding bs1_def by auto
    have sat_en_eq: "sat_comps (?w bs1) (set (n_pre ?sen)) = sat_comps (snd (M i)) (set (n_pre ?sen))"
      by (rule sat_comps_running_prefix[OF sen_mem bs1_sub sen_notin_bs1])
    have sat_en: "sat_comps (?w bs1) (set (n_pre ?sen))"
      unfolding sat_en_eq by (rule happening_snap_pre_sat[OF vss i sen_mem])
    have upd_lhs_en: "fst ` set (upds ?sen) \<subseteq> set nfluents"
      using snap_writes_nfluents_end aMem by blast
    \<comment> \<open>Apply the END kernel: @{term ?s2} to @{term ?s3}, fold += @{term ?sen}.\<close>
    have ending2: "fst ?s2 ! Suc n = ending_loc" using struct0(7) .
    have Llen2: "length (fst ?s2) = length net_automata" using struct0(8) .
    have L'eq2: "fst ?s3 = fst (end_edge_effect n (fst ?s2, fst (snd ?s2), snd (snd ?s2)))"
      by simp
    obtain vn3 where
        numstep2: "num_net_impl.sem \<turnstile> \<langle>fst ?s2, vn2, snd (snd ?s2)\<rangle> \<rightarrow> \<langle>fst ?s3, vn3, snd (snd ?s3)\<rangle>"
      and relE2: "REL (fst (snd ?s3)) vn3 (num_plan.num_rat_impl.snap_num_update ?sen (?w bs1))"
      using num_edge_upd_step_lift_end[OF rel2 Llen2 ending2 n_lt HOL.refl sen_mem
              pstep2 L'eq2 struct0(9) wok1 fin_en sat_en upd_lhs_en] by blast
    have rel3: "REL (fst (snd ?s3)) vn3 (?w bs2)" using relE2[unfolded foldapp_en] .
    \<comment> \<open>Package the numeric block-configs.\<close>
    obtain L1 vp1 c1 where s1eq: "?s1 = (L1, vp1, c1)" by (cases ?s1)
    obtain L2 vp2 c2 where s2eq: "?s2 = (L2, vp2, c2)" by (cases ?s2)
    obtain L3 vp3 c3 where s3eq: "?s3 = (L3, vp3, c3)" by (cases ?s3)
    define d1 where "d1 = (L1, vn1, c1)"
    define d2 where "d2 = (L2, vn2, c2)"
    define d3 where "d3 = (L3, vn3, c3)"
    have relC3: "RELC ?s3 d3 (?w bs2)"
      unfolding d3_def s3eq using RELCI[OF rel3] unfolding s3eq by simp
    \<comment> \<open>The three numeric steps, as single-step runs.\<close>
    have step_st: "num_graph_impl.steps [dn, d1]"
      unfolding dn d1_def Leq ceq
      by (rule num_single_step_intro) (use numstep0 s1eq in \<open>simp add: prod.case\<close>)
    have step_it: "num_graph_impl.steps [d1, d2]"
      unfolding d1_def d2_def
      by (rule num_single_step_intro)
         (use numstep1 s1eq s2eq in \<open>simp add: prod.case\<close>)
    have step_en: "num_graph_impl.steps [d2, d3]"
      unfolding d2_def d3_def
      by (rule num_single_step_intro)
         (use numstep2 s2eq s3eq in \<open>simp add: prod.case\<close>)
    have headblock: "num_graph_impl.steps [dn, d1, d2, d3]"
      using num_steps_extend[OF step_st] num_steps_extend[OF step_it] step_en by simp
    \<comment> \<open>IH premises for the tail suffix @{term as'} from @{term ?s3}, @{term d3}, @{term bs2}.\<close>
    have as'_inst: "m < length actions \<and> is_instant_index (planning_sem.time_index i) m"
      if "m \<in> set as'" for m
      using Cons.prems(1) that by simp
    have bs2_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs2" for t
      using that aMem Cons.prems(2) unfolding bs2_def by auto
    have bs2_sub: "set bs2 \<subseteq> ?S"
      using Cons.prems(3) sst_mem sen_mem unfolding bs2_def by auto
    \<comment> \<open>Re-index the per-block structural premise: block @{term k} of the tail is block @{term \<open>Suc k\<close>}
       of the full run (position @{term \<open>3 * k\<close>} of the tail = position @{term \<open>3 * Suc k\<close>} of the full run).\<close>
    have sstruct':
        "instant_block_struct ((?s3 # apply_instant_actions as' ?s3) ! (3 * k)) (as' ! k)"
      if k: "k < length as'" for k
    proof -
      have Sk: "Suc k < length (n # as')" using k by simp
      have idx: "(s # apply_instant_actions (n # as') s) ! (3 * Suc k)
                   = (?s3 # apply_instant_actions as' ?s3) ! (3 * k)"
        unfolding run_unfold by (simp add: numeral_3_eq_3)
      have m_idx: "(n # as') ! Suc k = as' ! k" by simp
      show ?thesis using Cons.prems(7)[OF Sk] unfolding idx m_idx .
    qed
    \<comment> \<open>Abbreviate the (large) block-end config so the IH instantiation stays first-order.\<close>
    define t3 where "t3 = ?s3"
    have as'_inst_t: "\<And>m. m \<in> set as' \<Longrightarrow> m < length actions
                            \<and> is_instant_index (planning_sem.time_index i) m"
      using as'_inst by blast
    have tailrun_t: "graph_impl.steps (t3 # apply_instant_actions as' t3)"
      unfolding t3_def by (rule tailrun)
    have sstruct_t: "\<And>k. k < length as' \<Longrightarrow>
                       instant_block_struct ((t3 # apply_instant_actions as' t3) ! (3 * k)) (as' ! k)"
      unfolding t3_def using sstruct' by blast
    have relC3_t: "RELC t3 d3 (?w bs2)" unfolding t3_def by (rule relC3)
    have ih: "\<exists>nss. num_graph_impl.steps (d3 # nss)
                   \<and> length nss = length (apply_instant_actions as' t3)
                   \<and> RELC (last (t3 # apply_instant_actions as' t3)) (last (d3 # nss))
                          (?w (bs2 @ ?snaps as'))"
      by (rule Cons.IH[OF as'_inst_t bs2_act bs2_sub cs_dist' cs_full' tailrun_t sstruct_t relC3_t])
    obtain nss' where
        nrun': "num_graph_impl.steps (d3 # nss')"
      and lnss': "length nss' = length (apply_instant_actions as' ?s3)"
      and rlast': "RELC (last (?s3 # apply_instant_actions as' ?s3)) (last (d3 # nss'))
                        (?w (bs2 @ ?snaps as'))"
      using ih unfolding t3_def by (elim exE conjE)
    \<comment> \<open>Splice the head block in front of the tail numeric run.\<close>
    have spliced: "num_graph_impl.steps (dn # d1 # d2 # d3 # nss')"
      using num_steps_extend[OF headblock] nrun' by simp
    show ?case
    proof (intro exI[where x = "d1 # d2 # d3 # nss'"] conjI)
      show "num_graph_impl.steps (dn # d1 # d2 # d3 # nss')" by (rule spliced)
    next
      have len_block: "length (apply_instant_actions (n # as') s)
                         = 3 + length (apply_instant_actions as' ?s3)"
        using run_unfold by (simp del: apply_instant_actions_Cons)
      show "length (d1 # d2 # d3 # nss') = length (apply_instant_actions (n # as') s)"
        using lnss' len_block by simp
    next
      have bsrew: "bs2 @ ?snaps as' = bs @ ?snaps (n # as')"
        unfolding bs2_def snaps_Cons by simp
      have lastrew: "last (s # apply_instant_actions (n # as') s)
                       = last (?s3 # apply_instant_actions as' ?s3)"
        unfolding run_unfold by simp
      have lastnum: "last (dn # d1 # d2 # d3 # nss') = last (d3 # nss')" by simp
      show "RELC (last (s # apply_instant_actions (n # as') s)) (last (dn # d1 # d2 # d3 # nss'))
                 (?w (bs @ ?snaps (n # as')))"
        using rlast' unfolding lastrew lastnum bsrew by simp
    qed
  qed
  show ?thesis
    by (rule gen[OF ns_inst ys_act ys_sub zs_dist zs_full prun struct rel0])
qed

text \<open>The relational lift predicate carried by the numeric run-lift's structural combinator. As a
predicate on the PROPOSITIONAL config-list @{term ps}, @{term \<open>RLP w ps\<close>} says: WHEN @{term ps} is a
propositional run, then for EVERY numeric start config @{const RELC}-related to its head there is a
numeric run of the same length whose last config is @{const RELC}-related to @{term \<open>last ps\<close>}. The
universal quantification over the numeric start is what makes the combinator's @{text step} splice
compose: the first sub-run's @{const RELC}-related endpoint is fed as the second sub-run's start.\<close>
definition RLP where
"RLP w ps \<longleftrightarrow> ps \<noteq> [] \<and> (graph_impl.steps ps \<longrightarrow>
   (\<forall>cn. RELC (hd ps) cn w \<longrightarrow>
      (\<exists>nss. num_graph_impl.steps (cn # nss)
             \<and> length nss = length ps - 1
             \<and> RELC (last ps) (last (cn # nss)) w)))"

lemma RLP_base: "RLP w [x]"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "[x] \<noteq> []" by simp
next
  fix cn assume "RELC (hd [x]) cn w"
  hence "RELC (last [x]) (last (cn # [])) w" by simp
  thus "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length [x] - 1 \<and> RELC (last [x]) (last (cn # nss)) w"
    by (intro exI[where x = "[]"]) (auto intro: num_graph_impl.steps.intros(1))
qed

lemma RLP_step:
  assumes RX: "RLP w xs"
      and RY: "RLP w (last xs # ys)"
      and xs: "xs \<noteq> []"
  shows "RLP w (xs @ ys)"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "xs @ ys \<noteq> []" using xs by simp
next
  fix cn
  assume steps: "graph_impl.steps (xs @ ys)"
     and relhd: "RELC (hd (xs @ ys)) cn w"
  show "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length (xs @ ys) - 1
              \<and> RELC (last (xs @ ys)) (last (cn # nss)) w"
  proof (cases "ys = []")
    case True
    have stepsX: "graph_impl.steps xs" using steps True by simp
    have rhd: "RELC (hd xs) cn w" using relhd True xs by simp
    obtain nss where
        nss: "num_graph_impl.steps (cn # nss)"
      and lnss: "length nss = length xs - 1"
      and rlast: "RELC (last xs) (last (cn # nss)) w"
      using conjunct2[OF RX[unfolded RLP_def], rule_format, OF stepsX rhd] by blast
    show ?thesis
      apply (intro exI[where x = nss] conjI)
      subgoal by (rule nss)
      subgoal using lnss True by simp
      subgoal using rlast True by simp
      done
  next
    case False
    have stepsX: "graph_impl.steps xs" by (rule graph_impl.steps_appendD1[OF steps xs])
    have stepsY: "graph_impl.steps ys" by (rule graph_impl.steps_appendD2[OF steps False])
    have edge: "(case last xs of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). net_impl.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (hd ys)"
      using graph_impl.steps_decomp[OF steps xs False] by simp
    have stepsLY: "graph_impl.steps (last xs # ys)"
      using False edge stepsY by (cases ys) (auto intro: graph_impl.steps.intros)
    \<comment> \<open>First sub-run from @{term cn}.\<close>
    have rhd: "RELC (hd xs) cn w" using relhd xs by simp
    obtain nss1 where
        nss1: "num_graph_impl.steps (cn # nss1)"
      and lnss1: "length nss1 = length xs - 1"
      and rmid: "RELC (last xs) (last (cn # nss1)) w"
      using conjunct2[OF RX[unfolded RLP_def], rule_format, OF stepsX rhd] by blast
    \<comment> \<open>Second sub-run from the @{const RELC}-related endpoint @{term \<open>last (cn # nss1)\<close>}.\<close>
    have relmid: "RELC (hd (last xs # ys)) (last (cn # nss1)) w" using rmid by simp
    obtain nss2 where
        nss2: "num_graph_impl.steps (last (cn # nss1) # nss2)"
      and lnss2: "length nss2 = length (last xs # ys) - 1"
      and rlast2: "RELC (last (last xs # ys)) (last (last (cn # nss1) # nss2)) w"
      using conjunct2[OF RY[unfolded RLP_def], rule_format, OF stepsLY relmid] by blast
    \<comment> \<open>Splice.\<close>
    have spliced: "num_graph_impl.steps ((cn # nss1) @ nss2)"
      by (rule num_steps_extend[OF nss1]) (use nss2 in simp)
    have nss2_ne: "nss2 \<noteq> []" using lnss2 False by (cases ys) auto
    have last_eq: "last ((cn # nss1) @ nss2) = last (last (cn # nss1) # nss2)"
      using nss2_ne by simp
    have last_ys: "last (last xs # ys) = last (xs @ ys)" using False xs by simp
    have len_eq: "length (nss1 @ nss2) = length (xs @ ys) - 1"
      using lnss1 lnss2 xs False by auto
    show ?thesis
      apply (intro exI[where x = "nss1 @ nss2"] conjI)
      subgoal using spliced by simp
      subgoal by (rule len_eq)
      subgoal using rlast2 last_eq last_ys by simp
      done
  qed
qed

text \<open>The per-step kernel, packaged in the @{const RLP} shape the structural combinator's @{text PQ}
case consumes: ONE @{const edge_3} step of the propositional run lifts to a single numeric step
preserving @{const RELC}. The required propositional pre-facts (the @{const running_loc} source
location and @{term \<open>n < length actions\<close>}) and the propositional post-bound are supplied by the
phase's @{const end_start_pre} invariant / @{const LvP} threading; @{term \<open>fluent_in_bounds w\<close>} comes
from the numeric valid-state sequence. The propositional step itself is the antecedent of @{const RLP},
so it is consumed -- not re-derived.\<close>
lemma RLP_edge_3_single:
  assumes run: "fst s ! Suc n = running_loc"
      and n: "n < length actions"
      and Llen: "length (fst s) = length net_automata"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (edge_3_effect n s)))"
      and fin: "fluent_in_bounds w"
    shows "RLP w [s, edge_3_effect n s]"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "[s, edge_3_effect n s] \<noteq> []" by simp
next
  fix cn
  assume pstep: "graph_impl.steps [s, edge_3_effect n s]"
     and relhd: "RELC (hd [s, edge_3_effect n s]) cn w"
  obtain L vp c where s: "s = (L, vp, c)" by (cases s)
  obtain L' vp' c' where t: "edge_3_effect n s = (L', vp', c')" by (cases "edge_3_effect n s")
  obtain Ln vn cnn where cn: "cn = (Ln, vn, cnn)" by (cases cn)
  have Leq: "Ln = L" and ceq: "cnn = c" and relS: "REL vp vn w"
    using relhd unfolding s cn list.sel by (auto dest: RELC_locD RELC_clkD RELC_relD)
  \<comment> \<open>The propositional single step, extracted from the antecedent.\<close>
  have t2: "edge_3_effect n (L, vp, c) = (L', vp', c')" using t unfolding s by simp
  have step1: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using pstep unfolding s t2 by (auto elim: graph_impl.steps.cases)
  have L'fst: "L' = fst (edge_3_effect n (L, vp, c))" using t unfolding s by simp
  have pbnd2: "Simple_Network_Language.bounded (map_of net_bounds) vp'" using pbnd' unfolding t by simp
  have run2: "L ! Suc n = running_loc" using run unfolding s by simp
  have Llen2: "length L = length net_automata" using Llen unfolding s by simp
  obtain vn' where
      numstep: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    and relE: "REL vp' vn' w"
    using num_edge_3_step_lift[OF relS Llen2 run2 n step1 L'fst pbnd2 fin] by blast
  have "num_graph_impl.steps [cn, (L', vn', c')]"
    unfolding cn Leq ceq by (rule num_single_step_intro) (use numstep in \<open>simp add: prod.case\<close>)
  moreover have "RELC (edge_3_effect n s) (L', vn', c') w"
    unfolding t by (rule RELCI[OF relE])
  ultimately show "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length [s, edge_3_effect n s] - 1
                         \<and> RELC (last [s, edge_3_effect n s]) (last (cn # nss)) w"
    by (intro exI[where x = "[(L', vn', c')]"]) (simp add: t)
qed

text \<open>@{const RLP} satisfies the @{locale sequence_rules} composition laws (singleton @{thm [source]
RLP_base} and the splice @{thm [source] RLP_step}), so the @{emph \<open>relational\<close>} run-lift predicate
plugs into the same structural combinator @{const num_graph_impl.steps} uses. This is the numeric
mirror of @{thm [source] steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable}, but threading
@{const RELC} instead of the propositional happening invariants.\<close>
lemma RLP_neD: "RLP w ps \<Longrightarrow> ps \<noteq> []"
  unfolding RLP_def by blast

lemma RLP_sequence_rules: "sequence_rules (RLP w)"
proof (unfold_locales)
  show "RLP w [x]" for x by (rule RLP_base)
next
  fix xs ys
  assume a: "RLP w xs" and b: "RLP w (last xs # ys)"
  show "RLP w (xs @ ys)" by (rule RLP_step[OF a b RLP_neD[OF a]])
qed

text \<open>The @{const edge_3} phase-lift, via the structural combinator. The propositional happening run
through the @{const edge_3} phase is GIVEN (its existence is the @{const RLP} antecedent fired by the
combinator per step); the per-step @{const edge_3} kernel @{thm [source] RLP_edge_3_single} discharges
the combinator's @{text PQ} obligation under a propositional pre/post invariant pair @{term P} / @{term
Q} that the CALLER threads (in the run-lift this is the @{const end_start_pre} / @{const end_start_post}
bookkeeping established by @{thm [source] end_starts_possible}). Given @{const RELC} at the start config,
the result is a numeric run @{const RELC}-related at the end.\<close>
lemma num_edge_3_phase_lift:
  fixes P Q :: "nat \<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool"
  assumes R0: "RLP w xs \<and> R (last xs)"
      and PQ: "\<And>j s. j < length ns \<Longrightarrow> P j s \<Longrightarrow> Q j (edge_3_effect (ns ! j) s) \<and> RLP w [s, edge_3_effect (ns ! j) s]"
      and QP: "\<And>j s. Suc j < length ns \<Longrightarrow> Q j s \<Longrightarrow> P (Suc j) s"
      and RP0: "\<And>x. 0 < length ns \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. 0 < length ns \<Longrightarrow> Q (length ns - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. length ns = 0 \<Longrightarrow> R x \<Longrightarrow> S x"
      and SR': "\<And>x. S x \<Longrightarrow> R' x"
    shows "RLP w ((ext_seq \<circ> seq_apply) (map edge_3_effect ns) xs)
           \<and> R' (last ((ext_seq \<circ> seq_apply) (map edge_3_effect ns) xs))"
  by (rule sequence_rules.ext_seq_comp_seq_apply_induct_list_prop_composable[
            OF RLP_sequence_rules,
            where R = R and P = P and Q = Q and S = S and R' = R' and fs = "map edge_3_effect ns",
            simplified length_map nth_map, OF R0])
     (use PQ QP RP0 QSl RS0 SR' in blast)+

text \<open>The @{const starting_loc} source location is shared by @{const edge_2} (target @{const running_loc})
and @{const instant_trans_edge} (target @{const ending_loc}); among the five edges of an action automaton
these are the only two leaving @{const starting_loc}. So a propositional internal step from a config whose
@{term \<open>Suc n\<close>}-th location is @{const starting_loc} AND whose fired edge targets @{const running_loc} must
have fired @{const edge_2} at automaton @{term \<open>Suc n\<close>} (the target distinguishes it from
@{const instant_trans_edge}).\<close>
lemma prop_edge_2_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and start0: "L ! Suc n = starting_loc"
      and tgt: "l' = running_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = edge_2 (actions ! n)"
proof -
  have l_start: "l = starting_loc" using Lp start0 pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_start tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel for the EDGE_2 internal step: lifting ONE propositional
@{const edge_2} step (the @{const starting_loc} \<rightarrow> @{const running_loc} running-entry edge) to a numeric
@{const num_graph_impl.steps} step, preserving @{const REL}. The structure mirrors
@{thm [source] num_edge_3_step_lift}: @{const edge_2} writes only the propositional @{const prop_to_lock}
over_all variables (fresh of the fluents), so the abstract valuation @{term w} is UNCHANGED and tracking
survives. The numeric edge is the AUGMENTED @{const num_edge_2}, which conjoins the numeric over_all guard
@{const num_inv_guard} (and appends no update). Discharging that extra numeric guard is the only difference
from the @{const edge_3} kernel: it needs the over_all comparisons to be @{const comp_ok} at @{term w}
(from @{thm [source] snap_inv_comp_ok} under @{const num_val_ok}) and @{const sat_comps}-satisfied at
@{term w} -- the latter is the deferred active-action over_all fact, supplied as @{text sat_inv} (it is
@{const True} vacuously when @{term \<open>n_inv (actions ! n) = []\<close>}, the common benchmark case).\<close>
lemma num_edge_2_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and start0: "L ! Suc n = starting_loc"
      and n: "n < length actions"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (edge_2_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and fin: "fluent_in_bounds w"
      and wok: "num_val_ok w"
      and sat_inv: "sat_comps w (set (n_inv (actions ! n)))"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle> \<and> REL vp' vn' w"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have aMem: "actions ! n \<in> set actions" using n by simp
  have L'_eq: "L' = L[Suc n := running_loc]"
    using L'eq by (simp add: edge_2_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const edge_2}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}.\<close>
  have starting_ne_running: "starting_loc \<noteq> running_loc" by (simp add: locations_unique)
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    moreover have "L[Suc n := running_loc] ! Suc n = running_loc" using Sn_lt by simp
    ultimately show False using L'eq2 L'_eq start0 starting_ne_running by simp
  qed
  \<comment> \<open>The fired edge targets @{const running_loc}: position @{term \<open>Suc n\<close>} of the post locations.\<close>
  have tgt: "l' = running_loc"
  proof -
    have "L[p := l'] ! Suc n = l'" using pSuc Sn_lt by simp
    moreover have "L[Suc n := running_loc] ! Suc n = running_loc" using Sn_lt by simp
    ultimately show ?thesis using L'eq2 L'_eq by simp
  qed
  have edge2: "(l, b, g, Sil a, f, r, l') = edge_2 (actions ! n)"
    by (rule prop_edge_2_pinned[OF P E LOC start0 tgt n pSuc])
  \<comment> \<open>The numeric edge: the AUGMENTED @{const num_edge_2}, with the conjoined @{const num_inv_guard}.\<close>
  have NE: "num_edge_2 (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc by (rule num_nth_auto_num_edge_2[OF n])
  \<comment> \<open>The numeric edge's components, read off @{const num_edge_2}: same source/target/clocks/reset/update
     as @{const edge_2}, with the guard conjoined with @{const num_inv_guard}.\<close>
  have ne_eq: "num_edge_2 (actions ! n) = (l, bexp.and b (num_inv_guard (actions ! n)), g, Sil a, f, r, l')"
    unfolding num_edge_2_def augment_edge_def edge2[symmetric] by simp
  have NEassembled: "(l, bexp.and b (num_inv_guard (actions ! n)), g, Sil a, f, r, l')
                       \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    using NE unfolding ne_eq .
  \<comment> \<open>The combined numeric guard fires on the extended store: the propositional half by monotonicity,
     the numeric over_all half by @{thm [source] check_bexp_comps_guard}.\<close>
  have NBprop: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have inv_ok: "\<forall>cc \<in> set (n_inv (actions ! n)). comp_ok w cc"
    using snap_inv_comp_ok aMem wok by blast
  have NBinv: "check_bexp vn (num_inv_guard (actions ! n)) True"
    unfolding num_inv_guard_def by (rule check_bexp_comps_guard[OF tr inv_ok sat_inv])
  have NB: "check_bexp vn (bexp.and b (num_inv_guard (actions ! n))) True"
    using check_bexp_is_val.intros(3)[OF NBprop NBinv] by simp
  \<comment> \<open>The (propositional) update fires on the extended store, preserving tracking.\<close>
  obtain vn' where
      NU: "is_upds vn f vn'"
    and LE: "vp' \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn' x = vn x"
    using is_upds_map_le[OF U le] by blast
  \<comment> \<open>@{const edge_2} writes only @{const prop_to_lock} variables, fresh of the fluents, so tracking
     survives.\<close>
  have f_eq: "f = map (inc_prop_lock_ab 1) (over_all (actions ! n))"
    using edge2 by (simp add: edge_2_def Let_def)
  have fst_f: "fst ` set f = prop_to_lock ` set (over_all (actions ! n))"
    unfolding f_eq set_map image_image inc_prop_lock_ab_def by (simp add: comp_def)
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
  proof
    assume "fluent_to_var h \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and ph: "fluent_to_var h = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus False using ph fluent_var_notin_net_bounds[OF h] by simp
  qed
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound from the propositional post-bound and tracking.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  have fset_sub: "fst ` set f \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and xp: "x = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus "x \<in> dom vn" using xp dom_vn dom_map_of_num_net_bounds by auto
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TR fin vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NEassembled NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TR BND by (auto intro: RELI)
qed

text \<open>The per-step kernel, packaged in the @{const RLP} shape the structural combinator's @{text PQ}
case consumes: ONE @{const edge_2} step of the propositional run lifts to a single numeric step
preserving @{const RELC}. Mirrors @{thm [source] RLP_edge_3_single}, with the extra over_all discharge
the augmented @{const num_edge_2} guard demands (@{text wok} / @{text sat_inv}) threaded through to
@{thm [source] num_edge_2_step_lift}: @{text sat_inv} is the deferred active-action over_all fact (it is
@{const True} vacuously when @{term \<open>n_inv (actions ! n) = []\<close>}).\<close>
lemma RLP_edge_2_single:
  assumes start0: "fst s ! Suc n = starting_loc"
      and n: "n < length actions"
      and Llen: "length (fst s) = length net_automata"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (edge_2_effect n s)))"
      and fin: "fluent_in_bounds w"
      and wok: "num_val_ok w"
      and sat_inv: "sat_comps w (set (n_inv (actions ! n)))"
    shows "RLP w [s, edge_2_effect n s]"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "[s, edge_2_effect n s] \<noteq> []" by simp
next
  fix cn
  assume pstep: "graph_impl.steps [s, edge_2_effect n s]"
     and relhd: "RELC (hd [s, edge_2_effect n s]) cn w"
  obtain L vp c where s: "s = (L, vp, c)" by (cases s)
  obtain L' vp' c' where t: "edge_2_effect n s = (L', vp', c')" by (cases "edge_2_effect n s")
  obtain Ln vn cnn where cn: "cn = (Ln, vn, cnn)" by (cases cn)
  have Leq: "Ln = L" and ceq: "cnn = c" and relS: "REL vp vn w"
    using relhd unfolding s cn list.sel by (auto dest: RELC_locD RELC_clkD RELC_relD)
  \<comment> \<open>The propositional single step, extracted from the antecedent.\<close>
  have t2: "edge_2_effect n (L, vp, c) = (L', vp', c')" using t unfolding s by simp
  have step1: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using pstep unfolding s t2 by (auto elim: graph_impl.steps.cases)
  have L'fst: "L' = fst (edge_2_effect n (L, vp, c))" using t unfolding s by simp
  have pbnd2: "Simple_Network_Language.bounded (map_of net_bounds) vp'" using pbnd' unfolding t by simp
  have start2: "L ! Suc n = starting_loc" using start0 unfolding s by simp
  have Llen2: "length L = length net_automata" using Llen unfolding s by simp
  obtain vn' where
      numstep: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    and relE: "REL vp' vn' w"
    using num_edge_2_step_lift[OF relS Llen2 start2 n step1 L'fst pbnd2 fin wok sat_inv] by blast
  have "num_graph_impl.steps [cn, (L', vn', c')]"
    unfolding cn Leq ceq by (rule num_single_step_intro) (use numstep in \<open>simp add: prod.case\<close>)
  moreover have "RELC (edge_2_effect n s) (L', vn', c') w"
    unfolding t by (rule RELCI[OF relE])
  ultimately show "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length [s, edge_2_effect n s] - 1
                         \<and> RELC (last [s, edge_2_effect n s]) (last (cn # nss)) w"
    by (intro exI[where x = "[(L', vn', c')]"]) (simp add: t)
qed

text \<open>The @{const edge_2} phase-lift, via the structural combinator. Identical in shape to
@{thm [source] num_edge_3_phase_lift} (this phase also writes no fluent, so the abstract valuation
@{term w} is fixed throughout): the propositional happening run through the @{const edge_2} phase is the
@{const RLP} antecedent fired per step, and the per-step @{const edge_2} kernel
@{thm [source] RLP_edge_2_single} discharges the combinator's @{text PQ} obligation under the caller's
propositional pre/post invariant pair @{term P} / @{term Q} (the per-step @{const num_val_ok} /
over_all-@{const sat_comps} facts the augmented @{const num_edge_2} guard needs are established by the
caller inside @{text PQ}). Given @{const RELC} at the start config, the result is a numeric run
@{const RELC}-related at the end.\<close>
lemma num_edge_2_phase_lift:
  fixes P Q :: "nat \<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool"
  assumes R0: "RLP w xs \<and> R (last xs)"
      and PQ: "\<And>j s. j < length ns \<Longrightarrow> P j s \<Longrightarrow> Q j (edge_2_effect (ns ! j) s) \<and> RLP w [s, edge_2_effect (ns ! j) s]"
      and QP: "\<And>j s. Suc j < length ns \<Longrightarrow> Q j s \<Longrightarrow> P (Suc j) s"
      and RP0: "\<And>x. 0 < length ns \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. 0 < length ns \<Longrightarrow> Q (length ns - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. length ns = 0 \<Longrightarrow> R x \<Longrightarrow> S x"
      and SR': "\<And>x. S x \<Longrightarrow> R' x"
    shows "RLP w ((ext_seq \<circ> seq_apply) (map edge_2_effect ns) xs)
           \<and> R' (last ((ext_seq \<circ> seq_apply) (map edge_2_effect ns) xs))"
  by (rule sequence_rules.ext_seq_comp_seq_apply_induct_list_prop_composable[
            OF RLP_sequence_rules,
            where R = R and P = P and Q = Q and S = S and R' = R' and fs = "map edge_2_effect ns",
            simplified length_map nth_map, OF R0])
     (use PQ QP RP0 QSl RS0 SR' in blast)+

text \<open>For the @{const num_edge_2} phase the entry guard's @{text sat_inv} obligation (the over_all
  comparisons of the just-started action @{term \<open>actions ! n\<close>}) is discharged at the running fold valuation
  @{term \<open>num_plan.num_rat_impl.happening_num_update ys (snd (M i))\<close>}: the over_all fluents are READ-ONLY along
  the run, so the fold (@{thm [source] happening_num_update_inv_unchanged}) and the state sequence
  (@{thm [source] num_seq_inv_const}) both pin them to the INITIAL valuation, where @{text n_inv_init_sat}
  certifies the over_all hold.\<close>
lemma inv_sat_at_fold:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i \<le> length planning_sem.htpl"
      and a: "a \<in> set actions"
      and ysmem: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>b \<in> set actions. s = at_start b \<or> s = at_end b"
    shows "sat_comps (num_plan.num_rat_impl.happening_num_update ys (snd (M i))) (set (n_inv a))"
proof -
  have agree: "num_plan.num_rat_impl.happening_num_update ys (snd (M i)) g = snd (M 0) g"
    if c: "c \<in> set (n_inv a)" and f: "g \<in> comp_fluents c" for c g
  proof -
    have ginv: "g \<in> (\<Union>a \<in> set actions. \<Union>c \<in> set (n_inv a). comp_fluents c)"
      using a c f by blast
    have "num_plan.num_rat_impl.happening_num_update ys (snd (M i)) g = snd (M i) g"
      by (rule happening_num_update_inv_unchanged[OF ginv ysmem])
    also have "\<dots> = snd (M 0) g" by (rule num_seq_inv_const[OF vss i ginv])
    finally show ?thesis .
  qed
  have "sat_comps (num_plan.num_rat_impl.happening_num_update ys (snd (M i))) (set (n_inv a))
          = sat_comps (snd (M 0)) (set (n_inv a))"
    by (rule sat_comps_cong) (use agree in blast)
  thus ?thesis unfolding m0 using n_inv_init_sat a by simp
qed

text \<open>The propositional @{const net_impl.sem} carries @{const net_bounds}-boundedness of the store as a
  PREMISE on the @{const Simple_Network_Language.label.Del} half of every @{const step_u'} (the
  @{thm [source] step_u_elims} extraction), so the HEAD store of any @{const graph_impl.steps} run that has
  a step from it is @{const net_bounds}-bounded. This supplies the @{text pbnd'} (PRE-store bound) the
  per-phase struct facts need, WITHOUT a propositional per-step post-bound invariant -- it is recovered by
  inverting the very step that leaves the config.\<close>
lemma graph_impl_steps_hd_bounded:
  assumes "graph_impl.steps (x # y # xs)"
  shows "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd x))"
proof -
  obtain L vp c where x: "x = (L, vp, c)" by (cases x)
  obtain Ly vy cy where y: "y = (Ly, vy, cy)" by (cases y)
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>Ly, vy, cy\<rangle>"
    using assms unfolding x y by (auto elim: graph_impl.steps.cases simp: prod.case)
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>Ly, vy, cy\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  have B: "B = map_of net_bounds"
    using as unfolding net_impl.sem_def by simp
  have "Simple_Network_Language.bounded B vp"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as TAG_def by blast
  thus ?thesis unfolding x fst_conv snd_conv B .
qed

text \<open>The POST-store of EVERY propositional @{const step_u'} step is @{const net_bounds}-bounded: the
  internal half (@{text step_int}, the only non-@{const Del} action shape reachable in our action nets)
  carries @{term \<open>bounded B s'\<close>} on its post-store as a tagged premise. This is the POST-store companion of
  @{thm [source] graph_impl_steps_hd_bounded} (which bounds the PRE-store): it bounds the store the step
  lands ON, so it reaches every non-head config of a run -- including each phase's LAST config.\<close>
lemma step_u'_net_impl_post_bounded:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
    shows "Simple_Network_Language.bounded (map_of net_bounds) vp'"
proof -
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "a \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding net_impl.sem_def TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain aa where aInt: "a = Internal aa"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  have B: "B = map_of net_bounds"
    using as unfolding net_impl.sem_def by simp
  have "Simple_Network_Language.bounded B vp'"
    apply (cases rule: step_u_elims'(2)[OF actI[unfolded aInt as]])
    unfolding TAG_def by blast
  thus ?thesis unfolding B .
qed

text \<open>The POST-store of any non-head config @{term \<open>xs ! Suc k\<close>} of a propositional @{const graph_impl.steps}
  run is @{const net_bounds}-bounded: the step @{term \<open>xs ! k \<rightarrow> xs ! Suc k\<close>} lands on it. Cleaner and more
  complete than @{thm [source] graph_impl_steps_hd_bounded}: it reaches the LAST config of every sub-run.\<close>
lemma graph_impl_steps_nth_bounded:
  assumes steps: "graph_impl.steps xs"
      and Sk: "Suc k < length xs"
      and Llen: "length (fst (xs ! k)) = length net_automata"
    shows "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (xs ! Suc k)))"
proof -
  have k_lt: "k < length xs" using Sk by simp
  have dropNN: "drop k xs \<noteq> []" using Sk by simp
  have split: "take k xs @ drop k xs = xs" by simp
  have stepstake: "graph_impl.steps (take k xs @ drop k xs)" using steps unfolding split .
  have stepsdrop: "graph_impl.steps (drop k xs)"
    by (rule graph_impl.steps_appendD2[OF stepstake dropNN])
  have drop_dec: "drop k xs = xs ! k # xs ! Suc k # drop (Suc (Suc k)) xs"
    using Sk k_lt by (simp add: Cons_nth_drop_Suc Suc_lessD)
  obtain L vp c where xk: "xs ! k = (L, vp, c)" by (cases "xs ! k")
  obtain L' vp' c' where xSk: "xs ! Suc k = (L', vp', c')" by (cases "xs ! Suc k")
  have stepsdec: "graph_impl.steps ((L, vp, c) # (L', vp', c') # drop (Suc (Suc k)) xs)"
    using stepsdrop unfolding drop_dec xk xSk .
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using stepsdec by (auto elim: graph_impl.steps.cases simp: prod.case)
  have Llen': "length L = length net_automata" using Llen unfolding xk by simp
  have "Simple_Network_Language.bounded (map_of net_bounds) vp'"
    by (rule step_u'_net_impl_post_bounded[OF step Llen'])
  thus ?thesis unfolding xSk by simp
qed

text \<open>The location-vector length and the main-automaton location @{const planning_loc} are preserved along
  any @{const seq_apply} run whose every step preserves them (each action edge effect is a list-update at a
  @{text \<open>Suc n\<close>} position, so it touches neither @{term 0} nor the length). Induct on the run position via
  @{thm [source] seq_apply_Cons_nth_Suc}.\<close>
lemma seq_apply_locs_preserved:
  assumes pres: "\<And>j s. j < length fs \<Longrightarrow>
                    length (fst ((fs ! j) s)) = length (fst s) \<and> fst ((fs ! j) s) ! 0 = fst s ! 0"
      and k: "k < length (x # seq_apply fs x)"
    shows "length (fst ((x # seq_apply fs x) ! k)) = length (fst x)
           \<and> fst ((x # seq_apply fs x) ! k) ! 0 = fst x ! 0"
  using k
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have klen: "k < length fs" using Suc.prems by simp
  have ih: "length (fst ((x # seq_apply fs x) ! k)) = length (fst x)
            \<and> fst ((x # seq_apply fs x) ! k) ! 0 = fst x ! 0"
    using Suc.IH Suc.prems by simp
  have step: "(x # seq_apply fs x) ! Suc k = (fs ! k) ((x # seq_apply fs x) ! k)"
    by (rule seq_apply_Cons_nth_Suc[OF klen])
  have "length (fst ((fs ! k) ((x # seq_apply fs x) ! k))) = length (fst ((x # seq_apply fs x) ! k))
        \<and> fst ((fs ! k) ((x # seq_apply fs x) ! k)) ! 0 = fst ((x # seq_apply fs x) ! k) ! 0"
    by (rule pres[OF klen])
  thus ?case using ih step by simp
qed

text \<open>The propositional internal step @{term \<open>xs ! k \<rightarrow> xs ! Suc k\<close>} of a @{const graph_impl.steps} run,
  extracted from the run by dropping the leading @{term k} configs and inverting the head step. Supplies the
  per-position step the source-location pinning lemmas consume.\<close>
lemma graph_impl_steps_nth_step:
  assumes steps: "graph_impl.steps xs"
      and Sk: "Suc k < length xs"
    shows "net_impl.sem \<turnstile> \<langle>fst (xs ! k), fst (snd (xs ! k)), snd (snd (xs ! k))\<rangle>
                          \<rightarrow> \<langle>fst (xs ! Suc k), fst (snd (xs ! Suc k)), snd (snd (xs ! Suc k))\<rangle>"
proof -
  have k_lt: "k < length xs" using Sk by simp
  have dropNN: "drop k xs \<noteq> []" using Sk by simp
  have split: "take k xs @ drop k xs = xs" by simp
  have stepstake: "graph_impl.steps (take k xs @ drop k xs)" using steps unfolding split .
  have stepsdrop: "graph_impl.steps (drop k xs)"
    by (rule graph_impl.steps_appendD2[OF stepstake dropNN])
  have drop_dec: "drop k xs = xs ! k # xs ! Suc k # drop (Suc (Suc k)) xs"
    using Sk k_lt by (simp add: Cons_nth_drop_Suc Suc_lessD)
  obtain L vp c where xk: "xs ! k = (L, vp, c)" by (cases "xs ! k")
  obtain L' vp' c' where xSk: "xs ! Suc k = (L', vp', c')" by (cases "xs ! Suc k")
  have stepsdec: "graph_impl.steps ((L, vp, c) # (L', vp', c') # drop (Suc (Suc k)) xs)"
    using stepsdrop unfolding drop_dec xk xSk .
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using stepsdec by (auto elim: graph_impl.steps.cases simp: prod.case)
  show ?thesis using step unfolding xk xSk by simp
qed

text \<open>The per-effect length/@{const planning_loc}-preservation facts for the five action edge effects: each
  is a list-update at @{text \<open>Suc n\<close>} (from the alt-rewrite forms), so it preserves the length and the
  @{term 0}-th (main-automaton) location.\<close>
lemma start_edge_effect_preserves_loc0:
  "length (fst (start_edge_effect n s)) = length (fst s) \<and> fst (start_edge_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: start_edge_effect_alt)

lemma end_edge_effect_preserves_loc0:
  "length (fst (end_edge_effect n s)) = length (fst s) \<and> fst (end_edge_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: end_edge_effect_alt)

lemma edge_2_effect_preserves_loc0:
  "length (fst (edge_2_effect n s)) = length (fst s) \<and> fst (edge_2_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: edge_2_effect_alt)

lemma edge_3_effect_preserves_loc0:
  "length (fst (edge_3_effect n s)) = length (fst s) \<and> fst (edge_3_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: edge_3_effect_alt)

lemma instant_trans_edge_effect_preserves_loc0:
  "length (fst (instant_trans_edge_effect n s)) = length (fst s) \<and> fst (instant_trans_edge_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: instant_trans_edge_effect_alt)

text \<open>Inverting a propositional internal step whose POST-location vector is @{term \<open>L[Suc n := l']\<close>}: under
  @{term \<open>L ! 0 = planning_loc\<close>} (which @{const Lv_conds} pins at every run config) the fired edge sits at
  automaton @{term \<open>Suc n\<close>} -- the main automaton (@{term \<open>p = 0\<close>}) is excluded because from
  @{const planning_loc} its only edge moves to @{const goal_loc}, which would change position @{term 0}; an
  action edge (@{term \<open>p = Suc m\<close>}) strictly moves its location, so the changed position
  @{term \<open>Suc n\<close>} pins @{term \<open>p = Suc n\<close>}. The edge targets @{term l'} and is one of the five action edges,
  so the SOURCE location @{term \<open>L ! Suc n\<close>} is recovered. TARGET analogue of the source-based pinning
  lemmas (@{thm [source] prop_start_edge_pinned} et al.).\<close>
lemma prop_step_edge_at_Sucn:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := l']"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "\<exists>e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                     end_edge (actions ! n), instant_trans_edge (actions ! n)].
             fst e = L ! Suc n \<and> snd (snd (snd (snd (snd (snd e))))) = l'"
proof -
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "a \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding net_impl.sem_def TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain aa where aInt: "a = Internal aa"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  obtain p l b g f r l'' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil aa, f, r, l'') \<in> trans (automaton_of (net_automata ! p))"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l'']"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have len0: "0 < length L" using Sn_lt by simp
  \<comment> \<open>The main automaton cannot fire: from @{const planning_loc} its only edge targets @{const goal_loc},
     which would change position @{term 0} -- but @{term L'} fixes position @{term 0}.\<close>
  have p_ne0: "p \<noteq> 0"
  proof
    assume p0: "p = 0"
    have l_pl: "l = planning_loc" using LOC p0 main_planning by simp
    have "(l, b, g, Sil aa, f, r, l'') \<in> set [main_auto_init_edge, main_auto_goal_edge, main_auto_loop]"
      using E unfolding p0 main_auto_trans by simp
    hence l''_goal: "l'' = goal_loc"
      using l_pl
      by (auto simp: main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def
                     Let_def locations_unique)
    have "L' ! 0 = goal_loc" using L'eq2 p0 l''_goal len0 by simp
    moreover have "L' ! 0 = planning_loc" using L'eq main_planning len0 by simp
    ultimately show False by (simp add: locations_unique)
  qed
  \<comment> \<open>So an action automaton fired; its edge strictly moves location (@{term \<open>l \<noteq> l''\<close>}).\<close>
  obtain m where pSucm: "p = Suc m" using p_ne0 by (cases p) auto
  have m_lt: "m < length actions" using P unfolding pSucm length_net_automata by simp
  have edge_m: "(l, b, g, Sil aa, f, r, l'') \<in> set [start_edge (actions ! m), edge_2 (actions ! m),
                  edge_3 (actions ! m), end_edge (actions ! m), instant_trans_edge (actions ! m)]"
    using E unfolding pSucm nth_auto_trans[OF m_lt] action_to_automaton_def Let_def by simp
  have l_ne: "l \<noteq> l''"
    using edge_m
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
  \<comment> \<open>Since the edge changes the location and @{term L'} differs from @{term L} only at @{term \<open>Suc n\<close>},
     the fired automaton is @{term \<open>Suc n\<close>}.\<close>
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume pne: "p \<noteq> Suc n"
    have "L' ! p = L ! p" using L'eq pne by simp
    moreover have "L' ! p = l''" using L'eq2 LOC P Llen by (simp add: length_net_automata)
    ultimately show False using LOC l_ne by simp
  qed
  have m_eq_n: "m = n" using pSuc pSucm by simp
  have edge: "(l, b, g, Sil aa, f, r, l'') \<in> set [start_edge (actions ! n), edge_2 (actions ! n),
                edge_3 (actions ! n), end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using edge_m unfolding m_eq_n .
  have l_src: "l = L ! Suc n" using LOC pSuc by simp
  have l''_tgt: "l'' = l'"
  proof -
    have "L' ! Suc n = l'" using L'eq Sn_lt by simp
    moreover have "L' ! Suc n = l''" using L'eq2 pSuc Sn_lt by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis
    apply (rule bexI[where x = "(l, b, g, Sil aa, f, r, l'')"])
    using l_src l''_tgt edge by auto
qed

text \<open>A propositional internal step whose POST location at @{term \<open>Suc n\<close>} is @{const starting_loc} fired
  @{const start_edge}, so its SOURCE location is @{const off_loc} (only @{const start_edge} targets
  @{const starting_loc} among the five action edges).\<close>
lemma prop_step_source_off:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := starting_loc]"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "L ! Suc n = off_loc"
proof -
  obtain e where e: "e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                              end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    and src: "fst e = L ! Suc n"
    and tgt: "snd (snd (snd (snd (snd (snd e))))) = starting_loc"
    using prop_step_edge_at_Sucn[OF step Llen L'eq main_planning n] by blast
  show ?thesis using e src tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>A propositional internal step whose POST location at @{term \<open>Suc n\<close>} is @{const off_loc} fired
  @{const end_edge}, so its SOURCE location is @{const ending_loc} (only @{const end_edge} targets
  @{const off_loc} among the five action edges).\<close>
lemma prop_step_source_ending:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := off_loc]"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "L ! Suc n = ending_loc"
proof -
  obtain e where e: "e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                              end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    and src: "fst e = L ! Suc n"
    and tgt: "snd (snd (snd (snd (snd (snd e))))) = off_loc"
    using prop_step_edge_at_Sucn[OF step Llen L'eq main_planning n] by blast
  show ?thesis using e src tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The START-phase @{text struct} export: for a @{const start_edge_effect} @{const seq_apply} sub-run
  whose head config has the @{const planning_loc} main location and the @{const net_automata} length, every
  run-position @{term k} satisfies the three @{text struct} facts @{thm [source] num_start_phase_lift}
  demands -- the @{const off_loc} SOURCE location (recovered from the @{const starting_loc} TARGET via
  @{thm [source] prop_step_source_off}), the length, and the @{const net_bounds} bound on the post-store
  (via @{thm [source] graph_impl_steps_nth_bounded}). Locations/length thread through the run by
  @{thm [source] seq_apply_locs_preserved}, the per-position step by @{thm [source] graph_impl_steps_nth_step}.\<close>
lemma start_phase_struct:
  assumes run: "graph_impl.steps (sp # seq_apply (map start_edge_effect ns) sp)"
      and head0: "fst sp ! 0 = planning_loc"
      and headlen: "length (fst sp) = length net_automata"
      and ns_act: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions"
      and k: "k < length ns"
    shows "fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k) ! Suc (ns ! k) = off_loc
           \<and> length (fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k)) = length net_automata
           \<and> Simple_Network_Language.bounded (map_of net_bounds)
                 (fst (snd (start_edge_effect (ns ! k)
                             ((sp # seq_apply (map start_edge_effect ns) sp) ! k))))"
proof -
  let ?xs = "sp # seq_apply (map start_edge_effect ns) sp"
  let ?ck = "?xs ! k"
  have lenxs: "length ?xs = Suc (length ns)" by simp
  have Sk: "Suc k < length ?xs" using k by simp
  have k_lt_xs: "k < length ?xs" using k by simp
  \<comment> \<open>Per-step location/length preservation along the run.\<close>
  have pres: "length (fst ((map start_edge_effect ns ! j) s)) = length (fst s)
                \<and> fst ((map start_edge_effect ns ! j) s) ! 0 = fst s ! 0"
    if j: "j < length (map start_edge_effect ns)" for j s
    using start_edge_effect_preserves_loc0[of "ns ! j" s] j by simp
  have loc0len: "length (fst ?ck) = length (fst sp) \<and> fst ?ck ! 0 = fst sp ! 0"
    using seq_apply_locs_preserved[OF pres, of k] k_lt_xs by simp
  have ckloc0: "fst ?ck ! 0 = planning_loc" using loc0len head0 by simp
  have cklen: "length (fst ?ck) = length net_automata" using loc0len headlen by simp
  \<comment> \<open>The next config is the @{const start_edge_effect} image, a @{const starting_loc}-targeting update.\<close>
  have nxt: "?xs ! Suc k = start_edge_effect (ns ! k) ?ck"
    using seq_apply_Cons_nth_Suc[of k "map start_edge_effect ns" sp] k by simp
  obtain L vp c where ck: "?ck = (L, vp, c)" by (cases ?ck)
  have nxt_eq: "fst (?xs ! Suc k) = L[Suc (ns ! k) := starting_loc]"
    unfolding nxt ck by (simp add: start_edge_effect_alt)
  \<comment> \<open>The per-position propositional step.\<close>
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?xs ! Suc k), fst (snd (?xs ! Suc k)), snd (snd (?xs ! Suc k))\<rangle>"
    using graph_impl_steps_nth_step[OF run Sk] unfolding ck by simp
  have nk_act: "ns ! k < length actions" using ns_act[of "ns ! k"] k by simp
  have Llen: "length L = length net_automata" using cklen ck by simp
  have main0: "L ! 0 = planning_loc" using ckloc0 ck by simp
  \<comment> \<open>Conjunct 1: the @{const off_loc} source location.\<close>
  have off: "L ! Suc (ns ! k) = off_loc"
    by (rule prop_step_source_off[OF step Llen nxt_eq main0 nk_act])
  have c1: "fst ?ck ! Suc (ns ! k) = off_loc" using off ck by simp
  \<comment> \<open>Conjunct 3: the @{const net_bounds} bound on the post-store.\<close>
  have c3: "Simple_Network_Language.bounded (map_of net_bounds)
              (fst (snd (start_edge_effect (ns ! k) ?ck)))"
    using graph_impl_steps_nth_bounded[OF run Sk] cklen nxt by simp
  show ?thesis using c1 cklen c3 by blast
qed

text \<open>The END-phase @{text struct} export, the mirror of @{thm [source] start_phase_struct}: each
  @{const end_edge_effect} step targets @{const off_loc}, so the SOURCE location is @{const ending_loc}
  (via @{thm [source] prop_step_source_ending}).\<close>
lemma end_phase_struct:
  assumes run: "graph_impl.steps (sp # seq_apply (map end_edge_effect ns) sp)"
      and head0: "fst sp ! 0 = planning_loc"
      and headlen: "length (fst sp) = length net_automata"
      and ns_act: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions"
      and k: "k < length ns"
    shows "fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k) ! Suc (ns ! k) = ending_loc
           \<and> length (fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k)) = length net_automata
           \<and> Simple_Network_Language.bounded (map_of net_bounds)
                 (fst (snd (end_edge_effect (ns ! k)
                             ((sp # seq_apply (map end_edge_effect ns) sp) ! k))))"
proof -
  let ?xs = "sp # seq_apply (map end_edge_effect ns) sp"
  let ?ck = "?xs ! k"
  have Sk: "Suc k < length ?xs" using k by simp
  have k_lt_xs: "k < length ?xs" using k by simp
  have pres: "length (fst ((map end_edge_effect ns ! j) s)) = length (fst s)
                \<and> fst ((map end_edge_effect ns ! j) s) ! 0 = fst s ! 0"
    if j: "j < length (map end_edge_effect ns)" for j s
    using end_edge_effect_preserves_loc0[of "ns ! j" s] j by simp
  have loc0len: "length (fst ?ck) = length (fst sp) \<and> fst ?ck ! 0 = fst sp ! 0"
    using seq_apply_locs_preserved[OF pres, of k] k_lt_xs by simp
  have ckloc0: "fst ?ck ! 0 = planning_loc" using loc0len head0 by simp
  have cklen: "length (fst ?ck) = length net_automata" using loc0len headlen by simp
  have nxt: "?xs ! Suc k = end_edge_effect (ns ! k) ?ck"
    using seq_apply_Cons_nth_Suc[of k "map end_edge_effect ns" sp] k by simp
  obtain L vp c where ck: "?ck = (L, vp, c)" by (cases ?ck)
  have nxt_eq: "fst (?xs ! Suc k) = L[Suc (ns ! k) := off_loc]"
    unfolding nxt ck by (simp add: end_edge_effect_alt)
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?xs ! Suc k), fst (snd (?xs ! Suc k)), snd (snd (?xs ! Suc k))\<rangle>"
    using graph_impl_steps_nth_step[OF run Sk] unfolding ck by simp
  have nk_act: "ns ! k < length actions" using ns_act[of "ns ! k"] k by simp
  have Llen: "length L = length net_automata" using cklen ck by simp
  have main0: "L ! 0 = planning_loc" using ckloc0 ck by simp
  have endl: "L ! Suc (ns ! k) = ending_loc"
    by (rule prop_step_source_ending[OF step Llen nxt_eq main0 nk_act])
  have c1: "fst ?ck ! Suc (ns ! k) = ending_loc" using endl ck by simp
  have c3: "Simple_Network_Language.bounded (map_of net_bounds)
              (fst (snd (end_edge_effect (ns ! k) ?ck)))"
    using graph_impl_steps_nth_bounded[OF run Sk] cklen nxt by simp
  show ?thesis using c1 cklen c3 by blast
qed

text \<open>The @{const apply_instant_actions} run has @{term \<open>3 * length ns\<close>} configs (each instant index
  contributes its three-config @{const apply_snap_action} block). Induct on @{term ns}.\<close>
lemma length_apply_instant_actions:
  "length (apply_instant_actions ns s) = 3 * length ns"
proof (induction ns arbitrary: s)
  case Nil
  show ?case by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil)
next
  case (Cons n ns')
  have "apply_instant_actions (n # ns') s
          = apply_snap_action n s @ apply_instant_actions ns' (last (apply_snap_action n s))"
    by (rule apply_instant_actions_Cons)
  thus ?case using Cons.IH by (simp add: apply_snap_action_unfold)
qed

text \<open>The block-config decomposition of an @{const apply_instant_actions} run: for any instant index
  @{term \<open>k < length ns\<close>}, the four configs of block @{term k} in @{term \<open>s # apply_instant_actions ns s\<close>}
  sit at positions @{term \<open>3 * k\<close>}, @{term \<open>3 * k + 1\<close>}, @{term \<open>3 * k + 2\<close>}, @{term \<open>3 * k + 3\<close>} and are
  the @{const start_edge_effect}/@{const instant_trans_edge_effect}/@{const end_edge_effect} chain. Induct
  on @{term ns} (the head block sits at the front, the rest shifts by 3).\<close>
lemma apply_instant_actions_block_nth_conj:
  assumes k: "k < length ns"
  shows "(s # apply_instant_actions ns s) ! (3 * k + 1)
            = start_edge_effect (ns ! k) ((s # apply_instant_actions ns s) ! (3 * k))
         \<and> (s # apply_instant_actions ns s) ! (3 * k + 2)
            = instant_trans_edge_effect (ns ! k) ((s # apply_instant_actions ns s) ! (3 * k + 1))
         \<and> (s # apply_instant_actions ns s) ! (3 * k + 3)
            = end_edge_effect (ns ! k) ((s # apply_instant_actions ns s) ! (3 * k + 2))"
  using k
proof (induction ns arbitrary: s k)
  case Nil
  thus ?case by simp
next
  case (Cons n ns')
  let ?s1 = "start_edge_effect n s"
  let ?s2 = "instant_trans_edge_effect n ?s1"
  let ?s3 = "end_edge_effect n ?s2"
  have run_unfold: "s # apply_instant_actions (n # ns') s
                      = s # ?s1 # ?s2 # ?s3 # apply_instant_actions ns' ?s3"
    by (subst apply_instant_actions_Cons) (simp add: apply_snap_action_unfold)
  show ?case
  proof (cases k)
    case 0
    show ?thesis unfolding run_unfold 0 by simp
  next
    case (Suc k')
    have k'lt: "k' < length ns'" using Cons.prems Suc by simp
    have shift1: "3 * Suc k' + 1 = Suc (Suc (Suc (3 * k' + 1)))" by simp
    have shift2: "3 * Suc k' + 2 = Suc (Suc (Suc (3 * k' + 2)))" by simp
    have shift3: "3 * Suc k' + 3 = Suc (Suc (Suc (3 * k' + 3)))" by simp
    have shift0: "3 * Suc k' = Suc (Suc (Suc (3 * k')))" by simp
    note IH = Cons.IH[OF k'lt, of ?s3]
    show ?thesis
      unfolding run_unfold Suc shift0 shift1 shift2 shift3
      using IH by (simp add: nth_Cons')
  qed
qed

lemmas apply_instant_actions_block_nth = apply_instant_actions_block_nth_conj[THEN conjunct1]
  apply_instant_actions_block_nth_conj[THEN conjunct2, THEN conjunct1]
  apply_instant_actions_block_nth_conj[THEN conjunct2, THEN conjunct2]

text \<open>The location-vector length and the @{const planning_loc} main location are preserved along any
  @{const apply_instant_actions} run: each of the three block effects is a @{text \<open>Suc n\<close>}-update. Induct on
  @{term ns}, threading the block-end config; the head block's three configs preserve loc0/length by the
  per-effect facts, the tail by the IH.\<close>
lemma apply_instant_actions_locs_preserved:
  assumes k: "k < length (s # apply_instant_actions ns s)"
  shows "length (fst ((s # apply_instant_actions ns s) ! k)) = length (fst s)
         \<and> fst ((s # apply_instant_actions ns s) ! k) ! 0 = fst s ! 0"
  using k
proof (induction ns arbitrary: s k)
  case Nil
  show ?case using Nil.prems
    by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil)
next
  case (Cons n ns')
  let ?s1 = "start_edge_effect n s"
  let ?s2 = "instant_trans_edge_effect n ?s1"
  let ?s3 = "end_edge_effect n ?s2"
  have run_unfold: "s # apply_instant_actions (n # ns') s
                      = s # ?s1 # ?s2 # ?s3 # apply_instant_actions ns' ?s3"
    by (subst apply_instant_actions_Cons) (simp add: apply_snap_action_unfold)
  \<comment> \<open>The three head-block configs preserve loc0/length relative to @{term s}.\<close>
  have p1: "length (fst ?s1) = length (fst s) \<and> fst ?s1 ! 0 = fst s ! 0"
    using start_edge_effect_preserves_loc0[of n s] .
  have p2: "length (fst ?s2) = length (fst s) \<and> fst ?s2 ! 0 = fst s ! 0"
    using instant_trans_edge_effect_preserves_loc0[of n ?s1] p1 by simp
  have p3: "length (fst ?s3) = length (fst s) \<and> fst ?s3 ! 0 = fst s ! 0"
    using end_edge_effect_preserves_loc0[of n ?s2] p2 by simp
  show ?case
  proof (cases k)
    case 0
    show ?thesis unfolding run_unfold 0 by simp
  next
    case (Suc k0)
    show ?thesis
    proof (cases k0)
      case 0
      show ?thesis unfolding run_unfold Suc 0 using p1 by simp
    next
      case (Suc k1)
      show ?thesis
      proof (cases k1)
        case 0
        show ?thesis unfolding run_unfold \<open>k = Suc k0\<close> Suc 0 using p2 by simp
      next
        case (Suc k2)
        \<comment> \<open>Positions @{term \<open>k \<ge> 3\<close>} land in the tail run from @{term ?s3}.\<close>
        have keq: "k = 3 + k2" using \<open>k = Suc k0\<close> \<open>k0 = Suc k1\<close> \<open>k1 = Suc k2\<close> by simp
        have ktail: "k2 < length (?s3 # apply_instant_actions ns' ?s3)"
          using Cons.prems unfolding run_unfold keq by simp
        have idx: "(s # apply_instant_actions (n # ns') s) ! k
                     = (?s3 # apply_instant_actions ns' ?s3) ! k2"
          unfolding run_unfold keq by simp
        have ih: "length (fst ((?s3 # apply_instant_actions ns' ?s3) ! k2)) = length (fst ?s3)
                  \<and> fst ((?s3 # apply_instant_actions ns' ?s3) ! k2) ! 0 = fst ?s3 ! 0"
          using Cons.IH[OF ktail] .
        show ?thesis unfolding idx using ih p3 by simp
      qed
    qed
  qed
qed

text \<open>The INSTANT-phase @{text struct} export: for an @{const apply_instant_actions} sub-run whose head
  config has the @{const planning_loc} main location and the @{const net_automata} length, every block index
  @{term k} satisfies @{const instant_block_struct} at run-position @{term \<open>3 * k\<close>}. The block entry config's
  @{const off_loc} source comes from @{thm [source] prop_step_source_off} (its start sub-step targets
  @{const starting_loc}); the two later block source locations (@{const starting_loc} after the start edge,
  @{const ending_loc} after the instant-trans edge) come straight from the effect shapes
  @{thm [source] start_edge_effect_alt} / @{thm [source] instant_trans_edge_effect_alt}; the three post-store
  bounds from @{thm [source] graph_impl_steps_nth_bounded}; lengths from
  @{thm [source] apply_instant_actions_locs_preserved}.\<close>
lemma instant_phase_struct:
  assumes run: "graph_impl.steps (sp # apply_instant_actions ns sp)"
      and head0: "fst sp ! 0 = planning_loc"
      and headlen: "length (fst sp) = length net_automata"
      and ns_act: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions"
      and k: "k < length ns"
    shows "instant_block_struct ((sp # apply_instant_actions ns sp) ! (3 * k)) (ns ! k)"
proof -
  let ?xs = "sp # apply_instant_actions ns sp"
  let ?m = "ns ! k"
  let ?c = "?xs ! (3 * k)"
  let ?s1 = "start_edge_effect ?m ?c"
  let ?s2 = "instant_trans_edge_effect ?m ?s1"
  let ?s3 = "end_edge_effect ?m ?s2"
  have lenxs: "length ?xs = Suc (3 * length ns)"
    by (simp add: length_apply_instant_actions)
  have m_act: "?m < length actions" using ns_act[of ?m] k by simp
  have Sm_lt: "Suc ?m < length net_automata" using m_act  by (simp add: length_net_automata)
  \<comment> \<open>The block configs at the three positions following @{term \<open>3 * k\<close>}.\<close>
  have b1: "?xs ! (3 * k + 1) = ?s1" by (rule apply_instant_actions_block_nth(1)[OF k])
  have b2: "?xs ! (3 * k + 2) = ?s2" using apply_instant_actions_block_nth(2)[OF k] b1 by simp
  have b3: "?xs ! (3 * k + 3) = ?s3" using apply_instant_actions_block_nth(3)[OF k] b2 by simp
  \<comment> \<open>Position bounds within the run.\<close>
  have p1lt: "3 * k + 1 < length ?xs" using k lenxs by simp
  have p2lt: "3 * k + 2 < length ?xs" using k lenxs by simp
  have p3lt: "3 * k + 3 < length ?xs" using k lenxs by simp
  have c_lt: "3 * k < length ?xs" using p1lt by simp
  \<comment> \<open>Lengths/loc0 along the run.\<close>
  have lc_pair: "length (fst ?c) = length (fst sp) \<and> fst ?c ! 0 = fst sp ! 0"
    using apply_instant_actions_locs_preserved[OF c_lt] .
  have c_len: "length (fst ?c) = length net_automata" using lc_pair headlen by simp
  have c_loc0: "fst ?c ! 0 = planning_loc" using lc_pair head0 by simp
  have s1_len: "length (fst ?s1) = length net_automata"
    using start_edge_effect_preserves_loc0[of ?m ?c] c_len by simp
  have s2_len: "length (fst ?s2) = length net_automata"
    using instant_trans_edge_effect_preserves_loc0[of ?m ?s1] s1_len by simp
  \<comment> \<open>Conjunct 1: the @{const off_loc} block-entry source location.\<close>
  obtain L vp c where ck: "?c = (L, vp, c)" by (cases ?c)
  have s1_alt: "fst (?xs ! (3 * k + 1)) = L[Suc ?m := starting_loc]"
    unfolding b1 ck by (simp add: start_edge_effect_alt)
  have stepc: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?xs ! (3 * k + 1)), fst (snd (?xs ! (3 * k + 1))), snd (snd (?xs ! (3 * k + 1)))\<rangle>"
    using graph_impl_steps_nth_step[OF run, of "3 * k"] p1lt unfolding ck by simp
  have Llen: "length L = length net_automata" using c_len ck by simp
  have main0: "L ! 0 = planning_loc" using c_loc0 ck by simp
  have off: "L ! Suc ?m = off_loc"
    by (rule prop_step_source_off[OF stepc Llen s1_alt main0 m_act])
  have conj1: "fst ?c ! Suc ?m = off_loc" using off ck by simp
  \<comment> \<open>Conjuncts 4, 7: the @{const starting_loc} / @{const ending_loc} source locations from the effect shapes.\<close>
  have Sm_ltL: "Suc ?m < length L" using Sm_lt Llen by simp
  have conj4: "fst ?s1 ! Suc ?m = starting_loc"
    unfolding ck by (simp add: start_edge_effect_alt nth_list_update_eq Sm_ltL)
  have conj7: "fst ?s2 ! Suc ?m = ending_loc"
  proof -
    obtain L1 v1 c1 where s1k: "?s1 = (L1, v1, c1)" by (cases ?s1)
    have l1len: "Suc ?m < length L1" using s1_len Sm_lt s1k by simp
    show ?thesis unfolding s1k by (simp add: instant_trans_edge_effect_alt l1len)
  qed
  \<comment> \<open>Conjuncts 3, 6, 9: the post-store bounds.\<close>
  have conj3: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s1))"
    using graph_impl_steps_nth_bounded[OF run, of "3 * k"] p1lt c_len b1 by simp
  have conj6: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s2))"
    using graph_impl_steps_nth_bounded[OF run, of "3 * k + 1"] p2lt s1_len b1 b2 by simp
  have conj9: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s3))"
    using graph_impl_steps_nth_bounded[OF run, of "3 * k + 2"] p3lt s2_len b2 b3 by simp
  show ?thesis
    unfolding instant_block_struct_def Let_def
    using conj1 c_len conj3 conj4 s1_len conj6 conj7 s2_len conj9 by blast
qed

lemma num_happening_steps_possible:
  assumes i: "i < length planning_sem.htpl"
      and vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and lvp: "num_LvP cfg"
      and pres: "num_happening_pre_pre_delay M i cfg"
  shows "\<exists>ns. num_graph_impl.steps (cfg # ns)
              \<and> num_happening_post M i (last (cfg # ns)) \<and> num_LvP (last (cfg # ns))"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have ppd: "happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)"
    using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_propD)
  have tr: "num_tracks v (snd (M i))" using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_trackD)
  \<comment> \<open>The boundedness now rides in the separately-carried @{const num_LvP}, from which we re-derive the
     full-store bound (still needed by the run-lift core) and -- via the bridge -- the propositional
     @{const LvP} on the projection store that @{thm [source] happening_steps_possible} now requires.\<close>
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    using lvp[unfolded cfg] by (simp add: num_Lv_conds_dests(3))
  have lvpr: "LvP (L, v |` dom (map_of net_bounds), c)"
    using lvp[unfolded cfg] by (rule num_LvP_imp_LvP)
  \<comment> \<open>The propositional happening run over the net_bounds PROJECTION store v |` dom (map_of net_bounds),
     which num_happening_pre_pre_delay_propD certifies as a valid propositional pre-state; the projected
     @{const LvP} premise is supplied by @{thm [source] num_LvP_imp_LvP}.\<close>
  have prun: "graph_impl.steps ((L, v |` dom (map_of net_bounds), c) # delay_and_apply i (L, v |` dom (map_of net_bounds), c))"
    and ppost: "happening_post i (last (delay_and_apply i (L, v |` dom (map_of net_bounds), c)))"
    using happening_steps_possible[OF i ppd lvpr] by blast+
  \<comment> \<open>TODO (the run-lift core): lift prun to a numeric run over the FULL store v, threading num_tracks
     (the running happening_num_update_set partial fold) and the num_net_bounds bound via num_int_step_lift
     + num_data_no_write_edge / num_data_upd_edge per internal step (L ! p pins the fired edge) and
     num_steps_delay_replace for the leading delay; num_happening_post then follows from ppost since the
     numeric run's last store projects (prop_proj_bounded) to the prop run's last store. The carried
     num_LvP on the last config follows from num_Lv_conds_maintained across the numeric edges (locations
     and planning_lock are preserved; the num_net_bounds bound is re-established per step by the lift).\<close>
  show "\<exists>ns. num_graph_impl.steps (cfg # ns) \<and> num_happening_post M i (last (cfg # ns)) \<and> num_LvP (last (cfg # ns))"
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

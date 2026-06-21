theory TP_NTA_Reduction_Correctness_Steps
  imports TP_NTA_Reduction_Correctness_Happenings
begin
context tp_nta_reduction_correctness
begin
section \<open>Properties of states\<close>
subsection \<open>The initial state\<close>

schematic_goal set_init_vars_exact: "set (map fst net_bounds) = ?x"
  unfolding all_vars_def Let_def set_append list.set filter_map filter_append comp_def
  fst_conv map_append map_map set_map 
  apply (subst image_insert)+
  apply (subst image_empty)
  apply (subst fst_conv)+
  ..

schematic_goal dom_map_of_net_bounds_exact: "dom (map_of net_bounds) = ?x"
  apply (subst dom_map_of_conv_image_fst)
  apply (subst image_set)
  apply (subst set_init_vars_exact)
  ..


lemma initial_step_possible: "graph_impl.steps ((ext_seq \<circ> seq_apply) [main_auto_init_edge_effect] [a\<^sub>0]) 
    \<and> init_planning_state_props' (last ((ext_seq \<circ> seq_apply) [main_auto_init_edge_effect] [a\<^sub>0]))"
proof (rule steps_seq.ext_seq_comp_seq_apply_single_list_prop_and_post_composable[where R = init_state_props and S = init_planning_state_props])
  show "graph_impl.steps (map (\<lambda>(x, y). (x, case y of (x, y) \<Rightarrow> (x, \<lambda>x. real_of_int (y x)))) [a\<^sub>0]) \<and> init_state_props (last (map (\<lambda>(x, y). (x, case y of (x, y) \<Rightarrow> (x, \<lambda>x. real_of_int (y x)))) [a\<^sub>0]))"
  proof (intro conjI, goal_cases)
    case 1
    then show ?case unfolding a\<^sub>0_def 
      apply (subst list.map)+
      by rule
  next
    case 2
    then show ?case  unfolding a\<^sub>0_alt
      apply (subst list.map)+
      unfolding prod.case
      apply (subst last_ConsL[OF HOL.refl])
      apply (rule init_state_propsI)
      apply (rule HOL.refl)
      using init_vars_bounded 
      unfolding init_vars_alt 
          apply simp
      apply (rule HOL.refl)
        subgoal for x
          apply (rule map_of_determ)
           apply fastforce
          by auto
       apply (subst map_of_eq_None_iff)
      by auto
  qed
  show "\<And>x. init_planning_state_props x \<Longrightarrow> init_planning_state_props' x"
    subgoal for x
      apply (cases x)
      subgoal for L v c
        apply simp
        apply (rule init_planning_state_props'I, simp)
              apply (rule init_planning_state_props_dests, simp, simp)
              apply (rule init_planning_state_props_dests, simp, simp)
            apply (rule init_planning_state_props_dests, simp, simp)
        unfolding prop_state_def
           apply (intro strip)
        subgoal for p 
          apply (cases "p \<in> set init")
           apply (subst if_P, simp)
          apply (blast intro: init_planning_state_props_dests)
          apply (subst if_not_P, simp)
          apply (rule init_planning_state_props_dests(5), assumption, simp)
            apply (subst dom_map_of_conv_image_fst[symmetric] set_map)+
            apply simp
          using variables_unique[symmetric] apply fast
          apply (rule notI)
          apply (erule imageE)
          using variables_unique init_in_props by fast
        subgoal apply (intro strip, elim conjE) 
          apply (rule init_planning_state_props_dests(5))
              apply (assumption, rule HOL.refl)
            apply (subst (asm) dom_map_of_conv_image_fst)
          apply simp
          using variables_unique apply fast
          using variable_sets_unique init_in_props by presburger
        subgoal using init_planning_state_props_dests by metis
        using init_planning_state_props_dests by fast
      done
    done
  show "\<And>x. init_state_props x \<Longrightarrow> init_planning_state_props (main_auto_init_edge_effect x) \<and> graph_impl.steps [x, main_auto_init_edge_effect x]"
  proof -
    fix x
    assume a: "init_state_props x"
    obtain L v c where
      Lvc: "x = (L,v,c)" by (cases x, auto)
    have x: "init_planning_state_props (main_auto_init_edge_effect x)"
      apply (insert a)
      apply (rule init_planning_state_propsI)
      unfolding main_auto_init_edge_effect_alt Lvc
               apply (rule HOL.refl)
      subgoal apply (rule Lv_condsI)
        using init_state_props_dests apply fastforce
        apply (rule nth_list_update_eq)
        using init_state_props_dests apply fastforce
          subgoal apply (rule upds_map_bounded[where v = "v(planning_lock \<mapsto> 1, acts_active \<mapsto> 0)"])
              apply (rule single_upd_bounded)
                 apply (rule single_upd_bounded)
            using init_state_props_dests apply blast
                   apply (rule map_of_net_bounds_planning_lock)
                  apply simp
                 apply simp
                apply (rule map_of_net_bounds_acts_active)
               apply simp
              apply simp
             apply (rule HOL.refl)
            subgoal apply (rule ballI)
              subgoal for x
                apply (intro exI)
                apply (intro conjI)
                  apply (rule map_of_net_bounds_init_goal)
                by simp+
              done
            done
          apply (subst map_upds_apply_nontin)
           apply (rule notI)
          using variable_sets_unique apply simp
          apply (subst fun_upd_other)
           apply (rule variables_unique)
          by simp
        subgoal by (simp add: variables_unique variable_sets_unique)
        subgoal using init_state_props_dests by fastforce
        subgoal by (fastforce intro!: map_upds_with_map)
        subgoal using init_state_props_dests by (fastforce intro!: map_upds_with_map)
        subgoal for p
          apply (subst map_upds_apply_nontin)
          subgoal apply (rule notI)
            apply (subst (asm) set_init_vars_exact) using init_in_props by auto
          apply (subst fun_upd_other)
           apply (subst (asm) set_init_vars_exact) apply blast
          apply (subst fun_upd_other)
           apply (subst (asm) set_init_vars_exact) apply blast
          using init_state_props_dests by simp
        subgoal using init_state_props_dests by simp
        done
    moreover
    have "graph_impl.steps [x, main_auto_init_edge_effect x]"
    proof (rule single_step_intro)
      obtain L v c where
        Lvc: "x = (L, v, c)" by (erule prod_cases3)  

      obtain L' v' c' where
        Lvc': "main_auto_init_edge_effect x = (L', v', c')" by (erule prod_cases3)

      have v': "v' = v(planning_lock \<mapsto> 1, acts_active \<mapsto> 0, map prop_to_var init [\<mapsto>] map (\<lambda>x. 1) (map prop_to_var init))"
        using Lvc' Lvc using main_auto_init_edge_effect_alt by auto

      have "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L', v', c'\<rangle>"
      proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
        show "Simple_Network_Language.bounded (map_of net_bounds) v" 
          apply (insert a)
          apply (erule init_state_propsE)
          using Lvc by simp
        show "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L', v', c'\<rangle>"
          unfolding net_impl.sem_def
          apply (rule step_u.step_int[where p = 0])
          unfolding TAG_def
                    apply (subst conv_trans)
                     apply (simp add: timed_automaton_net_def)
                    apply (subst main_auto_trans)
                    apply (rule image_eqI)
                     defer
                     apply (rule insertI1)
                    apply (rule disjI2)
                    prefer 11
                    apply (subst main_auto_init_edge_def)
          apply (subst Let_def)+
                    apply (subst prod.case)+
          apply (rule HOL.refl)
          using no_committed conv_committed apply force
          subgoal apply (insert a)
            unfolding Lvc
              apply (subst refl_True[symmetric])
              apply (rule check_bexp_is_val.intros)
             apply (rule check_bexp_is_val.intros)
             apply (rule init_state_props_dests, simp, simp)
            using set_init_vars_exact apply blast
            by (rule check_bexp_is_val.intros)
                 apply simp
          apply (rule allI impI)
          subgoal for p
            using no_invs by simp
               apply (rule init_state_propsE[OF a, simplified Lvc])
               apply simp
               apply (rule init_state_propsE[OF a, simplified Lvc])
              apply simp
          using Lvc'[simplified main_auto_init_edge_effect_alt Let_def Lvc prod.case] apply simp
          using Lvc'[simplified main_auto_init_edge_effect_alt Let_def Lvc prod.case] apply simp
           apply (subst v')
           apply (rule is_upds.intros)
            defer
            apply (rule is_upds.intros)
             defer
          unfolding set_prop_ab_def
             apply (rule is_upds_set_vars_map)
              apply (subst map_map[symmetric])
              apply blast
             apply simp
            apply (rule x[simplified Lvc', THEN init_planning_state_propsE])
          using Lv_conds_def apply blast
          by (simp add: is_upd_const_simp)+
      qed
      thus "(case x of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). net_impl.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (main_auto_init_edge_effect x)"
        using Lvc Lvc' by auto
    qed
    ultimately
    show "init_planning_state_props (main_auto_init_edge_effect x) \<and> graph_impl.steps [x, main_auto_init_edge_effect x]" by simp
  qed
qed

thm steps_seq.ext_seq'_induct_list_prop_and_post[where P = happening_pre_pre_delay and Q = happening_post and R = init_planning_state_props']

(* We need to prove these two for each happening. These are the same as the ones above *)
term "i < length planning_sem.htpl \<Longrightarrow> happening_pre_pre_delay i s \<Longrightarrow> happening_post i (last ((map delay_and_apply [0..<length planning_sem.htpl] ! i) s))"
term "i < length planning_sem.htpl \<Longrightarrow> happening_pre_pre_delay i s \<Longrightarrow> graph_impl.steps (s # (map delay_and_apply [0..<length planning_sem.htpl] ! i) s)"

thm graph_impl.steps.intros

(* The first function application is preceded by a delay *)

lemma apply_instant_actions_alt: "ext_seq (apply_instant_actions xs) = 
  fold (ext_seq o seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) xs) "
  unfolding apply_instant_actions_def 
  unfolding ext_seq_seq_apply'_conv_fold
  unfolding apply_snap_action_def
  by (induction xs) auto


schematic_goal action_auto_urg: "urgent ((automaton_of \<circ> conv_automaton) (action_to_automaton a)) = ?x"
  unfolding urgent_def action_to_automaton_def Let_def comp_apply fst_conv snd_conv conv_automaton_def prod.case automaton_of_def list.set ..

lemma in_setE:
  assumes "x \<in> set xs"
    and "\<And>i. i < length xs \<Longrightarrow> x = xs ! i \<Longrightarrow> thesis"
  shows thesis using assms unfolding in_set_conv_nth by blast

lemma sum_list_pos_if_ex_pos: "\<exists>x \<in> set xs. 0 < x \<Longrightarrow> (0::nat) < sum_list xs" 
  unfolding sum_list.eq_foldr apply (induction xs) apply simp
  by fastforce

lemma v_pl_cond_sat: 
  assumes "Lv_conds L v"
  shows "check_bexp v pl_is_1 True"
  unfolding pl_is_1_def
  unfolding check_bexp_simps is_val_simps
  using assms unfolding Lv_conds_def by simp

lemma end_starts_possible:
  assumes "graph_impl.steps xs \<and> happening_pre_end_starts i (last xs)"
      and end_indices: "end_indices = filter (is_ending_index (planning_sem.time_index i)) [0..<length actions]"
      and i: "i < length planning_sem.htpl"
    shows "graph_impl.steps ((ext_seq \<circ> seq_apply) (map edge_3_effect end_indices) xs) \<and> 
          happening_pre_instants i (last ((ext_seq \<circ> seq_apply) (map edge_3_effect end_indices) xs))"
proof -
  interpret eip: filter_sorted_distinct_list "[0..<length actions]" "is_ending_index (planning_sem.time_index i)" end_indices 
    apply (unfold_locales)
    using end_indices by auto

  have eij_in_act': "j < length actions" 
    if "i < length end_indices"
      "j \<le> end_indices ! i" for i j
    using set_nthI[OF that(1)]
    apply -
    apply (subst (asm) (2) end_indices)
    apply (subst (asm) set_filter)
    using that
    by simp
  
  have end_indices_inc_all: "\<not> is_ending_index (planning_sem.time_index i) m"
    if "Suc j < length end_indices" "Suc (end_indices ! j) \<le> m" "m < end_indices ! Suc j" for j m
    apply (rule eip.ys_inc_all)
    using eij_in_act' that by auto

  have end_indices_inc_all_below: "\<not> is_ending_index (planning_sem.time_index i) m"
    if "0 < length end_indices" "m < end_indices ! 0" for m
    apply (rule eip.ys_inc_all_below)
    using that eij_in_act'[OF that(1)] by auto

  have end_indices_inc_all_above: "\<not> is_ending_index (planning_sem.time_index i) m"
    if "end_indices ! (length end_indices - 1) < m" "m < length actions" for m
    apply (rule eip.ys_inc_all_above)
    using that by auto

  have image_end_indices_conv_actions: "((!) actions) ` set end_indices = planning_sem.ending_actions_at (planning_sem.time_index i)"
    unfolding planning_sem.ending_actions_at_def end_indices 
    unfolding set_filter image_Collect set_upt
    unfolding is_ending_index_def 
    apply (rule equalityI)
     apply auto[1]
    apply (rule subsetI)
    apply (elim CollectE conjE)
    apply (subst (asm) set_conv_nth)
    by auto

  show ?thesis
  proof (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[
            where R = "happening_pre_end_starts i" 
              and S = "happening_post_end_starts i" 
              and R' = "happening_pre_instants i"
              and fs = "map edge_3_effect end_indices"
              and P = "end_start_pre i o ((!) end_indices)"
              and Q = "end_start_post i o ((!) end_indices)",
              OF assms(1), simplified length_map nth_map],
            goal_cases)
    case (1 j s)

    have j: "j < length end_indices" using 1 by blast
    have esp: "end_start_pre i (end_indices ! j) s" using 1 by simp

    have eij_in_act: "end_indices ! j < length actions"
                    "actions ! (end_indices ! j) \<in> set actions"
      using eij_in_act'[OF j] by simp+
  
    have eij_ending: "is_ending_index (planning_sem.time_index i) (end_indices ! j)"
      using set_nthI[OF j]
      apply -
      apply (subst (asm) (2) end_indices)
      by simp
  
    obtain L v c where
      s: "s = (L, v, c)" using prod_cases3 by blast


    have v_prop_to_lock: "v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index i) p (end_indices ! j)))"
      if p_in_vars: "p \<in> set props" "prop_to_lock p \<in> dom (map_of net_bounds)" for p
      apply (insert esp)
      unfolding s
      apply (drule end_start_preD)
      using p_in_vars by simp

    have over_all_in_props: "set (over_all (actions ! (end_indices ! j))) \<subseteq> set props"
      using acts_ref_props planning_sem.act_ref_props_def planning_sem.snap_ref_props_def eij_in_act by auto

    define v' where "v' = (v(map prop_to_lock (over_all (actions ! (end_indices ! j))) [\<mapsto>] map (\<lambda>x. (the \<circ> v) x - 1) (map prop_to_lock (over_all (actions ! (end_indices ! j))))))"
    
    have variables_locked_after:"v' (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index i) p (Suc (end_indices ! j))))" 
      if p_in_vars: "p \<in> set props" "prop_to_lock p \<in> dom (map_of net_bounds)" 
      for p
    proof (cases "p \<in> set (over_all (actions ! (end_indices ! j)))")
      case True
        have v'_prop_to_lock: "v' (prop_to_lock p) = Some (the (v (prop_to_lock p)) - 1)"
          unfolding v'_def
          apply (subst distinct_map_upds)
          using True eij_in_act apply simp
          apply (rule distinct_inj_on_map)
          apply (rule distinct_over_all[THEN bspec[of _ _ "actions ! (end_indices ! j)"]])
          using eij_in_act apply simp
           apply (rule inj_on_subset)
          apply (rule variables_inj)
          using eij_in_act acts_ref_props unfolding planning_sem.act_ref_props_def apply simp
          unfolding comp_def by simp
      
      have pudp_Suc: "partially_updated_locked_before (planning_sem.time_index i) p (Suc (end_indices ! j)) = partially_updated_locked_before (planning_sem.time_index i) p (end_indices ! j) - 1"
        unfolding partially_updated_locked_before_def 
        apply (subst sum_list.eq_foldr)
        apply (subst upt_Suc_append, simp)
        apply (subst map_append)
        apply (subst filter_append)
        apply (subst map_append)
        apply (subst foldr_append)
        apply (subst list.map)+
        apply (subst filter.simps)
        apply (subst (3) if_P)
         apply (rule True)
        apply (subst filter.simps)
        apply (subst list.map)+
        apply (subst foldr.simps)
        unfolding comp_def
        apply (subst foldr.simps)
        apply (subst (2) if_P)
         apply (subst is_ending_index_def[symmetric])
        using eij_ending apply blast
        apply (subst id_def)
        apply (subst sum_list.eq_foldr)
        apply (subst foldr_assoc)
        by linarith
      show ?thesis 
        apply (subst v'_prop_to_lock)
        apply (subst pudp_Suc)
        apply (subst v_prop_to_lock[OF p_in_vars])
        using partially_updated_locked_before_pos[OF True eij_in_act(1) eij_ending] i
        by auto
    next
      case False
      have "partially_updated_locked_before (planning_sem.time_index i) p (Suc (end_indices ! j)) = partially_updated_locked_before (planning_sem.time_index i) p (end_indices ! j)" 
        unfolding partially_updated_locked_before_def using False by simp
      moreover
      have "v' (prop_to_lock p) = v (prop_to_lock p)"
        unfolding v'_def
        apply (subst map_upds_apply_nontin)
        using False variable_sets_unique p_in_vars over_all_in_props by simp+
      ultimately
      show ?thesis using v_prop_to_lock p_in_vars by presburger
    qed

    
    have bounded_after: "Simple_Network_Language.bounded (map_of net_bounds) v'"
    proof (rule updated_bounded[OF _ _ v'_def], goal_cases)
      case 1
      show ?case using esp s 
        by (auto intro: esp Lv_conds_dests happening_invs_dests end_start_invs_dests end_start_pre_dests)
    next
      case 2
      then show ?case by simp
    next
      case 3
      show ?case 
        apply (insert 3)
        apply (rule ballI)
      subgoal for x
        unfolding set_map
        apply (erule imageE)
        subgoal for p
          apply (erule ssubst[of x])
          apply (frule set_mp[OF over_all_in_props])
          apply (intro exI conjI)
            apply (rule map_of_net_bounds_action_inv[OF eij_in_act(2)])
          using variables_locked_after map_of_net_bounds_action_inv[OF eij_in_act(2)] 
            partially_updated_locked_before_ran by fastforce+
        done
      done
  qed 
 (* is_upd_make_updI *)
  have is_upds: "is_upds v (map (inc_prop_lock_ab (- 1)) (over_all (actions ! (end_indices ! j))))
     (v(map prop_to_lock (over_all (actions ! (end_indices ! j))) [\<mapsto>] map (\<lambda>x. plus_int (the (v x)) (- 1)) (map prop_to_lock (over_all (actions ! (end_indices ! j))))))"
    apply (rule is_upds_inc_vars)
       prefer 3
       apply (subst inc_prop_lock_ab_def) 
       apply (subst map_map[symmetric])
       apply (rule HOL.refl)
       apply (rule subsetI)
      apply (frule map_of_net_bounds_action_inv[rotated])
       apply (rule eij_in_act)
    subgoal for x
      unfolding set_map
      apply (erule imageE)
      using esp[simplified s, THEN end_start_pre_dests(2)] over_all_in_props by blast
     apply (rule distinct_inj_on_map)
    using distinct_over_all eij_in_act apply blast
    using inj_on_subset over_all_in_props variables_inj apply blast
    unfolding comp_def map_map by blast
  have plus_minus_rule: "(\<lambda>x. plus_int x (-1)) = (\<lambda>x. x - 1)" by auto

    show ?case
      apply (rule conjI)
      subgoal
        apply (insert esp)
        unfolding s
          unfolding edge_3_effect_alt comp_def
          apply (rule end_start_postI, simp)
               apply (drule end_start_pre_dests(1))
          subgoal
            apply (erule end_start_invs_maintained)
            subgoal                     
              apply (erule happening_invs_maintained)
              subgoal 
                apply (erule Lv_conds_maintained)
                   apply simp
                  apply simp
                 apply (subst map_upds_apply_nontin, force simp: variables_unique)+
                apply simp
                using bounded_after
                unfolding v'_def by auto
              subgoal apply (subst fun_upd_other)
                using clocks_unique by (blast, simp)
              subgoal 
                apply (intro strip)
                apply (subst fun_upd_other)
                 apply (rule clocks_unique)
                   apply simp
                using nth_actions_unique eij_in_act index_case_disj eij_ending by blast+
              subgoal apply (subst fun_upd_other)
                using clocks_unique by (blast, simp)
              subgoal 
                apply (intro strip)
                apply (subst fun_upd_other)
                 apply (rule clocks_unique)
                   apply simp
                using nth_actions_unique eij_in_act index_case_disj eij_ending by blast+
              subgoal 
                apply (intro allI impI)
                apply (frule index_case_disj)
                apply (subst nth_list_update_neq)
                using eij_ending by auto
              done
            subgoal
              apply (intro allI impI)
              apply (subst map_upds_apply_nontin)
              using variable_sets_unique over_all_in_props 
              by auto
            subgoal
              apply (subst map_upds_apply_nontin)
              using variable_sets_unique
              by auto
            subgoal using clocks_unique by auto
            subgoal using clocks_unique by auto
            subgoal 
                apply (intro strip)
                apply (subst fun_upd_other)
                 apply (rule clocks_unique)
                   apply simp
                using nth_actions_unique eij_in_act index_case_disj eij_ending by blast+
            subgoal 
                apply (intro allI impI)
                apply (frule index_case_disj)
                apply (subst nth_list_update_neq)
              using eij_ending nth_actions_unique eij_in_act 
              by auto
            subgoal
                apply (intro allI impI)
                apply (frule index_case_disj)
                apply (subst nth_list_update_neq)
              using eij_ending nth_actions_unique eij_in_act 
              by auto
            done
          subgoal by (auto dest!: variables_locked_after simp: comp_def v'_def)
          subgoal apply (intro allI impI)
            subgoal for k
              apply (subst nth_list_update)
               apply (drule end_start_pre_dests(1))
               apply (drule end_start_invs_dests(1))
               apply (drule happening_invs_dests(1))
               apply (drule Lv_condsD) 
              using eij_in_act apply simp
              apply (cases "k < end_indices ! j")
              by (auto dest: end_start_pre_dests)
            done
          subgoal apply (intro allI impI)
            subgoal for k
              apply (cases "k < end_indices ! j")
              by (auto dest: end_start_pre_dests)
            done
          subgoal apply (intro allI impI)
            subgoal for k
              apply (cases "k < end_indices ! j")
              by (auto dest: end_start_pre_dests)
            done
          subgoal
            apply (intro strip)
            unfolding act_clock_pre_happ_simps
                apply (subst fun_upd_other)
                 apply (rule clocks_unique)
                   apply simp
                using nth_actions_unique eij_in_act index_case_disj eij_ending apply blast
                using nth_actions_unique eij_in_act index_case_disj eij_ending apply blast
                using end_start_pre_dests by auto
              done
        subgoal apply (insert esp j)
          apply (rule single_step_intro)
          unfolding s prod.case edge_3_effect_alt Let_def prod.case
          apply (rule non_t_step_intro[where a="Internal (STR '''')", simplified])
           prefer 2
          subgoal by (force dest: end_start_pre_dests(1) end_start_invs_dests(1) happening_invs_dests(1) Lv_conds_dests)
          unfolding net_impl.sem_def
          apply (rule step_u.step_int[simplified TAG_def])
                    apply (subst conv_trans[of "Suc (end_indices ! j)"])
          using eij_in_act timed_automaton_net_def apply simp
                    apply (rule image_eqI[of _ _ "edge_3 (actions ! (end_indices ! j))"])
                     apply (subst edge_3_def)
                     apply simp
          using nth_auto_trans eij_in_act apply simp
          subgoal apply (rule disjI2) 
            apply (intro strip)
            apply (subst conv_committed, simp)
            apply (subst no_committed)
            by (auto simp: length_net_automata)
          subgoal by (force intro: end_start_pre_dests end_start_invs_dests  happening_invs_dests Lv_conds_dests v_pl_cond_sat)
          subgoal apply (intro guard_append)
            using eij_in_act eij_ending
            apply (auto intro: ending_actions_sat_dur_const_specs dest!: end_start_pre_dests(1)  end_start_invs_dests(1)  happening_invs_dests(2) simp: is_ending_index_def)[2]
            unfolding map_map[symmetric]
            subgoal apply (rule ending_actions_sat_mutex_const_specs)
                    apply (auto intro: eij_in_act intro: eij_ending simp: is_ending_index_def[symmetric])[2]
                  apply (auto dest!: end_start_pre_dests(1) end_start_invs_dests(1) dest: happening_invs_dests(2,3,4,5) simp: index_case_defs set_conv_nth)[4]
              by (auto dest!: end_start_pre_dests intro: eij_in_act eij_ending)[1]
            subgoal apply (rule ending_actions_sat_mutex_const_specs)
                    apply (auto intro: eij_in_act intro: eij_ending simp: is_ending_index_def[symmetric])[2]
                  apply (auto dest!: end_start_pre_dests(1) end_start_invs_dests(1) dest: happening_invs_dests(2,3,4,5) simp: index_case_defs set_conv_nth)[4]
              by (auto dest!: end_start_pre_dests intro: eij_in_act eij_ending)[1]
            done
          subgoal using no_invs by simp
          subgoal using eij_in_act eij_ending by (blast dest: end_start_pre_dests)
          subgoal using eij_in_act by (auto dest!: end_start_pre_dests(1) end_start_invs_dests(1) happening_invs_dests(1) Lv_conds_dests(1))
          subgoal by blast
          subgoal by simp
          subgoal using is_upds by blast
          using bounded_after unfolding map_map v'_def comp_apply by auto
        done
  next
    case (2 i s)
    thus ?case 
      apply (insert 2)
      apply (induction s)
      subgoal for L v c
        unfolding comp_def
        apply (rule end_start_preI, simp)
        subgoal by (drule end_start_post_dests(1), simp)
        subgoal
          apply (subst partially_updated_locked_before_inv[where n = "(Suc (end_indices ! i))", symmetric])
          using eip.ys_mono[rotated] apply fastforce
          using end_indices_inc_all is_ending_index_def by (auto simp: end_start_post_dests)
        subgoal 
          apply (intro strip, elim conjE)
          subgoal for j
            by (cases "j \<le> end_indices ! i") (auto simp: end_indices_inc_all end_start_post_dests)
          done
        subgoal by (auto simp: end_start_post_dests dest: eip.ys_mono[rotated])
        subgoal 
          apply (intro strip, elim conjE)
          subgoal for j
            by (cases "j \<le> end_indices ! i") (auto simp: end_indices_inc_all end_start_post_dests)
          done
        subgoal apply (drule end_start_post_dests(6), simp)
          by (auto dest: eip.ys_mono[rotated])
        done
      done
  next
    case (3 x)
    thus ?case 
      apply (induction x)
      subgoal for L v c
        unfolding comp_def
        apply (rule end_start_preI, simp)
        subgoal by (drule happening_pre_end_starts_dests(1)) simp+
       
        subgoal
          apply (subst partially_updated_locked_before_inv[where n = 0, symmetric], simp)
          using end_indices_inc_all_below[simplified is_ending_index_def] apply blast
          using partially_updated_locked_before_0_is_locked_before 
          by (simp add: happening_pre_end_starts_dests)+
        subgoal by (auto simp: end_indices_inc_all_below happening_pre_end_starts_dests)
        subgoal by (simp add: happening_pre_end_starts_dests)
        subgoal by (auto simp: end_indices_inc_all_below happening_pre_end_starts_dests)
        subgoal by (drule happening_pre_end_starts_dests, simp+)
        done
      done
  next
    case (4 x)
    thus ?case
      apply (induction x)
      subgoal for L v c 
        unfolding comp_def
        apply (rule happening_post_end_startsI, simp)
        subgoal by (drule end_start_post_dests(1), simp+)
       
        subgoal
          apply (subst partially_updated_locked_before_by_all_actions_is_locked_during[symmetric])
          apply (subst partially_updated_locked_before_inv[symmetric, where n = "Suc (end_indices ! (length end_indices - 1))"])
          subgoal using eip.nth_ys_ran by (force intro: Suc_leI)
          by (auto simp: end_indices_inc_all_above[simplified is_ending_index_def] end_start_post_dests)
        subgoal apply (intro strip)
          subgoal for k
            by (cases "k \<le> end_indices ! (length end_indices - 1)"; 
              force dest!: end_indices_inc_all_above[rotated] simp: end_start_post_dests)
          done
      subgoal apply (intro strip)
        subgoal for k
          by (cases "k \<le> end_indices ! (length end_indices - 1)"; 
              force dest!: end_indices_inc_all_above[rotated] simp: end_start_post_dests)
        done
      done
    done
  next
    case (5 x)
    thus ?case 
      apply (induction x)
      subgoal for L v c

        apply (subst (asm) length_0_conv)
        apply (drule arg_cong[where f = set])
        unfolding list.set
        apply (rule happening_post_end_startsI, simp)
        subgoal by (drule happening_pre_end_starts_dests(1), simp+)
        subgoal apply (drule happening_pre_end_starts_dests(2), simp)
          using planning_sem.locked_before_and_during_if_none_ending
          using image_end_indices_conv_actions by auto
        using end_indices by auto
      done
  next
    case (6 x)
    thus ?case 
      apply (induction x)
      subgoal for L v c
      apply (rule happening_pre_instantsI, simp)
        apply (rule instant_action_invsI, simp)
        by (intro end_start_invs_dests happening_post_end_starts_dests, simp, simp)+
      done
  qed
qed

lemma Suc_lessI: "n < m - 1 \<Longrightarrow> Suc n < m" by auto

lemma instant_actions_possible:
  assumes "graph_impl.steps xs \<and> happening_pre_instants i (last xs)"
      and instant_indices: "instant_indices = filter (is_instant_index (planning_sem.time_index i)) [0..<length actions]"
      and i: "i < length planning_sem.htpl"
    shows "graph_impl.steps (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) instant_indices) xs) 
  \<and> happening_pre_start_starts i (last (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) instant_indices) xs))"
proof -                             
  interpret iip: filter_sorted_distinct_list "[0..<length actions]" "is_instant_index (planning_sem.time_index i)" instant_indices
    apply (unfold_locales)
    using instant_indices by auto

  have iij_in_act': "j < length actions" 
    if "i < length instant_indices"
      "j \<le> instant_indices ! i" for i j
    using set_nthI[OF that(1)]
    apply -
    apply (subst (asm) (2) instant_indices)
    apply (subst (asm) set_filter)
    using that
    by simp
  
  have instant_indices_inc_all: "\<not> is_instant_index (planning_sem.time_index i) m"
    if "Suc j < length instant_indices" "Suc (instant_indices ! j) \<le> m" "m < instant_indices ! Suc j" for j m
    apply (rule iip.ys_inc_all)
    using iij_in_act' that by auto

  have instant_indices_inc_all_below: "\<not> is_instant_index (planning_sem.time_index i) m"
    if "0 < length instant_indices" "m < instant_indices ! 0" for m
    apply (rule iip.ys_inc_all_below)
    using that iij_in_act'[OF that(1)] by auto

  have instant_indices_inc_all_above: "\<not> is_instant_index (planning_sem.time_index i) m"
    if "instant_indices ! (length instant_indices - 1) < m" "m < length actions" for m
    apply (rule iip.ys_inc_all_above)
    using that by auto

  have image_instant_indices_conv_actions: "((!) actions) ` set instant_indices = planning_sem.instant_actions_at (planning_sem.time_index i)"
    unfolding planning_sem.instant_actions_at_def instant_indices 
    unfolding set_filter image_Collect set_upt
    unfolding is_instant_index_def 
    apply (rule equalityI)
     apply auto[1]
    apply (rule subsetI)
    apply (elim CollectE conjE)
    apply (subst (asm) set_conv_nth)
    by auto

  have nat_leE: thesis if  "x \<le> y" "x < y \<Longrightarrow> thesis" "x = y \<Longrightarrow> thesis"  for x y::nat and thesis using that by linarith

  show ?thesis
  proof (rule steps_seq.fold_ext_seq_comp_seq_apply_induct_list_prop_composable[
        where R = "happening_pre_instants i" 
          and S = "happening_post_instants i"
          and P = "instant_pre i o ((!) instant_indices)"
          and Q = "instant_post i o ((!) instant_indices)"
          and fs = "(map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) instant_indices)",
        simplified length_map length_upt nth_map set_map comp_apply , 
        OF assms(1)], 
      goal_cases)
    case (1 f)
    then show ?case by auto
  next
    case (2 j s)

    
    have iij_set: "instant_indices ! j \<in> set instant_indices" using 2 by auto
    with image_instant_indices_conv_actions
    have "(actions ! (instant_indices ! j)) \<in> planning_sem.instant_actions_at (planning_sem.time_index i)" by blast
    
    hence iij_instant: "planning_sem.is_instant_action (planning_sem.time_index i) (actions ! (instant_indices ! j))"
      and iij_in_act: "actions ! (instant_indices ! j) \<in> set actions" using planning_sem.instant_actions_at_def by simp_all

    have iij_instant_index: "is_instant_index (planning_sem.time_index i) (instant_indices ! j)" apply (insert iij_set) apply (subst (asm) (2) instant_indices) by simp

    have iij_ran: "instant_indices ! j < length actions" 
      apply (insert iij_set)
      apply (subst (asm) (2) instant_indices)
      by simp

    have pre_in_props: 
        "set (pre (at_start (actions ! (instant_indices ! j)))) \<subseteq> set props"
        "set (pre (at_end (actions ! (instant_indices ! j)))) \<subseteq> set props"
      using acts_ref_props planning_sem.act_ref_props_def planning_sem.snap_ref_props_def iij_in_act by auto
    have adds_in_props: 
        "set (adds (at_start (actions ! (instant_indices ! j)))) \<subseteq> set props"
        "set (adds (at_end (actions ! (instant_indices ! j)))) \<subseteq> set props"
      using acts_ref_props planning_sem.act_ref_props_def planning_sem.snap_ref_props_def iij_in_act by auto
    have dels_in_props: 
        "set (dels (at_start (actions ! (instant_indices ! j)))) \<subseteq> set props"
        "set (dels (at_end (actions ! (instant_indices ! j)))) \<subseteq> set props"
      using acts_ref_props planning_sem.act_ref_props_def planning_sem.snap_ref_props_def iij_in_act by auto

    
    have v_pre_conds_sat: "Simple_Expressions.check_bexp v (bexp_and_all (map (is_prop_ab 1) (pre (at_start (actions ! (instant_indices ! j)))))) True"
      if prop_state: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_part_updated_prop_state i (instant_indices ! j) p)" for v
    proof -
      { fix p
        assume p: "p \<in> set (pre (at_start (actions ! (instant_indices ! j))))"
        moreover
        have "p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds)" using map_of_net_bounds_action_start_pre iij_in_act pre_in_props p by auto
        ultimately
        have "v (prop_to_var p) = Some 1" using pre_val_in_instant_part_updated_prop_state_if i  prop_state iij_ran iij_instant[simplified planning_sem.is_instant_action_def] by metis 
        hence "Simple_Expressions.check_bexp v (is_prop_ab 1 p) True" 
          unfolding is_prop_ab_def comp_def
          by (simp add: check_bexp_simps  is_val_simps)
      } 
      hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_start (actions ! (instant_indices ! j))))). Simple_Expressions.check_bexp v b True" by auto
      thus ?thesis using check_bexp_all by blast
    qed
    
    have v_lock_conds_sat: "Simple_Expressions.check_bexp v (bexp_and_all (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! (instant_indices ! j))))) (dels (at_start (actions ! (instant_indices ! j))))))) True"
      if locked: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))" for v
    proof -
      { fix p
        assume p: "p \<notin> set (adds (at_start (actions ! (instant_indices ! j))))"
               "p \<in> set (dels (at_start (actions ! (instant_indices ! j))))"
        hence "p \<notin> planning_sem.plan_invs_during (planning_sem.time_index i)" using planning_sem.snap_does_not_delete_inv iij_instant planning_sem.action_happening_case_defs by auto
        hence "planning_sem.locked_during (planning_sem.time_index i) p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
        moreover
        have "prop_to_lock p \<in> set (map prop_to_lock (dels (at_start (actions ! (instant_indices ! j)))))" 
             "prop_to_lock p \<notin> set (map prop_to_lock (adds (at_start (actions ! (instant_indices ! j)))))" 
          using p apply simp
          unfolding set_map
          apply (rule variable_sets_unique)
          using adds_in_props p dels_in_props by auto
        hence "prop_to_lock p \<in> dom (map_of net_bounds)" 
          using map_of_net_bounds_action_start_del_lock[OF iij_in_act] by blast
        ultimately
        have "v (prop_to_lock p) = Some 0" using locked p dels_in_props by auto
        hence "Simple_Expressions.check_bexp v (is_prop_lock_ab 0 p) True" 
          unfolding is_prop_lock_ab_def 
          by (simp add: check_bexp_simps  is_val_simps)
      } 
      hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! (instant_indices ! j))))) (dels (at_start (actions ! (instant_indices ! j)))))). Simple_Expressions.check_bexp v b True"  by auto
      thus ?thesis using check_bexp_all by blast
    qed

    have v_ending_pre_conds_sat: "Simple_Expressions.check_bexp v' (bexp_and_all (map (is_prop_ab 1) (pre (at_end (actions ! (instant_indices ! j)))))) True"
      if prop_state: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_var p) = Some (instant_intermediate_prop_state i (instant_indices ! j) p)" for v'
    proof -
      { fix p
        assume p: "p \<in> set (pre (at_end (actions ! (instant_indices ! j))))"
        moreover
        have "prop_to_var p \<in> dom (map_of net_bounds)" using p pre_in_props iij_in_act p map_of_net_bounds_action_end_pre by force
        ultimately
        have "v' (prop_to_var p) = Some 1" 
          using pre_val_in_instant_intermediate_prop_state_if[OF i _ iij_instant_index] 
          using iij_ran prop_state pre_in_props by force
    
        hence "Simple_Expressions.check_bexp v' (is_prop_ab 1 p) True" 
          unfolding is_prop_ab_def
          by (simp add: check_bexp_simps is_val_simps)
      } 
      hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_end (actions ! (instant_indices ! j))))). Simple_Expressions.check_bexp v' b True" by auto
      thus ?thesis using check_bexp_all by blast
    qed

    
    have v_ending_lock_conds_sat: 
        "check_bexp v' (bexp_and_all (map (is_prop_lock_ab 0) 
                        (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! (instant_indices ! j))))) (dels (at_end (actions ! (instant_indices ! j))))))) True"
      if locked: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))" for v'
    proof -
      { fix p
        assume p: "p \<notin> set (adds (at_end (actions ! (instant_indices ! j))))"
               "p \<in> set (dels (at_end (actions ! (instant_indices ! j))))"
        hence "p \<notin> planning_sem.plan_invs_during (planning_sem.time_index i)" using planning_sem.snap_does_not_delete_inv iij_instant planning_sem.action_happening_case_defs by auto
        hence "planning_sem.locked_during (planning_sem.time_index i) p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
        moreover 
        have "prop_to_lock p \<in> set (map prop_to_lock (dels (at_end (actions ! (instant_indices ! j)))))" 
             "prop_to_lock p \<notin> set (map prop_to_lock (adds (at_end (actions ! (instant_indices ! j)))))" 
          using p apply simp
          unfolding set_map
          apply (rule variable_sets_unique)
          using adds_in_props p dels_in_props by auto
        hence "prop_to_lock p \<in> dom (map_of net_bounds)" 
          using map_of_net_bounds_action_end_del_lock[OF iij_in_act] by auto 
        ultimately
        have "v' (prop_to_lock p) = Some 0" using locked dels_in_props p by auto
        
        hence "Simple_Expressions.check_bexp v' (is_prop_lock_ab 0 p) True" 
          unfolding is_prop_lock_ab_def 
          by (simp add: check_bexp_simps is_val_simps)
      } 
      hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) 
                      (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! (instant_indices ! j))))) 
                        (dels (at_end (actions ! (instant_indices ! j)))))). 
            Simple_Expressions.check_bexp v' b True"  by auto
      thus ?thesis using check_bexp_all by blast
    qed


    have mutex_conds_sat: "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (net_int_clocks (at_start (actions ! (instant_indices ! j)))) @ map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (net_int_clocks (at_start (actions ! (instant_indices ! j))))" 
      if "instant_pre i (instant_indices ! j) (L, v, c)" for L v c
    proof (intro guard_append)
      have 1: "\<forall>b\<in>set actions. planning_sem.is_ending_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b (planning_sem.time_index i)"
          unfolding index_case_conv_action[symmetric] 
          by (blast intro:  instant_pre_dests instant_action_invs_dests happening_invs_dests that)
      have 2: "\<forall>b\<in>set actions. planning_sem.is_not_happening_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro:  instant_pre_dests instant_action_invs_dests happening_invs_dests that)
      have 3: "\<forall>b\<in>set actions. planning_sem.is_starting_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro:  instant_pre_dests instant_action_invs_dests happening_invs_dests that)
      have 4: "\<forall>b\<in>set actions. planning_sem.is_not_happening_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro:  instant_pre_dests instant_action_invs_dests happening_invs_dests that)
      have 5: "act_clock_pre_happ c act_to_start_clock (actions ! (instant_indices ! j)) (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        using that instant_pre_dests iij_instant_index iij_ran by auto
      show "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (net_int_clocks (at_start (actions ! (instant_indices ! j))))"
        apply  (rule instant_action_sat_mutex_start[OF iij_in_act iij_instant])
        using 1 2 3 4 5 by auto
      show "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (net_int_clocks (at_start (actions ! (instant_indices ! j))))"
        apply  (rule instant_action_sat_mutex_start[OF iij_in_act iij_instant])
        using 1 2 3 4 5 by auto
    qed

    show ?case 
      apply (insert 2)
      apply (subst last_ConsR[symmetric, where x = s, OF seq_apply_not_Nil, OF list.distinct(2)])
      apply (erule steps_seq.seq_apply_ConsI[where P = "instant_pre i (instant_indices ! j)" and Q = "instant_starting_cond i (instant_indices ! j)"])
      apply (erule steps_seq.seq_apply_ConsI[where P = "instant_starting_cond i (instant_indices ! j)" and Q = "instant_ending_cond i (instant_indices ! j)"])
      apply (erule steps_seq.seq_apply_ConsI[where P = "instant_ending_cond i (instant_indices ! j)" and Q = "instant_post i (instant_indices ! j)"])
      subgoal by auto
      unfolding triv_forall_equality 
      subgoal for x 
        apply (induction x)
        subgoal for L v c
          unfolding end_edge_effect_alt Let_def prod.case
          apply (rule instant_postI)
          subgoal apply (frule instant_ending_cond_dests(1)) 
            apply (erule instant_action_invs_maintained)
            subgoal apply (erule happening_invs_maintained)
              subgoal apply (erule Lv_conds_maintained)
                   apply simp
                  apply simp
                 apply (((subst map_upds_apply_nontin | subst fun_upd_other), force simp: variables_unique)+, simp)
                subgoal 
            apply (rule upds_map_bounded)
              prefer 2
              apply (rule HOL.refl)
             apply (rule upds_map_bounded)
               prefer 2
               apply (rule HOL.refl)
                    apply (rule single_upd_bounded)
                 apply simp
                apply (rule map_of_net_bounds_acts_active)
                     apply (drule instant_ending_cond_dests(3)) 
                        apply simp
            subgoal using planning_sem.active_before_less_if_scheduled iij_instant iij_in_act instant_ending_cond_dests(3)
              by (fastforce simp: planning_sem.action_happening_case_defs card_action_set)
            subgoal by (force intro: map_of_net_bounds_action_end_del iij_instant iij_in_act)+
            subgoal by (force intro: map_of_net_bounds_action_end_add iij_instant iij_in_act)+
            done
          done
            apply simp
           apply simp
          apply simp
         apply simp
        apply (intro allI impI)
        subgoal for k apply (cases "(instant_indices ! j)  = k")
          using iij_instant(1)[simplified index_case_defs[symmetric]]
          by (auto dest: index_case_dests_disj)
        done
      subgoal  apply (drule instant_ending_cond_dests(1))
        apply (drule instant_action_invs_dests(2))
        apply (intro allI impI)
        apply (subst map_upds_apply_nontin, force simp: variables_unique)+
        apply (subst fun_upd_other)
        by (simp_all add: variables_unique)
      subgoal
        apply (intro allI impI)
        subgoal for k apply (cases "(instant_indices ! j) = k")
          using iij_instant(1)[simplified index_case_defs[symmetric]]
          by (auto dest: index_case_dests_disj)
        done
      subgoal
        apply (intro allI impI)
        subgoal for k apply (cases "(instant_indices ! j)  = k")
          using iij_instant(1)[simplified index_case_defs[symmetric]]
          by (auto dest: index_case_dests_disj)
        done
      subgoal
        apply (intro allI impI)
        subgoal for k apply (cases "(instant_indices ! j)  = k")
          using iij_instant(1)[simplified index_case_defs[symmetric]]
          by (auto dest: index_case_dests_disj)
        done
      subgoal
        apply (intro allI impI)
        subgoal for k apply (cases "(instant_indices ! j)  = k")
          using iij_instant(1)[simplified index_case_defs[symmetric]]
          by (auto dest: index_case_dests_disj)
        done
      done
      subgoal apply (intro allI impI)
        subgoal for p
          apply (drule instant_ending_cond_dests(2))
          apply (subst instant_part_updated_prop_state_Suc_conv_intermediate)
          apply (auto simp: i iij_instant index_case_defs iij_ran)[4] 
          apply (cases "p \<in> set (adds (at_end (actions ! (instant_indices ! j))))"; cases "p \<in> set (dels (at_end (actions ! (instant_indices ! j))))")
          subgoal by (subst map_upds_with_map) simp+
          subgoal by (subst map_upds_with_map) simp+ 
          subgoal apply (subst map_upds_apply_nontin)
             apply (subst set_map)
             apply (rule variable_sets_unique)
               apply simp
            using adds_in_props
            apply blast
             apply force
            apply (subst map_upds_with_map)
            by simp+
          subgoal apply ((subst map_upds_apply_nontin, (rule variable_sets_unique; use adds_in_props dels_in_props in blast)) | (subst fun_upd_other, rule variables_unique))+
            by (auto simp: instant_intermediate_prop_state_def[OF i])
          done
        done
      subgoal apply ((subst map_upds_apply_nontin, (rule variable_sets_unique; use adds_in_props dels_in_props in blast)) | (subst fun_upd_other, rule variables_unique))+
        by (use instant_ending_cond_dests(3) in fastforce)
      subgoal by (auto dest: instant_ending_cond_dests)
      subgoal by (auto dest: instant_ending_cond_dests)
      subgoal by (auto dest: instant_ending_cond_dests)
      subgoal by (auto dest: instant_ending_cond_dests)
      subgoal
        apply (intro allI impI)
        subgoal for k
          apply (subst nth_list_update)
           apply (force dest: instant_ending_cond_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) simp: Lv_conds_dests(1) iij_ran)
          apply (cases "k = instant_indices ! j")
          by (auto dest: instant_ending_cond_dests)
        done
      done
    done
  subgoal for x 
    apply (induction x)
    subgoal for L v c
      apply (rule single_step_intro)
      unfolding end_edge_effect_alt prod.case Let_def
      apply (rule non_t_step_intro[where a="Internal (STR '''')", simplified])
      unfolding net_impl.sem_def
       apply (rule step_u.step_int[simplified TAG_def, where p = "Suc (instant_indices ! j)"])
                 apply (subst conv_trans)
      using iij_ran length_net_automata apply simp
                 apply (rule image_eqI[where x = "end_edge (actions ! (instant_indices ! j))"])
      apply (subst end_edge_def) apply simp
                 apply (subst nth_auto_trans)
      using iij_ran apply simp
                 apply simp
      subgoal apply (intro disjI2 strip)
        apply (subst conv_committed, simp)
        using no_committed length_net_automata by auto
      subgoal apply (rule check_bexp_Cons) 
        apply (force intro: v_pl_cond_sat instant_ending_cond_dests instant_action_invs_dests happening_invs_dests)
        apply (intro check_bexp_all_append v_ending_lock_conds_sat v_ending_pre_conds_sat)
        using instant_ending_cond_dests(1,2) instant_action_invs_dests(2) by fast+ 
      subgoal by simp
      subgoal using conv_invs no_invs by simp
      subgoal using instant_ending_cond_dests by fast
      subgoal by (fastforce dest!: instant_ending_cond_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) simp: Lv_conds_dests(1) iij_ran) 
      subgoal by auto
      subgoal by auto
      subgoal
        apply (rule is_upds.intros)
         apply (subst is_upd_def)
         apply (intro exI conjI)
           apply simp
          apply (subst is_val_simps)
          apply (intro exI conjI)
        apply (rule HOL.refl)
            apply (rule check_bexp_is_val.intros)
            apply (erule instant_ending_cond_dests)
          apply (rule check_bexp_is_val.intros)
         apply (rule HOL.refl)
        apply (rule is_upds_appendI)
         apply (rule is_upds_set_vars_map)
          apply (subst set_prop_ab_def)
          apply (subst map_map[symmetric])
          apply (rule HOL.refl)
         apply (rule HOL.refl)
        apply (rule is_upds_set_vars_map)
        apply (subst set_prop_ab_def)
         apply (subst map_map[symmetric])
         apply (rule HOL.refl)
        unfolding map_map comp_def option.sel
        by (subst instant_ending_cond_dests, simp, simp)+
      subgoal by (auto intro: instant_post_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) Lv_conds_dests)
      subgoal by (auto intro: instant_ending_cond_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) Lv_conds_dests)
      done
    done
  subgoal for x 
    apply (induction x)
    subgoal for L v c
      unfolding instant_trans_edge_effect_alt Let_def prod.case
      apply (rule instant_ending_condI)
      subgoal
        apply (drule instant_starting_cond_dests(1))
        apply (erule instant_action_invs_maintained)
        subgoal 
          apply (elim happening_invs_maintained Lv_conds_maintained)
                  apply simp
                 apply simp
                apply simp
               apply simp
              apply ((subst fun_upd_other), (use clocks_unique nth_actions_unique clocks_unique in blast))
              apply simp
          subgoal 
             apply (intro strip)
             apply (subst fun_upd_other)
              apply (rule clocks_unique)
                apply (use iij_ran in simp)+
             apply (intro nth_actions_unique)
            by (use iij_ran iij_instant_index index_case_disj in blast)+
          subgoal apply (intro strip)
            apply (subst fun_upd_other)
            using clocks_unique by auto
          subgoal 
             apply (intro strip)
             apply (subst fun_upd_other)
              apply (rule clocks_unique)
                apply (use iij_ran in simp)+
             apply (intro nth_actions_unique)
            by (use iij_ran iij_instant_index index_case_disj in blast)+
          subgoal apply (intro strip)
            apply (subst nth_list_update_neq)
            using iij_instant_index index_case_disj 
            by blast+
          done
        subgoal by simp
        subgoal using clocks_unique by auto
        subgoal 
             apply (intro strip)
             apply (subst fun_upd_other)
              apply (rule clocks_unique)
                apply (use iij_ran in simp)+
             apply (intro nth_actions_unique)
          by (use iij_ran iij_instant_index index_case_disj in blast)+
        subgoal apply (intro strip)
          apply (subst nth_list_update_neq)
          using iij_instant_index index_case_disj 
          by blast+
        subgoal apply (intro strip)
          apply (subst nth_list_update_neq)
          using iij_instant_index index_case_disj 
          by blast+
        done
      subgoal using instant_starting_cond_dests by blast
      subgoal by (auto dest: instant_starting_cond_dests)
      subgoal by (auto dest: index_case_dests_disj instant_starting_cond_dests)
      subgoal using instant_starting_cond_dests by (auto  elim: nat_leE)
      subgoal apply (intro strip, elim conjE)
        apply (subst act_clock_pre_happ_simps)
        apply (subst fun_upd_other)
        apply (rule clocks_unique)
        using instant_starting_cond_dests nth_actions_unique 
        by auto 
      subgoal apply (intro strip, elim conjE)
        apply (subst act_clock_pre_happ_simps)
        apply (subst fun_upd_other)
        apply (rule clocks_unique)
        using instant_starting_cond_dests nth_actions_unique 
        by auto 
      subgoal by (auto dest!: instant_starting_cond_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) dest: Lv_conds_dests simp: iij_ran)
      subgoal by (auto dest!: instant_starting_cond_dests(1,9) instant_action_invs_dests(1) happening_invs_dests(1) dest: Lv_conds_dests simp: iij_ran)
      done
    done
  subgoal for x 
    apply (induction x)
    subgoal for L v c
      unfolding instant_trans_edge_effect_alt
      apply (rule single_step_intro)
      unfolding prod.case
      apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
      unfolding net_impl.sem_def
        apply (rule step_u.step_int)
      unfolding TAG_def
                  apply (subst conv_trans[of "Suc (instant_indices ! j)"])
      using length_net_automata iij_ran apply simp
                  apply (subst nth_auto_trans)
      using iij_ran apply simp
                  apply (rule image_eqI[where x = "instant_trans_edge (actions ! (instant_indices ! j))"])
                   apply (subst instant_trans_edge_def)
                   apply simp
                  apply simp
      subgoal apply (intro disjI2 strip)
        apply (subst conv_committed, simp)
        using no_committed length_net_automata by auto
      subgoal by (force intro: v_pl_cond_sat instant_ending_cond_dests instant_action_invs_dests happening_invs_dests)
      subgoal apply (intro guard_append)
        subgoal 
          apply (rule l_dur_sat_if)
          apply (rule planning_sem.instant_act_sat_dur_bounds)
          using iij_instant iij_instant_index iij_in_act
          by (auto dest!: instant_starting_cond_dests(4))
        subgoal 
          apply (rule u_dur_sat_if)
          apply (rule planning_sem.instant_act_sat_dur_bounds)
          using iij_instant iij_instant_index iij_in_act
          by (auto dest!: instant_starting_cond_dests(4))
        subgoal apply (rule instant_action_sat_mutex_end)
                 apply (rule iij_in_act)
                apply (rule iij_instant)
          unfolding set_conv_nth
               apply (auto simp: index_case_defs dest!: instant_starting_cond_dests(1) instant_action_invs_dests(1) dest: happening_invs_dests)[4]
          by (auto dest!: instant_starting_cond_dests(7) simp: iij_instant_index iij_ran)
        subgoal apply (rule instant_action_sat_mutex_end)
                 apply (rule iij_in_act)
                apply (rule iij_instant)
          unfolding set_conv_nth
               apply (auto simp: index_case_defs dest!: instant_starting_cond_dests(1) instant_action_invs_dests(1) dest: happening_invs_dests)[4]
          by (auto dest!: instant_starting_cond_dests(7) simp: iij_instant_index iij_ran)
        done
      subgoal using conv_invs no_invs by auto
      subgoal by (force dest: instant_starting_cond_dests)
      subgoal by (auto dest!: instant_starting_cond_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) simp: Lv_conds_dests iij_ran)
      subgoal by simp
      subgoal by simp
      subgoal by rule
      by (auto intro: instant_ending_cond_dests instant_action_invs_dests happening_invs_dests Lv_conds_dests)
    done
  subgoal for x 
    apply (induction x)
    subgoal for L v c
      unfolding start_edge_effect_alt
      apply (rule instant_starting_condI)
      subgoal
        apply (frule instant_pre_dests(1))
        apply (erule instant_action_invs_maintained)
        subgoal
          apply (erule happening_invs_maintained)
          subgoal
            apply (erule Lv_conds_maintained)
               apply simp
              apply simp
             apply ((subst map_upds_apply_nontin | subst fun_upd_other), fastforce simp: variables_unique)+
             apply simp
            apply (rule upds_map_bounded'[OF _ _ HOL.refl])
              apply (rule upds_map_bounded'[OF _ _ HOL.refl])
                apply (erule single_upd_bounded)
                  apply (rule map_of_net_bounds_acts_active)
            subgoal using instant_pre_dests(3) by fastforce
            subgoal using planning_sem.active_before_less_if_scheduled iij_instant iij_in_act card_action_set planning_sem.action_happening_case_defs 
              by (fastforce dest:instant_pre_dests(3))
            using iij_instant map_of_net_bounds_action_start_del map_of_net_bounds_action_start_add iij_in_act
            by (auto dest: instant_pre_dests)
          subgoal apply (intro strip)
             apply (subst fun_upd_other)
              apply (rule clocks_unique)
                apply (use iij_ran in simp)+
             apply (intro nth_actions_unique)
            by (use iij_ran iij_instant_index index_case_disj in blast)+
          subgoal by (use iij_ran fun_upd_other clocks_unique in auto)
          subgoal apply (intro strip)
             apply (subst fun_upd_other)
              apply (rule clocks_unique)
                apply (use iij_ran in simp)+
             apply (intro nth_actions_unique)
            by (use iij_ran iij_instant_index index_case_disj in blast)+
          subgoal by (use iij_ran fun_upd_other clocks_unique in auto)
          subgoal apply (intro strip)
            apply (rule nth_list_update_neq)
            using iij_instant_index index_case_disj by blast
          done
        subgoal by ((subst map_upds_apply_nontin | subst fun_upd_other), fastforce simp: variables_unique)+ simp
        subgoal apply (intro strip)
             apply (subst fun_upd_other)
              apply (rule clocks_unique)
                apply (use iij_ran in simp)+
             apply (intro nth_actions_unique)
            by (use iij_ran iij_instant_index index_case_disj in blast)+
          subgoal by (use iij_ran fun_upd_other clocks_unique in auto)
        using iij_instant_index iij_ran nth_actions_unique
        by (auto dest: index_case_dests_disj intro: nth_list_update_neq)
      subgoal apply (intro strip)
        subgoal for p
        apply (subst instant_intermediate_prop_state_alt)
        using i apply simp
        using iij_instant_index apply simp
          apply simp
        using iij_ran apply simp
        apply (cases "p \<in> set (adds (at_start (actions ! (instant_indices ! j))))")
         apply (subst map_upds_with_map)
           apply simp
          apply simp
         apply simp
        apply (cases "p \<in> set (dels (at_start (actions ! (instant_indices ! j))))")
         apply (subst map_upds_apply_nontin)
        apply (rule variable_sets_unique; (use adds_in_props in blast))
         apply (subst map_upds_with_map)
           apply simp
          apply simp
        apply simp
         apply ((subst map_upds_apply_nontin,  (rule variable_sets_unique; (use dels_in_props adds_in_props in blast))) | (subst fun_upd_other, (rule variables_unique)))+
        by (auto simp: instant_pre_dests(2) instant_part_updated_prop_state_def i)
      done
    subgoal apply ((subst map_upds_apply_nontin,  (rule variable_sets_unique; (use dels_in_props adds_in_props in blast))) | (subst fun_upd_other, (rule variables_unique)))+
      by (force dest: instant_pre_dests)
    subgoal apply (intro strip, elim conjE nat_leE)
             apply (subst fun_upd_other)
        apply (rule clocks_unique)
      using nth_actions_unique iij_ran instant_pre_dests by auto
    subgoal apply (intro strip, elim conjE nat_leE)
             apply (subst fun_upd_other)
        apply (rule clocks_unique)
      using nth_actions_unique iij_ran instant_pre_dests by auto
    subgoal apply (intro strip, elim conjE)
      apply (subst act_clock_pre_happ_simps)
      apply (subst fun_upd_other)
       apply (rule clocks_unique)
      using iij_ran instant_pre_dests nth_actions_unique by auto
    subgoal apply (intro strip, elim conjE)
      apply (subst act_clock_pre_happ_simps)
      apply (subst fun_upd_other)
       apply (rule clocks_unique)
      using iij_ran instant_pre_dests nth_actions_unique by auto
    subgoal 
      using nth_actions_unique iij_instant iij_ran 
      by (auto dest!: instant_pre_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) simp: Lv_conds_dests)
    subgoal by (auto dest: instant_pre_dests)
    done
  done
  subgoal for x
    apply (induction x)
    subgoal for L v c
      unfolding start_edge_effect_alt
      apply (rule single_step_intro)
      unfolding prod.case
      apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
      unfolding net_impl.sem_def
        apply (rule step_int[where p = "Suc (instant_indices ! j)"])
      unfolding TAG_def
                  apply (subst conv_trans)
      using iij_ran timed_automaton_net_def apply simp
                  apply (rule image_eqI[where x = "start_edge (actions ! (instant_indices ! j))"])
                   apply (subst start_edge_def)
                   apply simp
                  apply (subst nth_auto_trans)
      using iij_ran timed_automaton_net_def apply simp
                  apply simp
      subgoal apply (intro disjI2 strip)
        apply (subst conv_committed, simp)
        using no_committed length_net_automata by auto
      subgoal apply (rule check_bexp_Cons)
        apply (force intro: v_pl_cond_sat instant_pre_dests instant_action_invs_dests happening_invs_dests)
        apply (rule check_bexp_all_append)
        subgoal apply (drule instant_pre_dests(1)) by (auto intro: v_pre_conds_sat v_lock_conds_sat dest: instant_action_invs_dests)
        subgoal by (auto intro: v_pre_conds_sat v_lock_conds_sat dest: instant_pre_dests)
        done
      subgoal using mutex_conds_sat by blast
      subgoal using conv_invs no_invs by auto
      subgoal by (auto dest: instant_pre_dests simp: iij_ran iij_instant_index)
      subgoal by (subst Lv_conds_dests, auto intro: instant_pre_dests instant_action_invs_dests happening_invs_dests simp: iij_ran)
      subgoal by simp
      subgoal by simp
      subgoal 
        apply (rule is_upds.intros(2))
         apply (subst is_upd_def)
         apply (intro exI conjI)
           apply simp
          apply (rule check_bexp_is_val.intros)
           apply (rule check_bexp_is_val.intros(12)[where v= "the (v acts_active)"])
           apply (drule instant_pre_dests(3), simp)
          apply (subst is_val.simps)
          apply simp
         apply simp
        apply (rule is_upds_appendI)
        unfolding set_prop_ab_def
         apply (rule is_upds_set_vars_map)
          apply (subst map_map[symmetric])
          apply (rule HOL.refl)
         apply simp
        apply (rule is_upds_set_vars_map)
        apply (subst map_map[symmetric])
         apply (rule HOL.refl)
        apply (subst map_map)
        apply (subst comp_def)+
        by simp
      by (auto intro: instant_starting_cond_dests instant_pre_dests instant_action_invs_dests happening_invs_dests Lv_conds_dests)
    done
  done
  next                                                        
    case (3 j s)
    then show ?case 
      apply (induction s)
      subgoal for L v c
        apply (rule instant_preI, simp)
        subgoal apply (drule instant_post_dests(1))
          apply (erule instant_action_invs_maintained)
          apply (erule happening_invs_maintained)
          by simp+
        subgoal apply (drule instant_post_dests(2))
          apply (drule Suc_lessI)
          apply (subst instant_part_upd_prop_state_inv[OF i, symmetric, of "Suc (instant_indices ! j)"])
          using instant_indices_inc_all is_instant_index_def by (auto simp: Suc_le_eq intro: iip.ys_Suc)
        subgoal using instant_post_dests by blast
        subgoal apply (drule Suc_lessI)
          apply (intro strip, elim conjE)
          subgoal for k
            apply (cases "Suc (instant_indices ! j) \<le> k")
            using instant_indices_inc_all by (auto dest: instant_post_dests)
          done
        subgoal apply (drule Suc_lessI)
          apply (intro strip, elim conjE)
          subgoal for k
            apply (cases "Suc (instant_indices ! j) \<le> k")
            using instant_indices_inc_all by (auto dest: instant_post_dests)
          done
        subgoal
          apply (drule Suc_lessI, frule iip.ys_Suc)
          using instant_indices_inc_all 
          by (auto dest: instant_post_dests)
        by (drule iip.ys_Suc[OF Suc_lessI], auto dest: instant_post_dests instant_indices_inc_all[OF Suc_lessI])
      done
  next
    case (4 x)
    from \<open>0 = length instant_indices\<close>
    have no_instant_indices: "set instant_indices = {}" by simp
    hence "planning_sem.instant_actions_at (planning_sem.time_index i) = {}"
      apply -
      unfolding instant_indices planning_sem.instant_actions_at_def is_instant_index_def 
      apply (subst set_conv_nth)
      by auto
    hence no_instant: "planning_sem.instant_actions_at (planning_sem.time_index i) = {}"
           "planning_sem.instant_snaps_at (planning_sem.time_index i) = {}" 
      using planning_sem.instant_snaps_at_def by auto

    have not_instant: "\<not>is_instant_index (planning_sem.time_index i) j" if "j < length actions" for j 
      apply (insert that no_instant_indices) 
      apply (subst (asm) instant_indices)  by simp
    show ?case 
      apply (insert 4)
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_instantsI)
        subgoal by (drule happening_pre_instants_dests(1), simp)
        subgoal apply (drule happening_pre_instants_dests(2))
          apply (intro allI impI)
          apply (subst no_instant_imp_prop_state_before_is_after_instant[symmetric])
          using i no_instant by auto
        using not_instant by (auto intro: happening_pre_instants_dests)
      done
  next
    case (5 x)
    then show ?case 
      apply -
      apply (induction x)
      subgoal for L v c
        apply (rule instant_preI, simp)
        subgoal by (auto intro: happening_pre_instants_dests)
        subgoal apply (intro allI impI)
          apply (subst instant_part_upd_prop_state_inv[where n = 0, symmetric])
          using i instant_indices_inc_all_below index_case_defs 
          by (auto dest: happening_pre_instants_dests(2) simp: instant_part_upd_prop_state_0_is_prop_state_before i)
        subgoal using happening_pre_instants_dests by blast
        subgoal using instant_indices_inc_all_below by auto
        subgoal using instant_indices_inc_all_below by auto
        subgoal using happening_pre_instants_dests instant_indices_inc_all_below by fast
        subgoal by (drule happening_pre_instants_dests) (use instant_indices_inc_all_below in auto)
        subgoal by (drule happening_pre_instants_dests) (use instant_indices_inc_all_below in auto)
        done
      done
  next
    case (6 x)
    then show ?case
      apply -
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_instantsI)
        subgoal by (rule instant_post_dests(1))
        subgoal apply (drule instant_post_dests(2))
          apply (intro allI impI)
          apply (subst instant_part_upd_prop_state_all_is_prop_state_after[symmetric])
          using i  apply simp
          apply (subst instant_part_upd_prop_state_inv[symmetric, where n = "Suc (instant_indices ! (length instant_indices - 1))"])
          using i apply simp
          using iip.nth_ys_ran[simplified set_upt, THEN spec[of _ "length instant_indices - 1"]] apply simp  
           apply (intro allI impI, elim conjE ssubst)
           apply (rule instant_indices_inc_all_above[simplified index_case_defs])
          using i by auto
        subgoal using instant_post_dests by blast
        subgoal apply (intro allI impI)
          subgoal for k
            apply (cases "k < Suc (instant_indices ! (length instant_indices - 1))") 
            using instant_indices_inc_all_above
            by (auto dest: instant_post_dests)
          done
        subgoal apply (intro allI impI)
          subgoal for k
            apply (cases "k < Suc (instant_indices ! (length instant_indices - 1))") 
            using instant_indices_inc_all_above
            by (auto dest: instant_post_dests)
          done
        subgoal apply (intro allI impI)
          subgoal for k
            apply (cases "k < Suc (instant_indices ! (length instant_indices - 1))") 
            using instant_indices_inc_all_above
            by (auto dest: instant_post_dests)
          done
        done
      done
  next
    case (7 x)
    then show ?case 
      apply -
      apply (induction x)
      subgoal for L v c
        apply (intro happening_pre_start_startsI)
        subgoal by (rule start_start_invsI) (auto dest: happening_post_instants_dests instant_action_invs_dests)
        subgoal by (auto dest: happening_post_instants_dests instant_action_invs_dests)
        subgoal by (auto intro: happening_post_instants_dests)
        by (auto dest!: happening_post_instants_dests(1) dest: instant_action_invs_dests)
      done
  qed 
qed

lemma start_starts_possible: 
  assumes "graph_impl.steps xs \<and> happening_pre_start_starts i (last xs)"
  assumes i: "i < length planning_sem.htpl" 
  assumes start_indices: "start_indices = filter (is_starting_index (planning_sem.time_index i)) [0..<length actions]"
  shows " graph_impl.steps ((ext_seq \<circ> seq_apply) (map start_edge_effect start_indices) xs) \<and>  happening_pre_end_ends i (last ((ext_seq \<circ> seq_apply) (map start_edge_effect start_indices) xs))"
proof -
  interpret sip: filter_sorted_distinct_list "[0..<length actions]" "is_starting_index (planning_sem.time_index i)" start_indices
    apply (unfold_locales)
    using start_indices by auto

  have sij_in_act': "j < length actions" 
    if "i < length start_indices"
      "j \<le> start_indices ! i" for i j
    using set_nthI[OF that(1)]
    apply -
    apply (subst (asm) (2) start_indices)
    apply (subst (asm) set_filter)
    using that
    by simp
  
  have start_indices_inc_all: "\<not> is_starting_index (planning_sem.time_index i) m"
    if "Suc j < length start_indices" "Suc (start_indices ! j) \<le> m" "m < start_indices ! Suc j" for j m
    apply (rule sip.ys_inc_all)
    using sij_in_act' that by auto

  have start_indices_inc_all_below: "\<not> is_starting_index (planning_sem.time_index i) m"
    if "0 < length start_indices" "m < start_indices ! 0" for m
    apply (rule sip.ys_inc_all_below)
    using that sij_in_act'[OF that(1)] by auto

  have start_indices_inc_all_above: "\<not> is_starting_index (planning_sem.time_index i) m"
    if "start_indices ! (length start_indices - 1) < m" "m < length actions" for m
    apply (rule sip.ys_inc_all_above)
    using that by auto

  have image_start_indices_conv_actions: "((!) actions) ` set start_indices = planning_sem.starting_actions_at (planning_sem.time_index i)"
    unfolding planning_sem.action_happening_case_defs start_indices 
    unfolding set_filter image_Collect set_upt
    unfolding index_case_defs planning_sem.starting_actions_at_def
    apply (subst set_conv_nth)
    by auto

  have nat_leE: thesis if  "x \<le> y" "x < y \<Longrightarrow> thesis" "x = y \<Longrightarrow> thesis"  for x y::nat and thesis using that by linarith



  show ?thesis
  proof (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[
          where R = "happening_pre_start_starts i" 
            and S = "happening_post_start_starts i"
            and fs = "map start_edge_effect start_indices"
            and P = "start_start_pre i o ((!) start_indices)"
            and Q = "start_start_post i o ((!) start_indices)",
            simplified length_map nth_map, OF assms(1)], goal_cases)
    case j: (1 j s)
      have sij_set: "start_indices ! j \<in> set start_indices"  using j by auto
      with image_start_indices_conv_actions
      have *: "(actions ! (start_indices ! j)) \<in> planning_sem.starting_actions_at (planning_sem.time_index i)" using j by blast
      
      hence sij_starting: "planning_sem.is_starting_action (planning_sem.time_index i) (actions ! (start_indices ! j))"  
        and sij_in_act[intro]: "actions ! (start_indices ! j) \<in> set actions"  using * planning_sem.starting_actions_at_def j by auto
  
      have sij_starting_index: "is_starting_index (planning_sem.time_index i) (start_indices ! j)" apply (insert sij_set) apply (subst (asm) (2) start_indices) by simp
  
      have sij_ran: "start_indices ! j < length actions" 
        apply (insert sij_set)
        apply (subst (asm) (2) start_indices)
        by simp

      have adds_in_props: "set (adds (at_start (actions ! (start_indices ! j)))) \<subseteq> set props"
        and dels_in_props: "set (dels (at_start (actions ! (start_indices ! j)))) \<subseteq> set props"
        and pre_in_props: "set (pre (at_start (actions ! (start_indices ! j)))) \<subseteq> set props"
        using acts_ref_props using sij_in_act planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

    show ?case
    proof (insert j, induction s; rule context_conjI, goal_cases)
      case (1 L v c)
      have sij_L: "Suc (start_indices ! j) < length L" using 1
        unfolding comp_def
        apply (subst Lv_conds_dests)
        apply (force intro: start_start_pre_dests start_start_invs_dests happening_invs_dests)
        using sij_ran by simp
      show ?case
        using 1
        unfolding start_edge_effect_alt comp_def
        apply -
      proof(rule start_start_postI, goal_cases)
        case 1
        then show ?case 
          apply - 
          apply (frule start_start_pre_dests(1))
          apply (erule start_start_invs_maintained)
          subgoal apply (erule happening_invs_maintained)
            subgoal apply (erule Lv_conds_maintained)
                   apply simp
                  apply simp
                 apply (((subst map_upds_apply_nontin | subst fun_upd_other), force simp: variables_unique)+, simp)
              subgoal apply (rule upds_map_bounded[rotated])
                 apply (subst comp_def[of "\<lambda>x. 1" prop_to_var, symmetric])
                  apply (subst map_map[symmetric])
                  apply (rule HOL.refl)
                using map_of_net_bounds_action_start_add apply fastforce
                apply (rule upds_map_bounded[rotated])
                  apply (subst comp_def[of "\<lambda>x. 0" prop_to_var, symmetric])
                  apply (subst map_map[symmetric])
                  apply (rule HOL.refl)
                using map_of_net_bounds_action_start_del apply fastforce
                   apply (erule single_upd_bounded)
                  apply (rule map_of_net_bounds_acts_active)
                 apply (fastforce simp: start_start_pre_dests)
                apply (subst start_start_pre_dests, assumption)
                subgoal using updated_active_before_less_if_starting[OF i sij_starting_index sij_ran] by simp
                done
              done
            subgoal apply (intro strip)
              apply (subst fun_upd_other)
               apply (rule clocks_unique)
                 apply simp
              using sij_ran apply simp
               apply (rule nth_actions_unique)
              using sij_ran index_case_disj sij_starting_index by fast+
            subgoal apply (intro strip)
              apply (subst fun_upd_other)
               apply (rule clocks_unique)
              by simp
            subgoal apply (intro strip)
              apply (subst fun_upd_other)
               apply (rule clocks_unique)
                 apply simp
              using sij_ran apply simp
               apply (rule nth_actions_unique)
              using sij_ran index_case_disj sij_starting_index by fast+
            subgoal apply (intro strip)
              apply (subst fun_upd_other)
               apply (rule clocks_unique)
              by simp
           subgoal apply (intro strip)
              apply (subst nth_list_update_neq)
             using sij_ran index_case_disj sij_starting_index by fast+
           done
          subgoal apply (intro strip)
            apply ((subst map_upds_apply_nontin|subst fun_upd_other), force simp: variables_unique)+
            by simp
          subgoal apply (intro strip)
            apply (subst fun_upd_other) 
            by (use sij_starting_index sij_ran  index_case_disj clocks_unique in fast)+
          subgoal apply (intro strip)
            apply (subst fun_upd_other)
             apply (intro clocks_unique nth_mem)
            using sij_in_act nth_actions_unique sij_ran sij_starting_index index_case_disj by blast+
          subgoal apply (intro strip)
            apply (subst fun_upd_other)
             apply (intro clocks_unique nth_mem)
            using sij_in_act nth_actions_unique sij_ran sij_starting_index index_case_disj by blast+
          subgoal apply (intro strip)
            apply (subst nth_list_update_neq)
            using sij_in_act nth_actions_unique sij_ran sij_starting_index index_case_disj by blast+
          subgoal apply (intro strip)
            apply (subst nth_list_update_neq)
            using sij_in_act nth_actions_unique sij_ran sij_starting_index index_case_disj by blast+
          done
      next
        case (2 p)
        then show ?case 
          apply -
          apply (subst starting_part_updated_prop_state_Suc)
          using i sij_starting_index sij_ran apply auto[4]
          apply (cases "p \<in> set (adds (at_start (actions ! (start_indices ! j))))")
           apply (subst map_upds_with_map)
             apply simp
            apply simp
          apply simp
          apply (subst map_upds_apply_nontin)
           apply (force simp: variable_sets_unique adds_in_props)
          apply (cases "p \<in> set (dels (at_start (actions ! (start_indices ! j))))")
           apply (subst map_upds_with_map)
             apply simp
            apply simp
           apply simp
          apply (subst map_upds_apply_nontin)
           apply (force simp: variable_sets_unique dels_in_props)
          apply (subst fun_upd_other)
           apply (simp add: variables_unique)
          apply (drule start_start_pre_dests(2))
          unfolding starting_part_updated_prop_state_def[OF i] prop_state_def starting_part_updated_state_seq_def[OF i]
          by simp+
      next
        case 3
        then show ?case 
          apply -
          apply (subst map_upds_apply_nontin, force simp: variables_unique)+
          using updated_active_before_Suc i sij_starting_index sij_ran
          by (auto simp: start_start_pre_dests)
      next
        case (4 k)
        then show ?case 
          apply (cases "k = start_indices ! j")
          using sij_L start_start_pre_dests by auto
      next
        case (5 k)
        then show ?case
          apply (subst act_clock_pre_happ_simps)
          apply (subst fun_upd_other)
           apply (intro clocks_unique)
          using nth_actions_unique sij_L start_start_pre_dests by auto
      next
        case (6 k)
        then show ?case 
          apply (cases "k = start_indices ! j")
          using sij_L start_start_pre_dests by auto
      next
        case (7 k)
        thus ?case
          apply (cases "k = start_indices ! j")
          using sij_L start_start_pre_dests by auto
      qed
    next
      case (2 L v c)
      have sij_L: "Suc (start_indices ! j) < length L" using 2
        unfolding comp_def
        apply (subst Lv_conds_dests)
        apply (force intro: start_start_pre_dests start_start_invs_dests happening_invs_dests)
        using sij_ran by simp
      have sij_set: "start_indices ! j \<in> set start_indices"  using j by auto
      with image_start_indices_conv_actions
      have *: "(actions ! (start_indices ! j)) \<in> planning_sem.starting_actions_at (planning_sem.time_index i)" using j by blast
      
      hence sij_starting: "planning_sem.is_starting_action (planning_sem.time_index i) (actions ! (start_indices ! j))"  
        and sij_in_act[intro]: "actions ! (start_indices ! j) \<in> set actions"  using * planning_sem.starting_actions_at_def j by auto
  
      have sij_starting_index: "is_starting_index (planning_sem.time_index i) (start_indices ! j)" apply (insert sij_set) apply (subst (asm) (2) start_indices) by simp
  
      have sij_ran: "start_indices ! j < length actions" 
        apply (insert sij_set)
        apply (subst (asm) (2) start_indices)
        by simp

      have adds_in_props: "set (adds (at_start (actions ! (start_indices ! j)))) \<subseteq> set props"
        and dels_in_props: "set (dels (at_start (actions ! (start_indices ! j)))) \<subseteq> set props"
        and pre_in_props: "set (pre (at_start (actions ! (start_indices ! j)))) \<subseteq> set props"
        using acts_ref_props using sij_in_act planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

       have v_pre_conds_sat: "Simple_Expressions.check_bexp v' (bexp_and_all (map (is_prop_ab 1) (pre (at_start (actions ! (start_indices ! j)))))) True"
          if prop_state: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_var p) = Some (starting_part_updated_prop_state i (start_indices ! j) p)" for v'
        proof -
          { fix p
            assume p: "p \<in> set (pre (at_start (actions ! (start_indices ! j))))"
            have  "p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds)" 
              using  p sij_in_act p map_of_net_bounds_action_start_pre pre_in_props by auto
            hence "v' (prop_to_var p) = Some (starting_part_updated_prop_state i (start_indices ! j) p)" 
              using prop_state * by auto
            moreover
            have "starting_part_updated_prop_state i (start_indices ! j) p = 1" 
              apply (rule pre_val_in_starting_part_updated_prop_state_if[OF i _ _ _ _ _ p])
              using sij_ran sij_starting_index p using is_starting_index_def planning_sem.is_starting_action_def by auto
            ultimately
            have "v' (prop_to_var p) = Some 1" by simp
        
            hence "Simple_Expressions.check_bexp v' (is_prop_ab 1 p) True" 
              unfolding is_prop_ab_def
              by (simp add: check_bexp_simps is_val_simps)
          } 
          hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_start (actions ! (start_indices ! j))))). Simple_Expressions.check_bexp v' b True" by auto
          thus ?thesis using check_bexp_all by blast
        qed

    
      have v_lock_conds_sat: 
          "check_bexp v' (bexp_and_all (map (is_prop_lock_ab 0) 
                          (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! (start_indices ! j))))) (dels (at_start (actions ! (start_indices ! j))))))) True"
        if locked: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))" for v'
      proof -
        { fix p
          assume p: "p \<notin> set (adds (at_start (actions ! (start_indices ! j))))"
                 "p \<in> set (dels (at_start (actions ! (start_indices ! j))))"
          hence "p \<notin> planning_sem.plan_invs_during (planning_sem.time_index i)" 
            using planning_sem.snap_does_not_delete_inv sij_starting unfolding planning_sem.action_happening_case_defs by auto
          hence "planning_sem.locked_during (planning_sem.time_index i) p = 0" 
            using planning_sem.in_invs_during_iff_locked_during by blast
          moreover
          have "prop_to_lock p \<in> set (map prop_to_lock (dels (at_start (actions ! (start_indices ! j)))))" 
               "prop_to_lock p \<notin> set (map prop_to_lock (adds (at_start (actions ! (start_indices ! j)))))" 
            using p apply simp
            unfolding set_map
            apply (rule variable_sets_unique)
            using adds_in_props p dels_in_props by auto
          hence "prop_to_lock p \<in> dom (map_of net_bounds)" 
            using map_of_net_bounds_action_start_del_lock p sij_in_act by auto
          moreover
          have "p \<in> set props" using dels_in_props p by auto
          ultimately
          have "v' (prop_to_lock p) = Some 0" using locked by simp
          
          hence "Simple_Expressions.check_bexp v' (is_prop_lock_ab 0 p) True" 
            unfolding is_prop_lock_ab_def 
            by (simp add: check_bexp_simps is_val_simps)
        } 
        hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) 
                        (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! (start_indices ! j))))) 
                          (dels (at_start (actions ! (start_indices ! j)))))). 
              Simple_Expressions.check_bexp v' b True"  by auto
        thus ?thesis using check_bexp_all by blast
      qed

      let ?dels = "dels (at_start (actions ! (start_indices ! j)))"
      let ?adds = "adds (at_start (actions ! (start_indices ! j)))"
    
      have is_upds: "is_upds v 
        ((acts_active, binop plus_int (var acts_active) (exp.const 1)) 
          # map (set_prop_ab 0) ?dels @ map (set_prop_ab 1) ?adds)
       (v(acts_active \<mapsto> plus_int (the (v acts_active)) 1, 
          map prop_to_var ?dels [\<mapsto>] map (\<lambda>x. 0) ?dels,
          map prop_to_var ?adds [\<mapsto>] map (\<lambda>x. 1) ?adds))"
      proof (rule is_upds.intros)

        have def: "\<exists>x. v acts_active = Some x" using 2 start_start_pre_dests(3,4) by fastforce+
        have is_val: "is_val v (var acts_active) (the (v acts_active))"
            using def
            by (auto intro: check_bexp_is_val.intros)

        show "is_upd v (acts_active, binop plus_int (var acts_active) (exp.const 1)) (v(acts_active \<mapsto> the (v acts_active) + 1))"
          unfolding is_upd_def
          by (auto intro: check_bexp_is_val.intros is_val)
        show "is_upds (v(acts_active \<mapsto> plus_int (the (v acts_active)) 1)) 
            (map (set_prop_ab 0) ?dels @ map (set_prop_ab 1) ?adds)
            (v(acts_active \<mapsto> plus_int (the (v acts_active)) 1,
                map prop_to_var ?dels [\<mapsto>] map (\<lambda>x. 0) ?dels,
                map prop_to_var ?adds [\<mapsto>] map (\<lambda>x. 1) ?adds))"
          apply (rule is_upds_appendI)
            unfolding set_prop_ab_def
             apply (rule is_upds_set_vars_map)
              apply (subst map_map[symmetric])
              apply (rule HOL.refl)
             apply simp
            unfolding set_prop_ab_def
             apply (rule is_upds_set_vars_map)
              apply (subst map_map[symmetric])
              apply (rule HOL.refl)
            apply simp
            unfolding comp_def map_map by blast
        qed


    have mutex_conds_sat: "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (net_int_clocks (at_start (actions ! (start_indices ! j)))) 
      @ map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (net_int_clocks (at_start (actions ! (start_indices ! j))))"
    proof (rule guard_append)
      have ssp: "start_start_pre i (start_indices ! j) (L, v, c)" "j < length start_indices" using 2 by auto
      have 1: "\<forall>b\<in>set actions. planning_sem.is_ending_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro: start_start_pre_dests start_start_invs_dests happening_invs_dests ssp)
      have 2: "\<forall>b\<in>set actions. planning_sem.is_not_happening_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro: start_start_pre_dests start_start_invs_dests happening_invs_dests ssp)
      have 3: "\<forall>b\<in>set actions. planning_sem.is_starting_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro: start_start_pre_dests start_start_invs_dests happening_invs_dests ssp)
      have 4: "\<forall>b\<in>set actions. planning_sem.is_not_happening_action (planning_sem.time_index i) b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro: start_start_pre_dests start_start_invs_dests happening_invs_dests ssp)
      have 5: "act_clock_pre_happ c act_to_start_clock (actions ! (start_indices ! j)) (planning_sem.time_index i)"
        unfolding index_case_conv_action[symmetric] 
        by (blast intro: start_start_pre_dests ssp sij_ran sij_starting_index)

      show "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (net_int_clocks (at_start (actions ! (start_indices ! j))))"
        apply (rule starting_action_sat_mutex_start[OF sij_in_act sij_starting])
        using 1 2 3 4 5 by auto
      show "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (net_int_clocks (at_start (actions ! (start_indices ! j))))"
        apply (rule starting_action_sat_mutex_start[OF sij_in_act sij_starting])
        using 1 2 3 4 5 by auto
    qed

      show ?case 
        apply (insert 2)
        unfolding comp_def start_edge_effect_alt
        apply (rule single_step_intro)
        unfolding prod.case
        apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
        unfolding net_impl.sem_def
          apply (rule step_u.step_int)
        unfolding TAG_def
                    apply (subst conv_trans[where p = "Suc (start_indices ! j)"])
        using sij_ran length_net_automata apply simp
                    apply (rule image_eqI[where x = "start_edge (actions ! (start_indices ! j))"])
                     apply (simp add: start_edge_def)
                    apply (simp add: sij_ran nth_auto_trans)
        subgoal apply (intro disjI2 strip)
          apply (subst conv_committed, simp)
          apply (subst no_committed, simp)
          by auto
        subgoal apply (rule check_bexp_Cons)
           apply (force intro: v_pl_cond_sat start_start_pre_dests start_start_invs_dests happening_invs_dests)
          by (auto intro: check_bexp_all_append v_pre_conds_sat v_lock_conds_sat start_start_pre_dests start_start_invs_dests)
        subgoal using mutex_conds_sat by auto
        subgoal using conv_invs no_invs by auto
        subgoal by (auto intro: start_start_pre_dests sij_starting_index sij_ran)
        subgoal using sij_L by simp
        subgoal by simp
        subgoal by simp
        subgoal using is_upds by auto
        subgoal apply (rule upds_map_bounded'[OF _ _ HOL.refl])
            apply (rule upds_map_bounded'[OF _ _ HOL.refl])
          subgoal apply (rule single_upd_bounded)
            subgoal by (blast intro: Lv_conds_dests happening_invs_dests start_start_invs_dests start_start_pre_dests)
                apply (rule map_of_net_bounds_acts_active)
               apply (force dest: start_start_pre_dests)
            by (drule start_start_pre_dests(3), use  updated_active_before_less_if_starting sij_starting_index i sij_ran in fastforce)
          subgoal by simp
          subgoal unfolding set_map apply (intro ballI exI conjI)
              apply (rule map_of_net_bounds_action_start_del)
               apply (rule sij_in_act)
            by auto
           apply simp
          subgoal unfolding set_map apply (intro ballI exI conjI)
              apply (rule map_of_net_bounds_action_start_add)
               apply (rule sij_in_act)
            by auto
          done
        subgoal by (blast intro: Lv_conds_dests happening_invs_dests start_start_invs_dests start_start_pre_dests)
        by simp
    qed
  next
    case (2 j s)
    then show ?case 
      apply -
      unfolding comp_def
      apply (induction s)
      subgoal for L v c
        apply (rule start_start_preI)
        subgoal by (rule start_start_post_dests)
        subgoal apply (subst starting_part_updated_prop_state_inv[OF i, where n = "Suc (start_indices ! j)", symmetric])
          using sip.ys_Suc apply fastforce
          apply (intro allI impI, elim conjE ssubst)
           apply (rule start_indices_inc_all[simplified index_case_defs])
          by (auto intro: start_start_post_dests)
        subgoal apply (subst updated_active_before_inv[OF i, where n = "Suc (start_indices ! j)", symmetric])
          using sip.ys_Suc apply fastforce
          apply (intro allI impI, elim conjE ssubst)
           apply (rule start_indices_inc_all)
          by (auto intro: start_start_post_dests)
        subgoal for k
          apply (cases "k < Suc (start_indices ! j)")
          using start_indices_inc_all 
          by (auto intro: start_start_post_dests)
        subgoal for k
          apply (erule start_start_post_dests)
          using sip.ys_Suc by force+
        subgoal for k
          apply (cases "k < Suc (start_indices ! j)")
          using start_indices_inc_all 
          by (auto intro: start_start_post_dests)
        subgoal for k
          apply (erule start_start_post_dests)
          using sip.ys_Suc by force+
        done
      done
  next
    case (3 x)
    then show ?case 
      apply -
      unfolding comp_def
      apply (induction x)
      subgoal for L v c
        apply (rule start_start_preI)
        subgoal by (rule happening_pre_start_starts_dests)
        subgoal for p
          apply (drule happening_pre_start_starts_dests(2), assumption, assumption)
          apply (subst (asm) starting_part_updated_prop_state_0_is_prop_state_after_instant_happ[symmetric, OF i])
          apply (subst starting_part_updated_prop_state_inv[symmetric, where n = 0, OF i])
          using start_indices_inc_all_below[simplified is_starting_index_def] by auto
        subgoal apply (drule happening_pre_start_starts_dests(3))
          apply (subst (asm) updated_active_before_0_is_active_before[symmetric, OF i])
          apply (subst updated_active_before_inv[symmetric, where n = 0])
          using i start_indices_inc_all_below by auto
        subgoal using start_indices_inc_all_below by auto
        subgoal by (rule happening_pre_start_starts_dests)
        subgoal using start_indices_inc_all_below by auto
        subgoal by (rule happening_pre_start_starts_dests)
        done
      done
  next
    case (4 x)
    then show ?case apply -
      unfolding comp_def
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_start_startsI)
        subgoal by (rule start_start_post_dests)
        subgoal for p
          apply (drule start_start_post_dests(2), assumption, assumption)
          apply (subst (asm) starting_part_updated_prop_state_inv[where m = "length actions", OF i])
          using sip.nth_ys_ran[simplified set_upt, THEN spec, of "length start_indices - 1"] apply simp
          using start_indices_inc_all_above index_case_defs apply simp
          apply (subst (asm) starting_part_updated_prop_state_all_is_prop_state_after_instant_start_happ[OF i])
          by auto
        subgoal
          apply (drule start_start_post_dests(3))
          apply (subst (asm) updated_active_before_inv[where m = "length actions", OF i])
          using sip.nth_ys_ran[simplified set_upt, THEN spec, of "length start_indices - 1"] apply simp
          using start_indices_inc_all_above apply simp
          apply (subst (asm) updated_active_before_all_is_active_during)
          using i by auto
        subgoal for k 
          apply (cases "k < Suc (start_indices ! (length start_indices - 1))")
          using start_indices_inc_all_above by (auto intro: start_start_post_dests)
        subgoal for k 
          apply (cases "k < Suc (start_indices ! (length start_indices - 1))")
          using start_indices_inc_all_above by (auto intro: start_start_post_dests)
        done
      done
  next
    case (5 x)
    hence no_starting_indices: "set start_indices = {}" by simp
    hence "planning_sem.starting_actions_at (planning_sem.time_index i) = {}"
      apply -
      unfolding start_indices planning_sem.starting_actions_at_def is_starting_index_def 
      apply (subst set_conv_nth)
      by auto
    hence no_starting: "planning_sem.starting_actions_at (planning_sem.time_index i) = {}"
           "planning_sem.starting_snaps_at (planning_sem.time_index i) = {}" 
      using planning_sem.starting_snaps_at_def by auto

    have not_starting: "\<not>is_starting_index (planning_sem.time_index i) j" if "j < length actions" for j 
      apply (insert that no_starting_indices) 
      apply (subst (asm) start_indices)  by simp
    show ?case 
      apply (insert 5)
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_start_startsI)
        subgoal by (rule happening_pre_start_starts_dests)
        subgoal apply (subst prop_state_after_instant_start_happ_is_prop_state_after_instant_happ_if_no_start)
          using i no_starting by (auto intro: happening_pre_start_starts_dests)
        subgoal apply (subst active_before_is_active_during_if_no_start[symmetric])
          using i no_starting by (auto intro: happening_pre_start_starts_dests)
        using not_starting by auto
      done
  next
    case (6 x)
    then show ?case 
      by (induction x) (auto intro: happening_pre_end_endsI end_end_invsI happening_post_start_starts_dests start_start_invs_dests)
  qed
qed

lemma end_ends_possible:
  assumes "graph_impl.steps xs \<and> happening_pre_end_ends i (last xs)"
      and i: "i < length planning_sem.htpl"
      and end_indices: "end_indices = (filter (is_ending_index (planning_sem.time_index i)) [0..<length actions])"
    shows "graph_impl.steps ((ext_seq \<circ> seq_apply) (map end_edge_effect end_indices) xs) \<and> happening_pre_start_ends i (last ((ext_seq \<circ> seq_apply) (map end_edge_effect end_indices) xs))"
proof -
  interpret eip: filter_sorted_distinct_list "[0..<length actions]" "is_ending_index (planning_sem.time_index i)" end_indices
    apply (unfold_locales)
    using end_indices by auto

  have eij_in_act': "j < length actions" 
    if "i < length end_indices"
      "j \<le> end_indices ! i" for i j
    using set_nthI[OF that(1)]
    apply -
    apply (subst (asm) (2) end_indices)
    apply (subst (asm) set_filter)
    using that
    by simp
  
  have end_indices_inc_all: "\<not> is_ending_index (planning_sem.time_index i) m"
    if "Suc j < length end_indices" "Suc (end_indices ! j) \<le> m" "m < end_indices ! Suc j" for j m
    apply (rule eip.ys_inc_all)
    using eij_in_act' that by auto

  have end_indices_inc_all_below: "\<not> is_ending_index (planning_sem.time_index i) m"
    if "0 < length end_indices" "m < end_indices ! 0" for m
    apply (rule eip.ys_inc_all_below)
    using that eij_in_act'[OF that(1)] by auto

  have end_indices_inc_all_above: "\<not> is_ending_index (planning_sem.time_index i) m"
    if "end_indices ! (length end_indices - 1) < m" "m < length actions" for m
    apply (rule eip.ys_inc_all_above)
    using that by auto

  have image_end_indices_conv_actions: "((!) actions) ` set end_indices = planning_sem.ending_actions_at (planning_sem.time_index i)"
    unfolding planning_sem.action_happening_case_defs end_indices 
    unfolding set_filter image_Collect set_upt
    unfolding index_case_defs planning_sem.ending_actions_at_def
    apply (subst set_conv_nth)
    by auto

  have nat_leE: thesis if  "x \<le> y" "x < y \<Longrightarrow> thesis" "x = y \<Longrightarrow> thesis"  for x y::nat and thesis using that by linarith
  have nat_less_SucE: thesis if "x < Suc y" "x = y \<Longrightarrow> thesis" "x < y \<Longrightarrow> thesis" for x y::nat and thesis using that by linarith

  show ?thesis
  proof (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[
        where R = "happening_pre_end_ends i" 
          and S = "happening_post_end_ends i"
          and P = "end_end_pre i o ((!) end_indices)"
          and Q = "end_end_post i o ((!) end_indices)"
          and fs = "map end_edge_effect end_indices",
        simplified nth_map length_map,
        OF assms(1)], 
      goal_cases)
    case j: (1 j s)
    have eij_set: "end_indices ! j \<in> set end_indices"  using j by auto
    with image_end_indices_conv_actions
    have *: "(actions ! (end_indices ! j)) \<in> planning_sem.ending_actions_at (planning_sem.time_index i)" using j by blast
    
    hence eij_ending: "planning_sem.is_ending_action (planning_sem.time_index i) (actions ! (end_indices ! j))"  
      and eij_in_act[intro]: "actions ! (end_indices ! j) \<in> set actions"  using * planning_sem.ending_actions_at_def j by auto

    have eij_ending_index: "is_ending_index (planning_sem.time_index i) (end_indices ! j)" apply (insert eij_set) apply (subst (asm) (2) end_indices) by simp

    have eij_ran: "end_indices ! j < length actions" 
      apply (insert eij_set)
      apply (subst (asm) (2) end_indices)
      by simp

      have adds_in_props: "set (adds (at_end (actions ! (end_indices ! j)))) \<subseteq> set props"
        and dels_in_props: "set (dels (at_end (actions ! (end_indices ! j)))) \<subseteq> set props"
        and pre_in_props: "set (pre (at_end (actions ! (end_indices ! j)))) \<subseteq> set props"
        using acts_ref_props using eij_in_act planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto


    show ?case 
    proof (insert j, induction s; rule context_conjI, goal_cases)
      case (1 L v c)
      have eij_L: "Suc (end_indices ! j) < length L" using 1 unfolding comp_def
        by (subst Lv_conds_dests) (auto intro: happening_invs_dests end_end_invs_dests end_end_pre_dests eij_ran)
      show ?case
        apply (insert 1)
        unfolding comp_def end_edge_effect_alt
        apply (rule end_end_postI)
        subgoal apply (frule end_end_pre_dests(1))
          apply (erule end_end_invs_maintained)
                 apply (erule happening_invs_maintained)
                      apply (erule Lv_conds_maintained)
                         apply simp
                        apply simp
          subgoal by ((subst map_upds_apply_nontin| subst fun_upd_other), (force simp: variables_unique)+)+
          subgoal apply (rule upds_map_bounded')
               prefer 3
               apply blast
              apply (rule upds_map_bounded')
                 prefer 3
                 apply blast
                apply (rule single_upd_bounded)
                   apply simp
                  apply (rule map_of_net_bounds_acts_active)
            subgoal apply (subst end_end_pre_dests, assumption)
              using updated_active_during_pos_if_ending eij_ending_index i eij_ran by simp
            subgoal apply (subst end_end_pre_dests, assumption)
              using updated_active_during_ran[where n = "end_indices ! j"] i
              by fastforce
            apply simp
            using map_of_net_bounds_action_end_del map_of_net_bounds_action_end_add eij_in_act by auto
                     apply auto[4]
          subgoal apply (intro strip)?
            apply (subst nth_list_update_neq)
             apply (frule index_case_dests_disj)
            using eij_ending_index by auto
          subgoal by ((subst map_upds_apply_nontin | subst fun_upd_other)?, (force simp: variables_unique)+)+
               apply auto[4]
          subgoal apply (subst nth_list_update_neq)
             apply (frule index_case_dests_disj)
            using eij_ending_index by auto
          subgoal apply (subst nth_list_update_neq)
             apply (frule index_case_dests_disj)
            using eij_ending_index by auto
          done
        subgoal for p 
          apply (subst ending_part_updated_prop_state_Suc)
          using i eij_ending_index eij_ran apply auto[4]
          apply (cases "p \<in> set (adds (at_end (actions ! (end_indices ! j))))")
           apply (subst map_upds_with_map)
             apply auto[3]
           apply (subst map_upds_apply_nontin)
            apply (force simp: adds_in_props variable_sets_unique)
          apply (cases "p \<in> set (dels (at_end (actions ! (end_indices ! j))))")
           apply (subst map_upds_with_map)
             apply auto[3]
          apply ((subst map_upds_apply_nontin | subst fun_upd_other), (force simp: dels_in_props variable_sets_unique variables_unique))+
          apply (subst end_end_pre_dests, simp, simp)
          unfolding  ending_part_updated_prop_state_def[OF i] ending_part_updated_state_seq_def[OF i] prop_state_def
          by auto
        subgoal apply (subst map_upds_apply_nontin, (force simp: dels_in_props variable_sets_unique variables_unique)+)+
          using updated_active_during_pos_if_ending i eij_ending_index eij_ran  
          by (fastforce simp: updated_active_during_Suc end_end_pre_dests)+
        subgoal apply (subst nth_list_update_neq, (force simp: dels_in_props variable_sets_unique variables_unique))+
          using end_end_pre_dests card_ending_actions_after_Suc[OF i eij_ending_index eij_ran, symmetric] 
          by auto
        subgoal by (erule nat_less_SucE, use end_end_pre_dests eij_L in auto)
        done
    next
      case j: (2 L v c)

      have eij_L: "Suc (end_indices ! j) < length L" using j unfolding comp_def
        by (subst Lv_conds_dests) (auto intro: happening_invs_dests end_end_invs_dests end_end_pre_dests eij_ran)
      
      have v_pre_conds_sat: "Simple_Expressions.check_bexp v' (bexp_and_all (map (is_prop_ab 1) (pre (at_end (actions ! (end_indices ! j)))))) True"
        if prop_state: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_var p) = Some (ending_part_updated_prop_state i (end_indices ! j) p)" for v'
      proof -
        { fix p
          assume p: "p \<in> set (pre (at_end (actions ! (end_indices ! j))))"
          have p_in_props: "p \<in> set props" and  "prop_to_var p \<in> dom (map_of net_bounds)" 
            using pre_in_props p eij_in_act p map_of_net_bounds_action_end_pre by auto
          hence "v' (prop_to_var p) = Some (ending_part_updated_prop_state i (end_indices ! j) p)" using prop_state * by auto
          moreover
          have "ending_part_updated_prop_state i (end_indices ! j) p = 1" 
            apply (rule pre_val_in_ending_part_updated_prop_state_if[OF i _ _ _ _ _ p])
            using eij_ran eij_ending_index p using is_ending_index_def planning_sem.is_ending_action_def by auto
          ultimately
          have "v' (prop_to_var p) = Some 1" by simp
      
          hence "Simple_Expressions.check_bexp v' (is_prop_ab 1 p) True" 
            unfolding is_prop_ab_def
            by (simp add: check_bexp_simps is_val_simps)
        } 
        hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_end (actions ! (end_indices ! j))))). Simple_Expressions.check_bexp v' b True" by auto
        thus ?thesis using check_bexp_all by blast
      qed
      
      
      have v_lock_conds_sat: 
          "check_bexp v' (bexp_and_all (map (is_prop_lock_ab 0) 
                          (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! (end_indices ! j))))) (dels (at_end (actions ! (end_indices ! j))))))) True"
        if locked: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))" for v'
      proof -
        { fix p
          assume p: "p \<notin> set (adds (at_end (actions ! (end_indices ! j))))"
                 "p \<in> set (dels (at_end (actions ! (end_indices ! j))))"
          hence "p \<notin> planning_sem.plan_invs_during (planning_sem.time_index i)" using planning_sem.snap_does_not_delete_inv eij_ending unfolding planning_sem.action_happening_case_defs by auto
          hence "planning_sem.locked_during (planning_sem.time_index i) p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
          moreover
          have "prop_to_lock p \<in> set (map prop_to_lock (dels (at_end (actions ! (end_indices ! j)))))" 
               "prop_to_lock p \<notin> set (map prop_to_lock (adds (at_end (actions ! (end_indices ! j)))))" 
            using p apply simp
            unfolding set_map
            apply (rule variable_sets_unique)
            using adds_in_props p dels_in_props by auto
          hence "prop_to_lock p \<in> dom (map_of net_bounds)" using map_of_net_bounds_action_end_del_lock p eij_in_act by auto
          moreover
          have "p \<in> set props" using p dels_in_props by auto
          ultimately
          have "v' (prop_to_lock p) = Some 0" using locked by simp 
          
          hence "Simple_Expressions.check_bexp v' (is_prop_lock_ab 0 p) True" 
            unfolding is_prop_lock_ab_def 
            by (simp add: check_bexp_simps is_val_simps)
        } 
        hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) 
                        (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! (end_indices ! j))))) 
                          (dels (at_end (actions ! (end_indices ! j)))))). 
              Simple_Expressions.check_bexp v' b True"  by auto
        thus ?thesis using check_bexp_all by blast
      qed

      (* Could be done by apply scripting and rotating the goal state to synthesize terms *)
      have is_upds: "is_upds v ((acts_active, binop plus_int (var acts_active) (exp.const (- 1))) # map (set_prop_ab 0) (dels (at_end (actions ! (end_indices ! j)))) @ map (set_prop_ab 1) (adds (at_end (actions ! (end_indices ! j)))))
     (v(acts_active \<mapsto> plus_int (the (v acts_active)) (- 1), map prop_to_var (dels (at_end (actions ! (end_indices ! j)))) [\<mapsto>] map (\<lambda>x. 0) (map prop_to_var (dels (at_end (actions ! (end_indices ! j))))),
          map prop_to_var (adds (at_end (actions ! (end_indices ! j)))) [\<mapsto>] map (\<lambda>x. 1) (map prop_to_var (adds (at_end (actions ! (end_indices ! j)))))))"
      proof (rule is_upds.intros(2)[of _ _ "(v(acts_active \<mapsto> plus_int (the (v acts_active)) (- 1)))"], goal_cases)
        case 1
        have vA: "v acts_active = Some (the (v acts_active))"
          using j end_end_pre_dests(3) unfolding comp_def by fastforce 
        show ?case 
          unfolding is_upd_def
          apply (intro exI conjI)
            apply simp
           apply (rule check_bexp_is_val.intros)
            apply (rule check_bexp_is_val.intros)
            apply (rule vA)
           apply (rule check_bexp_is_val.intros)
          by auto
      next
        case 2
        thus ?case apply (rule is_upds_appendI)
           prefer 2
           apply (rule is_upds_set_vars_map)
          unfolding set_prop_ab_def
            apply (subst map_map[symmetric])
            apply (rule HOL.refl)
           apply (rule HOL.refl)
          apply (rule is_upds_set_vars_map)
           apply (subst map_map[symmetric])
           apply (rule HOL.refl)
          by auto
      qed

      show ?case 
        apply (insert j)
        unfolding comp_def end_edge_effect_alt
        apply (rule single_step_intro)
        unfolding prod.case
        apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
        unfolding net_impl.sem_def
          apply (rule step_u.step_int)
        unfolding TAG_def
                    apply (subst conv_trans[where p = "Suc (end_indices ! j)"])
                     apply (simp add: eij_ran length_net_automata)
                    apply (rule image_eqI[where x = "end_edge (actions ! (end_indices ! j))"])
                     apply (simp add: end_edge_def)
                    apply (simp add: eij_ran nth_auto_trans)
        subgoal by (intro disjI2 strip) ((subst conv_committed no_committed | simp)+)
        subgoal  apply (rule check_bexp_Cons)
           apply (force intro: v_pl_cond_sat end_end_pre_dests end_end_invs_dests happening_invs_dests)
          by (auto intro: check_bexp_all_append v_pre_conds_sat v_lock_conds_sat end_end_pre_dests end_end_invs_dests)
        subgoal by simp
        subgoal using conv_invs no_invs by force
        subgoal using eij_ran eij_ending_index by (auto intro: end_end_pre_dests)
        subgoal using eij_L by auto
        subgoal by auto
        subgoal by auto
        subgoal using is_upds by blast
        subgoal by (auto intro: Lv_conds_dests happening_invs_dests end_end_invs_dests end_end_post_dests)
        by (auto intro: Lv_conds_dests happening_invs_dests end_end_invs_dests end_end_post_dests end_end_pre_dests)
    qed
  next
    case (2 j s)
    then show ?case 
      apply -
      unfolding comp_def
      apply (induction s)
      subgoal for L v c
        apply (rule end_end_preI)
        subgoal by (rule end_end_post_dests)
        subgoal apply (subst ending_part_updated_prop_state_inv[OF i, where n = "Suc (end_indices ! j)", symmetric])
          using eip.ys_Suc apply fastforce
          apply (intro allI impI, elim conjE ssubst)
           apply (rule end_indices_inc_all[simplified index_case_defs])
          by (auto intro: end_end_post_dests)
        subgoal apply (subst updated_active_during_inv[OF i, where n = "Suc (end_indices ! j)", symmetric])
          using eip.ys_Suc apply fastforce
          apply (intro allI impI, elim conjE ssubst)
           apply (rule end_indices_inc_all)
          by (auto intro: end_end_post_dests)
        subgoal for k
          apply (erule end_end_post_dests)
          using eip.ys_Suc by force+
        subgoal for k
          apply (cases "k < Suc (end_indices ! j)")
          using end_indices_inc_all 
          by (auto intro: end_end_post_dests)
        done
      done
  next
    case (3 x)
    then show ?case 
      apply -
      unfolding comp_def
      apply (induction x)
      subgoal for L v c
        apply (rule end_end_preI)
        subgoal by (rule happening_pre_end_ends_dests)
        subgoal for p
          apply (drule happening_pre_end_ends_dests(2), assumption, assumption)
          apply (subst (asm) ending_part_updated_prop_state_0_is_prop_state_after_instant_start_happ[symmetric, OF i])
          apply (subst ending_part_updated_prop_state_inv[symmetric, where n = 0, OF i])
          using end_indices_inc_all_below[simplified is_ending_index_def] by auto
        subgoal apply (drule happening_pre_end_ends_dests(3))
          apply (subst (asm) updated_active_during_0_is_active_during[symmetric, OF i])
          apply (subst updated_active_during_inv[symmetric, where n = 0])
          using i end_indices_inc_all_below by auto
        subgoal by (rule happening_pre_end_ends_dests)
        subgoal using end_indices_inc_all_below by auto
        done
      done
  next
    case (4 x)
    then show ?case  apply -
      unfolding comp_def
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_end_endsI)
        subgoal by (rule end_end_post_dests)
        subgoal for p
          apply (drule end_end_post_dests(2), assumption, assumption)
          apply (subst (asm) ending_part_updated_prop_state_inv[where m = "length actions", OF i])
          using eip.nth_ys_ran[simplified set_upt, THEN spec, of "length end_indices - 1"] apply simp
          using end_indices_inc_all_above index_case_defs apply simp
          apply (subst (asm) ending_part_updated_prop_state_all_is_prop_state_after_happ[OF i])
          by auto
        subgoal
          apply (drule end_end_post_dests(3))
          apply (subst (asm) updated_active_during_inv[where m = "length actions", OF i])
          using eip.nth_ys_ran[simplified set_upt, THEN spec, of "length end_indices - 1"] apply simp
          using end_indices_inc_all_above apply simp
          apply (subst (asm) updated_active_during_all_is_active_during_minus_ended)
          using i by auto
        subgoal for k 
          apply (cases "k < Suc (end_indices ! (length end_indices - 1))")
          using end_indices_inc_all_above by (auto intro: end_end_post_dests)
        done
      done
  next
    case (5 x)
    hence no_ending_indices: "set end_indices = {}" by simp
    hence "planning_sem.ending_actions_at (planning_sem.time_index i) = {}"
      apply -
      unfolding end_indices planning_sem.ending_actions_at_def is_ending_index_def 
      apply (subst set_conv_nth)
      by auto
    hence no_ending: "planning_sem.ending_actions_at (planning_sem.time_index i) = {}"
           "planning_sem.ending_snaps_at (planning_sem.time_index i) = {}" 
      using planning_sem.ending_snaps_at_def by auto

    have not_ending: "\<not>is_ending_index (planning_sem.time_index i) j" if "j < length actions" for j 
      apply (insert that no_ending_indices) 
      apply (subst (asm) end_indices)  by simp

    show ?case 
      apply (insert 5)
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_end_endsI)
        subgoal by (rule happening_pre_end_ends_dests)
        subgoal apply (subst prop_state_after_instant_start_happ_is_prop_state_after_happ_if_no_end[symmetric])
          using i no_ending by (auto intro: happening_pre_end_ends_dests)
        subgoal apply (subst active_during_minus_ended_is_active_during_if_no_end)
          using i no_ending by (auto intro: happening_pre_end_ends_dests)
        subgoal apply (subst happening_pre_end_ends_dests, assumption)
          using no_ending not_ending by auto
        done
      done
  next
    case (6 x)
    then show ?case 
      apply (induction x) 
      subgoal for L v c
        apply (rule happening_pre_start_endsI)
          apply (rule start_end_invsI)
        subgoal by (intro happening_post_end_ends_dests end_end_invs_dests)
        subgoal by (intro happening_post_end_ends_dests end_end_invs_dests)
        subgoal apply (subst planning_sem.active_after_conv_active_during_minus_ended)
          by (rule happening_post_end_ends_dests)
        by (auto intro: happening_pre_start_endsI start_end_invsI happening_post_end_ends_dests end_end_invs_dests simp: planning_sem.active_after_conv_active_during_minus_ended[symmetric])
      done
  qed
qed

lemma start_ends_possible:
  assumes "graph_impl.steps xs \<and> happening_pre_start_ends i (last xs)"
      and i: "i < length planning_sem.htpl"
      and start_indices: "start_indices = (filter (is_starting_index (planning_sem.time_index i)) [0..<length actions])"
    shows "graph_impl.steps ((ext_seq \<circ> seq_apply) (map edge_2_effect start_indices) xs) \<and> happening_post i (last ((ext_seq \<circ> seq_apply) (map edge_2_effect start_indices) xs))"
proof -
  interpret sip: filter_sorted_distinct_list "[0..<length actions]" "is_starting_index (planning_sem.time_index i)" start_indices
    apply (unfold_locales)
    using start_indices by auto

  have sij_in_act': "j < length actions" 
    if "i < length start_indices"
      "j \<le> start_indices ! i" for i j
    using set_nthI[OF that(1)]
    apply -
    apply (subst (asm) (2) start_indices)
    apply (subst (asm) set_filter)
    using that
    by simp
  
  
  have start_indices_inc_all: "\<not> is_starting_index (planning_sem.time_index i) m"
    if "Suc j < length start_indices" "Suc (start_indices ! j) \<le> m" "m < start_indices ! Suc j" for j m
    apply (rule sip.ys_inc_all)
    using sij_in_act' that by auto

  have start_indices_inc_all_below: "\<not> is_starting_index (planning_sem.time_index i) m"
    if "0 < length start_indices" "m < start_indices ! 0" for m
    apply (rule sip.ys_inc_all_below)
    using that sij_in_act'[OF that(1)] by auto

  have start_indices_inc_all_above: "\<not> is_starting_index (planning_sem.time_index i) m"
    if "start_indices ! (length start_indices - 1) < m" "m < length actions" for m
    apply (rule sip.ys_inc_all_above)
    using that by auto

  have image_start_indices_conv_actions: "((!) actions) ` set start_indices = planning_sem.starting_actions_at (planning_sem.time_index i)"
    unfolding planning_sem.action_happening_case_defs start_indices 
    unfolding set_filter image_Collect set_upt
    unfolding index_case_defs planning_sem.starting_actions_at_def
    apply (subst set_conv_nth)
    by auto



  have nat_leE: thesis if  "x \<le> y" "x < y \<Longrightarrow> thesis" "x = y \<Longrightarrow> thesis"  for x y::nat and thesis using that by linarith
  show ?thesis
  proof (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[
        where R = "happening_pre_start_ends i" 
          and S = "happening_post_start_ends i"
          and P = "start_end_pre i o ((!) start_indices)"
          and Q = "start_end_post i o ((!) start_indices)"
          and fs = "map edge_2_effect start_indices",
          simplified length_map nth_map,
          OF assms(1)], goal_cases)
    case j: (1 j s)
      have sij_set: "start_indices ! j \<in> set start_indices"  using j by auto
      with image_start_indices_conv_actions
      have *: "(actions ! (start_indices ! j)) \<in> planning_sem.starting_actions_at (planning_sem.time_index i)" using j by blast
      
      hence sij_starting: "planning_sem.is_starting_action (planning_sem.time_index i) (actions ! (start_indices ! j))"  
        and sij_in_act[intro]: "actions ! (start_indices ! j) \<in> set actions"  using * planning_sem.starting_actions_at_def j by auto
  
      have sij_starting_index: "is_starting_index (planning_sem.time_index i) (start_indices ! j)" apply (insert sij_set) apply (subst (asm) (2) start_indices) by simp
  
      have sij_ran: "start_indices ! j < length actions" 
        apply (insert sij_set)
        apply (subst (asm) (2) start_indices)
        by simp

      have adds_in_props: "set (adds (at_end (actions ! (start_indices ! j)))) \<subseteq> set props"
        and dels_in_props: "set (dels (at_end (actions ! (start_indices ! j)))) \<subseteq> set props"
        and pre_in_props: "set (pre (at_end (actions ! (start_indices ! j)))) \<subseteq> set props"
        and over_all_in_props: "set (over_all (actions ! (start_indices ! j))) \<subseteq> set props"
        using acts_ref_props using sij_in_act planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto


    show ?case
    proof (insert j, induction s; rule context_conjI, goal_cases)
      case (1 L v c)
      have sij_L: "Suc (start_indices ! j) < length L" using 1
        unfolding comp_def
        apply (subst Lv_conds_dests)
        apply (force intro: start_end_pre_dests start_end_invs_dests happening_invs_dests)
        using sij_ran by simp

      have *: "start_end_pre i (start_indices ! j) (L, v, c)" using 1 by auto
      have **: "start_end_invs i (L, v, c)" using start_end_pre_dests 1 by auto

      define v' where "v' = (v(map prop_to_lock (over_all (actions ! (start_indices ! j))) [\<mapsto>] map (\<lambda>x. plus_int (the (v x)) 1) (map prop_to_lock (over_all (actions ! (start_indices ! j))))))"
        
      have variables_locked_after: "v' (prop_to_lock p) = Some (int (updated_locked_during i (Suc (start_indices ! j)) p))" 
        if p_in_vars: "prop_to_lock p \<in> dom (map_of net_bounds)" and p_in_props: "p \<in> set props" 
        for p
      proof (cases "p \<in> set (over_all (actions ! (start_indices ! j)))")
        case True
          have v'_prop_to_lock: "v' (prop_to_lock p) = Some (the (v (prop_to_lock p)) + 1)"
            unfolding v'_def
            apply (subst distinct_map_upds)
            using True sij_in_act apply simp
            apply (rule distinct_inj_on_map)
            apply (rule distinct_over_all[THEN bspec[of _ _ "actions ! (start_indices ! j)"]])
            using sij_in_act inj_on_subset over_all_in_props variables_inj by auto

        show ?thesis 
          apply (subst v'_prop_to_lock)
          apply (subst updated_locked_during_Suc[OF i sij_starting_index sij_ran True])
          using start_end_pre_dests(2)[OF * p_in_props p_in_vars]
          by auto
      next
        case False
        have "updated_locked_during i (Suc (start_indices ! j)) p = updated_locked_during i (start_indices ! j) p" 
          using updated_locked_during_Suc_inv i sij_ran sij_starting_index False by blast
        moreover
        have "v' (prop_to_lock p) = v (prop_to_lock p)"
          unfolding v'_def
          apply (subst map_upds_apply_nontin)
          using False variable_sets_unique p_in_props over_all_in_props by auto
        ultimately
        show ?thesis using p_in_vars  using start_end_pre_dests(2)[OF * p_in_props] by auto  
      qed
        
      have bounded_after: "Simple_Network_Language.bounded (map_of net_bounds) v'"
      proof (rule updated_bounded[OF _ _ v'_def], goal_cases)
        case 1
        have v_bounded: "bounded (map_of net_bounds) v" using ** by (auto dest: start_end_pre_dests start_end_invs_dests happening_invs_dests Lv_conds_dests)
        have pos: "0 < card (starting_actions_after i (start_indices ! j))" using starting_actions_after_pos_if_starting i sij_ran sij_starting_index by auto
        have l: "card (starting_actions_after i (start_indices ! j)) \<le> length actions" using starting_actions_after_le i by auto
        show ?case by (rule v_bounded)
      next
        case 2
        then show ?case by simp
      next
        case 3
        then show ?case 
          apply (rule ballI)
          subgoal for x
            unfolding set_map
            apply (erule imageE)
            subgoal for p
              apply (erule ssubst[of x])
              apply (intro exI conjI)
                apply (rule map_of_net_bounds_action_inv[OF sij_in_act], simp)
              subgoal apply (frule set_mp[OF over_all_in_props]) 
                using variables_locked_after map_of_net_bounds_action_inv[OF sij_in_act] updated_locked_during_ran by fastforce
              subgoal apply (frule set_mp[OF over_all_in_props]) 
              apply (subst variables_locked_after)
              using map_of_net_bounds_action_inv[OF sij_in_act]
              using updated_locked_during_ran[OF i, of "Suc (start_indices ! j)"] sij_ran by auto
            done
          done
        done
      qed 

      show ?case
        using 1
        unfolding edge_2_effect_alt comp_def
        apply -
      proof(rule start_end_postI, goal_cases)
        case 1
        show ?case 
          apply (rule start_end_invs_maintained[OF **])
                  apply (erule happening_invs_maintained)
                       apply (erule Lv_conds_maintained)
                          apply simp
                         apply simp
          subgoal by ((subst map_upds_apply_nontin | subst fun_upd_other), (force simp: dels_in_props variable_sets_unique variables_unique))+ (simp)
          subgoal using bounded_after v'_def by simp
                      apply auto[4]
          subgoal apply (intro strip)?
            apply (subst nth_list_update_neq)
             apply (frule index_case_dests_disj)
            using sij_starting_index by auto
          subgoal by ((subst map_upds_apply_nontin | subst fun_upd_other), (force simp: dels_in_props variable_sets_unique variables_unique))+ (simp)
          subgoal by ((subst map_upds_apply_nontin | subst fun_upd_other), (force simp: dels_in_props variable_sets_unique variables_unique))+ (simp)
                      apply auto[4]
          subgoal apply (intro strip)?
            apply (subst nth_list_update_neq)
             apply (frule index_case_dests_disj)
            using sij_starting_index by auto
          subgoal apply (intro strip)?
            apply (subst nth_list_update_neq)
             apply (frule index_case_dests_disj)
            using sij_starting_index by auto
          done
      next
        case (2 p)
        then show ?case using variables_locked_after v'_def by auto
      next
        case (3 k)
        then show ?case using start_end_pre_dests sip.ys_Suc by auto
      next
        case (4 k)
        then show ?case 
          apply (cases "k = start_indices ! j")
          using sij_L apply simp
          using start_end_pre_dests by auto
      qed
    next
      case (2 L v c)
      have sij_L: "Suc (start_indices ! j) < length L" using 2
        unfolding comp_def
        apply (subst Lv_conds_dests)
        apply (force intro: start_end_pre_dests start_end_invs_dests happening_invs_dests)
        using sij_ran by simp

      have upds: "is_upds v (map (inc_prop_lock_ab 1) (over_all (actions ! (start_indices ! j)))) (v(map prop_to_lock (over_all (actions ! (start_indices ! j))) [\<mapsto>] map (\<lambda>x. plus_int (the (v x)) 1) (map prop_to_lock (over_all (actions ! (start_indices ! j))))))"
      proof (rule is_upds_inc_vars)
        show "set (map prop_to_lock (over_all (actions ! (start_indices ! j)))) \<subseteq> dom v"
        proof (intro subsetI)
          fix x
          assume a: "x \<in> set (map prop_to_lock (over_all (actions ! (start_indices ! j))))"
          from a obtain p where
            x: "x = prop_to_lock p" 
            and p_in_props: "p \<in> set props" using over_all_in_props by auto
          
          have *: "x \<in> dom (map_of net_bounds)" using map_of_net_bounds_action_inv a by blast
          show "x \<in> dom v" 
            apply (rule domI)
            using 2 * unfolding comp_def x using start_end_pre_dests  p_in_props by blast
        qed
        show "distinct (map prop_to_lock (over_all (actions ! (start_indices ! j))))" 
          apply (rule distinct_inj_on_map) using distinct_over_all sij_in_act 
          using variables_inj inj_on_subset over_all_in_props by auto
        show "map (inc_prop_lock_ab 1) (over_all (actions ! (start_indices ! j))) = map (\<lambda>v. (v, binop plus_int (var v) (exp.const 1))) (map prop_to_lock (over_all (actions ! (start_indices ! j))))" unfolding inc_prop_lock_ab_def by auto
        show "v(map prop_to_lock (over_all (actions ! (start_indices ! j))) [\<mapsto>] map (\<lambda>x. plus_int (the (v x)) 1) (map prop_to_lock (over_all (actions ! (start_indices ! j))))) = 
            v(map prop_to_lock (over_all (actions ! (start_indices ! j))) [\<mapsto>] map (\<lambda>x. plus_int x 1) (map (the \<circ> v) (map prop_to_lock (over_all (actions ! (start_indices ! j))))))"
          unfolding comp_def map_map by simp
      qed 

      have v_pre_sat: "check_bexp v  (bexp_and_all (map (is_prop_ab 1) (over_all (actions ! (start_indices ! j))))) True"
      proof (intro check_bexp_all ballI)
        { fix p
          assume a: "p \<in> set (over_all (actions ! (start_indices ! j)))"
          hence p_in_props: "p \<in> set props" using over_all_in_props by auto
          have "v (prop_to_var p) = Some (prop_state_after_happ i p)"
            apply (rule start_end_invs_dests)
             apply (rule start_end_pre_dests)
            using 2 unfolding comp_def
            using p_in_props
            using map_of_net_bounds_action_inv_props sij_in_act a 
            by auto
          moreover
          have "p \<in> planning_sem.upd_state i" using planning_sem.inv_sat_by_upd_state sij_starting sij_in_act i comp_def a by auto
          ultimately
          have "v (prop_to_var p) = Some 1" using prop_state_after_happ_def i prop_state_def by metis
          hence "is_val v (var (prop_to_var p)) 1" by (simp add: is_val_simps)
          hence "check_bexp v (bexp.eq (var (prop_to_var p)) (exp.const 1)) True"
            by (simp add: check_bexp_simps is_val_simps)
        } 
        moreover
        fix b
        assume "b \<in> set (map (is_prop_ab 1) (over_all (actions ! (start_indices ! j))))"
        ultimately
        show "Simple_Expressions.check_bexp v b True" 
          unfolding is_prop_ab_def set_map comp_def
          by blast
      qed

      show ?case 
        apply (insert 2)
        unfolding comp_def edge_2_effect_alt
        apply (rule single_step_intro)
        unfolding prod.case
        apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
        unfolding net_impl.sem_def
          apply (rule step_u.step_int)
        unfolding TAG_def
                    apply (subst conv_trans[where p = "Suc (start_indices ! j)"])
                     apply (simp add: sij_ran length_net_automata)
                    apply (rule image_eqI[where x = "edge_2 (actions ! (start_indices ! j))"])
                     apply (simp add: edge_2_def)
                    apply (simp add: sij_ran nth_auto_trans)
        subgoal apply (intro disjI2 strip)
          by (subst conv_committed no_committed | simp)+
        subgoal apply (rule check_bexp_Cons)
           apply (force intro: v_pl_cond_sat start_end_pre_dests start_end_invs_dests happening_invs_dests)
          using v_pre_sat by simp
        subgoal by simp
        subgoal using conv_invs no_invs by auto
        subgoal using start_end_pre_dests sij_starting_index sij_ran by auto
        subgoal using sij_L by simp
        subgoal by simp
        subgoal by simp
        subgoal by (rule upds)
        by (auto intro: Lv_conds_dests happening_invs_dests start_end_invs_dests start_end_post_dests start_end_pre_dests)
    qed
  next
    case (2 j s)
    then show ?case 
      unfolding comp_def
      apply -
      apply (induction s)
      subgoal for L v c
        apply (rule start_end_preI)
        subgoal by (rule start_end_post_dests)
        subgoal apply (subst updated_locked_during_inv[OF i, symmetric, where n = "Suc (start_indices ! j)"])
          using sip.ys_Suc apply force
          using start_indices_inc_all
          by (auto intro: start_end_post_dests)
        subgoal 
          apply (erule start_end_post_dests)
          using sip.ys_Suc apply force
          by auto
        subgoal
          apply (erule start_end_post_dests)
           apply (rule ccontr)
          using start_indices_inc_all
          by auto
        done
      done
  next
    case (3 x)
    then show ?case
      unfolding comp_def
      apply -
      apply (induction x)
      subgoal for L v c
        apply (intro start_end_preI)
        subgoal by (rule happening_pre_start_ends_dests)
        subgoal apply (subst updated_locked_during_inv[OF i, symmetric, where n = 0])
          using updated_locked_during_0_is_locked_during[OF i]
          using start_indices_inc_all_below 
          by (auto intro: happening_pre_start_ends_dests)
        subgoal by (auto intro: happening_pre_start_ends_dests)
        subgoal using start_indices_inc_all_below by blast
        done
      done
  next
    case (4 x)
    then show ?case
      unfolding comp_def
      apply -
      apply (induction x)
      subgoal for L v c
        apply (rule happening_post_start_endsI)
        subgoal by (rule start_end_post_dests)
        subgoal apply (subst updated_locked_during_all_is_locked_after[OF i, symmetric])
          apply (subst updated_locked_during_inv[OF i, symmetric, where n = "Suc (start_indices ! (length start_indices - 1))"])
          apply (rule Suc_leI)
          using sip.nth_ys_ran 
          using start_indices_inc_all_above
          by (auto intro: start_end_post_dests)
        subgoal for k
          apply (erule start_end_post_dests)
           apply (rule ccontr)
          using start_indices_inc_all_above 
          by auto
        done
      done
  next
    case (5 x)
    hence no_starting_indices: "set start_indices = {}" by simp
    hence "planning_sem.starting_actions_at (planning_sem.time_index i) = {}"
      apply -
      unfolding start_indices planning_sem.starting_actions_at_def is_starting_index_def 
      apply (subst set_conv_nth)
      by auto
    hence no_starting: "planning_sem.starting_actions_at (planning_sem.time_index i) = {}"
           "planning_sem.starting_snaps_at (planning_sem.time_index i) = {}" 
      using planning_sem.starting_snaps_at_def by auto

    have not_starting: "\<not>is_starting_index (planning_sem.time_index i) j" if "j < length actions" for j 
      apply (insert that no_starting_indices) 
      apply (subst (asm) start_indices)  by simp
    show ?case 
      apply (insert 5)
      apply (induction x)
      subgoal for L v c
        apply (intro happening_post_start_endsI)
        subgoal by (rule happening_pre_start_ends_dests)
        subgoal using happening_pre_start_ends_dests planning_sem.locked_after_and_during' no_starting by simp
        using not_starting by auto
      done
  next
    case (6 x)
    thus ?case 
      apply (induction x)
      subgoal for L v c
        apply (intro happening_postI, simp)
        subgoal by (blast intro: happening_post_start_ends_dests happening_invs_dests start_end_invs_dests)
        subgoal by (blast intro: happening_post_start_ends_dests happening_invs_dests start_end_invs_dests)
        subgoal by (blast intro: happening_post_start_ends_dests happening_invs_dests start_end_invs_dests)
        subgoal by (blast intro: happening_post_start_ends_dests happening_invs_dests start_end_invs_dests)
        subgoal for k apply (rule planning_sem.closed_active_count_0_happening_casesE[rotated], assumption)
          unfolding index_case_defs[symmetric]
          apply (blast intro: happening_invs_dests start_end_invs_dests happening_post_start_ends_dests)+
          by simp
        subgoal for k apply (rule planning_sem.closed_active_count_1_happening_casesE[rotated], assumption)
          unfolding index_case_defs[symmetric] 
          by (fastforce intro: happening_invs_dests start_end_invs_dests happening_post_start_ends_dests)+
        subgoal for k apply (rule act_clock_post_happ_intros)
          unfolding index_case_defs[symmetric] 
          by (fastforce intro: happening_invs_dests start_end_invs_dests happening_post_start_ends_dests)+
        subgoal for k apply (rule act_clock_post_happ_intros)
          unfolding index_case_defs[symmetric] 
          by (fastforce intro: happening_invs_dests start_end_invs_dests happening_post_start_ends_dests)+
        done
      done
  qed
qed

end
end

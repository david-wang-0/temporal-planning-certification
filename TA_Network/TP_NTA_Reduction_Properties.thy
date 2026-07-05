theory TP_NTA_Reduction_Properties
  imports TP_NTA_Reduction_Happenings
begin
context tp_nta_reduction_correctness
begin

subsection \<open>General properties of the automaton\<close>

lemma time_index_Suc_and_delay:
  assumes "i < length planning_sem.htpl"
  shows "real_of_rat (planning_sem.time_index (Suc i)) = real_of_rat (planning_sem.time_index i) + get_delay (Suc i)"
  unfolding get_delay_def planning_sem.time_index_def
  by (simp add: of_rat_add[symmetric])

lemma conv_trans:
assumes "p < length (map (automaton_of o conv_automaton) autos)"
shows "Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) autos ! p) = (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) ` (trans (automaton_of  (autos ! p)))"
  apply (subst nth_map)
  using assms apply simp
  apply (subst comp_def)
  apply (cases "autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "autos ! p"])
     apply assumption
    unfolding conv_automaton_def prod.case
    unfolding automaton_of_def prod.case
    unfolding trans_def fst_conv snd_conv
    unfolding set_map by blast
  done

lemma conv_committed: 
  assumes "p < length (map (automaton_of o conv_automaton) autos)"
  shows "committed (map (automaton_of \<circ> conv_automaton) autos ! p) = committed (map automaton_of autos ! p)"
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "autos ! p"])
     apply simp
    unfolding comp_apply
    unfolding conv_automaton_def automaton_of_def committed_def prod.case fst_conv ..
  done

lemma no_committed: 
  assumes "p < length net_automata"
  shows "committed (map automaton_of net_automata ! p) = {}"
  using assms
  unfolding timed_automaton_net_def automaton_of_def committed_def main_auto_def Let_def action_to_automaton_def
  apply (cases p)
  by simp+

lemma conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) net_automata)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) net_automata ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of net_automata ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "net_automata ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(net_automata ! p)"])
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

lemma no_invs': assumes "p < length net_automata"
  shows "inv (automaton_of (net_automata ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding timed_automaton_net_def Let_def prod.case 
    by simp+
  show ?thesis
    unfolding timed_automaton_net_def Let_def prod.case
  unfolding main_auto_def Let_def action_to_automaton_def
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

lemma no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) net_automata)"
  shows "inv (map (automaton_of \<circ> conv_automaton) net_automata ! p) = (\<lambda>x. [])"
  apply (subst conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using no_invs'
  apply (subst no_invs')
  using assms by auto

lemma cval_add_0: "z\<oplus>(0::real) = z" unfolding cval_add_def 
  by simp


lemma step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of net_bounds) y"
  shows "net_impl.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding net_impl.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using no_invs by auto
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by auto
  done


lemmas non_t_step_intro = step_t_possible[THEN step_u'.intros, rotated, rotated]


subsection \<open>Duration and mutex constraint satisfaction\<close>
lemma mutex_0_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.plan_happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.plan_happ_seq \<or> h = at_start a \<longrightarrow> act_clock_pre_happ c act_to_start_clock a t"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.plan_happ_seq \<or> h = at_end a \<longrightarrow> act_clock_pre_happ c act_to_end_clock a t"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap_action h b \<Longrightarrow> 0 < planning_sem.exec_time b t" for b by blast

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_start act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_start act) t" by simp
    moreover
    have "(t, at_start act) \<notin> planning_sem.plan_happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (act_to_start_clock act)" using s_corr act_clock_pre_happ_def a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (act_to_start_clock act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map act_to_start_clock (filter (\<lambda>a. mutex_effects h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by simp
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_end act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_end act) t" by simp
    moreover
    have "(t, at_end act) \<notin> planning_sem.plan_happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (act_to_end_clock act)" using e_corr act_clock_pre_happ_def clock_cons_unique a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (act_to_end_clock act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map act_to_end_clock (filter (\<lambda>a. mutex_effects h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by simp
    done
  ultimately
  show ?thesis 
    unfolding net_int_clocks_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed

lemma mutex_eps_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.plan_happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.plan_happ_seq \<or> h = at_start a \<longrightarrow> act_clock_pre_happ c act_to_start_clock a t"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.plan_happ_seq \<or> h = at_end a \<longrightarrow> act_clock_pre_happ c act_to_end_clock a t"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap_action h b \<Longrightarrow> rat_of_int \<epsilon> \<le> planning_sem.exec_time b t" for b 
    unfolding Rat.of_int_def by simp

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_start act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_start act) t" by simp
    have c: "(t, at_start act) \<notin> planning_sem.plan_happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (act_to_start_clock act)"
      using s_corr[THEN bspec, OF a(1), THEN mp, OF c, simplified]
      using x of_rat_less_eq unfolding act_clock_pre_happ_def
      by metis
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (act_to_start_clock act) \<epsilon>)"
      by auto
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map act_to_start_clock (filter (\<lambda>a. mutex_effects h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by blast
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_end act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_end act) t" by simp
    have c: "(t, at_end act) \<notin> planning_sem.plan_happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (act_to_end_clock act)"
      using e_corr[THEN bspec, OF a(1), THEN mp, OF c, simplified]
      using x of_rat_less_eq unfolding act_clock_pre_happ_def
      using clock_cons_unique by metis
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (act_to_end_clock act) \<epsilon>)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map act_to_end_clock (filter (\<lambda>a. mutex_effects h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by simp
    done
  ultimately
  show ?thesis 
    unfolding net_int_clocks_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed 

text \<open>Some duration constraints\<close>
lemma check_bexp_all: "check_bexp s (bexp_and_all bs) True" 
  if "\<forall>b \<in> set bs. check_bexp s b True"
  using that
  apply (induction bs)
   apply (subst bexp_and_all.simps)
    apply (rule check_bexp_is_val.intros)
  subgoal for b bs
    apply (subst bexp_and_all.simps)
    apply (subst simp_thms(21)[of True, symmetric])
    apply (rule check_bexp_is_val.intros)
    by auto
  done

lemma check_bexp_all_append: 
  assumes "check_bexp s (bexp_and_all bs) True"
      and "check_bexp s (bexp_and_all cs) True"
    shows "check_bexp s (bexp_and_all (bs @ cs)) True"
  using assms
  apply (induction bs arbitrary: cs)
  apply simp
  subgoal for b bs cs
    apply (subst append_Cons)
    apply (subst bexp_and_all.simps)
    apply (subst (asm) bexp_and_all.simps)
    apply (erule check_bexp_elims)
    apply (subst check_bexp_simps(3))
    by auto
  done

lemma check_bexp_Cons:
  assumes "check_bexp s b True"
      and "check_bexp s c True"
    shows "check_bexp s (bexp.and b c) True"
  apply (subst check_bexp_simps)
  using assms by simp


lemma l_dur_sat_if: 
  assumes "planning_sem.satisfies_duration_bounds act r"
      and "((cv (act_to_start_clock act))::real) = of_rat r"
    shows "cv \<turnstile> map conv_ac (l_dur act)"
  using assms
  unfolding planning_sem.satisfies_duration_bounds_def l_dur_def lower_sem_def comp_def Let_def 
  apply (subst (asm) temp_plan_defs.satisfies_duration_bounds_def)
  unfolding temp_plan_defs_def temp_planning_problem_def 
  using eps_ran apply blast
  apply (cases "lower act")
   apply simp
  subgoal for lb
    apply (cases lb)
    subgoal for tl
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less of_rat_of_int_eq)
    subgoal for tl
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct1)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less_eq of_rat_of_int_eq)
    done
  done
(* coercions *)
(* declare [[show_sorts]] *)
(* show sorts *)
find_theorems "?x < ?y"
lemma u_dur_sat_if:
  assumes "planning_sem.satisfies_duration_bounds act r"
      and "((cv (act_to_start_clock act))::real) = of_rat r"
    shows "cv \<turnstile> map conv_ac (u_dur act)"
  using assms
  unfolding planning_sem.satisfies_duration_bounds_def u_dur_def Let_def upper_sem_def comp_def
  apply (subst (asm) temp_plan_defs.satisfies_duration_bounds_def)
  unfolding temp_plan_defs_def temp_planning_problem_def 
  using eps_ran apply blast
  apply (cases "upper act")
   apply simp
  subgoal for ub
    apply (cases ub)
    subgoal for tu
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct2)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less of_rat_of_int_eq)
    subgoal for tu
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct2)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less_eq of_rat_of_int_eq)
    done
  done

lemma ending_actions_sat_dur_const_specs:
  assumes "a \<in> set actions"
      and "planning_sem.is_ending_action t a"
      and "act_clock_pre_happ c act_to_start_clock a t"
    shows "c \<turnstile> map conv_ac (u_dur a)" "c \<turnstile> map conv_ac (l_dur a)"
  apply -
   apply (rule u_dur_sat_if)
    apply (rule planning_sem.ending_act_sat_dur_bounds)
  apply (rule assms)+
  using assms unfolding act_clock_pre_happ_def apply simp
   apply (rule l_dur_sat_if)
    apply (rule planning_sem.ending_act_sat_dur_bounds)
  apply (rule assms)+
  using assms unfolding act_clock_pre_happ_def by simp


lemma instant_actions_sat_dur_const_specs:
  assumes "a \<in> set actions"
      and "planning_sem.is_instant_action t a"
      and "c (act_to_start_clock a) = 0"
    shows "c \<turnstile> map conv_ac (u_dur a)" "c \<turnstile> map conv_ac (l_dur a)"
  using assms by (auto intro: u_dur_sat_if l_dur_sat_if planning_sem.instant_act_sat_dur_bounds)

lemma ending_actions_sat_mutex_const_specs:
  assumes in_acts: "a \<in> set actions"
    and ending: "planning_sem.is_ending_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_end_clock a t"
              shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_end a)))" 
                "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_end a)))"
  subgoal
    apply (rule mutex_0_constraint_sat)
    using assms(2) planning_sem.is_ending_action_def apply blast
     apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_end b) \<in> planning_sem.plan_happ_seq")
      using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts 
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI)+
    apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts
       apply (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)
      apply (cases "a = b")
      using clocks in_acts rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def by auto
    done
  apply (rule mutex_eps_constraint_sat)
  using assms(2) planning_sem.is_ending_action_dests apply blast
   apply (intro ballI impI)
  subgoal for b
    apply (cases "(t, at_end b) \<in> planning_sem.plan_happ_seq")
    using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts 
    by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI)+
  apply (intro ballI impI)
  subgoal for b
    apply (erule disjE)
    using clocks in_acts
     apply (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)
    apply (cases "a = b")
    using clocks in_acts rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def by auto
  done

lemma instant_action_sat_mutex_start:
  assumes in_acts: "a \<in> set actions"
    and instant: "planning_sem.is_instant_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_start_clock a t"
    and g: " g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_start a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_start a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_end a) \<in> planning_sem.plan_happ_seq" 
          "(t, at_start a) \<in> planning_sem.plan_happ_seq" using instant planning_sem.is_instant_action_def by simp+
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_start b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
  apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts rat_impl.set_impl.at_start_inj_on_acts unfolding inj_on_def
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_end b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_start b) \<in> planning_sem.plan_happ_seq")
      using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_starting_actionI 
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed

lemma instant_action_sat_mutex_end:
  assumes in_acts: "a \<in> set actions"
    and instant: "planning_sem.is_instant_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_end_clock a t"
    and g: "g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_end a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_end a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_end a) \<in> planning_sem.plan_happ_seq" using instant planning_sem.is_instant_action_def by simp
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.plan_happ_seq \<or> at_end a = at_start b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_end b) \<in> planning_sem.plan_happ_seq")
      subgoal using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_ending_actionI by blast
      subgoal using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_not_happening_actionI by blast
      done
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.plan_happ_seq \<or> at_end a = at_end b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
  apply (intro ballI impI)
    subgoal for b
      using clocks in_acts rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed

lemma starting_action_sat_mutex_start:
  assumes in_acts: "a \<in> set actions"
    and starting: "planning_sem.is_starting_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_start_clock a t"
    and g: " g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_start a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_start a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_start a) \<in> planning_sem.plan_happ_seq" using starting planning_sem.is_starting_action_def by simp+
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_start b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
  apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts rat_impl.set_impl.at_start_inj_on_acts unfolding inj_on_def
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_end b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_start b) \<in> planning_sem.plan_happ_seq")
      using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_starting_actionI 
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed

subsection \<open>Run-construction rules\<close>
text \<open>The rules used to show that the composition of sequences results in a run\<close>
sublocale steps_seq: sequence_rules graph_impl.steps
  apply standard                                 
  using graph_impl.steps.intros(1) steps_extend .


subsection \<open>Invariant maintenance\<close>
lemma Lv_conds_maintained:
  assumes "Lv_conds L v"
    and "length L = length L'"
    and "L ! 0 = L' ! 0"
    and "v' planning_lock = v planning_lock"
    and "bounded (map_of net_bounds) v \<Longrightarrow> bounded (map_of net_bounds) v'"
  shows "Lv_conds L' v'"
  using assms unfolding Lv_conds_def by simp

lemma happening_invs_maintained:
  assumes "happening_invs n (L, v, c)"
      and clock: 
          "\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_start_clock (actions ! i))  = c (act_to_start_clock (actions ! i))"
          "\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_end_clock (actions ! i))  = c (act_to_end_clock (actions ! i))"
          "\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_start_clock (actions ! i))  = c (act_to_start_clock (actions ! i))"
          "\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_end_clock (actions ! i))  = c (act_to_end_clock (actions ! i))"
      and Loc: "\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
  shows "happening_invs n (L', v', c')"
  apply (insert assms(1))
  apply (rule happening_invsI)
         apply (rule HOL.refl)
  using happening_invs_dests
  unfolding act_clock_pre_happ_def
  using clock apply (presburger, presburger, presburger, presburger)
  using Loc happening_invs_dests by auto

lemma end_start_invs_maintained:
  assumes "end_start_invs n (L, v, c)"
      and happ_invs: "happening_invs n (L, v, c) \<Longrightarrow> happening_invs n (L', v', c')"
      and p: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_var p) = v (prop_to_var p)"
      and aa: "v' acts_active  = v acts_active"
      and clock: 
          "\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_start_clock (actions ! i))  = c (act_to_start_clock (actions ! i))"
          "\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_start_clock (actions ! i))  = c (act_to_start_clock (actions ! i))"
          "\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_end_clock (actions ! i))  = c (act_to_end_clock (actions ! i))"
      and Loc: 
          "\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
          "\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
  shows "end_start_invs n (L', v', c')"
  apply (rule end_start_invsI, simp)
         apply (rule happ_invs, rule end_start_invs_dests, simp add: assms(1))
  unfolding act_clock_pre_happ_def
  by (auto simp: clock[THEN spec, THEN mp, THEN mp] p[THEN spec, THEN mp] aa Loc[THEN spec, THEN mp, THEN mp] end_start_invs_dests[OF assms(1), simplified act_clock_pre_happ_def])

lemma instant_action_invs_maintained:
  assumes "instant_action_invs n (L, v, c)"
      and happ_invs: "happening_invs n (L, v, c) \<Longrightarrow> happening_invs n (L', v', c')"
      and lock: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_lock p) = v (prop_to_lock p)"
      and clock: 
          "\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_start_clock (actions ! i))  = c (act_to_start_clock (actions ! i))"
          "\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> c' (act_to_end_clock (actions ! i))  = c (act_to_end_clock (actions ! i))"
      and Loc: 
          "\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
          "\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
  shows "instant_action_invs n (L', v', c')"
  apply (insert assms(1))
  apply (rule instant_action_invsI, simp)
  by (auto dest: instant_action_invs_dests simp: happ_invs lock clock Loc act_clock_pre_happ_def)

lemma start_start_invs_maintained:
  assumes "start_start_invs i (L, v, c)"
      and "happening_invs i (L, v, c) \<Longrightarrow> happening_invs i (L', v', c')"
      and "(\<forall>p. p \<in> set props \<longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v' (prop_to_lock p) = v (prop_to_lock p))"
          "(\<forall>ia<length actions. is_ending_index (planning_sem.time_index i) ia \<longrightarrow> c' (act_to_end_clock (actions ! ia)) = c (act_to_end_clock (actions ! ia)))"
          "(\<forall>ia<length actions. is_instant_index (planning_sem.time_index i) ia \<longrightarrow> c' (act_to_start_clock (actions ! ia)) = c (act_to_start_clock (actions ! ia)))"
          "(\<forall>ia<length actions. is_instant_index (planning_sem.time_index i) ia \<longrightarrow> c' (act_to_end_clock (actions ! ia)) = c (act_to_end_clock (actions ! ia)))"
          "(\<forall>ia<length actions. is_ending_index (planning_sem.time_index i) ia \<longrightarrow> L' ! Suc ia = L ! Suc ia)"
          "(\<forall>ia<length actions. is_instant_index (planning_sem.time_index i) ia \<longrightarrow> L' ! Suc ia = L ! Suc ia)"
  shows "start_start_invs i (L', v', c')"
  using assms unfolding start_start_invs_def Let_def by (auto split: prod.splits)

lemma end_end_invs_maintained:
  assumes "end_end_invs i (L, v, c)"
    "happening_invs i (L, v, c) \<Longrightarrow> happening_invs i (L', v', c')"
  and syn: "\<And>p. p \<in> set props \<Longrightarrow>prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = v' (prop_to_lock p)"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = c'(act_to_start_clock (actions ! k))"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = c' (act_to_end_clock (actions ! k))"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = c' (act_to_start_clock (actions ! k))"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = c' (act_to_end_clock (actions ! k))"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = L' ! Suc k"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = L' ! Suc k"
  shows "end_end_invs i (L', v', c')"
  apply (insert assms(1))
  apply (rule end_end_invsI)
  subgoal by (intro assms(2) end_end_invs_dests)
  by (subst syn[symmetric], force+, blast intro: end_end_invs_dests)+

lemma start_end_invs_maintained:
  assumes prev: "start_end_invs i (L, v, c)"
      and happ: "happening_invs i (L, v, c) \<Longrightarrow> happening_invs i (L', v', c')"
      and syn: "v acts_active = v' acts_active"
        "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = v' (prop_to_var p)"
        "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = c' (act_to_start_clock (actions ! k))"
        "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = c' (act_to_end_clock (actions ! k))"
        "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = c' (act_to_start_clock (actions ! k))"
        "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = c' (act_to_end_clock (actions ! k))"
        "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = L' ! Suc k"
        "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = L' ! Suc k"
      shows "start_end_invs i (L', v', c')"
  apply (insert prev)
  apply (rule start_end_invsI)
  subgoal by (intro happ start_end_invs_dests)
  by (subst syn[symmetric], force?, force?, blast intro: start_end_invs_dests)+


end
end

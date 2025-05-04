theory TP_NTA_Reduction_Abs_Rename_Correctness
  imports TP_NTA_Reduction_Abs_Rename
begin

context tp_nta_reduction_spec
begin
(* lemma "abs_renum.sem, abs_renum.a\<^sub>0 \<Turnstile> form"
  sorry *)
(* To do: Don't actually prove this correct. Just provide the necessary assumptions to instantiate this *)
section \<open>Equivalence to temporal planning semantics\<close>


definition lower_sem where
"lower_sem \<equiv> (map_option (map_lower_bound Rat.of_int)) o lower"

definition upper_sem where
"upper_sem \<equiv> (map_option (map_upper_bound Rat.of_int)) o upper"

lemma form_alt: "form \<equiv> Simple_Network_Language_Model_Checking.formula.EX (sexp.loc 0 GoalLocation)"
  unfolding form_def Let_def timed_automaton_net_spec_def prod.case .

context 
  fixes \<pi>
  assumes vp: "valid_plan \<pi> (set init) (set goal) at_start at_end (set \<circ> over_all) lower_sem upper_sem (set \<circ> pre) (set \<circ> adds) (set \<circ> dels) (Rat.of_int \<epsilon>)"
      and pap: "plan_actions_in_problem \<pi> (set actions)"
      and nso: "no_self_overlap \<pi>"
begin
interpretation planning_sem: nta_temp_planning 
  "set init" "set goal" 
  at_start at_end 
  "set o over_all" 
  lower_sem upper_sem 
  "set o pre" "set o adds" "set o dels"
  "Rat.of_int \<epsilon>"
  "set props"
  "set actions"
  \<pi> 
  1
  apply standard 
  subgoal using some_propositions unfolding List.card_set apply (induction props) by auto
  subgoal using some_actions unfolding List.card_set apply (induction actions) by auto
  subgoal by simp
  subgoal by simp
  subgoal using eps_range unfolding Rat.of_int_def by auto
  subgoal using domain_ref_fluents using fluent_imp_const_valid_dom by blast
  using domain_ref_fluents init_props goal_props at_start_inj at_end_inj snaps_disj vp pap nso by simp+

subsection \<open>Preliminaries?\<close>

lemma card_action_set: "card (set actions) = length actions" using distinct_actions distinct_card by blast

lemma nth_action_unique:
  assumes "a \<in> set actions"
      and "n < length actions"
      and "actions ! n = a"
      and "m < length actions"
      and "actions ! m = a"
    shows "n = m" using assms 
  using distinct_conv_nth distinct_actions by metis

lemma nth_start_unique:
  assumes "a \<in> set actions"
      and "n < length actions"
      and "at_start (actions ! n) = at_start a"
    shows "actions ! n = a"
proof -
  have "actions ! n \<in> set actions" using assms set_conv_nth by simp
  with assms
  show ?thesis using at_start_inj unfolding inj_on_def by blast
qed


lemma nth_end_unique:
  assumes "a \<in> set actions"
      and "n < length actions"
      and "at_end (actions ! n) = at_end a"
    shows "actions ! n = a"
proof -
  have "actions ! n \<in> set actions" using assms set_conv_nth by simp
  with assms
  show ?thesis using at_end_inj unfolding inj_on_def by blast
qed

lemma nth_start_end_disj:
  assumes "a \<in> set actions"
      and "n < length actions"
    shows "at_start (actions ! n) \<noteq> at_end a"
  using assms in_set_conv_nth[of "actions ! n" actions] snaps_disj by blast

lemma nth_end_start_disj:
  assumes "a \<in> set actions"
      and "n < length actions"
    shows "at_end (actions ! n) \<noteq> at_start a"
  using assms in_set_conv_nth[of "actions ! n" actions] snaps_disj by blast
  

lemma set_nthI:
  assumes "n < length xs"
  shows "xs ! n \<in> set xs" using assms in_set_conv_nth by auto

lemma nth_actions_unique:
  assumes i: "i < length actions"
      and n: "n < length actions"
      and neq: "i \<noteq> n"
    shows "actions ! i \<noteq> actions ! n"
  using distinct_conv_nth assms distinct_actions by blast
    

lemma nth_starts_unique:
  assumes i: "i < length actions"
      and n: "n < length actions"
      and neq: "i \<noteq> n"
    shows "at_start (actions ! i) \<noteq> at_start (actions ! n)"
  apply -
  apply (rule notI)
  using at_start_inj unfolding inj_on_def
  using set_nthI[OF i] set_nthI[OF n] 
  using nth_actions_unique[OF assms]
  by blast


lemma nth_ends_unique:
  assumes i: "i < length actions"
      and n: "n < length actions"
      and neq: "i \<noteq> n"
    shows "at_end (actions ! i) \<noteq> at_end (actions ! n)"
  apply -
  apply (rule notI)
  using at_end_inj unfolding inj_on_def
  using set_nthI[OF i] set_nthI[OF n] 
  using nth_actions_unique[OF assms]
  by blast

(* Invariants of actions whose indexes are lower than n and are scheduled at t 
    have been deactivated. In other words, the parts of their end snap-actions that
    deactivate invariants have been executed *)                         
definition "partially_updated_locked_before t p n \<equiv> planning_sem.locked_before t p 
-  sum_list (map 
      (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0)) 
      (filter 
        (\<lambda>a. p \<in> set (over_all a)) 
        (map (\<lambda>n. actions ! n) [0..<n])))"

lemma sum_list_eq:
  assumes "distinct xs" "distinct ys" "set xs = set ys" 
  shows "sum_list ((map f xs)::nat list) = sum_list (map f ys)"
proof -
  have "mset xs = mset ys" using assms set_eq_iff_mset_eq_distinct by blast
  hence "mset (map f xs) = mset (map f ys)" by simp
  hence "fold (+) (map f xs) 0 = fold (+) (map f ys) 0"
    apply -
    apply (rule fold_permuted_eq[where P = "\<lambda>_. True"])
       apply simp
      apply simp
     apply simp
    by simp
  moreover
  have "foldr (+) (map f xs) 0 = fold (+) (map f xs) 0"
    apply (subst foldr_fold)
    by auto
  moreover
  have "foldr (+) (map f ys) 0 = fold (+) (map f ys) 0"
    apply (subst foldr_fold)
    by auto
  ultimately
  show ?thesis unfolding sum_list.eq_foldr by argo
qed

lemma partially_updated_locked_before_by_all_actions_is_locked_during: 
  "partially_updated_locked_before t p (length actions) = planning_sem.locked_during t p"
proof -
  have d1: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) actions)" using distinct_actions by auto
  have d2: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.distinct_action_list by simp
  have s: "set (filter (\<lambda>a. p \<in> set (over_all a)) actions) = set (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.set_action_list by auto
  
  show ?thesis
  unfolding partially_updated_locked_before_def planning_sem.locked_during_and_before
  apply (subst planning_sem.locked_by_def)
  apply (subst comp_apply)
  apply (subst List.map_nth)
  using sum_list_eq[OF d1 d2 s]
  by auto
qed

lemma partially_updated_locked_before_inv_mono: "partially_updated_locked_before t p n \<ge> partially_updated_locked_before t p (Suc n)"
  unfolding partially_updated_locked_before_def by simp


lemma partially_updated_locked_before_inv_mono': assumes "n \<le> m"
  shows "partially_updated_locked_before t p n \<ge> partially_updated_locked_before t p m"
  using assms
  apply (induction m arbitrary: n)
  subgoal for n
   apply (induction n)
    using partially_updated_locked_before_inv_mono apply blast
    using partially_updated_locked_before_inv_mono order_trans by blast
  subgoal for m n
    apply (subst (asm) le_Suc_eq)
    apply (erule disjE)
    apply (rule partially_updated_locked_before_inv_mono[THEN order_trans])
     apply blast
    by blast
  done

lemma partially_updated_locked_before_by_none_is_locked_before:
  "partially_updated_locked_before t p 0 = planning_sem.locked_before t p"
  unfolding partially_updated_locked_before_def
  by simp

lemma partially_updated_locked_before_ran: "partially_updated_locked_before t p n \<le> length actions" 
  using planning_sem.locked_before_ran unfolding distinct_card[OF distinct_actions]
  using partially_updated_locked_before_inv_mono'[of 0 n] unfolding partially_updated_locked_before_by_none_is_locked_before 
  using order_trans by blast

find_theorems "[?n..<?m] @ [?m..<?o]"

lemma partially_updated_locked_before_inv:
  assumes "n \<le> m"
      and "\<And>i a. n \<le> i \<Longrightarrow> i < m \<Longrightarrow> a = actions ! i \<Longrightarrow> \<not>((t, at_end a) \<in> planning_sem.happ_seq \<and> (t, at_start a) \<notin> planning_sem.happ_seq)" 
  shows "partially_updated_locked_before t p n = partially_updated_locked_before t p m"
proof (cases "n = m")
  case True
  then show ?thesis by simp
next
  have 0: "\<forall>x \<in> set (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<m]))). x = 0"
    unfolding set_map filter_map set_filter comp_def using assms by auto
  have 1: "foldr (+) xs 0 = (0::nat)" if "\<forall>x \<in> set xs. x = 0" for xs using that 
    apply (induction xs)
    by auto
  case False
  then show ?thesis 
  unfolding partially_updated_locked_before_def
  apply (subst upt_append[of n m, symmetric])
  using assms apply simp
  apply (subst map_append)
  apply (subst filter_append)
  apply (subst (2) sum_list.eq_foldr)
  apply (subst map_append)
  apply (subst foldr_append)
  apply (subst 1[OF 0])
  apply (subst sum_list.eq_foldr[symmetric])
  by blast
qed

lemma foldr_assoc: "foldr (+) xs (n + 0::nat) = (foldr (+) xs 0) + n"
  apply (induction xs)
   apply simp
  subgoal for x xs
    by auto
  done

lemma partially_updated_locked_before_alt: assumes "n < length actions"
  shows "partially_updated_locked_before t p n = planning_sem.locked_during t p 
+ sum_list (map 
      (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)) 
      (filter 
        (\<lambda>a. p \<in> set (over_all a)) 
        (map (\<lambda>n. actions ! n) [n..<length actions])))"
proof -
  have 1: "foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n]))) 0 +
  foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0 =
  foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n])))
   (foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0)"
    using foldr_assoc[symmetric, where xs = "(map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n])))" and n = "foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0"]
    by simp
  have d1: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) actions)" using distinct_actions by auto
  have d2: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.distinct_action_list by simp
  have s: "set (filter (\<lambda>a. p \<in> set (over_all a)) actions) = set (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.set_action_list by auto


  have "(\<Sum>a\<leftarrow>planning_sem.locked_by p. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0) 
      = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) 
      + (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0)"
    apply (subst (2) sum_list.eq_foldr)+
    apply (subst 1)
    apply (subst foldr_append[symmetric])
    apply (subst map_append[symmetric])
    apply (subst filter_append[symmetric])
    apply (subst map_append[symmetric])
    apply (subst upt_append)
    using assms
     apply simp
    apply (subst sum_list.eq_foldr[symmetric])
    apply (subst List.map_nth)
    apply (subst sum_list_eq[OF d1 d2 s])
    using planning_sem.locked_by_def unfolding comp_def
    by simp
  thus ?thesis 
    apply (subst partially_updated_locked_before_def)  
    apply (subst planning_sem.locked_before_and_during)
    by linarith
qed

definition "prop_state_before i p \<equiv> if (p \<in> planning_sem.plan_state_seq i) then 1 else (0::int)"

definition "actions_before n \<equiv>
  map ((!) actions) [0..<n]
"

definition "instant_actions_before t n \<equiv> 
  let 
    instant_actions_before = filter (planning_sem.is_instant_action t) (actions_before n)
  in (set instant_actions_before)"

definition "instant_snaps_before t n \<equiv> at_start ` instant_actions_before t n \<union> at_end ` instant_actions_before t n"

definition "apply_instant_snaps_before t n s \<equiv>
  let hs = instant_snaps_before t n
  in s - \<Union> ((set o dels) ` hs) \<union> \<Union> ((set o adds) ` hs)
"

definition "instant_prev_updated_plan_state_seq i n \<equiv> apply_instant_snaps_before (time_index \<pi> i) n (planning_sem.plan_state_seq i)"

definition "instant_prev_updated_prop_state i p n \<equiv> if (p \<in> instant_prev_updated_plan_state_seq i n) then 1 else (0::int)"

lemma instant_actions_before_all_is_instant_actions: "instant_actions_before t (length actions) = planning_sem.instant_actions_at t"
  unfolding instant_actions_before_def Let_def set_filter set_map set_upt planning_sem.instant_actions_at_def actions_before_def by simp

lemma instant_snaps_before_all_is_instant_snaps: "instant_snaps_before t (length actions) = planning_sem.instant_snaps_at t"
  unfolding instant_snaps_before_def planning_sem.instant_snaps_at_def using instant_actions_before_all_is_instant_actions by simp

lemma apply_instant_snaps_before_all_is_apply_instant_snaps: "apply_instant_snaps_before t (length actions) s = planning_sem.app_effs s (planning_sem.instant_snaps_at t)"
  unfolding planning_sem.app_effs_def apply_instant_snaps_before_def Let_def instant_snaps_before_all_is_instant_snaps apply_effects_def by auto

lemma instant_actions_before_0_is_none: "instant_actions_before t 0 = {}" 
  unfolding instant_actions_before_def Let_def actions_before_def by simp

lemma instant_snaps_before_0_is_none: "instant_snaps_before t 0 = {}"
  unfolding instant_snaps_before_def instant_actions_before_0_is_none by blast

lemma apply_instant_snaps_before_0_is_id: "apply_instant_snaps_before t 0 s = s"
  unfolding apply_instant_snaps_before_def instant_snaps_before_0_is_none by simp

abbreviation "is_instant_index t n \<equiv> (t, at_start (actions ! n)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! n)) \<in> planning_sem.happ_seq"

abbreviation "is_starting_index t n \<equiv> (t, at_start (actions ! n)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! n)) \<notin> planning_sem.happ_seq"

abbreviation "is_ending_index t n \<equiv> (t, at_start (actions ! n)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! n)) \<in> planning_sem.happ_seq"

abbreviation "is_not_happening_index t n \<equiv> (t, at_start (actions ! n)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! n)) \<notin> planning_sem.happ_seq"

definition "instant_indices_before t n \<equiv> filter (is_instant_index t) [0..<n]"

definition "starting_indices_before t n \<equiv> filter (is_starting_index t) [0..<n]"

definition "ending_indices_before t n \<equiv> filter (is_ending_index t) [0..<n]"

definition "not_happening_indices_before t n \<equiv> filter (is_not_happening_index t) [0..<n]"

lemma instant_actions_before_alt: "instant_actions_before t n = set (map ((!) actions) (instant_indices_before t n))"
  unfolding instant_actions_before_def instant_indices_before_def Let_def set_map actions_before_def
  apply (subst filter_map)
  apply (subst set_map)
  apply (subst comp_def)
  by blast


lemma instant_snaps_before_is_in_happ_seq: 
  assumes "n < length actions"
  shows "instant_snaps_before t n \<subseteq> happ_at planning_sem.happ_seq t"
proof -
  have 1: "(!) actions ` {0..<n} \<subseteq> set actions" using assms by fastforce 
  { fix x
    assume "x \<in> instant_snaps_before t n"
    then obtain a where
      "x = at_start a \<or> x = at_end a"
      "a \<in> set actions"
      "(t, at_start a) \<in> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq"
      unfolding instant_snaps_before_def instant_actions_before_def Let_def
      set_filter set_map set_upt actions_before_def using 1 by blast
    hence "(t, x) \<in> planning_sem.happ_seq" by blast
  } 
  thus "instant_snaps_before t n \<subseteq> happ_at planning_sem.happ_seq t" by blast
qed

(* To do: generalise? *)
lemma instant_snaps_before_not_include:
  assumes "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and "n < length actions"
  shows "h \<notin> instant_snaps_before t n"
proof -
  { fix x
    assume x: "x \<in> instant_snaps_before t n" 

    have 1: "instant_snaps_before t n = at_start ` {x \<in> (!) actions ` {0..<n}. (t, at_start x) \<in> planning_sem.happ_seq \<and> (t, at_end x) \<in> planning_sem.happ_seq} 
        \<union> at_end ` {x \<in> (!) actions ` {0..<n}. (t, at_start x) \<in> planning_sem.happ_seq \<and> (t, at_end x) \<in> planning_sem.happ_seq}"
      unfolding instant_snaps_before_def instant_actions_before_def Let_def set_filter set_map set_upt actions_before_def by simp
    with x 
    consider i where  "i < n" "x = at_start (actions ! i)" | i where  "i < n" "x = at_end (actions ! i)"
      by auto
    note xc = this
    { fix i
      assume i: "i < n"
      hence neq: "actions ! i \<noteq> actions ! n"  using distinct_actions distinct_nth_unique assms by force
      have ia: "actions ! i \<in> set actions" using assms(2) set_conv_nth i by simp
      have na: "actions ! n \<in> set actions" using assms by simp
      have "at_start (actions ! i) \<noteq> h" 
        apply (rule assms(1)[THEN disjE])
        using neq ia na at_start_inj unfolding inj_on_def apply blast
        using snaps_disj using na ia by blast
      moreover
      have "at_end (actions ! i) \<noteq> h" 
        apply (rule assms(1)[THEN disjE])
        using snaps_disj na ia apply blast
        using neq ia na at_end_inj unfolding inj_on_def by blast
      ultimately
      have "at_start (actions ! i) \<noteq> h" "at_end (actions ! i) \<noteq> h" by simp+
    } 
    hence "x \<noteq> h" apply (cases rule: xc)
      by simp+
  }
  thus ?thesis by blast
qed

lemma apply_instant_snaps_before_non_mutex:
  assumes "(t, h) \<in> planning_sem.happ_seq"
      and "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and "set (pre h) \<subseteq> s"
      and "n < length actions"
    shows "set (pre h) \<subseteq> apply_instant_snaps_before t n s"
proof -
  have 1: "instant_snaps_before t n \<subseteq> happ_at planning_sem.happ_seq t" using instant_snaps_before_is_in_happ_seq assms by blast
  have 2: "set (pre h) \<inter> set (adds x) = {} \<and> set (pre h) \<inter> set (dels x) = {}" if "x \<in> instant_snaps_before t n" for x 
  proof -
    have "(t, x) \<in> planning_sem.happ_seq" using that 1 by blast
    moreover
    have "x \<noteq> h" using instant_snaps_before_not_include that assms by blast
    ultimately
    show ?thesis using assms(1) planning_sem.mutex_pre_app by auto
  qed
  { fix p
    assume p: "p \<in> set (pre h)"
    with assms 
    have "p \<in> s" by blast
    moreover
    have "p \<notin>  \<Union> ((set o dels) ` instant_snaps_before t n)" using p 2 by auto
    moreover
    have "p \<notin>  \<Union> ((set o adds) ` instant_snaps_before t n)" using p 2 by auto
    ultimately
    have "p \<in> s - \<Union> ((set o dels) ` instant_snaps_before t n) \<union> \<Union> ((set o adds) ` instant_snaps_before t n)" by blast
  }
  thus ?thesis unfolding apply_instant_snaps_before_def by auto
qed

lemma pre_sat_by_upd_state_seq:
  assumes i: "i < length (htpl \<pi>)"
      and t: "t = time_index \<pi> i"
      and h: "(t, h) \<in> planning_sem.happ_seq"
             "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and n: "n < length actions"
    shows "set (pre h) \<subseteq> instant_prev_updated_plan_state_seq i n"
proof -
  from t h(1) i planning_sem.plan_state_seq_happ_pres
  have "set (pre h) \<subseteq> planning_sem.plan_state_seq i" by auto
  thus ?thesis unfolding instant_prev_updated_plan_state_seq_def using assms apply_instant_snaps_before_non_mutex by blast
qed

lemma pre_val_in_instant_prev_updated_prop_state_if:
  assumes i: "i < length (htpl \<pi>)"
      and t: "t = time_index \<pi> i"
      and h: "(t, h) \<in> planning_sem.happ_seq"
             "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and n: "n < length actions"
      and p: "p \<in> set (pre h)"
    shows "instant_prev_updated_prop_state i p n = 1"
  using assms pre_sat_by_upd_state_seq[THEN subsetD, OF assms] unfolding instant_prev_updated_prop_state_def by argo

lemma set_upt_Suc_alt: "{0..<Suc n} = {0..<n} \<union> {n}" by auto

lemma instant_snaps_before_Suc:
  assumes starting: "(t, (at_start (actions ! n))) \<in> planning_sem.happ_seq"
      and ending: "(t, (at_end (actions ! n))) \<in> planning_sem.happ_seq"
    shows "instant_snaps_before t (Suc n) = instant_snaps_before t n \<union> {at_start (actions ! n)} \<union>  {at_end (actions ! n)}"
  unfolding instant_snaps_before_def Let_def instant_actions_before_def
set_filter set_map set_upt  set_upt_Suc_alt actions_before_def
   image_Un image_insert image_empty 
    using starting ending by blast

lemma apply_instant_snaps_before_Suc:
  assumes starting: "(t, (at_start (actions ! n))) \<in> planning_sem.happ_seq"
      and ending: "(t, (at_end (actions ! n))) \<in> planning_sem.happ_seq"
      and n: "n < length actions"
    shows "apply_instant_snaps_before t (Suc n) s = 
  apply_instant_snaps_before t n s
  - set (dels (at_start (actions ! n)))
  \<union> set (adds (at_start (actions ! n)))
  - set (dels (at_end (actions ! n)))
  \<union> set (adds (at_end (actions ! n)))"
proof -
  have "planning_sem.app_effs (planning_sem.app_effs s (instant_snaps_before t n)) (planning_sem.snaps (actions ! n)) = planning_sem.app_effs s (instant_snaps_before t n \<union> planning_sem.snaps (actions ! n))"
    using planning_sem.happ_combine[of "(instant_snaps_before t n)" "{at_start (actions ! n), at_end (actions ! n)}"] starting ending instant_snaps_before_is_in_happ_seq[OF n] by blast
  hence 1: " s - \<Union> ((set \<circ> dels) ` (instant_snaps_before t n \<union> planning_sem.snaps (actions ! n))) \<union> \<Union> ((set \<circ> adds) ` (instant_snaps_before t n \<union> planning_sem.snaps (actions ! n))) 
    = s - \<Union> ((set \<circ> dels) ` instant_snaps_before t n) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before t n) - \<Union> ((set \<circ> dels) ` planning_sem.snaps (actions ! n)) \<union> \<Union> ((set \<circ> adds) ` planning_sem.snaps (actions ! n))" unfolding planning_sem.app_effs_def apply_effects_def by argo

  have "planning_sem.app_effs (planning_sem.app_effs M {at_start (actions ! n)}) {at_end (actions ! n)} = planning_sem.app_effs M ({at_start (actions ! n)} \<union> {at_end (actions ! n)})" for M using planning_sem.happ_combine[of "{at_start (actions ! n)}" "{at_end (actions ! n)}"] starting ending by blast
  hence 2: "M - \<Union> ((set \<circ> dels) ` ({at_start (actions ! n), at_end (actions ! n)})) \<union> \<Union> ((set \<circ> adds) ` ({at_start (actions ! n), at_end (actions ! n)})) = 
  M - \<Union> ((set \<circ> dels) ` {at_start (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n)}) - \<Union> ((set \<circ> dels) ` {at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_end (actions ! n)})"
    for M unfolding planning_sem.app_effs_def apply_effects_def by auto

  have "apply_instant_snaps_before t (Suc n) s =  s - \<Union> ((set \<circ> dels) ` instant_snaps_before t (Suc n)) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before t (Suc n))" unfolding apply_instant_snaps_before_def Let_def by simp
  also have "... = s - \<Union> ((set \<circ> dels) ` (instant_snaps_before t n \<union> {at_start (actions ! n), at_end (actions ! n)})) \<union> \<Union> ((set \<circ> adds) ` (instant_snaps_before t n \<union> {at_start (actions ! n), at_end (actions ! n)}))" using instant_snaps_before_Suc[OF starting ending] by auto
  also have "... = s - \<Union> ((set \<circ> dels) ` instant_snaps_before t n) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before t n) - \<Union> ((set \<circ> dels) ` {at_start (actions ! n), at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n), at_end (actions ! n)})" apply (subst 1) by blast
  also have "... = apply_instant_snaps_before t n s - \<Union> ((set \<circ> dels) ` {at_start (actions ! n), at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n), at_end (actions ! n)})" unfolding apply_instant_snaps_before_def Let_def by blast
  also have "... = apply_instant_snaps_before t n s - \<Union> ((set \<circ> dels) ` {at_start (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n)}) - \<Union> ((set \<circ> dels) ` {at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_end (actions ! n)})" apply (subst 2) by blast
  finally
  show ?thesis by simp
qed

lemma instant_prev_updated_prop_state_Suc:
  assumes t: "t = time_index \<pi> i"
      and starting: "(t, (at_start (actions ! n))) \<in> planning_sem.happ_seq"
      and ending: "(t, (at_end (actions ! n))) \<in> planning_sem.happ_seq"
      and n: "n < length actions"
    shows "instant_prev_updated_prop_state i p (Suc n) = (if p \<in> apply_instant_snaps_before t n (planning_sem.plan_state_seq i) - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) - set (dels (at_end (actions ! n))) \<union> set (adds (at_end (actions ! n))) then 1 else 0)"
  unfolding instant_prev_updated_prop_state_def instant_prev_updated_plan_state_seq_def 
  apply (subst t[symmetric])
  apply (subst apply_instant_snaps_before_Suc[OF assms(2,3,4)])
  by simp


(* A is Graph_Defs for the Bisimulation_Invariant of parts of the transition relation.
A is the original graph combined with semantics. *)

term "\<lambda>(L, s, u) (L', s', u'). step_u' abs_renum.sem L s u L' s' u'"

value "shd (shift [1::nat] x)"

term "planning_sem.happ_seq"

definition to_var_asmt::"'proposition set \<Rightarrow> 'proposition set \<Rightarrow> 'proposition variable \<Rightarrow> int option" where
"to_var_asmt ps iv vr \<equiv> (
  case vr of
    PropVar p \<Rightarrow> if (p \<in> ps) then 1 else 0
  | PropLock p \<Rightarrow> if (p \<in> iv) then 1 else 0
) |> Some
"


(* The main automaton is the first automaton, so the index must be incremented *)
definition enter_start_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"enter_start_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := StartInstant act];

  ds = dels (at_start act) |> map PropVar;
  as = adds (at_start act) |> map PropVar;
  var_asmt' = var_asmt(ActsActive \<mapsto> (the (var_asmt ActsActive) + 1));
  var_asmt'' = var_asmt'(ds [\<mapsto>] (list_of (0::int) (length ds)));
  var_asmt''' = var_asmt''(as [\<mapsto>] (list_of (1::int) (length as)));
  
  clock_asmt' = clock_asmt(ActStart act := 0)
in (act_locs', var_asmt''', clock_asmt')
"

definition enter_start_instants::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"enter_start_instants ns s \<equiv>
  seq_apply (map enter_start_instant ns) s
"


(* It is valid to assume that variables have an assignment. Hidden assumption (at this level)

The initial variable assignment has a domain equal to the set of actually occurring variables and
in no step is a variable unassigned *)
definition leave_start_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"leave_start_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := Running act];
  locks = over_all act |> map PropLock;
  cur_asmt = map (the o var_asmt) locks;
  next_asmt = map (\<lambda>x. x + 1) cur_asmt;
  var_asmt' = var_asmt(locks [\<mapsto>] next_asmt)
in (act_locs', var_asmt', clock_asmt)
"

definition leave_start_instants::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval) list" where
"leave_start_instants ns s \<equiv>
  seq_apply (map leave_start_instant ns) s
"

text \<open>Applying the end happenings first\<close>
definition enter_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"enter_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := EndInstant act];

  locks = over_all act |> map PropLock;
  cur_asmt = map (the o var_asmt) locks;
  next_asmt = map (\<lambda>x. x - 1) cur_asmt;
  var_asmt' = var_asmt(locks [\<mapsto>] next_asmt);

  clock_asmt' = clock_asmt(ActEnd act := 0)
in (act_locs', var_asmt', clock_asmt')
"

definition "enter_end_instants ns s \<equiv> seq_apply (map enter_end_instant ns) s"


definition leave_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"leave_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := Off act];

  
  ds = dels (at_end act) |> map PropVar;
  as = adds (at_end act) |> map PropVar;
  var_asmt' = var_asmt(ActsActive \<mapsto> (the (var_asmt ActsActive) - 1));
  var_asmt'' = var_asmt'(ds [\<mapsto>] (list_of (0::int) (length ds)));
  var_asmt''' = var_asmt''(as [\<mapsto>] (list_of (1::int) (length as)))
in (act_locs', var_asmt''', clock_asmt)
"

definition "leave_end_instants ns s \<equiv> seq_apply (map leave_end_instant ns) s"

definition start_to_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"start_to_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := EndInstant act];

  clock_asmt' = clock_asmt(ActEnd act := 0)
in (act_locs', var_asmt, clock_asmt')
"

definition apply_snap_action::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"apply_snap_action n s \<equiv>
seq_apply [enter_start_instant n, start_to_end_instant n, leave_end_instant n] s
"

definition "apply_instant_actions ns s \<equiv> seq_apply'' (map apply_snap_action ns) s" 

(* apply all snap actions of the nth happening in the plan *)
definition apply_nth_happening::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"apply_nth_happening n s \<equiv>
let
  t = time_index \<pi> n;
  act_indices = [0..<length actions];
  start_indices = filter (is_starting_index t) act_indices;
  end_indices = filter (is_ending_index t) act_indices;
  both = filter (is_instant_index t) act_indices
in 
  s 
  |> enter_end_instants end_indices
  |> (\<lambda>s. ext_seq' s (enter_start_instants start_indices))
  |> (\<lambda>s. ext_seq' s (apply_instant_actions both))
  |> (\<lambda>s. ext_seq' s (leave_end_instants end_indices))
  |> (\<lambda>s. ext_seq' s (leave_start_instants start_indices))
"

definition delay::"
real
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval)" where
"delay t s \<equiv> map_prod id (map_prod id (\<lambda>clock_asmt. clock_asmt \<oplus> t)) s"


find_theorems name: "real*of"

definition get_delay::"nat \<Rightarrow> real" where
"get_delay i \<equiv>
  if (i = 0) 
  then \<epsilon> + 1
  else real_of_rat (htpl \<pi> ! i - htpl \<pi> ! (i - 1)) 
"


definition delay_and_apply::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"delay_and_apply i s \<equiv>
let
  d = get_delay i
in
  s 
  |> delay d
  |> apply_nth_happening i
"

definition start_planning::"
('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"start_planning s \<equiv>
let 
  (locs, var_asmt, clock_asmt) = s;
  main_auto_index = 0;

  locs' = locs[main_auto_index := Planning];
  
  init_props = map PropVar init;
  var_asmt' = var_asmt(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0);
  var_asmt'' = var_asmt'(init_props [\<mapsto>] (list_of (1::int) (length init)))
in (locs', var_asmt'', clock_asmt)"

definition end_planning::"
('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"end_planning s \<equiv>
let
  (locs, var_asmt, clock_asmt) = s;
  main_auto_index = 0;

  locs' = locs[main_auto_index := GoalLocation];
  
  init_props = map PropLock init;
  var_asmt' = var_asmt(PlanningLock \<mapsto> 2)
in (locs', var_asmt', clock_asmt)"


primcorec goal_run::"
  ('action location list \<times>
    ('proposition variable \<rightharpoonup> int) \<times>
    ('action clock, real) cval) 
\<Rightarrow> ('action location list \<times>
    ('proposition variable \<rightharpoonup> int) \<times>
    ('action clock, real) cval) stream" where
"goal_run s = s ## (goal_run s)"

(* Just for testing *)
definition "goal_state \<equiv> (GoalLocation # map Off actions, map_of (zip (map fst nta_vars) (map (fst o snd) nta_vars)), (\<lambda>x. 0))"

definition plan_steps::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) list" where
"plan_steps \<equiv>
let 
  htp_indices = [0..<length (htpl \<pi>)];
  apply_happs = map delay_and_apply htp_indices;
  seq = [abs_renum.a\<^sub>0] 
        |> (\<lambda>s. ext_seq s [start_planning]) 
        |> (\<lambda>s. ext_seq'' s apply_happs)
        |> (\<lambda>s. ext_seq s [end_planning])
in seq"

definition plan_state_sequence::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) stream" where
"plan_state_sequence \<equiv> plan_steps @- (goal_run (last plan_steps))"



subsection \<open>General properties of the problem\<close>
lemma action_variables: 
  assumes "a \<in> set actions"
  shows "action_vars_spec a \<subseteq> PropLock ` (set props) \<union> PropVar ` (set props)"
  unfolding action_vars_spec_def Let_def inv_vars_spec_def set_map set_append snap_vars_spec_def 
  using domain_ref_fluents[simplified fluent_domain_def, THEN bspec, OF assms] 
  unfolding act_ref_fluents_def by auto

lemma init_variables:
  "PropVar ` (set init) \<union> PropVar ` (set goal) \<subseteq> PropVar ` (set props)"
  using init_props goal_props by auto

lemma all_vars_spec_exact: "all_vars_spec = [(ActsActive, 0, (length actions)), (PlanningLock, 0, 2)] @ map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props) @
    map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" 
proof -
  have 1: "filter (\<lambda>x. fst x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props) = 
    map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props) @
    map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)"
    apply (subst filter_append)
    apply (subst filter_map)+
    apply (subst comp_def)+
    apply (subst fst_conv)+ by simp
  
  have 2: "map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)
      = map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props)" apply (induction props) by auto
  
  show "all_vars_spec = [(ActsActive, 0, (length actions)), (PlanningLock, 0, 2)] @ map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props) @
    map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" 
    unfolding all_vars_spec_def Let_def fold_union' apply (subst 1)
    apply (subst 2)
    by simp
qed



lemma all_vars_spec_exact_set: "set (map fst all_vars_spec) = {ActsActive, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)"
proof -
  have 1: "set (map fst (filter (\<lambda>x. fst x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props))) 
    = \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)"
    apply (subst filter_append)
    unfolding filter_map comp_def
    unfolding set_append fst_conv map_append
    unfolding map_map comp_def fst_conv
    apply (subst (3) comp_def[of _ PropLock, symmetric])
    apply (subst filter_map[symmetric])
    apply (subst (4) comp_def[of _ PropVar, symmetric])
    apply (subst filter_map[symmetric])
    using action_variables init_variables 
    by auto
  show ?thesis 
    unfolding all_vars_spec_def Let_def prod.case fold_union'
    unfolding map_append
    unfolding set_append
    apply (subst list.map)+
    apply (subst fst_conv)+
    apply (subst list.set)+
    apply (subst 1)
    unfolding set_map ..
qed

subsection \<open>General properties of the automaton\<close>

lemma conv_trans:
assumes "p < length (map (automaton_of o conv_automaton) actual_autos)"
shows "Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) ` (trans (automaton_of  (actual_autos ! p)))"
  apply (subst nth_map)
  using assms apply simp
  apply (subst comp_def)
  apply (cases "actual_autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "actual_autos ! p"])
     apply assumption
    unfolding conv_automaton_def prod.case
    unfolding automaton_of_def prod.case
    unfolding trans_def fst_conv snd_conv
    unfolding set_map by blast
  done

lemma conv_committed: 
  assumes "p < length (map (automaton_of o conv_automaton) actual_autos)"
  shows "committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = committed (map automaton_of actual_autos ! p)"
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "actual_autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "actual_autos ! p"])
     apply simp
    unfolding comp_apply
    unfolding conv_automaton_def automaton_of_def committed_def prod.case fst_conv ..
  done

lemma no_committed: 
  assumes "p < length actual_autos"
  shows "committed (map automaton_of actual_autos ! p) = {}"
  using assms
  unfolding actual_autos_alt automaton_of_def committed_def main_auto_spec_def Let_def action_to_automaton_spec_def
  apply (cases p)
  by simp+

lemma conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) actual_autos)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of actual_autos ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "actual_autos ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(actual_autos ! p)"])
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

lemma no_invs': assumes "p < length actual_autos"
  shows "inv (automaton_of (actual_autos ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case 
    by simp+
  show ?thesis
  unfolding actual_autos_def  ntas_def timed_automaton_net_spec_def Let_def prod.case
  apply (subst map_map[symmetric])
  apply (subst map_snd_zip)
   apply simp
  unfolding main_auto_spec_def Let_def action_to_automaton_spec_def
  unfolding comp_apply
  apply (subst list.map)
  apply (subst map_map)
  unfolding snd_conv comp_def inv_def
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

lemma no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) actual_autos)"
  shows "inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>x. [])"
  apply (subst conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using no_invs'
  apply (subst no_invs')
  using assms by auto

lemma cval_add_0: "z\<oplus>(0::real) = z" unfolding cval_add_def 
  by simp

lemma step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of nta_vars) y"
  shows "abs_renum.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding abs_renum.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using no_invs by simp
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by simp
  done

lemmas single_step_intro = abs_renum.urge_bisim.A.steps.Cons[OF _ abs_renum.urge_bisim.A.steps.Single]
lemmas non_t_step_intro = step_t_possible[THEN step_u'.intros, rotated, rotated]

subsection \<open>Proofs\<close>

definition exec_state_to_loc_list::"'action set \<Rightarrow> 'action location list" where
"exec_state_to_loc_list S \<equiv> 
let es_to_loc = (\<lambda>a. if a \<in> S then Running a else Off a)
in (Planning # map es_to_loc actions)"

definition prop_state_to_var_asmt::"'proposition set \<Rightarrow> ('proposition \<Rightarrow> nat) \<Rightarrow> 'proposition variable \<Rightarrow> int option" where
"prop_state_to_var_asmt P PI p \<equiv> case p of
  PropVar p \<Rightarrow> if (p \<in> P) then Some 1 else Some 0
| PropLock p \<Rightarrow> Some (PI p)"

fun act_clock_spec::"rat \<Rightarrow> 'action clock \<Rightarrow> real" where
"act_clock_spec t (ActStart a) = real_of_rat (planning_sem.last_snap_exec (at_start a) t)" |
"act_clock_spec t (ActEnd a) = real_of_rat (planning_sem.last_snap_exec (at_end a) t)"


lemma "abs_renum.urge_bisim.A.steps ((undefined, undefined, undefined) # (undefined, undefined, undefined) # undefined)"
  apply (rule abs_renum.urge_bisim.A.steps.intros)
   apply (subst prod.case)+
  apply (rule non_t_step_intro)
  sorry

lemma a\<^sub>0_alt: "abs_renum.a\<^sub>0 = (InitialLocation # map Off actions, map_of (map (\<lambda>x. (fst x, 0)) nta_vars), \<lambda>_. 0)"
  unfolding abs_renum.a\<^sub>0_def
  unfolding ntas_inits_alt
  unfolding init_vars_def
  ..

(* Todo?: Change the locale definition to make sure that the set of propositions occurring in actions
  is exactly the set of fluents *)

lemma map_of_zip_dom_to_range':
  "a \<in> set A \<Longrightarrow> length A = length B \<Longrightarrow> \<exists>x. map_of (zip A B) a = Some x \<and> x \<in> set B"
  apply (frule map_of_zip_fst)
   apply assumption
  apply (rule ssubst[of "map_of (zip A B) a"])
   apply assumption
  apply (subst (asm) index_less_size_conv[symmetric])
  by simp
(* 
lemma step_int_simp: "x = (l, b, g, Sil a, f, r, l') \<Longrightarrow>
  TRANS ''silent'' \<bar> (l, b, g, Sil a, f, r, l') \<in> Simple_Network_Language.trans (N ! p) \<Longrightarrow>
  ''committed'' \<bar> l \<in> committed (N ! p) \<or> (\<forall>p<length N. L ! p \<notin> committed (N ! p)) \<Longrightarrow>
  ''bexp'' \<bar> Simple_Expressions.check_bexp s b True \<Longrightarrow>
  ''guard'' \<bar> u \<turnstile> g \<Longrightarrow>
  ''target invariant'' \<bar> \<forall>p<length N. u' \<turnstile> Simple_Network_Language.inv (N ! p) (L' ! p) \<Longrightarrow>
  ''loc'' \<bar> L ! p = l \<Longrightarrow>
  ''range'' \<bar> p < length L \<Longrightarrow> ''new loc'' \<bar> L' = L[p := l'] \<Longrightarrow>
  ''new valuation'' \<bar> u' = [r\<rightarrow>0]u \<Longrightarrow> ''is_upd'' \<bar> is_upds s f s' \<Longrightarrow>
  ''bounded'' \<bar> Simple_Network_Language.bounded B s' \<Longrightarrow> 
  (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>" apply (rule step_int) *)


subsubsection \<open>Relating maps and bounds\<close>
lemma "x \<in> dom v \<Longrightarrow> \<exists>y. v x = Some y" by auto

lemma is_upds_set_vars_list_of: "is_upds v (map (set_var n) xs) (v(xs [\<mapsto>] (list_of n (length xs))))"
  apply (induction xs arbitrary: v)
  subgoal 
    apply (subst list_of_def)
    apply simp
    by (rule is_upds.intros)
  subgoal for x xs v
    apply (subst length_nth_simps)
    apply (subst list_of_Suc)
    apply (subst list.map)
    apply (subst map_upds_Cons)
    apply (rule is_upds.intros)
    unfolding is_upd_def
    apply (intro exI conjI)
      apply (rule HOL.refl)
      apply (rule check_bexp_is_val.intros)
     apply (rule HOL.refl)
    by simp
  done

lemma is_upds_inc_vars: 
  assumes "set xs \<subseteq> dom v"
      and "distinct xs"
  shows "is_upds v (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (v(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the o v) xs)))"
  using assms
proof (induction xs arbitrary: v)
  case Nil
  then show ?case 
    apply simp
    by (rule is_upds.intros)
next
  case (Cons x xs v)
  have 1: "is_upd v (x, binop plus_int (var x) (exp.const n)) (v(x \<mapsto> the (v x) + n))" (is "is_upd v ?upd ?v'")
    unfolding is_upd_def
     apply (intro exI conjI)
       apply (rule HOL.refl)
      apply (rule check_bexp_is_val.intros(14)[of _ _ "the (v x)"])
      apply (rule check_bexp_is_val.intros)
       using Cons(2) apply auto[1]
        apply (rule check_bexp_is_val.intros)
       by simp
   from Cons(3)
   have "\<forall>x' \<in> set xs. x \<noteq> x'" by auto
   hence 2: "map (the o v) xs = map (the o ?v') xs"
     unfolding comp_def using fun_upd_other by auto

   have "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the \<circ> ?v') xs)))"
     apply (rule Cons.IH)
     using Cons(2,3) by auto
   hence 3: "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the \<circ> v) xs)))"
     apply (subst 2) by simp
   show ?case 
    apply (subst list.map)+
    apply (subst map_upds_Cons)
     apply (rule is_upds.intros(2)[OF 1])
     using 3 unfolding comp_apply by simp
qed

lemma single_upd_bounded:
  assumes "bounded M v"
      and "M x = Some (l, u)"
      and "l \<le> y"
      and "y \<le> u"
    shows "bounded M (v(x \<mapsto> y))"
proof -
  from assms[simplified bounded_def]
  have dom_v_M: "dom v = dom M"
    and bounds: "\<forall>x \<in> dom v. fst (the (M x)) \<le> the (v x) \<and> the (v x) \<le> snd (the (M x))"
    by auto
  
  from assms(2) dom_v_M
  have dom': "dom (v (x \<mapsto> y)) = dom v" by auto

  have "fst (the (M a)) \<le> the ((v (x \<mapsto> y)) a) \<and> the ((v (x \<mapsto> y)) a) \<le> snd (the (M a))" if "a \<in> dom (v (x \<mapsto> y))" for a
  proof (cases "a = x")
    case True
    then show ?thesis using assms(2,3,4) by simp
  next
    case False
    hence 1: "the (v a) = the ((v (x \<mapsto> y)) a)" using that by simp
    
    have "a \<in> dom v" using dom' that by argo
    from bounds[THEN bspec, OF this]
    show ?thesis unfolding 1 by simp
  qed
  with dom' dom_v_M
  show ?thesis unfolding bounded_def by simp
qed

find_theorems name: "map_upds"

lemma upds_bounded:
  assumes "bounded M v"
      and "length xs = length ys"
      and "\<forall>n < length xs. \<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> (ys ! n) \<and> (ys ! n) \<le> u"   
    shows "bounded M (v(xs [\<mapsto>] ys))"
  using assms
proof (induction xs arbitrary: ys v)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y' ys' where
    ys': "ys = y'#ys'"
    "length (x # xs) = length (y' # ys')" apply (cases ys) by simp+
  obtain l u where
    "M x = Some (l, u)"
    "l \<le> y'"
    "y' \<le> u" using Cons(4)[simplified ys'(1)] by auto
  with Cons(2)
  have 1: "Simple_Network_Language.bounded M (v(x \<mapsto> y'))" by (auto intro: single_upd_bounded)
  have 2: "\<forall>n<length xs. \<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> ys' ! n \<and> ys' ! n \<le> u"
  proof (intro allI impI)
    fix n
    assume a: "n < length xs"
    hence 1: "Suc n < length (x # xs)" by simp
    have "xs ! n = (x # xs) ! Suc n" by simp
    moreover
    have "ys' ! n = (y' # ys') ! Suc n" using ys' by simp
    ultimately
    show "\<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> ys' ! n \<and> ys' ! n \<le> u" using Cons(4)[simplified ys'(1), THEN spec[of _ "Suc n"], THEN mp[OF _ 1]] by simp 
  qed
  with 1 ys'(2) Cons(4)
  have "Simple_Network_Language.bounded M ((v(x \<mapsto> y'))(xs [\<mapsto>] ys'))"
    apply -
    apply (rule Cons.IH)
      apply assumption
    by simp+
  thus ?case unfolding ys'(1) by simp
qed

lemma updated_bounded:
  assumes previous: "bounded M v"
      and l: "length xs = length ys"
      and v': "v' = v(xs [\<mapsto>] ys)"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u)"   
    shows "bounded M v'"
  unfolding bounded_def
proof (rule conjI)
  show 1: "dom v' = dom M"
    apply (intro equalityI subsetI)
    subgoal for x
      unfolding v'
      apply (subst (asm) dom_map_upds)
      apply (subst (asm) assms(2)[symmetric])
      apply (subst (asm) take_all, simp)
      apply (erule UnE)
      subgoal using bounds by blast
      subgoal using previous unfolding bounded_def by argo
      done
    subgoal for x
      unfolding v'
      apply (subst dom_map_upds)
      using previous unfolding bounded_def by blast
    done
  show "\<forall>x\<in>dom v'. fst (the (M x)) \<le> the (v' x) \<and> the (v' x) \<le> snd (the (M x))"
    apply (rule ballI)
    subgoal for x
      apply (subst (asm) v')
      apply (subst (asm) dom_map_upds)
      apply (subst (asm) assms(2)[symmetric])
      apply (subst (asm) take_all, simp)
      apply (erule UnE)
      subgoal using bounds by auto
      apply (cases "x \<in> set xs")
      subgoal using bounds by auto
      unfolding v'
      apply (subst map_upds_apply_nontin)
      apply simp
      apply (subst map_upds_apply_nontin)
       apply simp
      using previous unfolding bounded_def by simp
    done
qed

lemma zip_list_of: 
  assumes "x \<in> set xs"
  shows "(x, n) \<in> set (zip xs (list_of n (length xs)))"
  using assms 
  apply (induction xs arbitrary: n x)
   apply simp
  subgoal for a as n x
    apply (subst length_Cons)
    apply (subst list_of_Suc)
    apply (subst zip_Cons_Cons)
    by auto
  done

lemma all_zip_list_of:
  assumes "x \<in> set xs"
  shows "\<forall>m. (x, m) \<in> set (zip xs (list_of n (length xs))) \<longrightarrow> m = n"
  using assms
proof (induction xs arbitrary: n x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have IH: "\<forall>m. (x, m) \<in> set (zip as (list_of n (length as))) \<longrightarrow> m = n"
    using Cons apply (cases "x \<in> set as")
     apply simp using set_zip_leftD by metis
  show ?case 
    apply (subst length_Cons)
    apply (subst list_of_Suc)
    apply (subst zip_Cons_Cons)
    apply (rule allI)
    subgoal for m
      apply (cases "m = n")
       apply simp
      apply (subst list.set)
      using IH by auto
    done
qed

lemma map_of_determ:
  assumes "\<forall>m. (x, m) \<in> set xs \<longrightarrow> m = n"
          and "(x, n) \<in> set xs"
        shows "map_of xs x = Some n"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain c d where
    a: "a = (c, d)" by fastforce
  then show ?case 
  proof (cases "a = (x,n)")
    case True
    then show ?thesis by simp
  next
    case False
    then 
    consider "x \<noteq> c" | "x = c \<and> n \<noteq> d" using a by blast
    then show ?thesis 
    proof cases
      case 1
      hence "map_of (a # xs) x = map_of xs x" using a map_of_Cons_code by auto
      moreover
      have i: "(x, n) \<in> set xs" using Cons (3) a 1 by auto
      moreover
      from Cons(2) i 1 False a
      have "\<forall>m. (x, m) \<in> set xs \<longrightarrow> m = n" by force
      ultimately
      show ?thesis using Cons.IH by metis
    next
      case 2
      then show ?thesis using a Cons by simp
    qed
  qed
qed

lemma map_upds_with_list_of:
  assumes "x \<in> set xs"
  shows "(v(xs [\<mapsto>] (list_of n (length xs)))) x = Some n"
  using assms 
  unfolding map_upds_def 
  apply (subst map_add_find_right)
   apply (rule map_of_determ)
  apply (subst set_rev)
    using all_zip_list_of
    apply fast
     apply (subst set_rev)
     apply (erule zip_list_of)
    by simp

lemma set_vars_bounded:
  assumes previous: "bounded M v"
      and v': "v' = v(xs [\<mapsto>] (list_of n (length xs)))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded[OF assms(1) length_list_of[symmetric] assms(2)])
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_list_of[OF a]) 
      by simp
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed

lemma distinct_map_upds:
  assumes "x \<in> set xs"
      and "distinct xs"
    shows "(v(xs [\<mapsto>] (map f xs))) x = Some (f x)"
  using assms 
  unfolding map_upds_def
  apply (subst map_add_find_right)
   apply (subst zip_rev[symmetric])
    apply simp
   apply (rule map_of_is_SomeI[where y = "f x"])
    apply simp
   apply (subst zip_rev)
    apply simp
   apply (subst set_rev)
   apply (subst in_set_zip)
   apply (subst (asm) in_set_conv_nth)
  by auto

  
text \<open>The bounds of nta_vars\<close>

lemma init_vars_alt: "init_vars = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" unfolding init_vars_def by auto

lemma init_vars_bounded: "bounded (map_of nta_vars) (map_of init_vars)"
  unfolding bounded_def
proof (intro conjI ballI)
  show 1: "dom (map_of init_vars) = dom (map_of nta_vars)" unfolding init_vars_alt apply (subst dom_map_of_map) apply (subst dom_map_of_conv_image_fst) by blast
  { fix x
    assume "x \<in> dom (map_of init_vars)" 
    then obtain y where
      y: "map_of nta_vars x = Some y" using 1 by auto
    hence "fst y = 0" unfolding nta_vars' unfolding all_vars_spec_def Let_def
      apply -
      apply (drule map_of_SomeD)
      by auto
    thus "fst (the (map_of nta_vars x)) \<le> the (map_of init_vars x)" unfolding init_vars_alt map_of_map comp_apply
      using y by simp
      
  }
  { fix x
    assume "x \<in> dom (map_of init_vars)"then obtain y where
      y: "map_of nta_vars x = Some y" using 1 by auto
    hence "snd y \<ge> 0" unfolding nta_vars' unfolding all_vars_spec_def Let_def
      apply -
      apply (drule map_of_SomeD)
      unfolding set_append
      apply (induction y)
      by auto
    thus "the (map_of init_vars x) \<le> snd (the (map_of nta_vars x))" unfolding init_vars_alt map_of_map comp_apply
      using y by simp
  }
qed

schematic_goal nta_vars_exact: "nta_vars = ?x"
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact)
  ..

schematic_goal map_of_nta_vars_exact: "map_of nta_vars = ?x"
  apply (subst nta_vars_exact)
  apply (subst map_of_map)
  unfolding comp_def map_of_append
  ..

schematic_goal dom_map_of_nta_vars: "dom (map_of nta_vars) = ?d"
  apply (subst dom_map_of_conv_image_fst)
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact_set[simplified set_map])
  ..

lemma map_of_nta_vars_ActsActive: 
  "map_of nta_vars ActsActive = Some (0, length actions)" using nta_vars_exact by simp

lemma map_of_nta_vars_PlanningLock:
  "map_of nta_vars PlanningLock = Some (0, 2)" using nta_vars_exact by simp

lemma map_prop_var_simp: "map (\<lambda>p. (PropVar p, 0, 1)) xs = map (\<lambda>(v, b). (v, id b)) (map (\<lambda>v. (v, 0, 1)) (map PropVar xs))"
  by simp

lemma map_of_nta_vars_init_goal:
  assumes "v \<in> set (map PropVar init) \<union> set (map PropVar goal)"
  shows "map_of nta_vars v = Some (0, 1)"
proof-
  from assms init_props goal_props
  obtain p where
    p: "p \<in> set init \<union> set goal"
    "p \<in> set props"
    "v = PropVar p" by auto

  hence 1: "p \<in> set (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" by auto
  have distinct: "distinct (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" using distinct_props by simp
  have 2:"(map_of (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)) p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    using distinct
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply simp
    using 1 by simp
  have 3: "map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props) = 
    map (\<lambda>(p, v). (PropVar p, v)) (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))"
    by simp
  have 4: "map_of (map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)) (PropVar p) 
    = (map_of (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)) p)" 
    apply (subst 3)
    apply (subst map_of_map_inj_fst)
     apply (subst inj_def)
    by simp+

  show ?thesis
    apply (subst map_of_nta_vars_exact)
    apply (subst p)
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (subst set_map)
     apply (subst image_image)
     apply (subst fst_conv)
     apply (rule notI)
     apply (rule imageE)
      apply simp
     apply simp
      apply (subst 4)
      apply (subst 2)
      by simp
qed


lemma map_of_nta_vars_action_inv:
  assumes "a \<in> set actions"
    "v \<in> set (map PropLock (over_all a))"
  shows "map_of nta_vars v = Some (0, length actions)"
proof -
  from assms local.planning_sem.finite_props_domain
  obtain p where
    p: "p \<in> set (over_all a)"
    "p \<in> set props"
    "v = PropLock p" unfolding fluent_domain_def act_ref_fluents_def by auto
  hence 1: "p \<in> set (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props)" 
    unfolding action_vars_spec_def Let_def inv_vars_spec_def set_map using assms
    by auto

  have 2: "map_of (map (\<lambda>p. (PropLock p, y)) (filter (\<lambda>x. PropLock x \<in> S) props)) (PropLock p) 
    = (map_of (map (\<lambda>p. (p, y)) (filter (\<lambda>x. PropLock x \<in> S) props)) p)" for S y 
    apply (subst (2) map_of_map_inj_fst[symmetric, where f = PropLock])
    unfolding inj_def apply simp
    apply (subst map_map)
    apply (subst comp_def)
    unfolding prod.case
    by blast


  show ?thesis
    apply (subst map_of_nta_vars_exact)
    apply (subst p)
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_right)
     apply (subst 2)
     apply (rule map_of_is_SomeI)
    using distinct_props unfolding map_map comp_apply apply simp
    using 1 apply fastforce
    by simp
qed

lemma map_of_nta_vars_action_start_del:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map PropVar (dels (at_start a)))"
    shows "map_of nta_vars v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (dels (at_start a))"
    "v = PropVar p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))) v = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    subgoal apply (subst map_map)
      apply (subst comp_def)
      apply (subst fst_conv)
      apply (subst distinct_map)
      apply (rule conjI)
       apply (rule distinct_filter)
       apply (rule distinct_props)
      apply(subst inj_on_def) by blast
    apply (subst set_map)
    apply (subst p)
    apply (intro imageI)
    apply (subst set_filter)
    apply (intro CollectI)
    apply (rule conjI)
     apply (rule p_in_props)
    apply (intro UnI1)
    apply (rule UnionI[of "action_vars_spec a"])
    using a_in_actions apply simp
    unfolding action_vars_spec_def Let_def
    apply (rule UnI2)
    apply (rule UnI1)
    unfolding snap_vars_spec_def Let_def set_append set_map
    apply (intro UnI2)
    using p by blast
  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (subst set_map)
     apply (subst image_image)
     apply (subst fst_conv)
     apply blast
    apply (subst 1[simplified p])
    by simp
qed

lemma map_of_nta_vars_action_start_add:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map PropVar (adds (at_start a)))"
    shows "map_of nta_vars v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (adds (at_start a))"
    "v = PropVar p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))) v = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    subgoal apply (subst map_map)
      apply (subst comp_def)
      apply (subst fst_conv)
      apply (subst distinct_map)
      apply (rule conjI)
       apply (rule distinct_filter)
       apply (rule distinct_props)
      apply(subst inj_on_def) by blast
    apply (subst set_map)
    apply (subst p)
    apply (intro imageI)
    apply (subst set_filter)
    apply (intro CollectI)
    apply (rule conjI)
     apply (rule p_in_props)
    apply (intro UnI1)
    apply (rule UnionI[of "action_vars_spec a"])
    using a_in_actions apply simp
    unfolding action_vars_spec_def Let_def snap_vars_spec_def Let_def set_append set_map
    using p by blast
  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (subst set_map)
     apply (subst image_image)
     apply (subst fst_conv)
     apply blast
    apply (subst 1[simplified p])
    by simp
qed

lemma map_of_nta_vars_action_start_del_lock:
  assumes "a \<in> set actions"
      and "v \<in> set (map PropLock (dels (at_start a)))"
    shows "map_of nta_vars v = Some (0, length actions)"
  sorry

lemma map_of_nta_vars_action_end_del:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map PropVar (dels (at_end a)))"
    shows "map_of nta_vars v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (dels (at_end a))"
    "v = PropVar p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))) v = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    subgoal apply (subst map_map)
      apply (subst comp_def)
      apply (subst fst_conv)
      apply (subst distinct_map)
      apply (rule conjI)
       apply (rule distinct_filter)
       apply (rule distinct_props)
      apply(subst inj_on_def) by blast
    apply (subst set_map)
    apply (subst p)
    apply (intro imageI)
    apply (subst set_filter)
    apply (intro CollectI)
    apply (rule conjI)
     apply (rule p_in_props)
    apply (intro UnI1)
    apply (rule UnionI[of "action_vars_spec a"])
    using a_in_actions apply simp
    unfolding action_vars_spec_def Let_def
    apply (rule UnI2)
    apply (rule UnI2)
    unfolding snap_vars_spec_def Let_def set_append set_map
    apply (intro UnI2)
    using p by blast
  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (subst set_map)
     apply (subst image_image)
     apply (subst fst_conv)
     apply blast
    apply (subst 1[simplified p])
    by simp
qed

lemma map_of_nta_vars_action_end_add:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map PropVar (adds (at_end a)))"
    shows "map_of nta_vars v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (adds (at_end a))"
    "v = PropVar p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))) v = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    subgoal apply (subst map_map)
      apply (subst comp_def)
      apply (subst fst_conv)
      apply (subst distinct_map)
      apply (rule conjI)
       apply (rule distinct_filter)
       apply (rule distinct_props)
      apply(subst inj_on_def) by blast
    apply (subst set_map)
    apply (subst p)
    apply (intro imageI)
    apply (subst set_filter)
    apply (intro CollectI)
    apply (rule conjI)
     apply (rule p_in_props)
    apply (intro UnI1)
    apply (rule UnionI[of "action_vars_spec a"])
    using a_in_actions apply simp
    unfolding action_vars_spec_def Let_def snap_vars_spec_def Let_def set_append set_map
    using p by blast
  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (subst set_map)
     apply (subst image_image)
     apply (subst fst_conv)
     apply blast
    apply (subst 1[simplified p])
    by simp
qed

lemma map_of_nta_vars_action_end_del_lock:
  assumes "a \<in> set actions"
      and "v \<in> set (map PropLock (dels (at_end a)))"
    shows "map_of nta_vars v = Some (0, length actions)"
  sorry

subsubsection \<open>The initial transition\<close>

lemma planning_start_state_char: 
  assumes "start_planning abs_renum.a\<^sub>0 = (l1, v1, c1)"
  shows "l1 = Planning # map Off actions 
    \<and> v1 PlanningLock = Some 1 
    \<and> v1 ActsActive = Some 0 
    \<and> (\<forall>p \<in> set init. v1 (PropVar p) = Some 1)
    \<and> (\<forall>v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0) 
    \<and> (\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None) 
    \<and> c1 = (\<lambda>_. 0)"
proof (intro conjI)
  have "l1 = Planning # map Off actions"
       "c1 = (\<lambda>_. 0)"
       and v1: "v1 = (map_of (map (\<lambda>x. (fst x, 0)) nta_vars))(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] list_of 1 (length init))"
    using assms unfolding a\<^sub>0_alt start_planning_def Let_def prod.case by simp+
  thus "l1 = Planning # map Off actions" "c1 = (\<lambda>_. 0)" by simp+
  show "v1 PlanningLock = Some 1" unfolding v1
    apply (subst Map.map_upds_apply_nontin) by auto
  show "v1 ActsActive = Some 0" unfolding v1
    apply (subst Map.map_upds_apply_nontin) by auto
  show "\<forall>p\<in>set init. v1 (PropVar p) = Some 1"
  proof (rule ballI)
    fix p
    assume a: "p \<in> set init"
    hence l: "0 < length init" by auto
    hence s: "set (list_of 1 (length init)) = {1}"
      apply (rule set_list_of) .
      
    have "map_of (zip (rev (map PropVar init)) (rev (list_of 1 (length init)))) (PropVar p) = Some 1" 
      using map_of_zip_dom_to_range'[of "PropVar p" "(rev (map PropVar init))", simplified, of "rev (list_of 1 (length init))", simplified length_list_of length_rev set_rev s]
      a by auto
    hence "map_of (rev (zip (map PropVar init) (list_of 1 (length init)))) (PropVar p) = Some 1" 
      apply -
      apply (subst zip_rev[symmetric])
       apply (subst length_list_of)
      by simp+
    thus "v1 (PropVar p) = Some 1" unfolding v1
      apply (subst map_upds_def)
      apply (subst map_add_Some_iff)
      by auto
  qed
  show "\<forall>v\<in>actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0" 
  proof (rule ballI)
    fix v
    assume a: "v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init)"
    hence b: "v \<in> actual_variables" by simp
    have "map_of (rev (zip (map PropVar init) (list_of 1 (length init)))) v = None"
      apply (subst zip_rev[symmetric])
      unfolding length_list_of
       apply simp
      apply (subst map_of_zip_is_None)
      unfolding length_list_of length_rev
       apply simp
      using a by simp
    moreover
    have 1: "(map (\<lambda>x. (fst x, 0)) nta_vars) = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" by auto
    have "((map_of (map (\<lambda>x. (fst x, 0)) nta_vars))(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0)) v = Some 0"
      apply (subst fun_upd_other)
      using a apply simp
      apply (subst fun_upd_other)
      using a apply simp
      using b unfolding actual_variables_correct
      apply (subst 1)
      apply (subst map_of_map)
      apply (subst comp_apply)
      apply (subst (asm) set_map)
      apply (erule imageE)
      subgoal for x
        apply (cases x)
        subgoal for y z
          using weak_map_of_SomeI by fastforce
        done
      done
    ultimately
    show "v1 v = Some 0" 
      unfolding v1
      apply (subst map_upds_def)
      apply (subst map_add_Some_iff)
      apply (rule disjI2)
      by simp
  qed
  show "\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None"
  proof (intro allI impI)
    fix v
    assume "v \<notin> actual_variables"
    with actual_variables_correct
    have 1: "v \<notin> set (map fst nta_vars)" by argo
    with all_vars_spec_exact_set nta_vars'
    have 2: "v \<notin> {ActsActive, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)" by simp
    
    have 3: "(map (\<lambda>x. (fst x, 0)) nta_vars) = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" by auto
    show "v1 v = None"
      unfolding v1
      apply (subst map_upds_apply_nontin)
      using 2 apply simp
      apply (subst fun_upd_other)
      using 2 apply simp
      apply (subst fun_upd_other)
      using 2 apply simp
      apply (subst 3)
      apply (subst map_of_map)
      apply (subst comp_def)
      using 1 
      unfolding set_map map_of_eq_None_iff[symmetric]
      by simp
  qed
qed

lemma main_auto_init_edge_spec_simp: "main_auto_init_edge_spec = (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning)"
  unfolding main_auto_init_edge_spec_def Let_def ..

lemma initial_steps_are_steps: "abs_renum.urge_bisim.A.steps ([abs_renum.a\<^sub>0] |> (\<lambda>s. ext_seq s [start_planning]))"
proof -
  have "abs_renum.urge_bisim.A.steps [abs_renum.a\<^sub>0, start_planning abs_renum.a\<^sub>0]" 
  proof (rule abs_renum.urge_bisim.A.steps.intros)
    show "(case abs_renum.a\<^sub>0 of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (start_planning abs_renum.a\<^sub>0)"
    proof -
      obtain l1 v1 c1 where
        sp: "start_planning abs_renum.a\<^sub>0 = (l1, v1, c1)"
        and l1: "l1 = Planning # map Off actions"
        and "v1 PlanningLock = Some 1"
        and v1: "v1 ActsActive = Some 0"
        "\<forall>p \<in> set init. v1 (PropVar p) = Some 1"
        "\<forall>v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0" 
        "\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None"
        and c1: "c1 = (\<lambda>_. 0)" using planning_start_state_char apply (cases "start_planning abs_renum.a\<^sub>0") by blast
      (* To do: clean up? *)

      obtain l v and c::"'action clock \<Rightarrow> real" where
        arc: "(l, v, c) = abs_renum.a\<^sub>0" apply (cases "abs_renum.a\<^sub>0::('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))") by simp
      hence l: "l = ntas_inits" 
        and v: "v = map_of init_vars"
        and c: "c = (\<lambda>_. 0)" unfolding abs_renum.a\<^sub>0_def by simp+
      from sp
      have v1': "v1 = v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] list_of 1 (length init))" unfolding start_planning_def Let_def arc[symmetric] prod.case by simp

      have "abs_renum.sem \<turnstile> \<langle>l, v, c\<rangle> \<rightarrow> \<langle>l1, v1, c1\<rangle>"
      proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
        show "abs_renum.sem \<turnstile> \<langle>l, v, c\<rangle> \<rightarrow>\<^bsub>Internal (STR '''')\<^esub> \<langle>l1, v1, c1\<rangle>"
          unfolding abs_renum.sem_def
        proof (rule step_u.step_int)
          show "TRANS ''silent'' \<bar> (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning) \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! 0)" 
            apply (subst TAG_def)
            apply (subst nth_map)
             apply (subst actual_autos_def)
             apply (subst ntas_def)
            apply (subst timed_automaton_net_spec_def)
            unfolding Let_def prod.case
             apply simp
             apply (subst actual_autos_def)
             apply (subst ntas_def)
            apply (subst timed_automaton_net_spec_def)
            unfolding Let_def prod.case
            apply (subst nth_map)
             apply simp
            apply (subst upt_conv_Cons)
             apply simp
            apply (subst nth_zip)
              apply simp
             apply simp
            apply (subst nth_Cons_0)+
            unfolding main_auto_spec_def Let_def prod.case comp_apply snd_conv
            unfolding conv_automaton_def prod.case
            unfolding automaton_of_def prod.case
            unfolding Simple_Network_Language.trans_def fst_conv snd_conv
            unfolding set_map
            apply (subst list.set)
            apply (subst image_insert)
            apply (subst main_auto_init_edge_spec_def)
            unfolding Let_def prod.case
            by simp
            
          show "''committed'' \<bar> InitialLocation \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! 0) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). l ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
            apply (subst TAG_def)
            apply (subst conv_committed)
            using some_actual_autos apply simp
            apply (rule disjI2)
            apply (intro allI impI)
            subgoal for p
            apply (subst conv_committed)
            using some_actual_autos apply simp
            apply (subst nth_map)
            using some_actual_autos apply simp
            apply (subst (asm) length_map)
            apply (frule no_committed)
            apply (subst (asm) nth_map)
            by simp+
          done
          show "''bexp'' \<bar> Simple_Expressions.check_bexp v (Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0)) True"
          proof -
            have "is_val v (var PlanningLock) 0"
              unfolding v init_vars_def 
              apply (rule check_bexp_is_val.intros)
              apply (subst nta_vars')
              unfolding all_vars_spec_def Let_def 
              by simp
            moreover
            have "is_val v (exp.const 0) 0"
              by (rule check_bexp_is_val.intros)
            ultimately
            show ?thesis 
              apply -
              apply (drule check_bexp_is_val.intros)
               apply assumption
              apply (subst TAG_def)
              by simp
          qed
          show "''guard'' \<bar> c \<turnstile> []" apply (subst TAG_def) by simp
          show "''target invariant'' \<bar> \<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c1 \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (l1 ! p)"
            apply (subst TAG_def)
            apply (intro allI impI)
            apply (subst no_invs)
            by simp+
          show "''loc'' \<bar> l ! 0 = InitialLocation"
            apply (subst TAG_def)
            apply (subst l)
            apply (subst ntas_inits_alt)
            by simp
          show "''range'' \<bar> 0 < length l"
            by (simp add: TAG_def l ntas_inits_alt)
          show "''new loc'' \<bar> l1 = l[0 := Planning]"
            apply (subst TAG_def)
            apply (subst l)
            apply (subst ntas_inits_alt)
            apply (subst l1)
            by simp
          show "''new valuation'' \<bar> c1 = [[]\<rightarrow>0]c"
            apply (subst TAG_def)
            unfolding c c1 by simp
          show "''is_upd'' \<bar> is_upds v ((PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init) v1"
          proof -
            have 1: "map (set_prop_ab 1) xs = map (set_var 1) (map PropVar xs)" for xs unfolding set_prop_ab_def by simp
            show ?thesis
            apply (subst TAG_def)
            apply (rule is_upds.intros)
             apply (subst is_upd_def)
             apply (intro exI conjI)
               apply (rule HOL.refl)
              apply (rule check_bexp_is_val.intros)
             apply (rule HOL.refl)
            apply (rule is_upds.intros)
            apply (subst is_upd_def)
             apply (intro exI conjI)
               apply (rule HOL.refl)
              apply (rule check_bexp_is_val.intros)
               apply (rule HOL.refl)
              unfolding v1'
              apply (subst 1)
              using is_upds_set_vars_list_of[where v = "v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0)" and n = 1 and xs = "(map PropVar init)"] 
              by simp
          qed
          show "''bounded'' \<bar> Simple_Network_Language.bounded (map_of nta_vars) v1"
          proof (subst TAG_def)
            have "bounded (map_of nta_vars) (v(PlanningLock # ActsActive # map PropVar init [\<mapsto>] (1 # 0 # list_of 1 (length init))))"
            proof (rule upds_bounded)
              show "bounded (map_of nta_vars) v"
                using arc unfolding abs_renum.a\<^sub>0_def
                using init_vars_bounded by simp
              show "length (PlanningLock # ActsActive # map PropVar init) = length (1 # 0 # list_of 1 (length init))" 
                apply (subst length_Cons)+
                apply (subst length_list_of)
                by auto
              show "\<forall>n<length (PlanningLock # ActsActive # map PropVar init). \<exists>l u. map_of nta_vars ((PlanningLock # ActsActive # map PropVar init) ! n) = Some (l, u) \<and> l \<le> (1 # 0 # list_of 1 (length init)) ! n \<and> (1 # 0 # list_of 1 (length init)) ! n \<le> u"
              proof (intro allI impI)
                fix n
                assume a: "n < length (PlanningLock # ActsActive # map PropVar init)"
                show "\<exists>l u. map_of nta_vars ((PlanningLock # ActsActive # map PropVar init) ! n) = Some (l, u) \<and> l \<le> (1 # 0 # list_of 1 (length init)) ! n \<and> (1 # 0 # list_of 1 (length init)) ! n \<le> u"
                proof (cases n)
                  case 0
                  then show ?thesis
                  using map_of_nta_vars_PlanningLock by simp
                next
                  case n': (Suc n')
                  then show ?thesis 
                  proof (cases n')
                    case 0
                    then show ?thesis 
                    using map_of_nta_vars_ActsActive n' by simp
                  next
                    case n'': (Suc n'')
                    have "n'' < length init" using a n' n'' by simp
                    hence "\<exists>l u. map_of nta_vars (map PropVar init ! n'') = Some (l, u) \<and> l \<le> (list_of 1 (length init)) ! n'' \<and> (list_of 1 (length init)) ! n'' \<le> u" 
                      apply (subst nth_list_of, assumption)+
                      using map_of_nta_vars_init_goal by simp
                    then show "\<exists>l u. map_of nta_vars ((PlanningLock # ActsActive # map PropVar init) ! n) = Some (l, u) \<and> l \<le> (1 # 0 # list_of 1 (length init)) ! n \<and> (1 # 0 # list_of 1 (length init)) ! n \<le> u" 
                      unfolding n'' n' by simp
                  qed
                qed
              qed
            qed
            thus "bounded (map_of nta_vars) v1"
              unfolding v1' by simp
          qed
        qed
        show "Simple_Network_Language.bounded (map_of nta_vars) v"
          using arc unfolding abs_renum.a\<^sub>0_def
          using init_vars_bounded by simp
      qed
      thus ?thesis using arc[symmetric] sp by simp
    qed
    show "abs_renum.urge_bisim.A.steps [start_planning abs_renum.a\<^sub>0]" by (rule abs_renum.urge_bisim.A.steps.intros)
  qed
  thus ?thesis by simp
qed

subsubsection \<open>Rules for constructing a run\<close>

lemma steps_prepend: "abs_renum.urge_bisim.A.steps (y#ys) \<Longrightarrow> abs_renum.urge_bisim.A.steps [x, y] \<Longrightarrow> abs_renum.urge_bisim.A.steps (x#y#ys)"
  using abs_renum.urge_bisim.A.steps_append'[where as = "[x, y]" and bs = "y#ys"]
  by auto

lemma steps_extend: "abs_renum.urge_bisim.A.steps xs \<Longrightarrow> abs_renum.urge_bisim.A.steps (last xs # seq_apply fs (last xs)) \<Longrightarrow> abs_renum.urge_bisim.A.steps (ext_seq xs fs)"
  apply (frule abs_renum.urge_bisim.A.steps_append'[where bs = "last xs # seq_apply fs (last xs)"])
     apply simp
    apply simp
   apply (subst List.tl_def)
   apply simp
  apply (subst (asm) ext_seq_alt[symmetric])
   apply (erule abs_renum.urge_bisim.A.steps.cases)
  subgoal for x by blast
  subgoal for x xs by auto
  by simp


lemma length_seq_apply[simp]: "length (seq_apply fs s) = length fs"
  apply (induction fs arbitrary: s)
  by auto

lemma steps_extend_induct:
  assumes "\<forall>i. Suc i < length xs \<longrightarrow> abs_renum.urge_bisim.A.steps [xs!i, xs!Suc i]"
      and "0 < length xs"
  shows "abs_renum.urge_bisim.A.steps xs"
proof -
  have "abs_renum.urge_bisim.A.steps (take n xs @ [xs ! n])" if "n < length xs" "0 < length xs" for n
    using that
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    have 1: "abs_renum.urge_bisim.A.steps (take n xs @ [xs ! n])" using Suc by simp
    have 2: "abs_renum.urge_bisim.A.steps ([xs ! n, xs ! Suc n])" using assms Suc by simp
    
    have "abs_renum.urge_bisim.A.steps (take n xs @ [xs ! n] @ [xs ! Suc n])" using abs_renum.urge_bisim.A.steps_append[OF 1 2] by force
    thus ?case 
        apply (subst take_Suc_conv_app_nth)
      using Suc by auto
  qed
  from this[of "length xs - 1", OF _ assms(2)]
  show ?thesis using take_Suc_conv_app_nth[of "length xs - 1" xs] take_all[of xs "length xs"] assms(2) by auto
qed

lemma seq_apply_steps_induct:
  assumes "\<forall>i. Suc i < length (s#seq_apply fs s) \<longrightarrow> abs_renum.urge_bisim.A.steps [(s#seq_apply fs s) ! i, (s#seq_apply fs s) ! Suc i]"
  shows "abs_renum.urge_bisim.A.steps (s # seq_apply fs s)" using assms steps_extend_induct by blast



schematic_goal nth_auto_trans:
  assumes "n < length actions"
  shows "trans (automaton_of (actual_autos ! Suc n)) = ?x"
  apply (subst actual_autos_alt)
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_Cons_Suc)
  apply (subst nth_map)
  apply (rule assms)
  unfolding action_to_automaton_spec_def Let_def comp_def snd_conv trans_def automaton_of_def prod.case fst_conv list.set ..
  

schematic_goal nth_auto_trans':
  assumes "n < length actions"
  shows "trans (automaton_of ((snd \<circ> snd) (action_to_automaton_spec (actions ! n)))) = ?x"
  unfolding action_to_automaton_spec_def Let_def comp_def snd_conv trans_def automaton_of_def prod.case fst_conv list.set ..

(* Indices of locations and automata are offset by 1 w.r.t. actions' indices *)

subsubsection \<open>Mutex constraints\<close>

text \<open>This only works for the direction from plan to run.\<close>

schematic_goal int_clocks_spec_alt:
  shows "set (int_clocks_spec h) = ?x"
  unfolding int_clocks_spec_def Let_def filter_append set_append set_map set_filter ..

lemma mutex_0_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> h = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> h = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap h b \<Longrightarrow> 0 < planning_sem.exec_time b t" for b by blast

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_start act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_start act) t" by simp
    moreover
    have "(t, at_start act) \<notin> planning_sem.happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (ActStart act)" using s_corr a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (ActStart act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map ActStart (filter (\<lambda>a. mutex_effects_spec h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_end act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_end act) t" by simp
    moreover
    have "(t, at_end act) \<notin> planning_sem.happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (ActEnd act)" using e_corr a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (ActEnd act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map ActEnd (filter (\<lambda>a. mutex_effects_spec h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  ultimately
  show ?thesis 
    unfolding int_clocks_spec_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed

lemma mutex_eps_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> h = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> h = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap h b \<Longrightarrow> rat_of_int \<epsilon> \<le> planning_sem.exec_time b t" for b 
    unfolding Rat.of_int_def by simp

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_start act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_start act) t" by simp
    have c: "(t, at_start act) \<notin> planning_sem.happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (ActStart act)"
      apply (subst s_corr[THEN bspec, OF a(1), THEN mp, OF c])
      using x of_rat_less_eq by blast
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (ActStart act) \<epsilon>)"
      apply simp
      by (erule clock_val_a.intros)
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map ActStart (filter (\<lambda>a. mutex_effects_spec h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_end act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_end act) t" by simp
    have c: "(t, at_end act) \<notin> planning_sem.happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (ActEnd act)"
      apply (subst e_corr[THEN bspec, OF a(1), THEN mp, OF c])
      using x of_rat_less_eq by blast
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (ActEnd act) \<epsilon>)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map ActEnd (filter (\<lambda>a. mutex_effects_spec h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  ultimately
  show ?thesis 
    unfolding int_clocks_spec_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed 

subsection \<open>Ending snap actions\<close>
context (* To do: simplify time conditions. *)
  fixes n t L v c L' v' c'
 assumes n: "n < length actions"
      and end_scheduled: "(t, at_end (actions ! n)) \<in> planning_sem.happ_seq"
      and start_not_scheduled: "(t, at_start (actions ! n)) \<notin> planning_sem.happ_seq"

      and L_len: "length L = Suc (length actions)"
      and v_bounded: "bounded (map_of nta_vars) v"
      and planning_state: "v PlanningLock = Some 1"


      and ending_executed_loc: "\<forall>i < n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
              \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (EndInstant (actions ! i))"
      and ending_not_executed_loc: "\<forall>i < length actions. n \<le> i 
              \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
              \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (Running (actions ! i))"

      and locked_before: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))"

      and ending_executed_clock: 
          "\<forall>i < n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
            \<longrightarrow> c (ActEnd (actions ! i)) = (0::real)"
      and ending_not_executed_clock: 
          "\<forall>i < length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq
            \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"

      and start_snap_time: "\<forall>i < length actions. c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"

      and s': "enter_end_instant n (L, v, c) = (L', v', c')"
begin

text \<open>Properties of current state\<close>
lemma partially_updated_locked_before_lower: 
  assumes "p \<in> set (over_all (actions ! n))"
  shows "0 < partially_updated_locked_before t p n" 
proof -
  have "0 < (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)"
  proof -
    { assume "0 = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)"
      hence "\<forall>n \<in> set (map 
        (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)) 
        (filter 
          (\<lambda>a. p \<in> set (over_all a)) 
          (map (\<lambda>n. actions ! n) [n..<length actions]))). n = 0"  apply (subst sum_list_eq_0_iff[symmetric])
        by metis
      moreover
      {
        have "(if (t, at_start (actions ! n)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! n)) \<in> planning_sem.happ_seq then (1::nat) else 0) = 1" using start_not_scheduled end_scheduled by simp
        moreover
        have "n \<in> set [n..<length actions]" using n by simp
        ultimately
        have "\<exists>n \<in> set (map 
          (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)) 
          (filter 
            (\<lambda>a. p \<in> set (over_all a)) 
            (map (\<lambda>n. actions ! n) [n..<length actions]))). n > 0" using assms n end_scheduled start_not_scheduled
          apply -
          apply (rule bexI)
          defer
           apply (subst set_map)
           apply (rule imageI[of "actions ! n"])
          using assms apply simp
          by simp
      }
      ultimately
      have False by fast
    }
    thus ?thesis 
      apply (cases "0 = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)")
       apply blast
      by linarith
  qed
  thus ?thesis using partially_updated_locked_before_alt[OF n] by presburger
qed

lemma locks_in_dom: "set (map PropLock (over_all (actions ! n))) \<subseteq> dom (map_of nta_vars)" 
      unfolding dom_map_of_nta_vars set_map action_vars_spec_def Let_def inv_vars_spec_def
      apply -
      apply (rule subsetI)
      apply (rule UnI2)
      apply (rule UnI1)+ 
      using n
      by auto

text \<open>Definition and properties of next state\<close>

private 
lemma L_ending_ended: "L' = L[Suc n := EndInstant (actions ! n)]" 
  and v_ending_ended: "v' = v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. x - 1) (map (the o v) (map PropLock (over_all (actions ! n)))))" 
  and c_ending_ended: "c' = c(ActEnd (actions ! n) := 0)" using s' unfolding enter_end_instant_def Let_def prod.case by blast+


lemma variables_locked_after:
  assumes p_has_lock: "PropLock p \<in> dom (map_of nta_vars)" 
    shows "v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p (Suc n)))"
proof (cases "p \<in> set (over_all (actions ! n))")
  case True
  have 1: "v' (PropLock p) = Some (the (v (PropLock p)) - 1)"
    unfolding v_ending_ended
    apply (subst map_map)
    apply (subst distinct_map_upds)
    using True n apply simp
    apply (rule distinct_inj_map)
    using over_all_distinct[THEN bspec[of _ _ "actions ! n"]] n apply simp
    unfolding inj_def apply simp
    unfolding comp_def by simp
  
  have 2: "partially_updated_locked_before t p (Suc n) = partially_updated_locked_before t p n - 1"
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
    using start_not_scheduled end_scheduled
     apply simp
    apply (subst id_def)
    apply (subst sum_list.eq_foldr)
    apply (subst foldr_assoc)
    by linarith

  show ?thesis 
    apply (subst 1)
    apply (subst locked_before[THEN spec, THEN mp, OF assms])
    apply (subst 2)
    apply simp
    using partially_updated_locked_before_lower[OF True] 
    unfolding int_of_nat_def by simp
next
  case False
  have "partially_updated_locked_before t p (Suc n) = partially_updated_locked_before t p n" 
    unfolding partially_updated_locked_before_def using False by simp
  moreover
  have "v' (PropLock p) = v (PropLock p)"
    unfolding v_ending_ended
    apply (subst map_upds_apply_nontin)
    using n False by auto
  ultimately
  show ?thesis using locked_before assms by simp
qed

lemma variables_same_after:
  assumes "x \<notin> set (map PropLock (over_all (actions ! n)))"
  shows "v' x = v x"
  unfolding v_ending_ended using assms map_upds_apply_nontin by simp

lemma ending_executed_clock':
  assumes "i \<le> n" 
    "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq" 
    "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq" 
    shows "c' (ActEnd (actions ! i)) = (0::real)"
  apply (cases "i = n")
  subgoal unfolding c_ending_ended by simp
  using assms ending_executed_clock unfolding c_ending_ended by auto

lemma ending_not_executed_clock': 
  assumes "n < i"
    "i < length actions"
    "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq" 
    "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq" 
  shows "c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
  unfolding c_ending_ended
  apply (subst fun_upd_other)
  using assms(1,2) distinct_actions distinct_conv_nth apply fastforce
  using ending_not_executed_clock assms by simp

lemma clocks_same_after:
  assumes "x \<noteq> ActEnd (actions ! n)"
  shows "c' x = c x"
  unfolding c_ending_ended using fun_upd_other assms by simp

lemma ending_executed_loc':
  assumes "i \<le> n" "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq" "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq"
    shows "L' ! Suc i = (EndInstant (actions ! i))"
  apply (cases "i = n")
  subgoal unfolding L_ending_ended using n nth_list_update_eq L_len by auto
  unfolding L_ending_ended using nth_list_update_neq assms ending_executed_loc L_len n by simp

lemma ending_not_executed_loc':
  assumes "i < length actions" 
    "n < i"
    "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq"
    "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq"
  shows "L' ! Suc i = (Running (actions ! i))"
  unfolding L_ending_ended using assms ending_not_executed_loc nth_list_update_neq by auto

lemma locs_same_after:
  assumes "i < length actions"
      and "i \<noteq> Suc n"
    shows "L' ! i = L ! i"
  using assms unfolding L_ending_ended using nth_list_update_neq by simp

lemma length_same_after:
  "length L' = length L" unfolding L_ending_ended by simp

lemma bounded_after: "Simple_Network_Language.bounded (map_of nta_vars) v'"
proof (rule updated_bounded[OF v_bounded _ v_ending_ended])
  show "length (map PropLock (over_all (actions ! n))) = length (map (\<lambda>x. x - 1) (map (the \<circ> v) (map PropLock (over_all (actions ! n)))))" by simp
  show "\<forall>x\<in>set (map PropLock (over_all (actions ! n))). \<exists>l u. map_of nta_vars x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
    apply (rule ballI)
    subgoal for x
      unfolding set_map
      apply (erule imageE)
      subgoal for p
        apply (intro exI conjI)
          apply (subst map_of_nta_vars_action_inv[of "actions ! n"])
        using n
            apply simp
           apply simp
          apply simp
         apply (erule ssubst[of x])
         apply (subst variables_locked_after)
        using locks_in_dom apply auto[1]
         apply (subst option.the_def)
        apply (subst int_of_nat_def)
         apply simp
         apply (erule ssubst[of x])
         apply (subst variables_locked_after)
        using locks_in_dom apply auto[1]
         apply (subst option.the_def)
        apply (subst int_of_nat_def)
        using partially_updated_locked_before_ran by simp
      done
    done
qed

lemma planning_locked_after:
  "v' PlanningLock = Some 1" using planning_state variables_same_after by fastforce

lemma enter_end_instant_okay:
    shows "abs_renum.urge_bisim.A.steps [(L, v, c), enter_end_instant n (L, v, c)]"
proof (rule single_step_intro)

  obtain l b g a f r l' where
    t: "(l, b, g, a, f, r, l') = (\<lambda>(l, b, g, a, f, r, l'). (l, b, map conv_ac g, a, f, r, l')) (edge_3_spec (actions ! n))" 
  and t': "l = Running (actions ! n)"
     "b = bexp.true"
     "g = map conv_ac (l_dur_spec (actions ! n) @ u_dur_spec (actions ! n) @ map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))"
     "a = Sil STR ''''"
     "f = map (inc_prop_lock_ab (-1)) (over_all (actions ! n))"
     "r = [ActEnd (actions ! n)]"
     "l' = EndInstant (actions ! n)"
    unfolding edge_3_spec_def Let_def prod.case by simp
    
  show "(case (L, v, c) of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (enter_end_instant n (L, v, c))"
    unfolding s' prod.case
  proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
    show "bounded (map_of nta_vars) v" using v_bounded .
    show "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L', v', c'\<rangle>"
      unfolding abs_renum.sem_def
    proof (rule step_int)
      show "TRANS ''silent'' \<bar> (l, b, g, Sil STR '''', f, r, l') \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! (Suc n))"
        apply (subst TAG_def)
        apply (subst t'(4)[symmetric])
        apply (subst conv_trans)
        using n actual_autos_alt apply simp
        apply (subst nth_auto_trans)
        using n t by fast+
      show "''committed'' \<bar> l \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! Suc n) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). L ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
        apply (subst TAG_def)
        apply (rule disjI2)
        apply (intro allI impI)
        subgoal for p
          apply (subst conv_committed)
           apply simp
          using no_committed
          by simp
        done
      show "''bexp'' \<bar> Simple_Expressions.check_bexp v b True"
        unfolding t'
        apply (subst TAG_def)
        by (rule check_bexp_is_val.intros)
      show "''guard'' \<bar> c \<turnstile> g"
      proof -
        (* The exec time satisfies the duration bounds *)
        (* There will be a similar, repetitive proof. Repetition is necessary, because the other case has 
            actions with a duration of 0 and therefore the duration bounds will be satisfied for other reasons. *)
        from planning_sem.exec_time_sat_dur_const[OF _ end_scheduled start_not_scheduled]
        have sat_dur_bounds: "satisfies_duration_bounds lower_sem upper_sem (actions ! n) (planning_sem.exec_time (at_start (actions ! n)) t)" using n by simp
        from this
        have "c \<turnstile> map conv_ac (l_dur_spec (actions ! n))"
          apply (subst clock_val_def)
          apply (subst l_dur_spec_def)
          apply (cases "lower (actions ! n)")
           apply simp
          subgoal for b
            apply (cases b)
            subgoal
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct1)
              unfolding lower_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n]) 
              by (metis Rat.of_int_def of_rat_less of_rat_of_int_eq)
            subgoal 
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct1)
              unfolding lower_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n])
              by (metis Rat.of_int_def of_rat_less_eq of_rat_of_int_eq)
            done
          done
        moreover
        from sat_dur_bounds
        have "c \<turnstile> map conv_ac (u_dur_spec (actions ! n))"
          apply (subst clock_val_def)
          apply (subst u_dur_spec_def)
          apply (cases "upper (actions ! n)")
           apply simp
          subgoal for b
            apply (cases b)
            subgoal
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct2)
              unfolding upper_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n]) 
              by (metis Rat.of_int_def of_rat_less of_rat_of_int_eq)
            subgoal 
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct2)
              unfolding upper_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n])
              by (metis Rat.of_int_def of_rat_less_eq of_rat_of_int_eq)
            done
          done
        moreover
        (* clean up s_corr and e_corr once the exact pre- and post-conditions are fixed *)
        have s_corr: "\<forall>a\<in>set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
        proof (intro ballI impI)
          fix a
          assume a: "a \<in> set actions" "(t, at_start a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_start a"
          then obtain i where
            "a = actions ! i"
            "i < length actions" 
            apply -
            apply (subst (asm) set_conv_nth)
            by auto
          thus "c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)" using start_snap_time[THEN spec] by blast
        qed
        have e_corr: "\<forall>a\<in>set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
        proof (intro ballI impI)
          fix a
          assume a: "a \<in> set actions" "(t, at_end a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_end a"
          then obtain i where
            i: "a = actions ! i"
            "i < length actions"
            apply -
            apply (subst (asm) set_conv_nth)
            apply (erule CollectE)
            by blast
          show "c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)" 
            unfolding i(1)
          proof (rule ending_not_executed_clock[THEN spec, THEN mp, OF i(2), THEN mp]) 
            from a(2)
            consider "(t, at_end a) \<notin> planning_sem.happ_seq" | "at_end (actions ! n) = at_end a" by auto
            thus "n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq"
            proof cases
              case 1
              then show ?thesis using i(1) by auto
            next
              assume "at_end (actions ! n) = at_end a" 
              hence "at_end (actions ! n) = at_end (actions ! i)" using i by blast
              moreover
              from i(2) n
              have "actions ! n \<in> set actions" "actions ! i \<in> set actions" by simp+
              ultimately
              have "actions ! n = actions ! i" using at_end_inj unfolding inj_on_def by blast
              with i n
              have "n = i" using distinct_actions using distinct_conv_nth by auto
              then show ?thesis by simp
            qed
          qed
        qed
        have "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))))"
          using mutex_0_constraint_sat end_scheduled s_corr e_corr by blast
        moreover
        have "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))"
          using  mutex_eps_constraint_sat end_scheduled s_corr e_corr by blast
        ultimately
        show ?thesis unfolding t' TAG_def
          unfolding map_append
          by (auto intro: guard_append)
      qed
      show "''target invariant'' \<bar> \<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c' \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (L' ! p)"
        unfolding TAG_def 
        apply (intro allI impI)
        apply (subst no_invs)
        by simp+
      show "''loc'' \<bar> L ! Suc n = l" unfolding TAG_def t' using ending_not_executed_loc[THEN spec, THEN mp, OF n] using start_not_scheduled end_scheduled by blast
      show "''range'' \<bar> Suc n < length L" unfolding TAG_def using n L_len by simp
      show "''new loc'' \<bar> L' = L[Suc n := l']" unfolding TAG_def t' using L_ending_ended by simp
      show "''new valuation'' \<bar> c' = [r\<rightarrow>0]c" unfolding TAG_def t' using c_ending_ended by simp


      show "''is_upd'' \<bar> is_upds v f v'" 
      proof (subst TAG_def)
        have v': "v' = v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. x - 1) (map (the o v) (map PropLock (over_all (actions ! n)))))" using v_ending_ended by simp
        have x: "map (\<lambda>prop. (PropLock prop, binop plus_int (var (PropLock prop)) (exp.const (- 1)))) xs = map (inc_var (-1)) (map PropLock xs)" for xs unfolding comp_apply map_map by simp
    
        have "is_upds v (map (\<lambda>v. (v, binop plus_int (var v) (exp.const (- 1)))) (map PropLock (over_all (actions ! n)))) (v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. plus_int x (- 1)) (map (the \<circ> v) (map PropLock (over_all (actions ! n))))))"
        proof (rule is_upds_inc_vars[of _ _ "-1"])
          show "set (map PropLock (over_all (actions ! n))) \<subseteq> dom v"
            using locks_in_dom v_bounded bounded_def by metis
          show "distinct (map PropLock (over_all (actions ! n)))" using n over_all_distinct
            unfolding distinct_map
            unfolding inj_on_def by simp
        qed

        thus "is_upds v f v'" unfolding v_ending_ended t'
          unfolding inc_prop_lock_ab_def x by auto
      qed
      show "''bounded'' \<bar> Simple_Network_Language.bounded (map_of nta_vars) v'" unfolding TAG_def
        by (rule bounded_after)
    qed
  qed
qed
end



context (* to apply all end snap actions of ending actions *)
  fixes M t l end_indices
    L v c
  assumes l: "l < length (htpl \<pi>)"
      and M: "M = planning_sem.plan_state_seq"
      and t: "t = time_index \<pi> l"
      and end_indices: "end_indices = filter (\<lambda>n. (t, at_end (actions ! n)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! n)) \<notin> planning_sem.happ_seq) [0..<length actions]"
      and L_len: "length L = Suc (length actions)"
      and v_bounded: "bounded (map_of nta_vars) v"
      and planning_state: "v PlanningLock = Some 1"
      and p_locked_before: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow>  v (PropLock p) = Some (planning_sem.locked_before t p)"
      and ending_clock: "\<forall>i < length actions. c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
      and starting_clock: "\<forall>i < length actions. c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and ending_loc: "\<forall>i < length actions. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (Running (actions ! i))"
begin 

lemma sorted_wrt_end_indices: "sorted_wrt (<) end_indices" unfolding end_indices using sorted_wrt_upt sorted_wrt_filter by blast
lemma length_end_indices: "length end_indices \<le> length actions" unfolding end_indices 
  apply (rule order_trans) 
   apply (rule length_filter_le)
  by simp

lemma sorted_end_indices: "sorted end_indices" unfolding end_indices using sorted_filter[of id, simplified list.map_id] using sorted_upt by blast 

lemma sorted_nth_sym: assumes "sorted xs" "xs ! i < xs ! j" "i < length xs" shows "i < j"
proof -
  { assume "j \<le> i"
    from sorted_nth_mono[OF assms(1) this assms(3)] assms(2)
    have False by simp
  }
  thus ?thesis by fastforce
qed

lemma sorted_wrt_nth_sym: assumes "sorted_wrt (<) xs" "(xs::'b::order list) ! i \<le> xs ! j" "i < length xs" shows "i \<le> j"
proof -
  { assume "j < i"
    from sorted_wrt_nth_less[OF assms(1) this assms(3)] assms(2)
    have False by simp
  }
  thus ?thesis by fastforce
qed

thm partially_updated_locked_before_def[no_vars]

lemma "dom (map_of MM) = set (map fst MM)" unfolding set_map dom_map_of_conv_image_fst ..

(* Todo?: refactor with seq_apply_pre_post *)
lemma enter_end_instants_ith_pre:
  fixes L' v' c'
  assumes "ei < length end_indices"
      and "n = end_indices ! ei"
      and "((L, v, c)#enter_end_instants end_indices (L, v, c)) ! ei = (L', v', c')"
    shows "length L' = Suc (length actions)
          \<and> bounded (map_of nta_vars) v' 
          \<and> v' PlanningLock = Some 1
          \<and> (\<forall>i < n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq  \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L' ! Suc i = (EndInstant (actions ! i)))
          \<and> (\<forall>i < length actions. n \<le> i \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq  \<longrightarrow> L' ! Suc i = (Running (actions ! i)))
          \<and> (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))) 
          \<and> (\<forall>i < n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c' (ActEnd (actions ! i)) = (0::real))
          \<and> (\<forall>i < length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t))
          \<and> (\<forall>i < length actions. c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t))"
  using assms
proof (induction ei arbitrary: L' v' c' n)
  case 0
  have unchanged: "L = L'" "v = v'" "c = c'" using 0 by simp+ 
  have some_end: "length end_indices > 0" using 0 by auto
  have n: "n = end_indices ! 0" using 0 by simp
  hence "n \<in> set end_indices" using some_end by simp
  hence n_len: "n < length actions" unfolding end_indices by auto

  have nothing_before_n: "\<not> ((t, at_end a) \<in> planning_sem.happ_seq \<and> (t, at_start a) \<notin> planning_sem.happ_seq)" if "i < n" "a = actions ! i" for a i 
  proof -
    show "\<not> ((t, at_end a) \<in> planning_sem.happ_seq \<and> (t, at_start a) \<notin> planning_sem.happ_seq) "
    proof (intro notI; erule conjE)

      have sorted_wrt_nth_le_end_indices: "end_indices ! i \<le> end_indices ! j \<Longrightarrow> i \<le> j" if "i < length end_indices" for i j 
        apply (rule ccontr)
        using sorted_wrt_nth_less[OF sorted_wrt_end_indices _ that, of j] 
        by linarith

      assume a: "(t, at_end a) \<in> planning_sem.happ_seq" "(t, at_start a) \<notin> planning_sem.happ_seq"
      with n_len \<open>i < n\<close>
      have "i < length actions" by simp
      hence "i \<in> set end_indices" using a 
        apply - 
        unfolding end_indices set_filter
        apply (rule CollectI, intro conjI)
        using some_actions apply simp
        using \<open>a = actions ! i\<close> by blast+
      then obtain iidx where
        iidx: "i = end_indices ! iidx"
        "iidx < length end_indices" using in_set_conv_nth by metis

      have "iidx = 0" using sorted_wrt_nth_le_end_indices[OF iidx(2), simplified iidx(1)[symmetric], where j2 = 0, simplified n[symmetric]] using \<open>i < n\<close> by simp
      with iidx(1) n \<open>i < n\<close>
      show False by blast
    qed
  qed
  show ?case
    unfolding unchanged[symmetric]
  proof (intro conjI)
    show "length L = Suc (length actions)" using L_len by blast
    show "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))"
    proof (intro allI impI)
      fix p
      assume "PropLock p \<in> dom (map_of nta_vars)"
      from p_locked_before[THEN spec, THEN mp, OF this]
      have "v (PropLock p) = Some (int (planning_sem.locked_before t p))" by auto
      moreover
      have "planning_sem.locked_before t p = partially_updated_locked_before t p n"
        apply (subst partially_updated_locked_before_by_none_is_locked_before[symmetric])
        apply (rule partially_updated_locked_before_inv, simp)
        using nothing_before_n by simp
      ultimately
      show "v (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))" unfolding int_of_nat_def by simp
    qed
    show "Simple_Network_Language.bounded (map_of nta_vars) v" using v_bounded by simp
    show "v PlanningLock = Some 1" using planning_state by simp
    show "\<forall>i<n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c (ActEnd (actions ! i)) = 0"  using nothing_before_n by blast
    show "\<forall>i<length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)" using n_len ending_clock by simp
    show "\<forall>i<length actions. c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)" using starting_clock n_len by simp
    show "\<forall>i<n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L ! Suc i = EndInstant (actions ! i)" using nothing_before_n by blast
    show "\<forall>i<length actions. n \<le> i \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L ! Suc i = Running (actions ! i)" using n_len ending_loc by blast
  qed
next
  case (Suc i)

  have n: "n = end_indices ! Suc i" 
          "Suc i < length end_indices" using Suc by linarith+

  have n_set: "n \<in> set end_indices" using Suc(2, 3) by auto
  hence n_len: "n < length actions" unfolding end_indices by auto
  

  obtain L1 v1 c1 n1 where
    n1: "n1 = end_indices ! i"
    and Lvc1: "((L, v, c) # enter_end_instants end_indices (L, v, c)) ! i = (L1, v1, c1)" 
    using prod_cases3 by metis

  have n1: "n1 = end_indices ! i"
           "i < length end_indices" using n using n1 by auto

  have n1_set: "n1 \<in> set end_indices" using n1 Suc (3) by simp
  hence n1_len: "n1 < length actions" unfolding end_indices by auto

  have ending: "(t, at_end (actions ! n1)) \<in> planning_sem.happ_seq" "(t, at_start (actions ! n1)) \<notin> planning_sem.happ_seq"
    using n1_set unfolding end_indices by simp+

  have Suc_n1_le_n: "Suc n1 \<le> n" unfolding n n1 using sorted_wrt_nth_less[OF sorted_wrt_end_indices] n(2) by force 

  have n1_pres:
    "length L1 = Suc (length actions)"
    "Simple_Network_Language.bounded (map_of nta_vars) v1"
    "v1 PlanningLock = Some 1"
    "(\<forall>i<n1. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L1 ! Suc i = EndInstant (actions ! i))"
    "(\<forall>i<length actions. n1 \<le> i \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L1 ! Suc i = Running (actions ! i))" 
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v1 (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n1)))"
    "(\<forall>i<n1. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c1 (ActEnd (actions ! i)) = 0)"
    "(\<forall>i<length actions. n1 \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c1 (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t))"
    "(\<forall>i<length actions. c1 (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t))"
    using Suc.IH[OF n1(2,1) Lvc1] by blast+

  have nothing_between: "\<not> ((t, at_end (actions ! x)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! x)) \<notin> planning_sem.happ_seq)" 
    if i_ran: "Suc n1 \<le> x" "x < n" 
    for x
  proof (intro notI)
    assume e: "(t, at_end (actions ! x)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! x)) \<notin> planning_sem.happ_seq"
    have "x < length actions" using \<open>x < n\<close> n_len by auto
    hence "x \<in> set (end_indices)" using a e unfolding end_indices by auto
    then obtain nx where
      nx: "x = end_indices ! nx" 
      "nx < length end_indices" unfolding in_set_conv_nth by blast

    have "nx < Suc i" using sorted_nth_sym[OF sorted_end_indices] 
      using nx(2)  \<open>x < n\<close>[simplified nx n] by blast 
    moreover
    have "n1 < x" using \<open>Suc n1 \<le> x\<close> by simp
    have "i < nx" using sorted_nth_sym[OF sorted_end_indices] \<open>n1 < x\<close>[simplified n1 nx] n1(2) by blast
    ultimately
    show False by fastforce
  qed

  have "((L, v, c) # enter_end_instants end_indices (L, v, c)) ! (Suc i) = enter_end_instant (end_indices ! i) (L1, v1, c1)"
    unfolding Lvc1[symmetric] enter_end_instants_def 
    apply (subst seq_apply_nth_Suc) 
    using Suc(2) apply simp
    using Suc(2) by simp
  hence Lvc': "(L', v', c') = enter_end_instant (end_indices ! i) (L1, v1, c1)" using Suc(4) by simp

  show ?case 
  proof (intro conjI)
    show "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))"
    proof (intro allI impI)
      fix p
      assume a: "PropLock p \<in> dom (map_of nta_vars)"
      have "v' (PropLock p) = Some (partially_updated_locked_before t p (Suc n1))" using variables_locked_after[OF n1_len ending n1_pres _ a]
        unfolding n1 Lvc'[symmetric] int_of_nat_def by blast
      moreover
      have "partially_updated_locked_before t p (Suc n1) = partially_updated_locked_before t p n" using partially_updated_locked_before_inv nothing_between Suc_n1_le_n
        by simp
      ultimately
      show "v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))" unfolding int_of_nat_def by simp
    qed
    show "length L' = Suc (length actions)" using length_same_after[OF n1_len ending n1_pres ] unfolding n1 Lvc'[symmetric] using n1_pres(1) by auto
    show "Simple_Network_Language.bounded (map_of nta_vars) v'" using bounded_after[OF n1_len ending n1_pres] unfolding n1 Lvc'[symmetric] by blast
    show "v' PlanningLock = Some 1" using planning_locked_after[OF n1_len ending n1_pres] unfolding n1 Lvc'[symmetric] by blast
    show "\<forall>i<length actions. n \<le> i \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L' ! Suc i = Running (actions ! i)"
    proof (intro allI impI, elim conjE)
      fix x
      assume a: "x < length actions" "n \<le> x" "(t, at_start (actions ! x)) \<notin> planning_sem.happ_seq" "(t, at_end (actions ! x)) \<in> planning_sem.happ_seq"
      show "L' ! Suc x = Running (actions ! x)"
        apply (rule ending_not_executed_loc'[OF n1_len ending n1_pres, simplified n1 Lvc'[symmetric]])
            apply (rule HOL.refl)
           apply (rule a(1))
        subgoal using n1 Suc_n1_le_n \<open>n \<le> x\<close> by auto
        using a(3,4) by auto
    qed
    show "\<forall>i<n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L' ! Suc i = EndInstant (actions ! i)"
    proof (intro allI impI, elim conjE)
      fix x
      assume a: "x < n" "(t, at_start (actions ! x)) \<notin> planning_sem.happ_seq" "(t, at_end (actions ! x)) \<in> planning_sem.happ_seq"
      have "x < Suc n1" using nothing_between[OF _ a(1)] a(2,3) by linarith
      show "L' ! Suc x = EndInstant (actions ! x)" 
        apply (rule ending_executed_loc'[OF n1_len ending n1_pres, simplified n1 Lvc'[symmetric]])
           apply (rule HOL.refl)
        subgoal using \<open>x < Suc n1\<close> unfolding n1 by simp
        using a(2, 3) by auto
    qed
    show "\<forall>i<n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c' (ActEnd (actions ! i)) = 0"
    proof (intro allI impI, elim conjE)
      fix x
      assume a: "x < n" "(t, at_start (actions ! x)) \<notin> planning_sem.happ_seq" "(t, at_end (actions ! x)) \<in> planning_sem.happ_seq"
      have "x < Suc n1" using nothing_between[OF _ a(1)] a(2,3) by linarith
      show "c' (ActEnd (actions ! x)) = 0" 
        apply (rule ending_executed_clock'[OF n1_len ending n1_pres, simplified n1 Lvc'[symmetric]])
           apply (rule HOL.refl)
        subgoal using \<open>x < Suc n1\<close> unfolding n1 by simp
        using a(2, 3) by auto
    qed
    show "\<forall>i<length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
    proof (intro allI impI)
      fix x
      assume a: "x < length actions" "n \<le> x \<or> (t, at_start (actions ! x)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! x)) \<notin> planning_sem.happ_seq"
      then consider "n \<le> x" | "(t, at_start (actions ! x)) \<in> planning_sem.happ_seq" | "(t, at_end (actions ! x)) \<notin> planning_sem.happ_seq" by blast
      thus "c' (ActEnd (actions ! x)) = real_of_rat (planning_sem.exec_time (at_end (actions ! x)) t)"
        apply cases
        subgoal apply (subst clocks_same_after[OF n1_len ending n1_pres])
              apply (subst n1) apply (rule Lvc'[symmetric])
          subgoal using Suc_n1_le_n distinct_actions[simplified distinct_conv_nth, THEN spec, THEN mp] using a(1) by auto
          subgoal using n1_pres(8) Suc_n1_le_n a(1) by simp
          done
        subgoal apply (subst clocks_same_after[OF n1_len ending n1_pres])
            apply (subst n1) apply (rule Lvc'[symmetric])
          using ending apply fastforce
          using n1_pres(8) a(1) by blast
        subgoal apply (subst clocks_same_after[OF n1_len ending n1_pres])
            apply (subst n1) apply (rule Lvc'[symmetric])
          using ending apply fastforce
          using n1_pres(8) a(1) by blast
        done
    qed
    show "\<forall>i<length actions. c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      apply (intro allI impI)
      subgoal for x
        apply (subst clocks_same_after[OF n1_len ending n1_pres])
          apply (subst n1) apply (rule Lvc'[symmetric])
        apply simp
        using n1_pres(9) by simp
      done
  qed
qed


lemma enter_end_instants_valid_steps:
 "abs_renum.urge_bisim.A.steps ((L, v, c)#enter_end_instants end_indices (L, v, c))"
  unfolding enter_end_instants_def
proof (rule seq_apply_steps_induct)
  show "\<forall>i. Suc i < length ((L, v, c) # seq_apply (map enter_end_instant end_indices) (L, v, c)) \<longrightarrow> abs_renum.urge_bisim.A.steps [((L, v, c) # seq_apply (map enter_end_instant end_indices) (L, v, c)) ! i, ((L, v, c) # seq_apply (map enter_end_instant end_indices) (L, v, c)) ! Suc i]"
  proof (intro allI impI)
    fix i
    assume "Suc i < length ((L, v, c) # seq_apply (map enter_end_instant end_indices) (L, v, c))"
    hence i: "i < length end_indices" unfolding enter_end_instants_def by simp
    obtain n where
      n: "n = end_indices ! i" by simp
    have n_in_set: "n \<in> set end_indices" using i n  in_set_conv_nth by simp
    hence n_len: "n < length actions" unfolding end_indices by simp
    have ending: "(t, at_end (actions ! n)) \<in> planning_sem.happ_seq" "(t, at_start (actions ! n)) \<notin> planning_sem.happ_seq" using n_in_set unfolding end_indices by simp+
    obtain L' v' c' where
      Lvc': "((L, v, c) # enter_end_instants end_indices (L, v, c)) ! i = (L', v', c')" using prod_cases3 by blast
  
    from enter_end_instants_ith_pre[OF i n Lvc']
    have i_pres: "length L' = Suc (length actions)" 
      "Simple_Network_Language.bounded (map_of nta_vars) v' "
      "v' PlanningLock = Some 1 "
      "\<forall>i<n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L' ! Suc i = EndInstant (actions ! i) "
      "(\<forall>i<length actions. n \<le> i \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<longrightarrow> L' ! Suc i = Running (actions ! i))"
      "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n)) "
      "\<forall>i<n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c' (ActEnd (actions ! i)) = 0"
      "\<forall>i<length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq \<longrightarrow> c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t) "
      "\<forall>i<length actions. c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)" by blast+
    have "abs_renum.urge_bisim.A.steps [(L', v', c'), enter_end_instant (end_indices ! i) (L', v', c')]"
      using enter_end_instant_okay[OF n_len ending i_pres(1,2,3,4,5,6,7,8,9)] unfolding n by blast
    thus "abs_renum.urge_bisim.A.steps [((L, v, c) # seq_apply (map enter_end_instant end_indices) (L, v, c)) ! i, ((L, v, c) # seq_apply (map enter_end_instant end_indices) (L, v, c)) ! Suc i]" 
      apply (subst seq_apply_nth_Suc) using i apply simp
      apply (subst Lvc'[simplified enter_end_instants_def])+
      using i by simp
  qed
qed

end

subsection \<open>Instant snap actions\<close>
text \<open>
Transitions are grouped by specific parts of the happening time point they simulate. 

We only care about the conditions which:
  - Are necessary for the transitions
  - Can change during the larger sequence of transitions to which these belong

Post-conditions are a to-do, because they depend on the pre-conditions of other parts
\<close>

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

lemma l_dur_spec_sat_if: 
  assumes "satisfies_duration_bounds lower_sem upper_sem act i"
      and "((cv (ActStart act))::real) = real_of_rat i"
    shows "cv \<turnstile> map conv_ac (l_dur_spec act)"
  using assms
  unfolding satisfies_duration_bounds_def l_dur_spec_def
Let_def lower_sem_def comp_def
  apply (cases "lower act")
   apply simp
  subgoal for lb
    apply (cases lb)
    subgoal for tl
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct1)
      apply (erule ssubst[of "cv (ActStart act)"])
      unfolding Rat.of_int_def
      by (metis of_rat_less of_rat_of_int_eq)
    subgoal for tl
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct1)
      apply (erule ssubst[of "cv (ActStart act)"])
      unfolding Rat.of_int_def 
      by (metis of_rat_less_eq of_rat_of_int_eq)
    done
  done

lemma u_dur_spec_sat_if:
  assumes "satisfies_duration_bounds lower_sem upper_sem act i"
      and "((cv (ActStart act))::real) = real_of_rat i"
    shows "cv \<turnstile> map conv_ac (u_dur_spec act)"
  using assms
  unfolding satisfies_duration_bounds_def u_dur_spec_def
Let_def upper_sem_def comp_def
  apply (cases "upper act")
   apply simp
  subgoal for ub
    apply (cases ub)
    subgoal for tu
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct2)
      apply (erule ssubst[of "cv (ActStart act)"])
      unfolding Rat.of_int_def
      by (metis of_rat_less of_rat_of_int_eq)
    subgoal for tu
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct2)
      apply (erule ssubst[of "cv (ActStart act)"])
      unfolding Rat.of_int_def 
      by (metis of_rat_less_eq of_rat_of_int_eq)
    done
  done

context (* For a timepoint and its snap actions *)
  fixes i t
assumes i: "i < length (htpl \<pi>)"
      and t: "t = time_index \<pi> i"
begin (* To do: extend to include above contexts *)


context (* for a single instant action n *)
  fixes n L v c L' v' c'
   assumes n: "n < length actions"
      and end_scheduled: "(t, at_end (actions ! n)) \<in> planning_sem.happ_seq"
      and start_scheduled: "(t, at_start (actions ! n)) \<in> planning_sem.happ_seq"

      and L_len: "length L = Suc (length actions)"
      and v_bounded: "bounded (map_of nta_vars) v"
      and planning_state: "v PlanningLock = Some 1"

      and instant_executed_loc: "\<forall>i < n. (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (Off (actions ! i))"

      and instant_not_executed_loc: "\<forall>i < length actions. n \<le> i \<and> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (Off (actions ! i))"

      and locked: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (planning_sem.locked_during t p))"
      and prop_state: "\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_prev_updated_prop_state i p n)"
      and active: "v ActsActive = Some (planning_sem.active_before t)"

      and instant_executed_time: "\<forall>i < n. is_instant_index t i
            \<longrightarrow> c (ActEnd (actions ! i)) = 0 \<and> c (ActStart (actions ! i)) = 0"
      and instant_not_executed_time:  "\<forall>i < length actions. n \<le> i \<and> is_instant_index t i
            \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t) 
              \<and> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"

      and ending_start_time: "\<forall>i < length actions. is_ending_index t i
            \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and ending_end_time:  "\<forall>i < length actions. is_ending_index t i
            \<longrightarrow> c (ActEnd (actions ! i)) = (0::real)"

      and starting_start_time: "\<forall>i < length actions. is_starting_index t i
            \<longrightarrow>  c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and starting_end_time: "\<forall>i < length actions. is_starting_index t i
            \<longrightarrow>  c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"

      and other_start_time: "\<forall>i < length actions. is_not_happening_index t i
            \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and other_end_time: "\<forall>i < length actions. is_not_happening_index t i
            \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"

      and s': "leave_end_instant n (start_to_end_instant n (enter_start_instant n (L, v, c))) = (L', v', c')"
begin

lemma act_n_in_actions: "actions ! n \<in> set actions" using in_set_conv_nth n by simp

subsubsection \<open>Definitions\<close>
definition "L_started = fst (enter_start_instant n (L, v, c))" 
definition "v_started = fst (snd (enter_start_instant n (L, v, c)))"
definition "c_started = snd (snd (enter_start_instant n (L, v, c)))"

definition "L_ending = fst (start_to_end_instant n (enter_start_instant n (L, v, c)))"
definition "v_ending = fst (snd (start_to_end_instant n (enter_start_instant n (L, v, c))))"
definition "c_ending = snd (snd (start_to_end_instant n (enter_start_instant n (L, v, c))))"

lemma Lvc_started: "enter_start_instant n (L, v, c) = (L_started, v_started, c_started)" 
  using L_started_def v_started_def c_started_def by auto

lemma Lvc_ending: "(start_to_end_instant n (enter_start_instant n (L, v, c))) = (L_ending, v_ending, c_ending)"
  using L_ending_def v_ending_def c_ending_def by auto


subsubsection \<open>Lvc\<close>

lemma start_dels_in_dom: "set (map PropLock (dels (at_start (actions ! n)))) - set (map PropLock (adds (at_start (actions ! n)))) \<subseteq> dom (map_of nta_vars)"
unfolding dom_map_of_nta_vars set_map action_vars_spec_def Let_def snap_vars_spec_def
  apply (rule subsetI)
  apply (rule UnI2)
  apply (rule UnI1)+
  unfolding set_map map_append set_append using n by fastforce

lemma start_pres_in_dom: "set (map PropVar (pre (at_start (actions ! n)))) \<subseteq> dom (map_of nta_vars)"
  unfolding dom_map_of_nta_vars set_map action_vars_spec_def Let_def snap_vars_spec_def
    apply (rule subsetI)
    apply (rule UnI2)
    apply (rule UnI1)+
    unfolding set_map map_append set_append using n by fastforce

lemma v_pre_conds_sat: "Simple_Expressions.check_bexp v (bexp_and_all (map (is_prop_ab 1) (pre (at_start (actions ! n))))) True"
proof -
  { fix p
    assume p: "p \<in> set (pre (at_start (actions ! n)))"
    moreover
    have "PropVar p \<in> dom (map_of nta_vars)" using start_pres_in_dom p by auto
    ultimately
    have "v (PropVar p) = Some 1" using pre_val_in_instant_prev_updated_prop_state_if[OF i t start_scheduled _ n p]  using prop_state by metis
    hence "Simple_Expressions.check_bexp v (is_prop_ab 1 p) True" 
      unfolding is_prop_ab_def 
      apply (subst check_bexp_simps)
      apply (subst is_val_simps)+
      by simp
  } 
  hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_start (actions ! n)))). Simple_Expressions.check_bexp v b True" by auto
  thus ?thesis using check_bexp_all by blast
qed

lemma v_lock_conds_sat: "Simple_Expressions.check_bexp v (bexp_and_all (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! n)))) (dels (at_start (actions ! n)))))) True"
proof -
  { fix p
    assume p: "p \<notin> set (adds (at_start (actions ! n)))"
           "p \<in> set (dels (at_start (actions ! n)))"
    hence "p \<notin> planning_sem.plan_invs_during t" using planning_sem.snap_does_not_delete_inv start_scheduled by auto
    hence "planning_sem.locked_during t p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
    moreover
    have "PropLock p \<in> dom (map_of nta_vars)" using start_dels_in_dom p by auto
    ultimately
    have "v (PropLock p) = Some 0" using locked unfolding int_of_nat_def by simp
    hence "Simple_Expressions.check_bexp v (is_prop_lock_ab 0 p) True" 
      unfolding is_prop_lock_ab_def 
      apply (subst check_bexp_simps)
      apply (subst is_val_simps)+
      by simp
  } 
  hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! n)))) (dels (at_start (actions ! n))))). Simple_Expressions.check_bexp v b True"  by auto
  thus ?thesis using check_bexp_all by blast
qed

subsubsection \<open>Lvc_started\<close>

lemma L_started: "L_started = L[Suc n := StartInstant (actions ! n)]" 
  and v_started: "v_started = v(ActsActive \<mapsto> (the (v ActsActive)) + 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))), map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n)))))) "
  and c_started: "c_started = c(ActStart (actions ! n) := 0)" 
  using Lvc_started[symmetric] unfolding enter_start_instant_def Let_def prod.case by blast+

lemma L_started_length: "length L_started = Suc (length actions)" unfolding L_started using L_len n by simp

lemma v_started_bounded: "bounded (map_of nta_vars) v_started"
proof (rule set_vars_bounded[OF set_vars_bounded[OF single_upd_bounded[OF v_bounded] HOL.refl] v_started])
  show "map_of nta_vars ActsActive = Some (0, int (length actions))" using map_of_nta_vars_ActsActive by simp
  have "the (v ActsActive) < length actions" using active card_action_set
      planning_sem.active_before_less_if_scheduled[OF start_scheduled act_n_in_actions] by simp
  thus "plus_int (the (v ActsActive)) 1 \<le> int (length actions)" by simp
  show "0 \<le> plus_int (the (v ActsActive)) 1" unfolding active by simp
  have map_f_conv: "map (\<lambda>prop. (PropLock prop, n)) xs = map (\<lambda>p. (p, n)) (map PropLock xs)" for xs and n by simp
  show "\<forall>x\<in>set (map PropVar (dels (at_start (actions ! n)))). \<exists>l u. map_of nta_vars x = Some (l, u) \<and> l \<le> 0 \<and> 0 \<le> u"
    apply (intro ballI exI conjI)
        apply (rule map_of_nta_vars_action_start_del)
         apply (rule act_n_in_actions)
      by simp+
  show "\<forall>x\<in>set (map PropVar (adds (at_start (actions ! n)))). \<exists>l u. map_of nta_vars x = Some (l, u) \<and> l \<le> 1 \<and> 1 \<le> u"
    apply (intro ballI exI conjI)
        apply (rule map_of_nta_vars_action_start_add)
         apply (rule act_n_in_actions)
      by simp+
  qed

lemma instant_executed_time': "\<forall>i < n. (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
            \<longrightarrow> c_started (ActEnd (actions ! i)) = 0 \<and> c_started (ActStart (actions ! i)) = 0" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n]
    using instant_executed_time unfolding c_started by simp
  done

lemma c_started_instant_not_executed_time:  "\<forall>i < length actions. n < i \<and> is_instant_index t i
            \<longrightarrow> c_started (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t) 
              \<and> c_started (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
  apply (intro allI impI conjI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i]
    using instant_not_executed_time unfolding c_started
    by auto
  subgoal for i
    using instant_not_executed_time unfolding c_started
    by auto
  done

lemma c_started_act_n_clocks:  "c_started (ActStart (actions ! n)) = 0"
            "c_started (ActEnd (actions ! n)) = real_of_rat (planning_sem.exec_time (at_end (actions ! n)) t)"
  subgoal unfolding c_started by simp
    using instant_not_executed_time n start_scheduled end_scheduled unfolding c_started by simp
    
lemma c_started_ending_start_time: "\<forall>i < length actions. is_ending_index t i
            \<longrightarrow> c_started (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i] nth_ends_unique[OF _ n, of i] 
      start_scheduled end_scheduled ending_start_time 
    unfolding c_started by auto
  done

lemma c_started_ending_end_time:  "\<forall>i < length actions. is_ending_index t i
            \<longrightarrow> c_started (ActEnd (actions ! i)) = (0::real)" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i] nth_ends_unique[OF _ n, of i] 
      start_scheduled end_scheduled ending_end_time 
    unfolding c_started by auto
  done

lemma c_started_starting_start_time: "\<forall>i < length actions. is_starting_index t i
            \<longrightarrow>  c_started (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i] nth_ends_unique[OF _ n, of i] 
      start_scheduled end_scheduled starting_start_time 
    unfolding c_started by auto
  done

lemma c_started_starting_end_time: "\<forall>i < length actions. is_starting_index t i
            \<longrightarrow>  c_started (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i] nth_ends_unique[OF _ n, of i] 
      start_scheduled end_scheduled starting_end_time 
    unfolding c_started by auto
  done

lemma c_started_other_start_time: "\<forall>i < length actions. is_not_happening_index t i
            \<longrightarrow> c_started (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i] nth_ends_unique[OF _ n, of i] 
      start_scheduled end_scheduled other_start_time 
    unfolding c_started by auto
  done

lemma c_started_other_end_time: "\<forall>i < length actions. is_not_happening_index t i
            \<longrightarrow> c_started (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)" 
  apply (intro allI impI)
  subgoal for i
    using nth_starts_unique[OF _ n, of i] nth_ends_unique[OF _ n, of i] 
      start_scheduled end_scheduled other_end_time 
    unfolding c_started by auto
  done

subsubsection \<open>Lvc_ending\<close>

lemma L_ending: "L_ending = L[Suc n := EndInstant (actions ! n)]" 
  and v_ending: "v_ending = v(ActsActive \<mapsto> (the (v ActsActive)) + 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))), map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n))))))"
  and c_ending: "c_ending = c(ActStart (actions ! n) := 0, ActEnd (actions ! n) := 0)" using L_ending_def v_ending_def c_ending_def unfolding Lvc_started start_to_end_instant_def Let_def prod.case fst_conv snd_conv L_started v_started c_started by simp+

lemma v_ending_ActsActive: "the (v_ending ActsActive) = (the (v ActsActive) + 1)" 
proof -
  have "ActsActive \<notin> set (map PropVar (adds (at_start (actions ! n))))" by auto
  moreover
  have "ActsActive \<notin> set (map PropVar (dels (at_start (actions ! n))))" by auto
  ultimately
  have "v_ending ActsActive = (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1)) ActsActive" unfolding v_ending by simp
  thus ?thesis by auto
qed

lemma L_ending_length: "length L_ending = Suc (length actions)" unfolding L_ending using L_len n by simp

lemma L_ending_started: "L_ending = L_started[Suc n := EndInstant (actions ! n)]" using L_ending_def unfolding Lvc_started start_to_end_instant_def by simp
lemma v_ending_started: "v_ending = v_started" using v_ending_def unfolding Lvc_started start_to_end_instant_def by fastforce
lemma c_ending_started: "c_ending = c_started(ActEnd (actions ! n) := 0)" using c_ending_def unfolding Lvc_started start_to_end_instant_def by auto

lemma end_dels_in_dom: "set (map PropLock (dels (at_end (actions ! n)))) - set (map PropLock (adds (at_end (actions ! n)))) \<subseteq> dom (map_of nta_vars)"
unfolding dom_map_of_nta_vars set_map action_vars_spec_def Let_def snap_vars_spec_def
  apply (rule subsetI)
  apply (rule UnI2)
  apply (rule UnI1)+
  unfolding set_map map_append set_append using n by fastforce

lemma end_pres_in_dom: "set (map PropVar (pre (at_end (actions ! n)))) \<subseteq> dom (map_of nta_vars)"
  unfolding dom_map_of_nta_vars set_map action_vars_spec_def Let_def snap_vars_spec_def
    apply (rule subsetI)
    apply (rule UnI2)
    apply (rule UnI1)+
  unfolding set_map map_append set_append using n by fastforce


lemma v_ending_pre_conds_sat: "Simple_Expressions.check_bexp v_ending (bexp_and_all (map (is_prop_ab 1) (pre (at_end (actions ! n))))) True"
proof -
  { fix p
    assume p: "p \<in> set (pre (at_end (actions ! n)))"
    moreover
    have "PropVar p \<in> dom (map_of nta_vars)" using end_pres_in_dom p by auto
    ultimately
    have 1: "v (PropVar p) = Some 1" using pre_val_in_instant_prev_updated_prop_state_if[OF i t end_scheduled  _ n p]  using prop_state by metis
    
    have 2: "PropVar p \<notin> set (map PropVar (dels (at_start (actions ! n))))" using p planning_sem.mutex_pre_app[OF end_scheduled start_scheduled] snaps_disj act_n_in_actions unfolding comp_def set_map by blast
    
    have 3: "PropVar p \<notin> set (map PropVar (adds (at_start (actions ! n))))" using p planning_sem.mutex_pre_app[OF end_scheduled start_scheduled] snaps_disj act_n_in_actions unfolding comp_def set_map by blast
    
    have "v_ending (PropVar p) = Some 1"
      unfolding v_ending 
      apply (subst map_upds_apply_nontin[OF 3])
      apply (subst map_upds_apply_nontin[OF 2])
      using 1 by simp

    hence "Simple_Expressions.check_bexp v_ending (is_prop_ab 1 p) True" 
      unfolding is_prop_ab_def 
      apply (subst check_bexp_simps)
      apply (subst is_val_simps)+
      by simp
  } 
  hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_end (actions ! n)))). Simple_Expressions.check_bexp v_ending b True" by auto
  thus ?thesis using check_bexp_all by blast
qed

lemma v_ending_lock_conds_sat: "Simple_Expressions.check_bexp v_ending (bexp_and_all (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! n)))) (dels (at_end (actions ! n)))))) True"
proof -
  { fix p
    assume p: "p \<notin> set (adds (at_end (actions ! n)))"
           "p \<in> set (dels (at_end (actions ! n)))"
    hence "p \<notin> planning_sem.plan_invs_during t" using planning_sem.snap_does_not_delete_inv end_scheduled by auto
    hence "planning_sem.locked_during t p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
    moreover
    have "PropLock p \<in> dom (map_of nta_vars)" using end_dels_in_dom p by auto
    ultimately
    have "v (PropLock p) = Some 0" using locked unfolding int_of_nat_def by simp
    hence "v_ending (PropLock p) = Some 0" unfolding v_ending 
      apply (subst map_upds_apply_nontin, fastforce)
      apply (subst map_upds_apply_nontin, fastforce)
      by simp
    hence "Simple_Expressions.check_bexp v_ending (is_prop_lock_ab 0 p) True" 
      unfolding is_prop_lock_ab_def 
      apply (subst check_bexp_simps)
      apply (subst is_val_simps)+
      by simp
  } 
  hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! n)))) (dels (at_end (actions ! n))))). Simple_Expressions.check_bexp v_ending b True"  by auto
  thus ?thesis using check_bexp_all by blast
qed


lemma v_ending_bounded: "bounded (map_of nta_vars) v_ending" using v_ending_started v_started_bounded by simp

subsubsection \<open>Lvc_ended\<close>

lemma L_instant_ended: "L' = L[Suc n := Off (actions ! n)]" 
  and c_instant_ended: "c' = c(ActStart (actions ! n) := 0, ActEnd (actions ! n) := 0)" 
  using s' unfolding Lvc_ending leave_end_instant_def Let_def prod.case L_ending v_ending c_ending by simp+

lemma map_upds_override: 
  shows "f(x \<mapsto> y, xs [\<mapsto>] ys, x \<mapsto> z) = f(xs [\<mapsto>] ys, x \<mapsto> z)" 
proof (rule ext) 
  fix xa
  show "(f(x \<mapsto> y, xs [\<mapsto>] ys, x \<mapsto> z)) xa = (f(xs [\<mapsto>] ys, x \<mapsto> z)) xa"
    unfolding map_upds_def
  proof -
    show "((f(x \<mapsto> y) ++ map_of (rev (zip xs ys)))(x \<mapsto> z)) xa = ((f ++ map_of (rev (zip xs ys)))(x \<mapsto> z)) xa"
    proof (cases "x = xa")
      case True
      then show ?thesis by simp
    next
      case False
      have 2: "(f(x \<mapsto> y)) xa = f xa" using False by simp
      hence "((f(x \<mapsto> y) ++ map_of (rev (zip xs ys)))) xa = ((f ++ map_of (rev (zip xs ys)))) xa" 
        apply (cases "map_of (rev (zip xs ys)) xa")
         apply (subst map_add_find_left,simp)+
        using False apply simp
        apply (subst map_add_find_right,simp)+
        by blast
      thus ?thesis using False by fastforce
    qed
  qed
qed

lemma map_upds_twist':
  assumes "x \<notin> set ys"
      and "x \<notin> set zs"
  shows "f(xs [\<mapsto>] xs', x \<mapsto> y, ys [\<mapsto>] ys', zs [\<mapsto>] zs') = f(xs [\<mapsto>] xs', ys [\<mapsto>] ys', zs [\<mapsto>] zs', x \<mapsto> y)" using assms by auto


lemma v_instant_ended': "v' = v(
      map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))), 
      map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n))))),
      map PropVar (dels (at_end (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_end (actions ! n))))), 
      map PropVar (adds (at_end (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_end (actions ! n))))))" (is "v' = v(?ds1 [\<mapsto>] ?ds1', ?as1 [\<mapsto>] ?as1', ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2')")
proof -
  from s'
  have "(L', v', c') =  leave_end_instant n (L_ending, v_ending, c_ending)" using Lvc_ending by auto
  from this
  have "v' = v_ending(ActsActive \<mapsto> the (v_ending ActsActive) - 1, ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2')"
    unfolding leave_end_instant_def Let_def prod.case by blast
  hence "v' = v_ending(ActsActive \<mapsto> the (v ActsActive), ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2')" using v_ending_ActsActive by simp
  hence "v' = v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, ?ds1 [\<mapsto>] ?ds1', ?as1 [\<mapsto>] ?as1', ActsActive \<mapsto> the (v ActsActive), ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2')" unfolding v_ending by blast
  hence "v' = v(?ds1 [\<mapsto>] ?ds1', ?as1 [\<mapsto>] ?as1', ActsActive \<mapsto> the (v ActsActive), ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2')" using map_upds_override by metis
  hence 1: "v' = v(?ds1 [\<mapsto>] ?ds1', ?as1 [\<mapsto>] ?as1', ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2', ActsActive \<mapsto> the (v ActsActive))" 
    apply (subst (asm) map_upds_twist'[of ActsActive ?ds2 ?as2])
    by fastforce+
  have 2: "\<exists>x. v ActsActive = Some x" using v_bounded dom_map_of_nta_vars unfolding bounded_def by auto
  have 3: "(v (?ds1 [\<mapsto>] ?ds1', ?as1 [\<mapsto>] ?as1', ?ds2 [\<mapsto>] ?ds2', ?as2 [\<mapsto>] ?as2')) ActsActive = v ActsActive" 
    apply (subst map_upds_apply_nontin[of ActsActive ?as2], fastforce) 
    apply (subst map_upds_apply_nontin[of ActsActive ?ds2], fastforce) 
    apply (subst map_upds_apply_nontin[of ActsActive ?as1], fastforce) 
    apply (subst map_upds_apply_nontin[of ActsActive ?ds1], fastforce) 
    ..
  show ?thesis 
    apply (subst 1)
    apply (rule ext)
    subgoal for x
      apply (cases "x = ActsActive")
       apply (erule ssubst[of x])
       apply (subst 3)
      using 2 apply simp
      by auto
    done
qed

lemma L_ended_ending: "L' = L_ending[Suc n := Off (actions ! n)]" 
  and v_ended_ending: "v' = v_ending(ActsActive \<mapsto> the (v_ending ActsActive) - 1, map PropVar (dels (at_end (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_end (actions ! n))))), map PropVar (adds (at_end (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_end (actions ! n))))))" 
  and c_ended_ending: "c' = c_ending"
  using s' unfolding Lvc_ending leave_end_instant_def Let_def prod.case fst_conv snd_conv by simp+

lemma v_ended_bounded: "bounded (map_of nta_vars) v'"
proof (rule set_vars_bounded[OF set_vars_bounded[OF single_upd_bounded[OF v_ending_bounded] HOL.refl] v_ended_ending])
  show "map_of nta_vars ActsActive = Some (0, int (length actions))" using map_of_nta_vars_ActsActive by simp
  have 1: "the (v_ending ActsActive) = the (v ActsActive) + 1" unfolding v_ending 
    apply (subst map_upds_apply_nontin)
     apply fastforce
    apply (subst map_upds_apply_nontin)
     apply fastforce
    by simp
  moreover
  have "the (v ActsActive) < length actions" using active card_action_set
      planning_sem.active_before_less_if_scheduled[OF start_scheduled act_n_in_actions] by simp
  ultimately
  show "the (v_ending ActsActive) - 1 \<le> int (length actions)" by simp
  show "0 \<le> the (v_ending ActsActive) - 1" apply (subst 1) apply (subst active) by simp
  show "\<forall>x\<in>set (map PropVar (dels (at_end (actions ! n)))). \<exists>l u. map_of nta_vars x = Some (l, u) \<and> l \<le> 0 \<and> 0 \<le> u"
    apply (intro ballI exI conjI)
        apply (rule map_of_nta_vars_action_end_del)
         apply (rule act_n_in_actions)
      by simp+
  show "\<forall>x\<in>set (map PropVar (adds (at_end (actions ! n)))). \<exists>l u. map_of nta_vars x = Some (l, u) \<and> l \<le> 1 \<and> 1 \<le> u"
    apply (intro ballI exI conjI)
      apply (rule map_of_nta_vars_action_end_add)
       apply (rule act_n_in_actions)
    by simp+
qed


subsubsection \<open>Post-conditions\<close>

lemma L_ended_len: "length L' = Suc (length actions)" using L_instant_ended L_len by auto

lemma v_ended_planning_state: "v' PlanningLock = Some 1" unfolding v_instant_ended' using planning_state 
  apply (subst map_upds_apply_nontin, fastforce)+
  by blast

lemma v_ended_instant_executed_loc: "\<forall>i \<le> n. (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L' ! Suc i = (Off (actions ! i))" 
  apply (intro allI impI, elim conjE)
  subgoal for i
    apply (cases "i = n")
    unfolding L_instant_ended
    subgoal apply simp using nth_list_update_eq[of "Suc n" L] L_len n by simp
    using instant_executed_loc by auto
  done

lemma v_ended_locked: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = Some (int_of_nat (planning_sem.locked_during t p))"
  apply (intro allI impI)
  unfolding v_instant_ended'
  apply (subst map_upds_apply_nontin, fastforce)+
  using locked by simp

lemma v_ended_prop_state: "\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropVar p) = Some (instant_prev_updated_prop_state i p (Suc n))"
proof (intro allI impI)                                                                                                    
  fix p
  assume p: "PropVar p \<in> dom (map_of nta_vars)" 
  show "v' (PropVar p) = Some (instant_prev_updated_prop_state i p (Suc n))"
    unfolding v_instant_ended'
    apply (subst instant_prev_updated_prop_state_Suc[OF t start_scheduled end_scheduled n])
    apply (subst t)
    apply (subst instant_prev_updated_plan_state_seq_def[symmetric])
    apply (cases "p \<in> set (adds (at_end (actions !n)))")
     apply (subst map_upds_with_list_of)
      apply simp
     apply simp
    apply (subst map_upds_apply_nontin)
     apply fastforce
    apply (cases "p \<in> set (dels (at_end (actions ! n)))")
     apply (subst map_upds_with_list_of)
      apply simp
     apply simp
    apply (subst map_upds_apply_nontin)
    apply fastforce
    apply (cases "p \<in> set (adds (at_start (actions !n)))")
     apply (subst map_upds_with_list_of)
      apply simp
     apply simp
    apply (subst map_upds_apply_nontin)
     apply fastforce
    apply (cases "p \<in> set (dels (at_start (actions ! n)))")
     apply (subst map_upds_with_list_of)
      apply simp
     apply simp
    apply (subst map_upds_apply_nontin)
     apply fastforce
    apply (subst prop_state[THEN spec, THEN mp, OF p, simplified instant_prev_updated_prop_state_def])
    by auto
qed


lemma v_ended_acts_active: "v' ActsActive = Some (planning_sem.active_before t)" unfolding v_instant_ended' using active
  apply (subst map_upds_apply_nontin, fastforce)+
  by blast

lemma c_ended_instant_executed_time: "\<forall>i < Suc n. (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
      \<longrightarrow> c' (ActEnd (actions ! i)) = 0 \<and> c' (ActStart (actions ! i)) = 0"
  apply (intro allI impI, elim conjE)
  subgoal for i
    apply (erule less_SucE)
    unfolding c_instant_ended
    using nth_starts_unique[OF _ n] n
    using instant_executed_time a apply simp
    by simp
  done


lemma c_ended_instant_not_executed_time:  "\<forall>i < length actions. (Suc n) \<le> i \<and> is_instant_index t i
      \<longrightarrow> c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t) 
        \<and> c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
  apply (intro allI impI, elim conjE)
  apply (drule Suc_le_lessD)
  unfolding c_instant_ended 
  subgoal for i
  using instant_not_executed_time 
  using nth_starts_unique[of i, OF _ n]
  by auto
done

lemma c_ended_ending_start_time: "\<forall>i < length actions. is_ending_index t i
      \<longrightarrow> c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
  apply (intro allI impI)
  subgoal for i
    unfolding c_instant_ended
    using ending_start_time start_scheduled end_scheduled
    by auto
  done

lemma c_ended_ending_end_time:  "\<forall>i < length actions. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
      \<longrightarrow> c' (ActEnd (actions ! i)) = (0::real)"
  apply (intro allI impI)
  subgoal for i
    unfolding c_instant_ended
    using ending_end_time start_scheduled end_scheduled
    by auto
  done

lemma c_ended_starting_start_time: "\<forall>i < length actions. is_starting_index t i
      \<longrightarrow>  c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
  apply (intro allI impI)
  subgoal for i
    unfolding c_instant_ended
    using starting_start_time start_scheduled end_scheduled
    by auto
  done

lemma c_ended_starting_end_time: "\<forall>i < length actions. is_starting_index t i
      \<longrightarrow>  c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
  apply (intro allI impI)
  subgoal for i
    unfolding c_instant_ended
    using starting_end_time start_scheduled end_scheduled
    by auto
  done

lemma c_ended_other_start_time: "\<forall>i < length actions. is_not_happening_index t i
      \<longrightarrow> c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
  apply (intro allI impI)
  subgoal for i
    unfolding c_instant_ended
    using other_start_time start_scheduled end_scheduled
    by auto
  done


lemma c_ended_other_end_time: "\<forall>i < length actions. is_not_happening_index t i
      \<longrightarrow> c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
  apply (intro allI impI)
  subgoal for i
    unfolding c_instant_ended
    using other_end_time start_scheduled end_scheduled
    by auto
  done

subsubsection \<open>First transition\<close>
lemma steps_starting: "abs_renum.urge_bisim.A.steps [(L, v, c), (L_started, v_started, c_started)]"
proof (rule single_step_intro)
  obtain l b g a f r l' where
    t: "(l, b, g, a, f, r, l') = (\<lambda>(l, b, g, a, f, r, l'). (l, b, map conv_ac g, a, f, r, l')) (start_edge_spec (actions ! n))" 
  and t': "l = Off (actions ! n)"
     "b = bexp_and_all (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! n)))) (dels (at_start (actions ! n)))) @ map (is_prop_ab 1) (pre (at_start (actions ! n))))"
     "g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_start (actions ! n))) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_start (actions ! n))))"
     "a = Sil STR ''''"
     "f = inc_var 1 ActsActive # map (set_prop_ab 0) (dels (at_start (actions ! n))) @ map (set_prop_ab 1) (adds (at_start (actions ! n)))"
     "r = [ActStart (actions ! n)]"
     "l' = StartInstant (actions ! n)"
    unfolding start_edge_spec_def Let_def prod.case by blast
  have "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L_started, v_started, c_started\<rangle>"
  proof (rule non_t_step_intro)
    show "Internal (STR '''') \<noteq> Simple_Network_Language.label.Del" by simp
    show "Simple_Network_Language.bounded (map_of nta_vars) v" using v_bounded by simp
    show "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L_started, v_started, c_started\<rangle>" unfolding L_started v_started c_started
      unfolding abs_renum.sem_def
    proof (rule step_int[of l b g _ f r l' _ "Suc n", simplified TAG_def])
      show "(l, b, g, Sil STR '''', f, r, l') \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! (Suc n))"
        apply (subst t'(4)[symmetric])
        apply (subst conv_trans)
        using n actual_autos_alt apply simp
        using nth_auto_trans
        apply (subst nth_auto_trans)
        using n t by fast+
      show "l \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! Suc n) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). L ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
        apply (rule disjI2)
        apply (intro allI impI)
        subgoal for p
          apply (subst conv_committed)
           apply simp
          using no_committed
          by simp
        done
      show "Simple_Expressions.check_bexp v b True"
        unfolding t'
        apply (rule check_bexp_all_append)
        using v_pre_conds_sat v_lock_conds_sat by blast+
      show "c \<turnstile> g" 
      proof -
        have s_corr: "\<forall>a\<in>set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> at_start (actions ! n) = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
        proof (intro ballI impI, elim disjE)
          fix a
          assume a: "a \<in> set actions" "(t, at_start a) \<notin> planning_sem.happ_seq"
          consider "(t, at_end a) \<in> planning_sem.happ_seq" | "(t, at_end a) \<notin> planning_sem.happ_seq" by blast
          thus "c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)" 
            apply (cases)
            subgoal using ending_start_time a in_set_conv_nth by metis
            subgoal using other_start_time a in_set_conv_nth by metis
            done
        next
          fix a
          assume a: "a \<in> set actions" "at_start (actions ! n) = at_start a"
          thus "c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"  
            using instant_not_executed_time[THEN spec, THEN mp, OF n] start_scheduled end_scheduled unfolding nth_start_unique[OF a(1) n a(2)] by simp
        qed
        have e_corr: "\<forall>a\<in>set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> at_start (actions ! n) = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
        proof (intro ballI impI, elim disjE)
          fix a
          assume a: "a \<in> set actions" "(t, at_end a) \<notin> planning_sem.happ_seq"
          consider "(t, at_start a) \<in> planning_sem.happ_seq" | "(t, at_start a) \<notin> planning_sem.happ_seq" by blast
          thus "c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)" 
            apply cases
            subgoal using starting_end_time a unfolding in_set_conv_nth by blast
            subgoal using other_end_time a unfolding in_set_conv_nth by blast
            done
        next
          fix a
          assume a: "a \<in> set actions" "at_start (actions ! n) = at_end a"
          thus "c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)" using nth_start_end_disj n by blast
        qed
        have "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_start (actions ! n))))"
          using mutex_0_constraint_sat start_scheduled s_corr e_corr by blast
        moreover
        have "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_start (actions ! n))))"
          using mutex_eps_constraint_sat start_scheduled s_corr e_corr by blast
        ultimately
        show ?thesis unfolding t' 
          unfolding map_append
          by (auto intro: guard_append)
      qed
      show "\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c(ActStart (actions ! n) := 0) \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (L[Suc n := StartInstant (actions ! n)] ! p)" using conv_invs no_invs by simp
      show "L ! Suc n = l" unfolding t' using instant_not_executed_loc n start_scheduled end_scheduled by blast
      show "Suc n < length L" using L_len n by simp
      show "L[Suc n := StartInstant (actions ! n)] = L[Suc n := l']" unfolding t' by blast
      show "c(ActStart (actions ! n) := 0) = [r\<rightarrow>0]c" unfolding t' by simp
      show "is_upds v f (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))), map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n)))))))"
        unfolding t'
      proof -
        have v_some: "\<exists>x. v ActsActive = Some x" using v_bounded dom_map_of_nta_vars unfolding bounded_def by auto 
        have map_f_conv: "map (\<lambda>prop. (PropVar prop, exp.const n)) xs = map (set_var n) (map PropVar xs)" for xs and n by simp
        
        have 1:"is_upd v (ActsActive, binop plus_int (var ActsActive) (exp.const 1)) (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1))"  (is "is_upd v _ ?v")
         apply (subst is_upd_def)
         apply (intro exI conjI)
          apply (rule HOL.refl)
          apply (subst is_val_simps)+
          apply (rule exI[of _ "the (v ActsActive)"])
        apply (rule exI[of _ 1])
          apply (intro exI conjI)
            apply (rule HOL.refl)
          using v_some by simp+

        have 2: "is_upds (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1)) (map (set_prop_ab 0) (dels (at_start (actions ! n)))) (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))))) "
          unfolding set_prop_ab_def map_f_conv by (rule is_upds_set_vars_list_of)

        have 3: "is_upds (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))))) (map (set_prop_ab 1) (adds (at_start (actions ! n))))
            (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))),
            map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n)))))))" 
          unfolding set_prop_ab_def map_f_conv by (rule is_upds_set_vars_list_of)
        show "is_upds v ((ActsActive, binop plus_int (var ActsActive) (exp.const 1)) # map (set_prop_ab 0) (dels (at_start (actions ! n))) @ map (set_prop_ab 1) (adds (at_start (actions ! n))))
            (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))),
             map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n)))))))"
          apply (rule is_upds.intros)
          apply (rule 1)
          apply (rule is_upds_appendI)
           apply (rule 2)
          by (rule 3)
      qed
      show "bounded (map_of nta_vars) (v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1, map PropVar (dels (at_start (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_start (actions ! n))))), map PropVar (adds (at_start (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_start (actions ! n)))))))"
        unfolding v_started[symmetric]
        using v_started_bounded by simp
    qed
  qed
  thus "(case (L, v, c) of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (L_started, v_started, c_started)" by auto
qed

subsubsection \<open>Second transition\<close>

lemma steps_ending: "abs_renum.urge_bisim.A.steps [(L_started, v_started, c_started), (L_ending, v_ending, c_ending)]"
proof (rule single_step_intro)
  obtain l b g a f r l' where
    t: "(l, b, g, a, f, r, l') = (\<lambda>(l, b, g, a, f, r, l'). (l, b, map conv_ac g, a, f, r, l')) (instant_trans_edge_spec (actions ! n))" 
  and t': "l = StartInstant (actions ! n)"
     "b = bexp.true"
     "g = map conv_ac (l_dur_spec (actions ! n)
          @ u_dur_spec (actions ! n)
          @ map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))"
     "a = Sil STR ''''"
     "f = []"
     "r = [ActEnd (actions ! n)]"
     "l' = EndInstant (actions ! n)"
    unfolding instant_trans_edge_spec_def Let_def prod.case by blast

  have "abs_renum.sem \<turnstile> \<langle>L_started, v_started, c_started\<rangle> \<rightarrow> \<langle>L_ending, v_ending, c_ending\<rangle>"
  proof (rule non_t_step_intro)
    show "Simple_Network_Language.bounded (map_of nta_vars) v_started" using v_started_bounded .
    show "Internal (STR '''') \<noteq> Simple_Network_Language.label.Del" by simp
    show "abs_renum.sem \<turnstile> \<langle>L_started, v_started, c_started\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L_ending, v_ending, c_ending\<rangle>" unfolding L_ending_started v_ending_started c_ending_started
      unfolding abs_renum.sem_def
    proof (rule step_int[of l b g _ f r l' _ "Suc n", simplified TAG_def])
      show "(l, b, g, Sil STR '''', f, r, l') \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! (Suc n))"
        apply (subst t'(4)[symmetric])
        apply (subst conv_trans)
        using n actual_autos_alt apply simp
        using nth_auto_trans
        apply (subst nth_auto_trans)
        using n t by fast+
      show "l \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! Suc n) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). L_started ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
        apply (rule disjI2)
        apply (intro allI impI)
        subgoal for p
          apply (subst conv_committed)
           apply simp
          using no_committed
          by simp
        done
      show "Simple_Expressions.check_bexp v_started b True" 
        unfolding t' by rule
      show "c_started \<turnstile> g" 
      proof -
        have 1: "c_started (ActStart (actions ! n)) = 0" unfolding c_started by auto
        have "c_started \<turnstile> map conv_ac (l_dur_spec (actions ! n))" 
          using planning_sem.instant_acts_sat_dur_const[OF act_n_in_actions end_scheduled start_scheduled]
          1 l_dur_spec_sat_if by simp
        moreover
        have "c_started \<turnstile> map conv_ac (u_dur_spec (actions ! n))" 
          using planning_sem.instant_acts_sat_dur_const[OF act_n_in_actions end_scheduled start_scheduled]
          1 u_dur_spec_sat_if by simp
        moreover
        have "c_started \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))))" 
             "c_started \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))"
        proof -
          have s_corr: "\<forall>a\<in>set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_start a \<longrightarrow> c_started (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
          proof (intro ballI impI, elim disjE)
            fix a
            assume "a \<in> set actions" "(t, at_start a) \<notin> planning_sem.happ_seq"
            thus "c_started (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)" 
              apply (cases "(t, at_end a) \<in> planning_sem.happ_seq")
              subgoal using c_started_ending_start_time unfolding in_set_conv_nth by blast
              subgoal using c_started_other_start_time unfolding in_set_conv_nth by blast
              done
          next
            fix a
            assume a: "a \<in> set actions" "at_end (actions ! n) = at_start a"
            show "c_started (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)" 
              using nth_end_start_disj[OF a(1) n] a(2) by simp
          qed
          have e_corr: "\<forall>a\<in>set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_end a \<longrightarrow> c_started (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
          proof (intro ballI impI, elim disjE)
            fix a
            assume "a \<in> set actions" "(t, at_end a) \<notin> planning_sem.happ_seq"
            thus "c_started (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)" 
              apply (cases "(t, at_start a) \<in> planning_sem.happ_seq")
              subgoal using c_started_starting_end_time unfolding in_set_conv_nth by blast
              subgoal using c_started_other_end_time unfolding in_set_conv_nth by blast
              done
          next
            fix a
            assume a: "a \<in> set actions" "at_end (actions ! n) = at_end a"
            show "c_started (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)" 
              using nth_end_unique[OF a(1) n a(2)] c_started_act_n_clocks by blast
          qed
          show "c_started \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))))" 
            apply (rule mutex_0_constraint_sat)
            using end_scheduled s_corr e_corr by blast+
          show "c_started \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))" 
            apply (rule mutex_eps_constraint_sat)
            using end_scheduled s_corr e_corr by blast+
        qed
        ultimately
        show "c_started \<turnstile> g"
          unfolding t' map_append 
          apply (elim guard_append)
          by assumption
      qed
      show "\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c_started(ActEnd (actions ! n) := 0) \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (L_started[Suc n := EndInstant (actions ! n)] ! p)"
        apply (intro allI impI)
        apply (subst no_invs, simp)
        by simp
      show "L_started ! Suc n = l" unfolding t' L_started using L_len n by auto
      show "Suc n < length L_started"  using L_started_length n by auto
      show "L_started[Suc n := EndInstant (actions ! n)] = L_started[Suc n := l']" unfolding t' by blast
      show "c_started(ActEnd (actions ! n) := 0) = [r\<rightarrow>0]c_started" unfolding t' by simp
      show "is_upds v_started f v_started" unfolding t' by rule
      show "bounded (map_of nta_vars) v_started" using v_started_bounded by simp
    qed
  qed
  thus "(case (L_started, v_started, c_started) of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (L_ending, v_ending, c_ending)" by simp
qed

subsubsection \<open>Third transition\<close>

lemma steps_end: "abs_renum.urge_bisim.A.steps [(L_ending, v_ending, c_ending), (L', v', c')]"
proof (rule single_step_intro)
  obtain l b g a f r l' where
    t: "(l, b, g, a, f, r, l') = (\<lambda>(l, b, g, a, f, r, l'). (l, b, map conv_ac g, a, f, r, l')) (end_edge_spec (actions ! n))" 
  and t': "l = EndInstant (actions ! n)"
     "b = bexp_and_all (
            map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_end (actions ! n)))) (dels (at_end (actions ! n)))) 
          @ map (is_prop_ab 1) (pre (at_end (actions ! n))))"
     "g = map conv_ac []"
     "a = Sil STR ''''"
     "f = (inc_var (-1) ActsActive) # map (set_prop_ab 0) (dels (at_end (actions ! n))) @ map (set_prop_ab 1) (adds (at_end (actions ! n)))"
     "r = []"
     "l' = Off (actions ! n)"
    unfolding end_edge_spec_def Let_def prod.case by simp

  have "abs_renum.sem \<turnstile> \<langle>L_ending, v_ending, c_ending\<rangle> \<rightarrow> \<langle>L', v', c'\<rangle>"
  proof (rule non_t_step_intro)
    show "Internal (STR '''') \<noteq> Simple_Network_Language.label.Del" by simp
    show "Simple_Network_Language.bounded (map_of nta_vars) v_ending" using v_ending_bounded by simp
    show "abs_renum.sem \<turnstile> \<langle>L_ending, v_ending, c_ending\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L', v', c'\<rangle>" unfolding L_ended_ending v_ended_ending c_ended_ending
      unfolding abs_renum.sem_def
    proof (rule step_int[of l b g _ f r l' _ "Suc n", simplified TAG_def])
      show "(l, b, g, Sil STR '''', f, r, l') \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! (Suc n))"
        apply (subst t'(4)[symmetric])
        apply (subst conv_trans)
        using n actual_autos_alt apply simp
        using nth_auto_trans
        apply (subst nth_auto_trans)
        using n t by fast+
      show "l \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! Suc n) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). L_ending ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
        apply (rule disjI2)
        apply (intro allI impI)
        subgoal for p
          apply (subst conv_committed)
           apply simp
          using no_committed
          by simp
        done
      show "Simple_Expressions.check_bexp v_ending b True" 
        unfolding t' 
        apply (rule check_bexp_all_append)
        using v_ending_pre_conds_sat v_ending_lock_conds_sat by blast+
      show "c_ending \<turnstile> g"
        unfolding t' by simp
      show "\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c_ending \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (L_ending[Suc n := Off (actions ! n)] ! p)"
        apply (intro allI impI)
        apply (subst no_invs) 
         apply satx
        by simp
      show "L_ending ! Suc n = l" unfolding t' using n L_ending_length unfolding L_ending by simp
      show "Suc n < length L_ending" using n L_ending_length by auto
      show "L_ending[Suc n := Off (actions ! n)] = L_ending[Suc n := l']" unfolding t' by blast
      show "c_ending = [r\<rightarrow>0]c_ending" unfolding t' by auto
      show "is_upds v_ending f (v_ending(ActsActive \<mapsto> the (v_ending ActsActive) - 1, map PropVar (dels (at_end (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_end (actions ! n))))), map PropVar (adds (at_end (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_end (actions ! n)))))))"
      unfolding t'
      proof -
        have v_some: "\<exists>x. v_ending ActsActive = Some x" using v_ending_bounded dom_map_of_nta_vars unfolding bounded_def by auto 
        have map_f_conv: "map (\<lambda>prop. (PropVar prop, exp.const n)) xs = map (set_var n) (map PropVar xs)" for xs and n by simp
        
        have 1:"is_upd v_ending (ActsActive, binop plus_int (var ActsActive) (exp.const (-1))) (v_ending(ActsActive \<mapsto> plus_int (the (v_ending ActsActive)) (-1)))"  (is "is_upd v_ending _ ?v")
         apply (subst is_upd_def)
         apply (intro exI conjI)
          apply (rule HOL.refl)
          apply (subst is_val_simps)+
          apply (rule exI[of _ "the (v_ending ActsActive)"])
        apply (rule exI[of _ "-1"])
          apply (intro exI conjI)
            apply (rule HOL.refl)
          using v_some by simp+

        have 2: "is_upds ?v (map (set_prop_ab 0) (dels (at_end (actions ! n)))) (?v( map PropVar (dels (at_end (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_end (actions ! n)))))))" (is "is_upds ?v  _ ?v'")
          unfolding set_prop_ab_def map_f_conv by (rule is_upds_set_vars_list_of)

        have 3: "is_upds ?v' (map (set_prop_ab 1) (adds (at_end (actions ! n)))) (?v'(map PropVar (adds (at_end (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_end (actions ! n)))))))" 
          unfolding set_prop_ab_def map_f_conv by (rule is_upds_set_vars_list_of)
        show "is_upds v_ending ((ActsActive, binop plus_int (var ActsActive) (exp.const (- 1))) # map (set_prop_ab 0) (dels (at_end (actions ! n))) @ map (set_prop_ab 1) (adds (at_end (actions ! n))))
     (v_ending(ActsActive \<mapsto> the (v_ending ActsActive) - 1, map PropVar (dels (at_end (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_end (actions ! n))))), map PropVar (adds (at_end (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_end (actions ! n)))))))"
          apply (rule is_upds.intros)
          apply (rule 1)
          apply (rule is_upds_appendI)
           apply (rule 2)
          using 3 by simp
      qed
      show "Simple_Network_Language.bounded (map_of nta_vars) (v_ending(ActsActive \<mapsto> the (v_ending ActsActive) - 1, map PropVar (dels (at_end (actions ! n))) [\<mapsto>] list_of 0 (length (map PropVar (dels (at_end (actions ! n))))), map PropVar (adds (at_end (actions ! n))) [\<mapsto>] list_of 1 (length (map PropVar (adds (at_end (actions ! n)))))))"
        unfolding v_ended_ending[symmetric]
        using v_ended_bounded by blast
    qed
  qed
  thus "(case (L_ending, v_ending, c_ending) of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (L', v', c')" by force
qed

lemma instant_action_steps_if: "abs_renum.urge_bisim.A.steps ((L, v, c) # apply_snap_action n (L, v, c))"
  unfolding apply_snap_action_def seq_apply.simps
  apply (subst s')
  apply (subst Lvc_ending)
  apply (subst Lvc_started)
  apply (rule steps_prepend)
  apply (rule steps_prepend)
  apply (rule steps_prepend)
     apply (rule)
    apply (rule steps_end)
   apply (rule steps_ending)
  by (rule steps_starting)
end (* for a single instant action n *)

definition "single_snap_pres n L v c \<equiv> 
let 
  n_conds = (n < length actions) \<and> is_instant_index t i;
  L_conds = (length L = Suc (length actions));
  v_conds = (bounded (map_of nta_vars) v) \<and> (v PlanningLock = Some 1);

  instant_executed_loc = (\<forall>i < n. (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
        \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  instant_not_executed_loc = (\<forall>i < length actions. n \<le> i \<and> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
        \<longrightarrow> L ! Suc i = (Off (actions ! i)));

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (planning_sem.locked_during t p)));
  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_prev_updated_prop_state i p n));
  active = (v ActsActive = Some (planning_sem.active_before t));
  
  instant_executed_time = (\<forall>i < n. is_instant_index t i
      \<longrightarrow> (c (ActEnd (actions ! i)) = 0) \<and> (c (ActStart (actions ! i)) = 0));
  instant_not_executed_time =  (\<forall>i < length actions. n \<le> i \<and> is_instant_index t i
      \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t) 
        \<and> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t));
  
  ending_start_time = (\<forall>i < length actions. is_ending_index t i
      \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t));
  ending_end_time =  (\<forall>i < length actions. is_ending_index t i
      \<longrightarrow> c (ActEnd (actions ! i)) = 0);
  
  starting_start_time = (\<forall>i < length actions. is_starting_index t i
      \<longrightarrow>  c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t));
  starting_end_time = (\<forall>i < length actions. is_starting_index t i
      \<longrightarrow>  c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t));
  
  other_start_time = (\<forall>i < length actions. is_not_happening_index t i
      \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t));
  other_end_time = (\<forall>i < length actions. is_not_happening_index t i
      \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t))
in n_conds \<and> L_conds \<and> v_conds 
  \<and> instant_executed_loc \<and> instant_not_executed_loc 
  \<and> locked \<and> prop_state \<and> active 
  \<and> instant_executed_time \<and> instant_not_executed_time 
  \<and> ending_start_time \<and> ending_end_time 
  \<and> starting_start_time \<and> starting_end_time 
  \<and> other_start_time \<and> other_end_time"

definition "single_snap_posts n L v c \<equiv> 
let
  L_conds = (length L = Suc (length actions));
  v_conds = ((bounded (map_of nta_vars) v) \<and> (v PlanningLock = Some 1));

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (planning_sem.locked_during t p)));
  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_prev_updated_prop_state i p n));
  active = (v ActsActive = Some (planning_sem.active_before t));

  instant_executed_loc = (\<forall>i \<le> n. (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
        \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  instant_not_executed_loc = (\<forall>i < length actions. n < i \<and> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
        \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  
  instant_executed_time = (\<forall>i \<le> n. is_instant_index t i
      \<longrightarrow> (c (ActEnd (actions ! i)) = 0) \<and> (c (ActStart (actions ! i)) = 0));
  instant_not_executed_time =  (\<forall>i < length actions. n < i \<and> is_instant_index t i
      \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t) 
        \<and> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t));
  
  ending_start_time = (\<forall>i < length actions. is_ending_index t i
      \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t));
  ending_end_time =  (\<forall>i < length actions. is_ending_index t i
      \<longrightarrow> c (ActEnd (actions ! i)) = 0);
  
  starting_start_time = (\<forall>i < length actions. is_starting_index t i
      \<longrightarrow>  c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t));
  starting_end_time = (\<forall>i < length actions. is_starting_index t i
      \<longrightarrow>  c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t));
  
  other_start_time = (\<forall>i < length actions. is_not_happening_index t i
      \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t));
  other_end_time = (\<forall>i < length actions. is_not_happening_index t i
      \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t))
in undefined"

context (* for all instant actions at a timepoint *)
  fixes L v c 
  assumes L_len: "length L = Suc (length actions)"
      and v_bounded: "bounded (map_of nta_vars) v"
      and planning_state: "v PlanningLock = Some 1"

      and instant_loc: "\<forall>i < length actions. is_instant_index t i
          \<longrightarrow> L ! Suc i = (Off (actions ! i))"

      and locked: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (planning_sem.locked_during t p))"
      and prop_state: "\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_prev_updated_prop_state i p n)"
      and active: "v ActsActive = Some (planning_sem.active_before t)"

      and instant_time:  "\<forall>i < length actions.  is_instant_index t i
            \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t) 
              \<and> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"

      and ending_start_time: "\<forall>i < length actions. is_ending_index t i
            \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and ending_end_time:  "\<forall>i < length actions. is_ending_index t i
            \<longrightarrow> c (ActEnd (actions ! i)) = (0::real)"

      and starting_start_time: "\<forall>i < length actions. is_starting_index t i
            \<longrightarrow>  c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and starting_end_time: "\<forall>i < length actions. is_starting_index t i
            \<longrightarrow>  c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"

      and other_start_time: "\<forall>i < length actions. is_not_happening_index t i
            \<longrightarrow> c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and other_end_time: "\<forall>i < length actions. is_not_happening_index t i
            \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
begin
term "apply_instant_actions (filter (\<lambda>n. at_start (actions ! n) \<in> h \<and> at_end (actions ! n) \<in> h) [0..<length actions]) (L, v, c)"

(* Prove pre- and post-conditions using seq_apply'' of apply_instant_action *)

term "filter (is_instant_index t) [0..<length actions]"

term "seq_apply'' (map apply_snap_action (instant_indices_before t (length actions)))"

thm seq_apply''_pre_post_induct_Cons
(* The rule depends on the assumption that the list is not empty. We need a more general rule that 
work with empty lists and ext_seq' *)
term instant_actions_before
end




end (* context for a timepoint t and its snap-actions *)


lemma apply_happening:
  assumes "n < length (htpl \<pi>)"
      and "P s"
    shows "abs_renum.urge_bisim.A.steps (s # apply_nth_happening n s)"
  sorry

lemma apply_happenings:
  assumes "n < length (htpl \<pi>)"
      and "P s"
    shows "abs_renum.urge_bisim.A.steps (s # delay_and_apply n s)"
  sorry


thm plan_steps_def[simplified Let_def ext_seq''_alt]

lemma plan_steps_are_steps: "abs_renum.urge_bisim.A.steps plan_steps"
  unfolding plan_steps_def Let_def
  sorry


lemma end_of_steps_is_run: "abs_renum.urge_bisim.A.run (goal_run (last plan_steps))" sorry

lemma "abs_renum.urge_bisim.A.run (goal_run goal_state)" sorry


lemma "abs_renum.urge_bisim.A.steps (undefined # undefined # undefined)"
  find_theorems intro name: "steps"
  apply (rule abs_renum.urge_bisim.A.stepsI)
  using abs_renum.urge_bisim.A.steps.intros
  sorry

lemma state_seq_sat_goal: "ev (holds (\<lambda>(L, s, _). check_sexp (sexp.loc 0 GoalLocation) L (the \<circ> s))) plan_state_sequence"
  find_theorems intro name: "ev" sorry

find_theorems name: "abs_renum*steps"

lemma state_seq_is_run: "abs_renum.urge_bisim.A.run plan_state_sequence"
  find_theorems name: "run*con"
  apply (rule abs_renum.urge_bisim.A.extend_run'[where zs = plan_state_sequence])
  unfolding plan_state_sequence_def
  sorry

find_theorems name: "Simple_Network_Language_Model_Checking.step_u'.intros"

lemma "abs_renum.sem, abs_renum.a\<^sub>0 \<Turnstile> form"
proof -
  show "?thesis" unfolding form_alt 
    unfolding models_def 
    unfolding formula.case
    find_theorems name: "abs_renumEx_ev"
    apply (subst abs_renum.urge_bisim.A.Ex_ev_def)
    find_theorems (200) name: "abs_renum*run"
    find_theorems name: deadlock
    apply (rule exI)
    apply (rule conjI)
     apply (coinduction rule: abs_renum.urge_bisim.A.run.coinduct) sorry
  qed

(* Functions from actions to locations and clocks, and from propositions to variables must be fixed
  later. Renamings like in Munta. *)

(* Lists are used to implement sets. Lift this to a higher level. *)

(* Do the conversion to strings later, as renamings *)
(* Right now, do the conversion using the actual types as placeholders.
Propositions and actions are not renamed in variables  *)

end
end
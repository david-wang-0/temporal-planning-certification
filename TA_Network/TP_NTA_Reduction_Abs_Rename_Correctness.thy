theory TP_NTA_Reduction_Abs_Rename_Correctness
  imports TP_NTA_Reduction_Abs_Rename
          "Temporal_Planning_Base.Sequences"
          "Temporal_Planning_Base.ListMisc"
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
      (\<lambda>a. (if planning_sem.is_ending_action t a then 1 else 0)) 
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

lemma partially_updated_locked_before_0_is_locked_before:
  "partially_updated_locked_before t p 0 = planning_sem.locked_before t p"
  unfolding partially_updated_locked_before_def
  by simp

lemma partially_updated_locked_before_ran: "partially_updated_locked_before t p n \<le> length actions" 
  using planning_sem.locked_before_ran unfolding distinct_card[OF distinct_actions]
  using partially_updated_locked_before_inv_mono'[of 0 n] unfolding partially_updated_locked_before_0_is_locked_before 
  using order_trans by blast

find_theorems "[?n..<?m] @ [?m..<?o]"

lemma partially_updated_locked_before_inv:
  assumes "n \<le> m"
      and "\<And>i a. n \<le> i \<Longrightarrow> i < m \<Longrightarrow> a = actions ! i \<Longrightarrow> \<not>(planning_sem.is_ending_action t a)" 
  shows "partially_updated_locked_before t p n = partially_updated_locked_before t p m"
proof (cases "n = m")
  case True
  then show ?thesis by simp
next
  have 0: "\<forall>x \<in> set (map (\<lambda>a. if planning_sem.is_ending_action t a then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<m]))). x = 0"
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

lemma partially_updated_locked_before_alt: 
  assumes "n < length actions"
  shows "partially_updated_locked_before t p n = planning_sem.locked_during t p 
+ sum_list (map 
      (\<lambda>a. (if planning_sem.is_ending_action t a then (1::nat) else 0)) 
      (filter 
        (\<lambda>a. p \<in> set (over_all a)) 
        (map (\<lambda>n. actions ! n) [n..<length actions])))"
proof -
  have 1: "foldr (+) (map (\<lambda>a. if planning_sem.is_ending_action t a then (1::nat) else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n]))) 0 +
  foldr (+) (map (\<lambda>a. if planning_sem.is_ending_action t a then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0 =
  foldr (+) (map (\<lambda>a. if planning_sem.is_ending_action t a then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n])))
   (foldr (+) (map (\<lambda>a. if planning_sem.is_ending_action t a then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0)"
    using foldr_assoc[symmetric, where xs = "(map (\<lambda>a. if planning_sem.is_ending_action t a then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n])))" 
        and n = "foldr (+) (map (\<lambda>a. if planning_sem.is_ending_action t a then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0"]
    by simp
  have d1: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) actions)" using distinct_actions by auto
  have d2: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.distinct_action_list by simp
  have s: "set (filter (\<lambda>a. p \<in> set (over_all a)) actions) = set (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.set_action_list by auto


  have "(\<Sum>a\<leftarrow>planning_sem.locked_by p. if planning_sem.is_ending_action t a then (1::nat) else 0) 
      = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n]). if planning_sem.is_ending_action t a then 1 else 0) 
      + (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if planning_sem.is_ending_action t a then 1 else 0)"
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

definition "locked_during_and_by t a p \<equiv> planning_sem.locked_during t p + (if (p \<in> (set o over_all) a) then 1 else 0)"

text \<open>Propositional states of the plan converted to functions\<close>

definition "prop_state S p \<equiv> if (p \<in> S) then 1 else 0"

lemma prop_state_simps[simp]:
  "p \<in> S \<Longrightarrow> prop_state S p = 1"
  "p \<notin> S \<Longrightarrow> prop_state S p = 0" unfolding prop_state_def by simp+

lemma prop_stateD:
  "prop_state S p = (1::int) \<Longrightarrow> p \<in> S"
  "prop_state S p = (0::int) \<Longrightarrow> p \<notin> S"  
  by (cases "p \<in> S") auto

lemma prop_state_cases:
  assumes "prop_state S p = (1::int) \<Longrightarrow> thesis"
      and "prop_state S p = (0::int) \<Longrightarrow> thesis"
    shows thesis using assms unfolding prop_state_def by argo

lemma prop_state_iff:
  "p \<in> S \<longleftrightarrow> prop_state S p = (1::int)"
  "p \<notin> S \<longleftrightarrow> prop_state S p = (0::int)" using prop_stateD by fastforce+


definition "is_instant_index t n \<equiv> planning_sem.is_instant_action t (actions ! n)"
 
definition "is_starting_index t n \<equiv> planning_sem.is_starting_action t (actions ! n)"

definition "is_ending_index t n \<equiv> planning_sem.is_ending_action t (actions ! n)"

definition "is_not_happening_index t n \<equiv> planning_sem.is_not_happening_action t (actions ! n)"

lemmas index_case_defs = is_instant_index_def is_starting_index_def is_ending_index_def is_not_happening_index_def

lemma index_case_dests: 
  "is_instant_index t n \<Longrightarrow> planning_sem.is_instant_action t (actions ! n)"
  "is_starting_index t n \<Longrightarrow> planning_sem.is_starting_action t (actions ! n)"
  "is_ending_index t n \<Longrightarrow> planning_sem.is_ending_action t (actions ! n)"
  "is_not_happening_index t n \<Longrightarrow> planning_sem.is_not_happening_action t (actions ! n)"
  using index_case_defs by simp+
  
lemma time_index_action_index_happening_cases:
  assumes "i < length (htpl \<pi>)" 
      and "(\<And>n. n < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) n \<Longrightarrow> thesis)" 
          "(\<And>n. n < length actions \<Longrightarrow> is_ending_index (time_index \<pi> i) n \<Longrightarrow> thesis)" 
          "(\<And>n. n < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) n \<Longrightarrow> thesis)"
        shows thesis
  apply (rule planning_sem.time_index_action_happening_cases)
     apply (rule assms(1))
  unfolding set_conv_nth
  using assms unfolding is_starting_index_def is_ending_index_def is_instant_index_def 
  by blast+

lemma index_case_dests_disj:
  "is_instant_index t n \<Longrightarrow> \<not>is_starting_index t n \<and> \<not>is_ending_index t n \<and> \<not>is_not_happening_index t n"
  "is_starting_index t n \<Longrightarrow> \<not>is_instant_index t n \<and> \<not>is_ending_index t n \<and> \<not>is_not_happening_index t n"
  "is_ending_index t n \<Longrightarrow> \<not>is_instant_index t n \<and> \<not>is_starting_index t n \<and> \<not>is_not_happening_index t n"
  "is_not_happening_index t n \<Longrightarrow> \<not>is_instant_index t n \<and> \<not>is_starting_index t n \<and> \<not>is_ending_index t n"
  using planning_sem.action_happening_disj unfolding index_case_defs by blast+
  

lemma index_case_disj: 
  "\<not>(is_instant_index t n \<and> is_starting_index t n)"
  "\<not>(is_instant_index t n \<and> is_ending_index t n)"
  "\<not>(is_instant_index t n \<and> is_not_happening_index t n)"
  "\<not>(is_starting_index t n \<and> is_ending_index t n)"
  "\<not>(is_starting_index t n \<and> is_not_happening_index t n)"
  "\<not>(is_ending_index t n \<and> is_not_happening_index t n)"
  "is_instant_index t n \<Longrightarrow> \<not>is_starting_index t n \<and> \<not>is_ending_index t n \<and> \<not>is_not_happening_index t n"
  "is_starting_index t n \<Longrightarrow> \<not>is_instant_index t n \<and> \<not>is_ending_index t n \<and> \<not>is_not_happening_index t n"
  "is_ending_index t n \<Longrightarrow> \<not>is_instant_index t n \<and> \<not>is_starting_index t n \<and> \<not>is_not_happening_index t n"
  "is_not_happening_index t n \<Longrightarrow> \<not>is_instant_index t n \<and> \<not>is_starting_index t n \<and> \<not>is_ending_index t n"
  using planning_sem.action_happening_disj unfolding index_case_defs by blast+


context 
  fixes i::nat
assumes i: "i < length (htpl \<pi>)"
begin


(* before anything happens *)
definition "prop_state_before_happ \<equiv> prop_state (planning_sem.plan_state_seq i)"
(* after instant actions happen *)
definition "prop_state_after_instant_happ \<equiv> prop_state (planning_sem.inst_upd_state i)"
(* after instant actions and starts happen *)
definition "prop_state_after_instant_start_happ \<equiv> prop_state (planning_sem.inst_start_upd_state i)"
(* after every snap action has been applied *)
definition "prop_state_after_happ \<equiv> prop_state (planning_sem.upd_state i)"

(* Like application of effects when lists are used to implement sets *)
definition "apply_snaps hs s \<equiv> s - \<Union> ((set o dels) ` hs) \<union> \<Union> ((set o adds) ` hs)"

(* Intermediate prop states *)
definition "actions_before n \<equiv>
  map ((!) actions) [0..<n]
"

definition "instant_actions_before n \<equiv> 
  let 
    instant_actions_before = filter (planning_sem.is_instant_action (time_index \<pi> i)) (actions_before n)
  in (set instant_actions_before)"

definition "instant_starts_before n \<equiv> at_start ` instant_actions_before n"

definition "instant_ends_before n \<equiv> at_end ` instant_actions_before n"

definition "instant_snaps_before n \<equiv> instant_starts_before n \<union> instant_ends_before n"

definition "apply_instant_snaps_before n s \<equiv> apply_snaps (instant_snaps_before n) s"

definition "instant_part_updated_plan_state_seq n \<equiv> apply_instant_snaps_before n (planning_sem.plan_state_seq i)"

definition "instant_part_updated_prop_state n \<equiv> prop_state (instant_part_updated_plan_state_seq n)"

definition "instant_snaps_before_and_start n = instant_starts_before (Suc n) \<union> instant_ends_before n"

definition "apply_instant_snaps_before_and_start n = apply_snaps (instant_snaps_before_and_start n)"

definition "instant_intermediate_plan_state_seq n \<equiv> apply_instant_snaps_before_and_start n (planning_sem.plan_state_seq i)"

definition "instant_intermediate_prop_state n \<equiv> prop_state (instant_intermediate_plan_state_seq n)"

(* starting *)
definition "starting_actions_before n \<equiv> set (filter (planning_sem.is_starting_action (time_index \<pi> i)) (actions_before n))"

definition "starting_snaps_before n = at_start ` starting_actions_before n"

definition "apply_starting_snaps_before n s \<equiv> apply_snaps (starting_snaps_before n) s"

definition "starting_part_updated_state_seq n \<equiv> apply_starting_snaps_before n (planning_sem.inst_upd_state i)"

definition "starting_part_updated_prop_state n \<equiv> prop_state (starting_part_updated_state_seq n)"

(* ending *)
definition "ending_actions_before n \<equiv> set (filter (planning_sem.is_ending_action (time_index \<pi> i)) (actions_before n))"

definition "ending_snaps_before n = at_end ` ending_actions_before n"

definition "apply_ending_snaps_before n s \<equiv>
  apply_snaps (ending_snaps_before n) s
"

definition "ending_part_updated_state_seq n \<equiv> apply_ending_snaps_before n (planning_sem.inst_start_upd_state i)"

definition "ending_part_updated_prop_state n \<equiv> prop_state (ending_part_updated_state_seq n)"

(*instant*)
lemma instant_actions_before_all_is_instant_actions: "instant_actions_before (length actions) = planning_sem.instant_actions_at (time_index \<pi> i)"
  unfolding instant_actions_before_def Let_def set_filter set_map set_upt planning_sem.instant_actions_at_def actions_before_def by simp

lemma instant_snaps_before_all_is_instant_snaps: "instant_snaps_before (length actions) = planning_sem.instant_snaps_at (time_index \<pi> i)"
  unfolding instant_snaps_before_def planning_sem.instant_snaps_at_def instant_ends_before_def instant_starts_before_def 
  using instant_actions_before_all_is_instant_actions by simp

lemma apply_instant_snaps_before_all_is_apply_instant_snaps: "apply_instant_snaps_before (length actions) s = planning_sem.app_effs (planning_sem.instant_snaps_at (time_index \<pi> i)) s"
  unfolding planning_sem.app_effs_def apply_instant_snaps_before_def Let_def instant_snaps_before_all_is_instant_snaps apply_effects_def apply_snaps_def by blast

lemma instant_actions_before_0_is_none: "instant_actions_before 0 = {}" 
  unfolding instant_actions_before_def Let_def actions_before_def by simp

lemma instant_snaps_before_0_is_none: "instant_snaps_before 0 = {}"
  unfolding instant_snaps_before_def instant_starts_before_def instant_ends_before_def instant_actions_before_0_is_none by blast

lemma apply_instant_snaps_before_0_is_id: "apply_instant_snaps_before 0 = id"
  unfolding apply_instant_snaps_before_def instant_snaps_before_0_is_none apply_snaps_def id_def by blast

(* starting *)

lemma starting_actions_before_all_is_starting_actions: 
  "starting_actions_before (length actions) = planning_sem.starting_actions_at (time_index \<pi> i)"
  unfolding starting_actions_before_def Let_def set_filter set_map set_upt 
    planning_sem.starting_actions_at_def actions_before_def by simp

lemma starting_snaps_before_all_is_starting_snaps: "starting_snaps_before (length actions) = planning_sem.starting_snaps_at (time_index \<pi> i)"
  unfolding starting_snaps_before_def planning_sem.starting_snaps_at_def  
  using starting_actions_before_all_is_starting_actions by simp

lemma apply_starting_snaps_before_all_is_apply_starting_snaps: "apply_starting_snaps_before (length actions) s = planning_sem.app_effs (planning_sem.starting_snaps_at (time_index \<pi> i)) s"
  unfolding planning_sem.app_effs_def apply_starting_snaps_before_def Let_def starting_snaps_before_all_is_starting_snaps apply_effects_def apply_snaps_def by blast

lemma starting_actions_before_0_is_none: "starting_actions_before 0 = {}"
  using starting_actions_before_def actions_before_def by auto

lemma starting_snaps_before_0_is_none: "starting_snaps_before 0 = {}" 
  using starting_snaps_before_def starting_actions_before_0_is_none by blast

lemma apply_starting_snaps_before_0_is_id: "apply_starting_snaps_before 0 = id"
  unfolding apply_starting_snaps_before_def apply_snaps_def starting_snaps_before_0_is_none by auto

(* ending - to do *)

definition "instant_indices_before n \<equiv> filter (is_instant_index (time_index \<pi> i)) [0..<n]"

definition "starting_indices_before n \<equiv> filter (is_starting_index (time_index \<pi> i)) [0..<n]"

definition "ending_indices_before n \<equiv> filter (is_ending_index (time_index \<pi> i)) [0..<n]"

lemma instant_actions_before_alt: "instant_actions_before n = set (map ((!) actions) (instant_indices_before n))"
  unfolding instant_actions_before_def instant_indices_before_def set_map set_filter 
    Let_def is_instant_index_def actions_before_def by blast

lemma instant_snaps_before_is_in_happ_seq: 
  assumes "n < length actions"
  shows "instant_snaps_before n \<subseteq> happ_at planning_sem.happ_seq (time_index \<pi> i)"
proof -
  have 1: "(!) actions ` {0..<n} \<subseteq> set actions" using assms by fastforce 
  { fix x
    assume "x \<in> instant_snaps_before n"
    then obtain a where
      "x = at_start a \<or> x = at_end a"
      "a \<in> set actions"
      "(time_index \<pi> i, at_start a) \<in> planning_sem.happ_seq \<and> (time_index \<pi> i, at_end a) \<in> planning_sem.happ_seq"
      unfolding instant_snaps_before_def instant_actions_before_def instant_starts_before_def instant_ends_before_def Let_def
      set_filter set_map set_upt actions_before_def planning_sem.is_instant_action_def using 1 by blast
    hence "(time_index \<pi> i, x) \<in> planning_sem.happ_seq" by blast
  } 
  thus "instant_snaps_before n \<subseteq> happ_at planning_sem.happ_seq (time_index \<pi> i)" by blast
qed

(* To do: generalise? *)
lemma instant_snaps_before_not_include:
  assumes "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and t: "t = time_index \<pi> i"
      and n: "n < length actions"
  shows "h \<notin> instant_snaps_before n"
proof -
  { fix x
    assume x: "x \<in> instant_snaps_before n" 

    have 1: "instant_snaps_before n = 
          at_start ` {x \<in> (!) actions ` {0..<n}. (t, at_start x) \<in> planning_sem.happ_seq \<and> (t, at_end x) \<in> planning_sem.happ_seq} 
        \<union> at_end ` {x \<in> (!) actions ` {0..<n}. (t, at_start x) \<in> planning_sem.happ_seq \<and> (t, at_end x) \<in> planning_sem.happ_seq}"
      unfolding instant_snaps_before_def instant_actions_before_def instant_starts_before_def instant_ends_before_def 
        planning_sem.is_instant_action_def Let_def set_filter set_map set_upt actions_before_def t by simp
    with x 
    consider i where  "i < n" "x = at_start (actions ! i)" | i where  "i < n" "x = at_end (actions ! i)"
      by auto
    note xc = this
    { fix i
      assume i: "i < n"
      hence neq: "actions ! i \<noteq> actions ! n"  using distinct_actions distinct_nth_unique assms by force
      have ia: "actions ! i \<in> set actions" using assms n set_conv_nth i by simp
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
      and "t = time_index \<pi> i"
      and "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and "set (pre h) \<subseteq> s"
      and "n < length actions"
    shows "set (pre h) \<subseteq> apply_instant_snaps_before n s"
proof -
  have 1: "instant_snaps_before n \<subseteq> happ_at planning_sem.happ_seq t" using instant_snaps_before_is_in_happ_seq assms by blast
  have 2: "set (pre h) \<inter> set (adds x) = {} \<and> set (pre h) \<inter> set (dels x) = {}" if "x \<in> instant_snaps_before n" for x 
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
    have "p \<notin>  \<Union> ((set o dels) ` instant_snaps_before n)" using p 2 by auto
    moreover
    have "p \<notin>  \<Union> ((set o adds) ` instant_snaps_before n)" using p 2 by auto
    ultimately
    have "p \<in> s - \<Union> ((set o dels) ` instant_snaps_before n) \<union> \<Union> ((set o adds) ` instant_snaps_before n)" by blast
  }
  thus ?thesis unfolding apply_instant_snaps_before_def apply_snaps_def by blast
qed


lemma pre_sat_by_upd_state_seq:
  assumes t: "t = time_index \<pi> i"
      and h: "(t, h) \<in> planning_sem.happ_seq"
             "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and n: "n < length actions"
    shows "set (pre h) \<subseteq> instant_part_updated_plan_state_seq n"
proof -
  from t h(1) i planning_sem.plan_state_seq_happ_pres
  have "set (pre h) \<subseteq> planning_sem.plan_state_seq i" by auto
  thus ?thesis unfolding instant_part_updated_plan_state_seq_def using assms apply_instant_snaps_before_non_mutex by blast
qed

lemma pre_val_in_instant_part_updated_prop_state_if:
  assumes t: "t = time_index \<pi> i"
      and h: "(t, h) \<in> planning_sem.happ_seq"
             "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and n: "n < length actions"
      and p: "p \<in> set (pre h)"
    shows "instant_part_updated_prop_state n p = 1"
  using assms pre_sat_by_upd_state_seq[THEN subsetD] assms
  unfolding instant_part_updated_prop_state_def by auto 

lemma set_upt_Suc_alt: "{0..<Suc n} = {0..<n} \<union> {n}" by auto

lemma instant_snaps_before_Suc:
  assumes is_instant: "is_instant_index t n"
      and t: "t = time_index \<pi> i"
    shows "instant_snaps_before (Suc n) = instant_snaps_before n \<union> {at_start (actions ! n)} \<union>  {at_end (actions ! n)}"
  unfolding instant_snaps_before_def Let_def instant_actions_before_def
set_filter set_map set_upt  set_upt_Suc_alt actions_before_def
   image_Un image_insert image_empty planning_sem.is_instant_action_def
    instant_starts_before_def instant_ends_before_def
    using is_instant unfolding planning_sem.action_happening_case_defs index_case_defs t by blast

lemma apply_instant_snaps_before_Suc:
  assumes is_instant: "is_instant_index t n"
      and n: "n < length actions"
      and t: "t = time_index \<pi> i"
    shows "apply_instant_snaps_before (Suc n) s = 
  apply_instant_snaps_before n s
  - set (dels (at_start (actions ! n)))
  \<union> set (adds (at_start (actions ! n)))
  - set (dels (at_end (actions ! n)))
  \<union> set (adds (at_end (actions ! n)))"
proof -
  have "planning_sem.app_effs (planning_sem.snaps (actions ! n)) (planning_sem.app_effs (instant_snaps_before n) s) = 
  planning_sem.app_effs (instant_snaps_before n \<union> planning_sem.snaps (actions ! n)) s"
    using planning_sem.happ_combine is_instant is_instant_index_def instant_snaps_before_is_in_happ_seq[OF n] t instant_snaps_before_def planning_sem.action_happening_case_defs by auto
  hence 1: " s - \<Union> ((set \<circ> dels) ` (instant_snaps_before n \<union> planning_sem.snaps (actions ! n))) \<union> \<Union> ((set \<circ> adds) ` (instant_snaps_before n \<union> planning_sem.snaps (actions ! n))) 
    = s - \<Union> ((set \<circ> dels) ` instant_snaps_before n) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before n) - \<Union> ((set \<circ> dels) ` planning_sem.snaps (actions ! n)) \<union> \<Union> ((set \<circ> adds) ` planning_sem.snaps (actions ! n))" 
    unfolding planning_sem.app_effs_def apply_effects_def by argo

  have "planning_sem.app_effs {at_end (actions ! n)} (planning_sem.app_effs {at_start (actions ! n)} M) = planning_sem.app_effs ({at_start (actions ! n)} \<union> {at_end (actions ! n)}) M" for M 
    using planning_sem.happ_combine[of "{at_start (actions ! n)}" "{at_end (actions ! n)}"] is_instant
    unfolding index_case_defs planning_sem.action_happening_case_defs by auto
  hence 2: "M - \<Union> ((set \<circ> dels) ` ({at_start (actions ! n), at_end (actions ! n)})) \<union> \<Union> ((set \<circ> adds) ` ({at_start (actions ! n), at_end (actions ! n)})) = 
  M - \<Union> ((set \<circ> dels) ` {at_start (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n)}) - \<Union> ((set \<circ> dels) ` {at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_end (actions ! n)})"
    for M unfolding planning_sem.app_effs_def apply_effects_def by auto

  have "apply_instant_snaps_before (Suc n) s =  s - \<Union> ((set \<circ> dels) ` instant_snaps_before (Suc n)) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before (Suc n))" unfolding apply_instant_snaps_before_def Let_def apply_snaps_def by simp
  also have "... = s - \<Union> ((set \<circ> dels) ` (instant_snaps_before n \<union> {at_start (actions ! n), at_end (actions ! n)})) \<union> \<Union> ((set \<circ> adds) ` (instant_snaps_before n \<union> {at_start (actions ! n), at_end (actions ! n)}))" 
    apply (subst instant_snaps_before_Suc[OF is_instant t])+ by blast
  also have "... = s - \<Union> ((set \<circ> dels) ` instant_snaps_before n) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before n) - \<Union> ((set \<circ> dels) ` {at_start (actions ! n), at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n), at_end (actions ! n)})" apply (subst 1) by blast
  also have "... = apply_instant_snaps_before n s - \<Union> ((set \<circ> dels) ` {at_start (actions ! n), at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n), at_end (actions ! n)})" unfolding apply_instant_snaps_before_def Let_def apply_snaps_def by blast
  also have "... = apply_instant_snaps_before n s - \<Union> ((set \<circ> dels) ` {at_start (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n)}) - \<Union> ((set \<circ> dels) ` {at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_end (actions ! n)})" apply (subst 2) by blast
  finally
  show ?thesis by auto
qed

lemma instant_part_updated_prop_state_Suc:
  assumes is_instant: "is_instant_index t n"
      and t: "t = time_index \<pi> i"
      and n: "n < length actions"
    shows "instant_part_updated_prop_state (Suc n) p = 
  (if p \<in> instant_part_updated_plan_state_seq n - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) - set (dels (at_end (actions ! n))) \<union> set (adds (at_end (actions ! n))) then 1 else 0)"
  unfolding instant_part_updated_prop_state_def instant_part_updated_plan_state_seq_def 
  apply (subst apply_instant_snaps_before_Suc)
  using assms
  by simp_all

lemma instant_intermediate_plan_state_alt:
  assumes is_instant: "is_instant_index t n"
    and t: "t = time_index \<pi> i"
    and n: "n < length actions"
  shows "instant_intermediate_plan_state_seq n = instant_part_updated_plan_state_seq n - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n)))"
proof -
  have 1: "instant_actions_before (Suc n) = insert (actions ! n) (instant_actions_before n)" using is_instant unfolding instant_actions_before_def index_case_defs actions_before_def Let_def set_filter 
    set_map set_upt t[symmetric] 
    apply -
    apply (intro equalityI subsetI) 
    subgoal for x
      apply (elim CollectE conjE imageE)
      subgoal for m
        apply (cases "n = m")
        by auto
      done
    by auto
  have 2: "f x = \<Union> (f ` {x})" for f x by blast

  show ?thesis
    unfolding instant_intermediate_plan_state_seq_def instant_part_updated_plan_state_seq_def apply_instant_snaps_before_and_start_def apply_instant_snaps_before_def
    apply_snaps_def instant_snaps_before_and_start_def
    instant_starts_before_def instant_ends_before_def instant_snaps_before_def
    unfolding 1 
    apply (subst insert_is_Un[of "(actions ! n)"])
    apply (subst (2) insert_is_Un[of "(actions ! n)"])
    apply (subst image_Un[of "at_start"])+
    apply (subst Un_commute[of "at_start ` {actions ! n}"])+
    apply (subst Un_assoc[of _ "at_start ` {actions ! n}"])+
    apply (subst Un_commute[of "at_start ` {actions ! n}"])+
    apply (subst Un_assoc[symmetric])+
    apply (subst planning_sem.happ_combine[simplified planning_sem.app_effs_def apply_effects_def comp_apply, of _ _ t, symmetric])
    subgoal using instant_snaps_before_is_in_happ_seq[OF n] is_instant 
    unfolding t instant_actions_before_def instant_snaps_before_def instant_starts_before_def instant_ends_before_def Let_def set_filter index_case_defs planning_sem.action_happening_case_defs by blast
    by auto
qed

lemma instant_intermediate_prop_state_alt:
  assumes is_instant: "is_instant_index t n"
    and t: "t = time_index \<pi> i"
    and n: "n < length actions"
  shows "instant_intermediate_prop_state n p = (if p \<in> instant_part_updated_plan_state_seq n - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) then 1 else 0)"
  using assms by (simp add: instant_intermediate_prop_state_def prop_state_def instant_intermediate_plan_state_alt)


lemma instant_part_updated_prop_state_Suc_conv_intermediate:
  assumes is_instant: "is_instant_index t n"
    and t: "t = time_index \<pi> i"
    and n: "n < length actions"
  shows "instant_part_updated_prop_state (Suc n) p = (if p \<in> instant_intermediate_plan_state_seq n - set (dels (at_end (actions ! n))) \<union> set (adds (at_end (actions ! n))) then 1 else 0)"
  by (simp add: instant_part_updated_prop_state_Suc[OF assms] instant_intermediate_plan_state_alt[OF assms])

lemma partially_updated_locked_before_pos: 
  assumes p: "p \<in> set (over_all (actions ! n))" 
      and n: "n < length actions"
      and n_ending: "is_ending_index t n"
  shows "0 < partially_updated_locked_before t p n" 
  proof -
    have "0 < (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if planning_sem.is_ending_action t a then (1::nat) else 0)"
    proof -
      { assume "0 = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if planning_sem.is_ending_action t a then (1::nat) else 0)"
        hence "\<forall>n \<in> set (map 
          (\<lambda>a. (if planning_sem.is_ending_action t a then (1::nat) else 0)) 
          (filter 
            (\<lambda>a. p \<in> set (over_all a)) 
            (map (\<lambda>n. actions ! n) [n..<length actions]))). n = 0"  apply (subst sum_list_eq_0_iff[symmetric])
          by metis
        moreover
        {
          have "(if planning_sem.is_ending_action t (actions ! n) then (1::nat) else 0) = 1" using is_ending_index_def n_ending by auto
          moreover
          have "n \<in> set [n..<length actions]" using n by simp
          ultimately
          have "\<exists>n \<in> set (map 
            (\<lambda>a. (if planning_sem.is_ending_action t a then (1::nat) else 0)) 
            (filter 
              (\<lambda>a. p \<in> set (over_all a)) 
              (map (\<lambda>n. actions ! n) [n..<length actions]))). n > 0" using assms n 
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
        apply (cases "0 = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if planning_sem.is_ending_action t a then (1::nat) else 0)")
         apply blast
        by linarith
    qed
    thus ?thesis apply (subst partially_updated_locked_before_alt) 
      using n by auto
  qed

lemma pre_val_in_instant_intermediate_prop_state_if:
  assumes t: "t = time_index \<pi> i"
      and h: "is_instant_index t n"
      and n: "n < length actions"
      and p: "p \<in> set (pre (at_end (actions ! n)))"
    shows "instant_intermediate_prop_state n p = 1"
proof -
  have happening: "(t, at_start (actions ! n)) \<in> planning_sem.happ_seq"
        "(t, at_end (actions ! n)) \<in> planning_sem.happ_seq" 
    using index_case_defs planning_sem.action_happening_case_defs h by auto
  have is_act: "actions ! n \<in> set actions" using n by auto
  have non_int: "(set o pre) (at_end (actions ! n)) \<inter> (set o dels) (at_start (actions ! n)) = {}"
       "(set o pre) (at_end (actions ! n)) \<inter> (set o adds) (at_start (actions ! n)) = {}"
    using snaps_disj planning_sem.mutex_not_in_same_instant[OF happening] 
    unfolding planning_sem.mutex_snap_def mutex_snap_action_def 
    using is_act by fast+
  hence p': "p \<notin> (set o dels) (at_start (actions ! n)) \<union> (set o adds) (at_start (actions ! n))" using p by auto
  show ?thesis
    apply (subst instant_intermediate_prop_state_alt[OF h t n])
    using p' pre_sat_by_upd_state_seq[OF t happening(2) _ n] p by auto
qed

lemma instant_part_upd_prop_state_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<and> a = actions ! j \<longrightarrow> \<not>(planning_sem.is_instant_action (time_index \<pi> i) a)" 
    shows "instant_part_updated_prop_state n p = instant_part_updated_prop_state m p"
proof -
  have 1: "[0..<m] = [0..<n] @ [n..<m]" using assms upt_append by auto
  have 2: "filter (planning_sem.is_instant_action (time_index \<pi> i)) (map ((!) actions) [n..<m]) = []"
    apply (subst filter_empty_conv)
    using assms(2) by auto
  have "filter (planning_sem.is_instant_action (time_index \<pi> i)) (map ((!) actions) [0..<n]) =
      filter (planning_sem.is_instant_action (time_index \<pi> i)) (map ((!) actions) [0..<m])"
    apply (subst 1)
    using 2 by auto
  thus ?thesis 
    unfolding instant_part_updated_prop_state_def 
    unfolding instant_part_updated_plan_state_seq_def 
    unfolding apply_instant_snaps_before_def
    unfolding instant_snaps_before_def
    unfolding instant_starts_before_def instant_ends_before_def
    unfolding instant_actions_before_def
    unfolding actions_before_def by argo
qed


lemma no_instant_imp_prop_state_before_is_after_instant:
  assumes "planning_sem.instant_snaps_at (time_index \<pi> i) = {}"
  shows "prop_state_before_happ = prop_state_after_instant_happ"
  unfolding
  prop_state_after_instant_happ_def prop_state_before_happ_def
  using assms planning_sem.no_instant_imp_state_is_inst_upd by presburger

lemma instant_part_upd_prop_state_0_is_prop_state_before:
  shows "instant_part_updated_prop_state 0 = prop_state_before_happ"
  unfolding instant_part_updated_prop_state_def prop_state_before_happ_def
  unfolding instant_part_updated_plan_state_seq_def apply_instant_snaps_before_def
  using instant_snaps_before_0_is_none apply_snaps_def by simp

lemma instant_part_upd_prop_state_all_is_prop_state_after:
  shows "instant_part_updated_prop_state (length actions) = prop_state_after_instant_happ"
  unfolding instant_part_updated_prop_state_def prop_state_after_instant_happ_def
  unfolding instant_part_updated_plan_state_seq_def
  using apply_instant_snaps_before_all_is_apply_instant_snaps planning_sem.inst_upd_state_def by simp

subsubsection \<open>Active Actions\<close>

definition "updated_active_before n \<equiv> 
planning_sem.active_before (time_index \<pi> i) + card (starting_actions_before n) 
"

lemma updated_active_before_0_is_active_before: "updated_active_before 0 = planning_sem.active_before (time_index \<pi> i)"
  using updated_active_before_def starting_actions_before_0_is_none by auto

lemma updated_active_before_all_is_active_during: 
   "updated_active_before (length actions) = planning_sem.active_during (time_index \<pi> i)"
  using updated_active_before_def starting_actions_before_all_is_starting_actions
    planning_sem.active_during_conv_active_before by auto

lemma starting_actions_before_mono:
  assumes "n \<le> m"
  shows "starting_actions_before n \<subseteq> starting_actions_before m"
  using assms unfolding starting_actions_before_def actions_before_def by auto

lemma card_starting_actions_before_mono:
  assumes "n \<le> m"
  shows "card (starting_actions_before n) \<le> card (starting_actions_before m)"
  using assms unfolding starting_actions_before_def actions_before_def 
  by (auto intro: card_mono)

lemma updated_active_before_mono:
  assumes "n \<le> m"
  shows "updated_active_before n \<le> updated_active_before m"
  using assms card_starting_actions_before_mono updated_active_before_def by simp

lemma starting_actions_before_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_starting_index (time_index \<pi> i) j)" 
    shows "starting_actions_before n = starting_actions_before m"
proof-
  have 1: "[0..<m] = [0..<n] @ [n..<m]" using assms by simp
  show ?thesis 
    unfolding starting_actions_before_def
    unfolding actions_before_def
    apply (subst 1)
    apply (subst map_append)
    apply (subst filter_append)
    apply (subst set_append)
    using assms index_case_defs
    by auto
qed

lemma starting_actions_before_Suc:
  assumes "is_starting_index (time_index \<pi> i) n"
      and "n < length actions"
  shows "starting_actions_before (Suc n) = starting_actions_before n \<union> {actions ! n}"
  using assms
  unfolding starting_actions_before_def actions_before_def index_case_defs by simp

lemma finite_starting_actions_before:
  shows "finite (starting_actions_before n)"
  unfolding starting_actions_before_def actions_before_def by blast

lemma updated_active_before_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_starting_index (time_index \<pi> i) j)" 
    shows "updated_active_before n = updated_active_before m"
  using assms starting_actions_before_inv updated_active_before_def by auto

lemma updated_active_before_ran:  
  assumes "n \<le> length actions"
  shows "updated_active_before n \<le> length actions"
  using updated_active_before_mono[OF assms]
  using updated_active_before_all_is_active_during 
  using planning_sem.active_during_ran card_action_set 
  using order.trans by auto

lemma updated_active_before_Suc:
  assumes "is_starting_index (time_index \<pi> i) n"
    and "n < length actions"
  shows "updated_active_before (Suc n) = updated_active_before n + 1"
proof -
  have "disjnt (starting_actions_before n) {actions ! n}"
    unfolding disjnt_def starting_actions_before_def actions_before_def
    using nth_actions_unique assms(2) by auto
  thus "updated_active_before (Suc n) = updated_active_before n + 1"
    unfolding updated_active_before_def 
    using starting_actions_before_Suc[OF assms]
    using card_Un_disjnt finite_starting_actions_before by auto
qed

lemma updated_active_before_less_if_starting:
  assumes "is_starting_index (time_index \<pi> i) n"
    and "n < length actions"
    shows "updated_active_before n < length actions"
proof -
  have"updated_active_before (Suc n) = updated_active_before n + 1"
    using updated_active_before_Suc assms by blast
  thus ?thesis using updated_active_before_ran[of "Suc n"] assms(2) by simp
qed


lemma apply_starting_snaps_before_Suc:
  assumes is_starting: "is_starting_index t n"
      and n: "n < length actions"
      and t: "t = time_index \<pi> i"
    shows "apply_starting_snaps_before (Suc n) s = 
  apply_starting_snaps_before n s
  - set (dels (at_start (actions ! n)))
  \<union> set (adds (at_start (actions ! n)))"
proof -
  have "at_start ` starting_actions_before n \<union> at_start ` {actions ! n} \<subseteq> at_start ` planning_sem.starting_actions_at t"
  proof -
    have "starting_actions_before (Suc n) \<subseteq> planning_sem.starting_actions_at (time_index \<pi> i)"
      apply (subst starting_actions_before_all_is_starting_actions[symmetric])
      apply (rule starting_actions_before_mono)
      using n by auto
    with starting_actions_before_if_starting assms
    show ?thesis by auto
  qed
  hence 1: "at_start ` starting_actions_before n \<union> at_start ` {actions ! n} \<subseteq> happ_at planning_sem.happ_seq t"
    unfolding planning_sem.starting_actions_at_def planning_sem.action_happening_case_defs by auto

  show ?thesis
    unfolding apply_starting_snaps_before_def
    unfolding starting_snaps_before_def
    apply (subst starting_actions_before_if_starting)
    using assms apply auto[2]
    apply (subst image_Un)
    unfolding apply_snaps_def
    apply (subst planning_sem.happ_combine[simplified planning_sem.app_effs_def apply_effects_def, symmetric])
    using 1 
    unfolding planning_sem.app_effs_def apply_effects_def 
    by auto
qed

lemma starting_part_updated_prop_state_Suc:
  assumes is_starting: "is_starting_index t n"
      and n: "n < length actions"
      and t: "t = time_index \<pi> i"
  shows "starting_part_updated_prop_state (Suc n) p =  (if p \<in> apply_starting_snaps_before n (planning_sem.inst_upd_state i) - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) then 1 else 0)"
  unfolding starting_part_updated_prop_state_def prop_state_def starting_part_updated_state_seq_def
  using apply_starting_snaps_before_Suc
  using assms by auto

end

subsection \<open>Effects of Edges\<close>

definition edge_effect::"
  nat 
  \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp 
    \<times> ('action clock, int) acconstraint list \<times> String.literal act 
    \<times> ('proposition variable \<times> ('proposition variable, int) exp) list 
    \<times> 'action clock list \<times> 'action location 
  \<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
  \<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"edge_effect n e Lvc \<equiv> 
let 
  (_, _, _, _, u, r, s') = e;
  (L, v, c) = Lvc;
  (vs, as) = unzip (map (map_prod id (eval (the o v))) u);
  L' = L[n := s'];
  v' = v(vs [\<mapsto>] as);
  c' = clock_set r 0 c
in (L', v', c')
"
definition "start_edge_effect n = edge_effect (Suc n) (start_edge_spec (actions ! n))"

definition "edge_2_effect n = edge_effect (Suc n) (edge_2_spec (actions ! n))"

definition "edge_3_effect n = edge_effect (Suc n) (edge_3_spec (actions ! n))"

definition "end_edge_effect n = edge_effect (Suc n) (end_edge_spec (actions ! n))"

definition "instant_trans_edge_effect n = edge_effect (Suc n) (instant_trans_edge_spec (actions ! n))"

definition "main_auto_init_edge_effect = edge_effect 0 main_auto_init_edge_spec"

definition "main_auto_goal_edge_effect = edge_effect 0 main_auto_goal_edge_spec"

lemma start_edge_effect_alt: "start_edge_effect n (L, v, c) = 
  (L[Suc n := StartInstant (actions ! n)],
     v(ActsActive \<mapsto> plus_int (the (v ActsActive)) 1,
         map PropVar (dels (at_start (actions ! n))) [\<mapsto>] map (\<lambda>x. 0) (dels (at_start (actions ! n))),
         map PropVar (adds (at_start (actions ! n))) [\<mapsto>] map (\<lambda>x. 1) (adds (at_start (actions ! n)))),
     c(ActStart (actions ! n) := 0))"
  unfolding start_edge_effect_def start_edge_spec_def
  unfolding  edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append fst_conv snd_conv
  by (auto simp: map_upds_append eval.simps)

lemma edge_2_effect_alt: "edge_2_effect n (L, v, c) = 
  (L[Suc n := Running (actions ! n)],
    v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. (the (v x)) + 1) (map PropLock (over_all (actions ! n)))), 
    c)"
  unfolding edge_2_effect_def edge_2_spec_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma edge_3_effect_alt: "edge_3_effect n (L, v, c) = 
  (L[Suc n := EndInstant (actions ! n)],
    v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. plus_int (the (v x)) (- 1)) (map PropLock (over_all (actions ! n)))),
    c(ActEnd (actions ! n) := 0))"
  unfolding edge_3_effect_def edge_3_spec_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma end_edge_effect_alt: "end_edge_effect n (L, v, c) = 
  (L[Suc n := Off (actions ! n)],
    v(ActsActive \<mapsto> plus_int (the (v ActsActive)) (- 1),
      map PropVar (dels (at_end (actions ! n))) [\<mapsto>] map (\<lambda>x. 0) (map PropVar (dels (at_end (actions ! n)))),
      map PropVar (adds (at_end (actions ! n))) [\<mapsto>] map (\<lambda>x. 1) (map PropVar (adds (at_end (actions ! n))))),
    c)"
  unfolding end_edge_effect_def end_edge_spec_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by (auto simp: map_upds_append)

lemma instant_trans_edge_effect_alt: "instant_trans_edge_effect n (L, v, c) = 
  (L[Suc n := EndInstant (actions ! n)], v, c(ActEnd (actions ! n):=0))"
  unfolding instant_trans_edge_effect_def instant_trans_edge_spec_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma main_auto_init_edge_effect_alt: "main_auto_init_edge_effect (L, v, c) =
  (L[0 := Planning], v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] map (\<lambda>x. 1) (map PropVar init)), c)"
  unfolding main_auto_init_edge_effect_def main_auto_init_edge_spec_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma main_auto_goal_edge_effect_alt: "main_auto_goal_edge_effect (L, v, c) = 
  (L[0 := GoalLocation], v(PlanningLock \<mapsto> 2), c)"
  unfolding main_auto_goal_edge_effect_def main_auto_goal_edge_spec_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

definition apply_start_edge_effects::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"apply_start_edge_effects ns s \<equiv>
  seq_apply (map start_edge_effect ns) s
"

definition "apply_edge_2_effects ns s = seq_apply (map edge_2_effect ns) s"

definition "apply_edge_3_effects ns s \<equiv> seq_apply (map edge_3_effect ns) s"

definition "apply_end_edge_effects ns s \<equiv> seq_apply (map end_edge_effect ns) s"

definition "apply_snap_action n s \<equiv> seq_apply [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n] s"

definition "apply_instant_actions ns s \<equiv> seq_apply' (map apply_snap_action ns) s"


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
in [s] 
    |> ext_seq (apply_edge_3_effects end_indices)
    |> ext_seq (apply_instant_actions both)
    |> ext_seq (apply_start_edge_effects start_indices)
    |> ext_seq (apply_end_edge_effects end_indices)
    |> ext_seq (apply_edge_2_effects start_indices)
    |> tl
"

definition delay::"
real
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval)" where
"delay t s \<equiv> map_prod id (map_prod id (\<lambda>clock_asmt. clock_asmt \<oplus> t)) s"

definition get_delay::"nat \<Rightarrow> real" where
"get_delay i \<equiv>
  if (i = 0) 
  then real_of_int (\<epsilon> + 1)
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
  [abs_renum.a\<^sub>0]
    |> ext_seq (seq_apply [main_auto_init_edge_effect])
    |> ext_seq' (map delay_and_apply [0..<length (htpl \<pi>)])
    |> ext_seq (seq_apply [main_auto_goal_edge_effect])"

definition plan_state_sequence::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) stream" where
"plan_state_sequence \<equiv> plan_steps @- (goal_run (last plan_steps))"

subsection \<open>General properties of the automaton\<close>

lemma time_index_Suc_and_delay:
  assumes "i < length (htpl \<pi>)"
  shows "real_of_rat (time_index \<pi> (Suc i)) = real_of_rat (time_index \<pi> i) + get_delay (Suc i)"
  by (simp add: of_rat_add[symmetric] get_delay_def)

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


subsection \<open>Some testing\<close>

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

subsubsection \<open>Relating maps and bounds\<close>

lemma is_upds_set_vars_replicate: 
  assumes "upds = (map (set_var n) xs)"
      and "v' = (v(xs [\<mapsto>] (replicate (length xs) n)))"
    shows "is_upds v upds v'"
  unfolding assms
  by (induction xs arbitrary: v) (auto intro: is_upds.intros simp: is_upd_def check_bexp_simps is_val_simps)

lemma map_const_eq_conv_length_eq:
  "map (\<lambda>x. n) xs = map (\<lambda>y. m) ys \<longleftrightarrow> length xs = length ys \<and> ((xs \<noteq> []) \<longrightarrow> n = m)"
  apply (rule iffI)
   apply (induction xs arbitrary: ys)
    apply simp
  subgoal for x xs ys
    apply (induction ys)
    by auto
  apply (induction xs arbitrary: ys)
   apply simp
  subgoal for x xs ys
    apply (induction ys)
    by auto
  done

lemma is_upds_set_vars_map: 
  assumes "upds = (map (set_var n) xs)"
      and "v' = (v(xs [\<mapsto>] (map (\<lambda>x. n) xs)))"
    shows "is_upds v upds v'"
  unfolding assms
  by (induction xs arbitrary: v) (auto intro: is_upds.intros simp: is_upd_def check_bexp_simps is_val_simps)

lemma is_upds_inc_vars: 
  assumes "set xs \<subseteq> dom v"
      and "distinct xs"
      and "upds = (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs)"
      and "v' = v(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the o v) xs))"
  shows "is_upds v upds v'"
  using assms(1,2)
  unfolding assms(3,4)
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
      using assms(2)[symmetric] bounds previous unfolding  v' bounded_def by auto
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

lemma all_zip_replicate:
  assumes "x \<in> set xs"
  shows "\<forall>m. (x, m) \<in> set (zip xs (replicate (length xs) n)) \<longrightarrow> m = n"
  using assms
proof (induction xs arbitrary: n x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have IH: "\<forall>m. (x, m) \<in> set (zip as (replicate (length as) n)) \<longrightarrow> m = n"
    using Cons apply (cases "x \<in> set as")
     apply simp using set_zip_leftD by metis
  show ?case 
    apply (subst length_Cons)
    apply (subst replicate.simps)
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

lemma map_upds_with_replicate:
  assumes "x \<in> set xs"
  shows "(v(xs [\<mapsto>] (replicate (length xs) n))) x = Some n"
proof -
  have "(x, n) \<in> set (zip xs (replicate (length xs) n))"
    apply (subst set_zip)
    using length_replicate assms
    using nth_replicate
    by (auto simp: set_conv_nth)
  thus ?thesis
    using assms 
    unfolding map_upds_def 
    apply (subst map_add_find_right)
     apply (rule map_of_determ)
    apply (subst set_rev)
    using all_zip_replicate
    by (fast, auto)
qed


lemma map_upds_with_map:
  assumes "x \<in> set xs"
      and "length xs = length ys"
  shows "(v(xs [\<mapsto>] (map (\<lambda>x. n) ys))) x = Some n"
proof -
  have "\<forall>m. (x, m) \<in> set (zip xs (map (\<lambda>x. n) ys)) \<longrightarrow> m = n"
    apply (subst set_zip)
    by auto
  moreover
  have "(x, n) \<in> set (zip xs (map (\<lambda>x. n) ys))"
    apply (subst set_zip)
    using assms
    by (auto simp: set_conv_nth set_zip)
  ultimately
  show ?thesis
    using assms unfolding map_upds_def 
    apply (subst map_add_find_right)
    by (auto intro: map_of_determ)
qed

lemma upds_replicate_bounded:
  assumes previous: "bounded M v"
      and v': "v' = v(xs [\<mapsto>] (replicate (length xs) n))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded[OF assms(1) length_replicate[symmetric] assms(2)])
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_replicate[OF a]) 
      by simp
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed

lemma upds_map_bounded':
  assumes previous: "bounded M v"
      and length: "length xs = length ys"
      and v': "v' = v(xs [\<mapsto>] (map (\<lambda>x. n) ys))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded)
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_map) 
      using assms a by auto
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed (use assms in auto)

lemma upds_map_bounded:
  assumes previous: "bounded M v"
      and v': "v' = v(xs [\<mapsto>] (map (\<lambda>x. n) xs))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded)
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_map) 
      using assms a by auto
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed (use assms in auto)

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

lemma map_of_nta_vars_ActsActive: 
  "map_of nta_vars ActsActive = Some (0, int (length actions))" using nta_vars_exact by simp

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
  shows "map_of nta_vars v = Some (0, int (length actions))"
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
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map PropLock (dels (at_start a)))"
          "v \<notin> set (map PropLock (adds (at_start a)))"
    shows "map_of nta_vars v = Some (0, int (length actions))"
proof -
  obtain p where
    p: "p \<in> set (dels (at_start a))"
       "p \<notin> set (adds (at_start a))"
       "v = PropLock p" using v by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropLock p, 0, n)) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props))) v = Some (0, n)" for n
    apply (rule map_of_is_SomeI)
    subgoal by (auto intro: distinct_filter distinct_props simp: inj_on_def distinct_map)
    unfolding set_map set_filter
    unfolding p(3)
    apply (rule imageI)
    unfolding action_vars_spec_def 
    using a_in_acts p_in_props
    unfolding snap_vars_spec_def 
    using p by auto

  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left, simp)
    apply (subst map_add_find_right)
    using 1 p(3) by fast+
qed

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
    subgoal by (auto intro: distinct_filter distinct_props simp: inj_on_def distinct_map) 
    apply (subst set_map)
    apply (subst p)
    apply (intro imageI)
    unfolding action_vars_spec_def snap_vars_spec_def
    using a_in_actions p_in_props p
    by auto
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
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map PropLock (dels (at_end a)))"
          "v \<notin> set (map PropLock (adds (at_end a)))"
    shows "map_of nta_vars v = Some (0, int (length actions))"
proof -
  obtain p where
    p: "p \<in> set (dels (at_end a))"
       "p \<notin> set (adds (at_end a))"
       "v = PropLock p" using v by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropLock p, 0, n)) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props))) v = Some (0, n)" for n
    apply (rule map_of_is_SomeI)
    subgoal by (auto intro: distinct_filter distinct_props simp: inj_on_def distinct_map) 
    unfolding action_vars_spec_def 
    using a_in_acts p_in_props p
    unfolding snap_vars_spec_def 
    using p by auto

  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left, simp)
    apply (subst map_add_find_right)
    using 1 p(3) by fast+
qed

lemma map_of_nta_vars_action_end_pre:
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map PropVar (pre (at_end a)))"
    shows "map_of nta_vars v = Some (0, 1)"
proof -
  obtain p where
    p: "p \<in> set (pre (at_end a))"
       "v = PropVar p" using v by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropVar p, 0, n)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))) v = Some (0, n)" for n
    apply (rule map_of_is_SomeI)
    subgoal by (auto intro: distinct_filter distinct_props simp: inj_on_def distinct_map) 
    apply (subst set_map)
    apply (rule image_eqI) 
    using p apply fast
    unfolding action_vars_spec_def 
    using a_in_acts p_in_props p
    unfolding snap_vars_spec_def
    by auto 

  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left, simp)
    apply (subst map_add_find_left)
    apply (subst map_of_eq_None_iff)
     apply fastforce
    unfolding p(2)[symmetric]
    apply (subst 1)
    by simp
qed



lemma map_of_nta_vars_action_start_pre:
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map PropVar (pre (at_start a)))"
    shows "map_of nta_vars v = Some (0, 1)"
proof -
  obtain p where
    p: "p \<in> set (pre (at_start a))"
       "v = PropVar p" using v by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) local.planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by auto

  have 1: "(map_of (map (\<lambda>p. (PropVar p, 0, n)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))) v = Some (0, n)" for n
    apply (rule map_of_is_SomeI)
    subgoal by (auto intro: distinct_filter distinct_props simp: inj_on_def distinct_map) 
    apply (subst set_map)
    apply (rule image_eqI) 
    using p apply fast
    unfolding action_vars_spec_def 
    using a_in_acts p_in_props p
    unfolding snap_vars_spec_def
    by auto

  show ?thesis 
    unfolding map_of_nta_vars_exact p
    apply (subst map_add_find_left, simp)
    apply (subst map_add_find_left)
    apply (subst map_of_eq_None_iff)
     apply fastforce
    unfolding p(2)[symmetric]
    apply (subst 1)
    by simp
qed

subsubsection \<open>The initial transition\<close>

lemma main_auto_init_edge_spec_simp: "main_auto_init_edge_spec = (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning)"
  unfolding main_auto_init_edge_spec_def Let_def ..

subsubsection \<open>Rules for constructing a run\<close>


lemma steps_extend: 
  "abs_renum.urge_bisim.A.steps xs 
  \<Longrightarrow> abs_renum.urge_bisim.A.steps (last xs # ys) 
  \<Longrightarrow> abs_renum.urge_bisim.A.steps (xs @ ys)"
  apply (rule abs_renum.urge_bisim.A.steps_append'[where as = xs and bs = "last xs # ys"])
  by simp+

lemma steps_replace_Cons_hd:
  assumes "abs_renum.urge_bisim.A.steps [x, hd ys]"
          "abs_renum.urge_bisim.A.steps (y # ys)"
    shows "abs_renum.urge_bisim.A.steps (x # ys)"
proof (cases ys)
  case Nil
  then show ?thesis using assms(1) by blast
next
  case (Cons a list)
  hence 1: "abs_renum.urge_bisim.A.steps ys" using assms abs_renum.urge_bisim.A.steps_ConsD by blast
  show ?thesis using abs_renum.urge_bisim.A.steps_append[OF assms(1) 1] Cons by simp
qed


lemma steps_delay_replace:
  assumes "abs_renum.urge_bisim.A.steps (delay t x # xs)"
      and t: "0 \<le> t"
      and not_urgent: "(\<forall>p < length (fst (snd abs_renum.sem)). (fst x) ! p \<notin> urgent (fst (snd abs_renum.sem) ! p))"
    shows "abs_renum.urge_bisim.A.steps (x # xs)"
proof (cases rule: abs_renum.urge_bisim.A.steps.cases[OF assms(1)])
  case 1
  then show ?thesis by blast
next
  fix tx y ys
  assume a: "delay t x # xs = tx # y # ys"
    "(case tx of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) y"
    "abs_renum.urge_bisim.A.steps (y # ys)"

  have xs: "xs = y # ys" using a by simp

  obtain Ly vy cy where
    y: "y = (Ly, vy, cy)" by (cases y; auto)

  obtain L v c where
    x: "x = (L, v, c)" by (cases x; auto)

  from a(1)
  have tx: "tx = (L, v, c \<oplus> t)" unfolding delay_def map_prod_def x prod.case id_def by simp

  from a(2)[simplified tx prod.case y, THEN step_u'_elims]
  obtain L' v' c' a where
    del: "abs_renum.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>" 
    and a: "a \<noteq> Simple_Network_Language.label.Del" "abs_renum.sem \<turnstile> \<langle>L', v', c'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>Ly, vy, cy\<rangle>" by blast

  obtain broad N B where
    as: "abs_renum.sem = (broad, N, B)" by (cases abs_renum.sem) auto
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
  have del': "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>"
    unfolding as
    unfolding L' v' c'
    apply (rule step_u.step_t)
    unfolding TAG_def 
    subgoal using other c' by blast
    subgoal using assms(2) t' by simp
    subgoal using other(2) t' assms(2) not_urgent unfolding x as fst_conv snd_conv by blast
    by (rule other(3))

  show ?thesis
    apply (rule steps_replace_Cons_hd[OF _ assms(1)])
    unfolding xs list.sel
    apply (rule single_step_intro)
    unfolding x y prod.case
    by (rule step_u'.intros[OF del' a])
qed



schematic_goal nth_auto_trans:
  assumes "n < length actions"
  shows "trans (automaton_of (actual_autos ! Suc n)) = ?x"
  apply (subst actual_autos_alt)
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_Cons_Suc)
  apply (subst nth_map)
  apply (rule assms)
  unfolding action_to_automaton_spec_def Let_def comp_def snd_conv trans_def 
    automaton_of_def prod.case fst_conv list.set ..

schematic_goal main_auto_trans:
  shows "trans (automaton_of (actual_autos ! 0)) = ?x"
  apply (subst actual_autos_alt)
  apply (subst nth_map, simp)
  apply (subst nth_Cons_0)
  unfolding main_auto_spec_def Let_def comp_def snd_conv trans_def automaton_of_def prod.case fst_conv list.set ..


schematic_goal nth_auto_trans':
  assumes "n < length actions"
  shows "trans (automaton_of ((snd \<circ> snd) (action_to_automaton_spec (actions ! n)))) = ?x"
  unfolding action_to_automaton_spec_def Let_def comp_def snd_conv trans_def 
    automaton_of_def prod.case fst_conv list.set ..

(* Indices of locations and automata are offset by 1 w.r.t. actions' indices *)

subsection \<open>Definitions for conditions\<close>
fun act_clock_pre_happ_spec::"('action clock, real) cval \<Rightarrow> 'action clock \<Rightarrow> rat \<Rightarrow> bool" where
"act_clock_pre_happ_spec c (ActStart a) t = (c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t))" |
"act_clock_pre_happ_spec c (ActEnd a) t = (c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t))"

subsubsection \<open>Mutex constraints\<close>

text \<open>This only works for the direction from plan to run.\<close>
(* goal cases*)
schematic_goal int_clocks_spec_alt:
  shows "set (int_clocks_spec h) = ?x"
  unfolding int_clocks_spec_def Let_def filter_append set_append set_map set_filter ..

lemma mutex_0_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> h = at_start a \<longrightarrow> act_clock_pre_happ_spec c (ActStart a) t"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> h = at_end a \<longrightarrow> act_clock_pre_happ_spec c (ActEnd a) t"
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
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> h = at_start a \<longrightarrow> act_clock_pre_happ_spec c (ActStart a) t"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> h = at_end a \<longrightarrow> act_clock_pre_happ_spec c (ActEnd a) t"
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
      using s_corr[THEN bspec, OF a(1), THEN mp, OF c, simplified]
      using x of_rat_less_eq by metis
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
      using e_corr[THEN bspec, OF a(1), THEN mp, OF c, simplified]
      using x of_rat_less_eq by metis
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

lemma l_dur_spec_sat_if: 
  assumes "satisfies_duration_bounds lower_sem upper_sem act r"
      and "((cv (ActStart act))::real) = of_rat r"
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
(* coercions *)
(* declare [[show_sorts]] *)
(* show sorts *)
find_theorems "?x < ?y"
lemma u_dur_spec_sat_if:
  assumes "satisfies_duration_bounds lower_sem upper_sem act r"
      and "((cv (ActStart act))::real) = of_rat r"
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

lemma ending_actions_sat_dur_const_specs:
  assumes "a \<in> set actions"
      and "planning_sem.is_ending_action t a"
      and "act_clock_pre_happ_spec c (ActStart a) t"
    shows "c \<turnstile> map conv_ac (u_dur_spec a)" "c \<turnstile> map conv_ac (l_dur_spec a)"
   using assms by (auto intro: u_dur_spec_sat_if l_dur_spec_sat_if planning_sem.ending_act_sat_dur_bounds)


lemma instant_actions_sat_dur_const_specs:
  assumes "a \<in> set actions"
      and "planning_sem.is_instant_action t a"
      and "c (ActStart a) = 0"
    shows "c \<turnstile> map conv_ac (u_dur_spec a)" "c \<turnstile> map conv_ac (l_dur_spec a)"
  using assms by (auto intro: u_dur_spec_sat_if l_dur_spec_sat_if planning_sem.instant_act_sat_dur_bounds)

lemma ending_actions_sat_mutex_const_specs:
  assumes in_acts: "a \<in> set actions"
    and ending: "planning_sem.is_ending_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
                "act_clock_pre_happ_spec c (ActEnd a) t"
              shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end a)))" 
                "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end a)))"
  subgoal
    apply (rule mutex_0_constraint_sat)
    using assms(2) planning_sem.is_ending_action_def apply blast
     apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_end b) \<in> planning_sem.happ_seq")
      using clocks snaps_disj in_acts 
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI)+
    apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts
       apply (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)
      apply (cases "a = b")
      using clocks in_acts at_end_inj unfolding inj_on_def by auto
    done
  apply (rule mutex_eps_constraint_sat)
  using assms(2) planning_sem.is_ending_action_dests apply blast
   apply (intro ballI impI)
  subgoal for b
    apply (cases "(t, at_end b) \<in> planning_sem.happ_seq")
    using clocks snaps_disj in_acts 
    by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI)+
  apply (intro ballI impI)
  subgoal for b
    apply (erule disjE)
    using clocks in_acts
     apply (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)
    apply (cases "a = b")
    using clocks in_acts at_end_inj unfolding inj_on_def by auto
  done

lemma instant_action_sat_mutex_start:
  assumes in_acts: "a \<in> set actions"
    and instant: "planning_sem.is_instant_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
                "act_clock_pre_happ_spec c (ActStart a) t"
    and g: " g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_start a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_start a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_end a) \<in> planning_sem.happ_seq" 
          "(t, at_start a) \<in> planning_sem.happ_seq" using instant planning_sem.is_instant_action_def by simp+
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.happ_seq \<or> at_start a = at_start b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
  apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts at_start_inj unfolding inj_on_def
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.happ_seq \<or> at_start a = at_end b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_start b) \<in> planning_sem.happ_seq")
      using clocks snaps_disj in_acts planning_sem.is_starting_actionI 
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed

lemma instant_action_sat_mutex_end:
  assumes in_acts: "a \<in> set actions"
    and instant: "planning_sem.is_instant_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
                "act_clock_pre_happ_spec c (ActEnd a) t"
    and g: "g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_end a) \<in> planning_sem.happ_seq" using instant planning_sem.is_instant_action_def by simp
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.happ_seq \<or> at_end a = at_start b \<longrightarrow> act_clock_pre_happ_spec c (ActStart b) t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_end b) \<in> planning_sem.happ_seq")
      subgoal using clocks snaps_disj in_acts planning_sem.is_ending_actionI by blast
      subgoal using clocks snaps_disj in_acts planning_sem.is_not_happening_actionI by blast
      done
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.happ_seq \<or> at_end a = at_end b \<longrightarrow> act_clock_pre_happ_spec c (ActEnd b) t"
  apply (intro ballI impI)
    subgoal for b
      using clocks in_acts at_end_inj unfolding inj_on_def
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed
section \<open>Applying happenings\<close>



(* This should record t + \<epsilon> + c for unexecuted actions. What about plans of length 0? Clock valuations
  do not matter for some plans. *)
fun act_clock_post_happ_spec::"('action clock, real) cval \<Rightarrow> 'action clock \<Rightarrow> rat \<Rightarrow> bool" where
"act_clock_post_happ_spec c (ActStart a) t = (c (ActStart a) = real_of_rat (planning_sem.exec_time' (at_start a) t))" |
"act_clock_post_happ_spec c (ActEnd a) t = (c (ActEnd a) = real_of_rat (planning_sem.exec_time' (at_end a) t))"

(* The properties of the state once the initial transition has been taken *)

text \<open>Invariants\<close>
definition "Lv_conds L v \<equiv> 
  length L = Suc (length actions) 
\<and> L ! 0 = Planning
\<and> bounded (map_of nta_vars) v 
\<and> v PlanningLock = Some 1"

text \<open>Actual starting state\<close>
definition init_state_props::"('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) \<Rightarrow> bool" where
"init_state_props Lvc \<equiv> 
let 
  (L, v, c) = Lvc;
  bounded = bounded (map_of nta_vars) v;
  locs = (L = InitialLocation # map Off actions); 
  def_vars = (\<forall>x \<in> actual_variables. v x = Some 0);
  undef_vars = (\<forall>x. x \<notin> actual_variables \<longrightarrow> v x = None); 
  clock_state = (c = (\<lambda>_. 0))
in bounded
\<and> locs 
\<and> def_vars
\<and> undef_vars
\<and> clock_state"

text \<open>Initial and goal state w.r.t. planning\<close>
definition "init_planning_state_props Lvc \<equiv>
let 
  (L, v, c) = Lvc;

  acts_active = v ActsActive = Some 0;

  locs = (L = Planning # map Off actions); 
  true_props = (\<forall>p \<in> set init. v (PropVar p) = Some 1);
  false_props = (\<forall>x \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v x = Some 0); 

  undef_vars = (\<forall>x. x \<notin> actual_variables \<longrightarrow> v x = None); 

  clock_state =  (c = (\<lambda>_. 0))
in 
  Lv_conds L v 
\<and> acts_active 
\<and> locs 
\<and> true_props 
\<and> false_props 
\<and> undef_vars 
\<and> clock_state"

definition "init_planning_state_props' Lvc \<equiv> 
let 
  (L, v, c) = Lvc;

  acts_active = v ActsActive = Some 0;

  locs = (L = Planning # map Off actions); 

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state (set init) p));
  lock_state = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0);

  start_time = (\<forall>i < length actions. c (ActStart (actions ! i)) = 0);
  end_time = (\<forall>i < length actions. c (ActEnd (actions ! i)) = 0)
in 
  Lv_conds L v 
\<and> acts_active
\<and> locs
\<and> prop_state
\<and> lock_state
\<and> start_time
\<and> end_time"


(* The final transition does not consider clock valuations as conditions *)
definition "goal_trans_pre Lvc \<equiv> 
let 
  (L, v, c) = Lvc;

  acts_active = v ActsActive = Some 0;

  locs = (L = Planning # map Off actions); 
  prop_state = (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state S p)));
  lock_state = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0)

in 
  Lv_conds L v 
\<and> acts_active
\<and> locs
\<and> prop_state 
\<and> lock_state"

definition "goal_state_conds Lvc \<equiv> 
let 
  (L, v, c) = Lvc;
  bounded = bounded (map_of nta_vars) v;  

  acts_active = v ActsActive = Some 0;
  planning_state = v PlanningLock = Some 2;

  locs = (L = GoalLocation # map Off actions); 
  prop_state = (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state S p)));
  lock_state = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0)

in 
  bounded
\<and> acts_active
\<and> planning_state
\<and> locs
\<and> prop_state 
\<and> lock_state"


text \<open>Each happening\<close>

definition "happening_pre i Lvc \<equiv>
let
  t = time_index \<pi> i;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ i p));
  lock_state = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before t p)));

  active = (v ActsActive = Some (int (planning_sem.active_before t)));

  active_locs = (\<forall>i < length actions. planning_sem.open_active_count t (actions ! i) = 0 \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  inactive_locs = (\<forall>i < length actions. planning_sem.open_active_count t (actions ! i) = 1  \<longrightarrow> L ! Suc i = (Running (actions ! i)));

  start_time = (\<forall>i < length actions. act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  end_time = (\<forall>i < length actions. act_clock_pre_happ_spec c (ActEnd (actions ! i)) t)
in Lv_conds L v
  \<and> prop_state \<and> lock_state 
  \<and> active 
  \<and> active_locs \<and> inactive_locs
  \<and> start_time \<and> end_time"

(* These should delay c and not t *)
definition "happening_pre_pre_delay i Lvc \<equiv>
let 
  (L, v, c) = Lvc;
  \<delta> = get_delay i
in happening_pre i (L, v, c \<oplus> \<delta>)"

definition "happening_pre_post_delay i Lvc \<equiv> happening_pre i Lvc"

definition "happening_post i Lvc \<equiv>
let 
  t = time_index \<pi> i;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_happ i p));
  lock_state = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_after t p)));

  active = (v ActsActive = Some (int (planning_sem.active_after t)));

  active_locs = (\<forall>i < length actions. planning_sem.closed_active_count t (actions ! i) = 0 \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  inactive_locs = (\<forall>i < length actions. planning_sem.closed_active_count t (actions ! i) = 1  \<longrightarrow> L ! Suc i = (Running (actions ! i)));

  start_time = (\<forall>i < length actions. act_clock_post_happ_spec c (ActStart (actions ! i)) t);
  end_time = (\<forall>i < length actions. act_clock_post_happ_spec c (ActEnd (actions ! i)) t)
in Lv_conds L v
  \<and> prop_state \<and> lock_state 
  \<and> active 
  \<and> active_locs \<and> inactive_locs
  \<and> start_time \<and> end_time"


definition "happening_invs n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  ending_start_time = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  starting_end_time = (\<forall>i < length actions. is_starting_index t i \<longrightarrow>  act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);

  other_start_time = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  other_end_time = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);

  other_inactive_loc = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> planning_sem.closed_active_count t (actions ! i) = 0 \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  other_active_loc = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> planning_sem.closed_active_count t (actions ! i) = 1  \<longrightarrow> L ! Suc i = (Running (actions ! i)))
in Lv_conds L v
  \<and> ending_start_time
  \<and> starting_end_time
  \<and> other_start_time \<and> other_end_time
  \<and> other_inactive_loc \<and> other_active_loc"

text \<open>The beginning of the end of an action\<close>

definition "end_start_invs n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p));
  active = (v ActsActive = Some (int (planning_sem.active_before t)));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);


  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))

in happening_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> starting_start_time
  \<and> instant_start_time \<and> instant_end_time
  \<and> starting_loc
  \<and> instant_loc"

definition "happening_pre_end_starts n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before t p)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (Running (actions ! i)));

  ending_end_time =  (\<forall>i < length actions. is_ending_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t)

in end_start_invs n Lvc
  \<and> locked 
  \<and> ending_loc
  \<and> ending_end_time"

definition "happening_post_end_starts n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during t p)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (EndInstant (actions ! i)));

  ending_end_time =  (\<forall>i < length actions. is_ending_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0)

in end_start_invs n Lvc
  \<and> locked 
  \<and> ending_loc
  \<and> ending_end_time"

definition "end_start_cond n i Lvc \<equiv> 
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (partially_updated_locked_before t p i));

  updated_locs = (\<forall>j. j < i \<and> is_ending_index t j \<longrightarrow> L ! Suc j = (EndInstant (actions ! j)));
  not_updated_locs = (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index t j \<longrightarrow> L ! Suc j = (Running (actions ! j)));

  updated_clocks =  (\<forall>j. j < i \<and> is_ending_index t j \<longrightarrow> c (ActEnd (actions ! j)) = 0);
  not_updated_clocks =  (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index t j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n))

in end_start_invs n Lvc
  \<and> locked 
  \<and> updated_locs
  \<and> not_updated_locs
  \<and> updated_clocks
  \<and> not_updated_clocks"

definition "end_start_pre n \<equiv> end_start_cond n"

definition "end_start_post n \<equiv> end_start_cond n o Suc"

text \<open>Actions which are executed in their entirety\<close>

definition "instant_action_invs n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  lock_state = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (planning_sem.locked_during t  p));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (EndInstant (actions ! i)))

in happening_invs n Lvc
  \<and> lock_state
  \<and> starting_start_time
  \<and> ending_end_time
  \<and> starting_loc
  \<and> ending_loc"


definition "happening_pre_instants n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p));

  active = (v ActsActive = Some (int (planning_sem.active_before t)));

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);
  
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in instant_action_invs n Lvc
  \<and> prop_state
  \<and> active 
  \<and> instant_start_time \<and> instant_end_time
  \<and> instant_loc"

definition "happening_post_instants n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_instant_happ n p));

  active = (v ActsActive = Some (int (planning_sem.active_before t)));

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);
  
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in instant_action_invs n Lvc
  \<and> prop_state
  \<and> active 
  \<and> instant_start_time \<and> instant_end_time
  \<and> instant_loc"
                          
definition "instant_cond n j Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_part_updated_prop_state n j p));

  active = (v ActsActive = Some (int (planning_sem.active_before t)));

  updated_start_time = (\<forall>i. i < j \<and> is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  updated_end_time = (\<forall>i. i < j \<and> is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  not_updated_start_time = (\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  not_updated_end_time =  (\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);
  
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in instant_action_invs n Lvc
  \<and> prop_state 
  \<and> active 
  \<and> updated_start_time \<and> updated_end_time
  \<and> not_updated_start_time \<and> not_updated_end_time
  \<and> instant_loc"

definition "instant_pre n \<equiv> instant_cond n"

definition "instant_post n \<equiv> instant_cond n o Suc"

find_theorems name: "locked_during*and"

definition "instant_starting_cond n j Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_intermediate_prop_state n j p));

  active = (v ActsActive = Some (int (planning_sem.active_before t + 1)));

  updated_start_time = (\<forall>i. i \<le> j \<and> is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  updated_end_time = (\<forall>i. i < j \<and> is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  not_updated_start_time = (\<forall>i. j < i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  not_updated_end_time =  (\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);
  
  loc = (L ! Suc j = StartInstant (actions ! j));
  other_instant_loc = (\<forall>i < length actions. i \<noteq> j \<and> is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in instant_action_invs n Lvc
  \<and> prop_state 
  \<and> active 
  \<and> updated_start_time \<and> updated_end_time
  \<and> not_updated_start_time \<and> not_updated_end_time
  \<and> loc
  \<and> other_instant_loc"

definition "instant_ending_cond n j Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_intermediate_prop_state n j p));

  active = (v ActsActive = Some (int (planning_sem.active_before t + 1)));

  updated_start_time = (\<forall>i. i \<le> j \<and> is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  updated_end_time = (\<forall>i. i \<le> j \<and> is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  not_updated_start_time = (\<forall>i. j < i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  not_updated_end_time =  (\<forall>i. j < i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) t);
  
  loc = (L ! Suc j = EndInstant (actions ! j));
  other_instant_loc = (\<forall>i < length actions. i \<noteq> j \<and> is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in instant_action_invs n Lvc
  \<and> prop_state 
  \<and> active 
  \<and> updated_start_time \<and> updated_end_time
  \<and> not_updated_start_time \<and> not_updated_end_time
  \<and> loc
  \<and> other_instant_loc"

definition "start_start_invs n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during t p)));

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (EndInstant (actions ! i)));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))

in happening_invs n Lvc
  \<and> locked
  \<and> ending_end_time
  \<and> instant_start_time
  \<and> instant_end_time
  \<and> ending_loc
  \<and> instant_loc"

definition "happening_pre_start_starts n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_instant_happ n p));

  active = (v ActsActive = Some (int (planning_sem.active_before t)));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in start_start_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> starting_start_time
  \<and> starting_loc"

definition "start_start_cond n j Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (starting_part_updated_prop_state n j p));

  active = (v ActsActive = Some (int (updated_active_before n j)));

  updated_start_time = (\<forall>i. i < j \<and> is_starting_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  not_updated_start_time = (\<forall>i. j \<le> i \<longrightarrow> i  < length actions \<longrightarrow> is_starting_index t i  \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) t);
  
  not_updated_start_loc =  (\<forall>i. i < j \<and> is_starting_index t i \<longrightarrow> L ! Suc i = (StartInstant (actions ! i)));
  updated_start_loc = (\<forall>i. j \<le> i \<longrightarrow> i < length actions \<longrightarrow> is_starting_index t i  \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in start_start_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> not_updated_start_loc \<and> updated_start_time
  \<and> not_updated_start_loc \<and> updated_start_loc"

definition "start_start_pre \<equiv> start_start_cond"

definition "start_start_post n j \<equiv> start_start_cond n (Suc j)"

definition "happening_post_start_starts n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_instant_start_happ n p));

  active = (v ActsActive = Some (int (planning_sem.active_during t)));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> c (ActStart (actions ! i)) = 0);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (StartInstant (actions ! i)))
in start_start_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> starting_start_time
  \<and> starting_loc"

definition "end_end_invs n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during t p)));

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (ActEnd (actions ! i)) = 0);
  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> c (ActStart (actions ! i)) = 0);

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (StartInstant (actions ! i)));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))

in happening_invs n Lvc
  \<and> locked
  \<and> starting_start_time
  \<and> ending_end_time
  \<and> instant_start_time \<and> instant_end_time
  \<and> starting_loc
  \<and> instant_loc"

(* active_during not correct *)
definition "happening_pre_end_ends n Lvc \<equiv> 
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_instant_start_happ n p));

  active = (v ActsActive = Some (int (planning_sem.active_during t)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (EndInstant (actions ! i)))

in end_end_invs n Lvc
  \<and> prop_state \<and> active
  \<and> ending_loc"

definition "happening_post_end_ends n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_happ n p));

  active = (v ActsActive = Some (int (planning_sem.active_during_minus_ended t)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))
in end_end_invs n Lvc
  \<and> prop_state \<and> active
  \<and> ending_loc"

definition "start_end_invs n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_happ n p));

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (ActEnd (actions ! i)) = 0);
  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> c (ActStart (actions ! i)) = 0);

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActStart (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (ActEnd (actions ! i)) = 0);

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (Off (actions ! i)))

in happening_invs n Lvc
  \<and> prop_state
  \<and> starting_start_time
  \<and> ending_end_time
  \<and> instant_start_time \<and> instant_end_time
  \<and> ending_loc
  \<and> instant_loc"

definition "happening_pre_start_ends n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during t p)));

  active = (v ActsActive = Some (int (planning_sem.active_during_minus_ended t)));

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (StartInstant (actions ! i)))
in start_end_invs n Lvc
  \<and> locked
  \<and> active
  \<and> starting_loc"

definition "happening_post_start_ends n Lvc \<equiv>
let 
  t = time_index \<pi> n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during t p)));

  active = (v ActsActive = Some (int (planning_sem.active_after t)));

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (Running (actions ! i)))
in start_end_invs n Lvc
  \<and> locked
  \<and> active
  \<and> starting_loc"

text \<open>rules\<close>

(* To do: these rules are better when forall quantifiers are replaced with meta-logic binders *)
lemma init_state_propsE: 
  assumes "init_state_props x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> bounded (map_of nta_vars) v \<Longrightarrow> L = InitialLocation # map Off actions \<Longrightarrow> \<forall>x\<in>actual_variables. v x = Some 0 \<Longrightarrow> \<forall>x. x \<notin> actual_variables \<longrightarrow> v x = None \<Longrightarrow> c = (\<lambda>_. 0) \<Longrightarrow> thesis"
      shows thesis 
  using assms unfolding init_state_props_def by auto

lemma init_state_propsI:
  assumes "x = (L, v, c)"
    and "bounded (map_of nta_vars) v"
    and "L = InitialLocation # map Off actions"
    and "\<And>x. x \<in> actual_variables \<Longrightarrow> v x = Some 0"
    and "\<And>x. x \<notin> actual_variables \<Longrightarrow> v x = None" 
    and "c = (\<lambda>_. 0)" 
  shows "init_state_props x"
  unfolding init_state_props_def using assms by simp

lemma init_planning_state_propsE:
  assumes "init_planning_state_props x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> Lv_conds L v \<Longrightarrow> v ActsActive = Some 0 \<Longrightarrow> L = Planning # map Off actions \<Longrightarrow> (\<forall>p\<in>set init. v (PropVar p) = Some 1) \<Longrightarrow> (\<forall>x\<in>actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v x = Some 0) \<Longrightarrow> (\<forall>x. x \<notin> actual_variables \<longrightarrow> v x = None) \<Longrightarrow> c = (\<lambda>_. 0) \<Longrightarrow> thesis"
    shows thesis 
  using assms unfolding init_planning_state_props_def Let_def prod.case by blast

lemma init_planning_state_propsI:
  assumes "x = (L, v, c)" "Lv_conds L v" "v ActsActive = Some 0" "L = Planning # map Off actions" "\<And>p. p\<in>set init \<Longrightarrow> v (PropVar p) = Some 1" "\<And>x. x \<in> actual_variables \<Longrightarrow> x \<notin> {PlanningLock, ActsActive} \<Longrightarrow> x \<notin> PropVar ` set init \<Longrightarrow> v x = Some 0" "\<And>x. x \<notin> actual_variables \<Longrightarrow> v x = None" "c = (\<lambda>_. 0)"
  shows "init_planning_state_props x"  
  using assms unfolding init_planning_state_props_def by auto


lemma init_planning_state_props'E:
  assumes "init_planning_state_props' x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> Lv_conds L v \<Longrightarrow> v ActsActive = Some 0 \<Longrightarrow> L = Planning # map Off actions \<Longrightarrow> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state (set init) p)) \<Longrightarrow> (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0) \<Longrightarrow> (\<forall>i<length actions. c (ActStart (actions ! i)) = 0) \<Longrightarrow> (\<forall>i<length actions. c (ActEnd (actions ! i)) = 0) \<Longrightarrow> thesis"
    shows thesis 
  using assms unfolding init_planning_state_props'_def by auto

lemma init_planning_state_props'I:
  assumes "x = (L, v, c)" "Lv_conds L v" "v ActsActive = Some 0 " "L = Planning # map Off actions " "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state (set init) p))" "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0)" "(\<forall>i<length actions. c (ActStart (actions ! i)) = 0)" "(\<forall>i<length actions. c (ActEnd (actions ! i)) = 0)"
  shows "init_planning_state_props' x"  
  apply (subst assms(1)) 
  unfolding init_planning_state_props'_def Let_def prod.case using assms by blast

lemma goal_trans_preE:
  assumes "goal_trans_pre x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> Lv_conds L v \<Longrightarrow> v ActsActive = Some 0 \<Longrightarrow> L = Planning # map Off actions 
    \<Longrightarrow> \<exists>S. set goal \<subseteq> S \<and> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state S p)) 
  \<Longrightarrow> (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0) \<Longrightarrow> thesis"
    shows thesis 
  using assms by (auto simp: goal_trans_pre_def)

lemma goal_trans_preI:
  assumes "x = (L, v, c)"  
    "Lv_conds L v" 
    "v ActsActive = Some 0" 
    "L = Planning # map Off actions" 
    "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state S p))" 
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0)"
  shows "goal_trans_pre x"
  using assms by (auto simp: goal_trans_pre_def)

lemma goal_state_condsE:
  assumes "goal_state_conds x"
      and "\<And>L v c. x = (L, v, c)
        \<Longrightarrow> Simple_Network_Language.bounded (map_of nta_vars) v
        \<Longrightarrow> v ActsActive = Some 0
        \<Longrightarrow> v PlanningLock = Some 2
        \<Longrightarrow> L = GoalLocation # map Off actions
        \<Longrightarrow> (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state S p)))
        \<Longrightarrow> (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0)
        \<Longrightarrow> thesis"
    shows thesis
  apply (cases x)
  using assms unfolding goal_state_conds_def by simp

lemma goal_state_condsI:
  assumes "x = (L, v, c)"
    "Simple_Network_Language.bounded (map_of nta_vars) v"
    "v ActsActive = Some 0" 
    "v PlanningLock = Some 2" 
    "L = GoalLocation # map Off actions" 
    "(\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state S p)))" 
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some 0)"
  shows "goal_state_conds x"
  using assms by (auto simp: goal_state_conds_def)
  
lemma Lv_condsE:
  assumes "Lv_conds L v"
    and "length L = Suc (length actions) \<Longrightarrow> L ! 0 = Planning \<Longrightarrow> Simple_Network_Language.bounded (map_of nta_vars) v \<Longrightarrow> v PlanningLock = Some 1 \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding Lv_conds_def by blast


lemma Lv_condsD:
  assumes "Lv_conds L v"
  shows "length L = Suc (length actions) \<and> L ! 0 = Planning \<and> Simple_Network_Language.bounded (map_of nta_vars) v \<and> v PlanningLock = Some 1"
  using assms unfolding Lv_conds_def by auto

lemma Lv_conds_dests:
  assumes "Lv_conds L v"
  shows "length L = Suc (length actions)" "L ! 0 = Planning" "Simple_Network_Language.bounded (map_of nta_vars) v" "v PlanningLock = Some 1"
  using assms unfolding Lv_conds_def by auto


lemma Lv_condsI:
  assumes "length L = Suc (length actions)" "L ! 0 = Planning" "Simple_Network_Language.bounded (map_of nta_vars) v" "v PlanningLock = Some 1"
  shows "Lv_conds L v"
  using Lv_conds_def assms by blast

lemma happening_pre_pre_delayI:
  assumes "x = (L, v, c)"
    "Lv_conds L v"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))" 
    "(\<forall>i<length actions. act_clock_pre_happ_spec (c \<oplus> get_delay n) (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec (c \<oplus> get_delay n) (ActEnd (actions ! i)) (time_index \<pi> n))"
  shows "happening_pre_pre_delay n x" 
  unfolding happening_pre_pre_delay_def Let_def happening_pre_def  assms prod.case
  using assms by blast

lemma happening_pre_pre_delayE: 
  assumes "happening_pre_pre_delay n x"
  and "\<And>L v c. x = (L, v, c) 
    \<Longrightarrow> Lv_conds L v
    \<Longrightarrow> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))
    \<Longrightarrow> (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))
    \<Longrightarrow> v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))
    \<Longrightarrow> (\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))
    \<Longrightarrow> (\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))
    \<Longrightarrow> (\<forall>i<length actions. act_clock_pre_happ_spec (c \<oplus> get_delay n) (ActStart (actions ! i)) (time_index \<pi> n))
    \<Longrightarrow> (\<forall>i<length actions. act_clock_pre_happ_spec (c \<oplus> get_delay n) (ActEnd (actions ! i)) (time_index \<pi> n))
    \<Longrightarrow> thesis"
shows thesis using assms(1)
  apply (cases x rule: prod_cases3)
  unfolding happening_pre_pre_delay_def Let_def happening_pre_def 
  subgoal
    apply (rule assms(2))
    by blast+
  done

lemma happening_pre_pre_delay_dests: 
  assumes "happening_pre_pre_delay n x"
          "x = (L, v, c)"
  shows  "Lv_conds L v"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec (c \<oplus> get_delay n) (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec (c \<oplus> get_delay n) (ActEnd (actions ! i)) (time_index \<pi> n))"
  using assms unfolding happening_pre_pre_delay_def happening_pre_def by auto

lemma happening_pre_post_delay_dests:
  assumes "happening_pre_post_delay n x"
      "x = (L, v, c)"
    shows "Lv_conds L v"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))" 
  using assms unfolding happening_pre_post_delay_def happening_pre_def by auto


lemma happening_pre_post_delayI:
  assumes "x = (L, v, c)"
    "Lv_conds L v"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. planning_sem.open_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))" 
  shows "happening_pre_post_delay n x"
  using assms unfolding happening_pre_post_delay_def happening_pre_def by auto

lemma happening_postI:
  assumes "x = (L, v, c)"
  and "Lv_conds L v"
      "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_happ t p))"
      "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_after (time_index \<pi> t) p)))"
      "v ActsActive = Some (int (planning_sem.active_after (time_index \<pi> t)))"
      "(\<forall>i<length actions. planning_sem.closed_active_count (time_index \<pi> t) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
      "(\<forall>i<length actions. planning_sem.closed_active_count (time_index \<pi> t) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))" 
      "(\<forall>i<length actions. act_clock_post_happ_spec c (ActStart (actions ! i)) (time_index \<pi> t))"
      "(\<forall>i<length actions. act_clock_post_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> t))"
  shows "happening_post t x"
  unfolding happening_post_def Let_def 
  using assms by blast


lemma happening_postE:
  assumes "happening_post n x"
    and "\<And>L v c. x = (L, v, c)
      \<Longrightarrow> Lv_conds L v
      \<Longrightarrow> (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_happ n p))
      \<Longrightarrow> (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_after (time_index \<pi> n) p)))
      \<Longrightarrow> v ActsActive = Some (int (planning_sem.active_after (time_index \<pi> n)))
      \<Longrightarrow> (\<forall>i<length actions. planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))
      \<Longrightarrow> (\<forall>i<length actions. planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))
      \<Longrightarrow> (\<forall>i<length actions. act_clock_post_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))
      \<Longrightarrow> (\<forall>i<length actions. act_clock_post_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n)) \<Longrightarrow> thesis"
  shows "thesis"
  apply (cases x)
  subgoal 
    using assms(1)
    unfolding happening_post_def Let_def apply simp
    apply (elim conjE)
    apply (erule assms(2))
    by simp_all
  done


lemma happening_post_dests:
  assumes "happening_post n x"
    and "x = (L, v, c)"
  shows "Lv_conds L v"
      "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_happ n p))"
      "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_after (time_index \<pi> n) p)))"
      "v ActsActive = Some (int (planning_sem.active_after (time_index \<pi> n)))"
      "(\<forall>i<length actions. planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
      "(\<forall>i<length actions. planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))"
      "(\<forall>i<length actions. act_clock_post_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. act_clock_post_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
  using assms unfolding happening_post_def Let_def by auto

lemma end_start_invsE:
  assumes "end_start_invs n x"
    and "\<And>L v c. happening_invs n (L, v, c) \<Longrightarrow>
    (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p)) \<Longrightarrow>
    v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n))) \<Longrightarrow>
    (\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
    (\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
    (\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
    (\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i)) \<Longrightarrow>
    (\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i)) \<Longrightarrow>
    thesis"
  shows thesis
  using assms by (auto simp: end_start_invs_def)


lemma end_start_invsD:
  assumes "end_start_invs n (L, v, c)"
  shows "happening_invs n (L, v, c) \<and>
    (\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p)) \<and>
    v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n))) \<and>
    (\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n)) \<and>
    (\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n)) \<and>
    (\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n)) \<and>
    (\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i)) \<and>
    (\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms by (auto simp: end_start_invs_def)


lemma end_start_invs_dests:
  assumes "end_start_invs n (L, v, c)"
  shows "happening_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms by (auto dest!: end_start_invsD)

lemma end_start_invsI:
  assumes "x = (L, v, c)"
      "happening_invs n (L, v, c)" 
      "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
      "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
      "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
      "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  shows "end_start_invs n x"
  using assms by (auto simp: end_start_invs_def)

lemma happening_invsE:
  assumes "happening_invs n x"
    "\<And>L v c. x = (L, v, c) \<Longrightarrow>
     Lv_conds L v \<Longrightarrow>
     (\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
     (\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i)) \<Longrightarrow>
       thesis"
  shows thesis
  using assms by (auto simp: happening_invs_def)

lemma happening_invs_dests:
  assumes "happening_invs n (L, v, c)"
  shows "Lv_conds L v"
      "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
      "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
      "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))"
  using assms by (auto simp: happening_invs_def)

lemma happening_invsI:
  assumes "x = (L, v, c)"
    "Lv_conds L v"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> planning_sem.closed_active_count (time_index \<pi> n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = Running (actions ! i))"
  shows "happening_invs n x"
  using assms by (auto simp: happening_invs_def)

lemma end_start_preE:
  assumes "end_start_pre n i x"
    and "\<And>L v c. x = (L, v, c) \<Longrightarrow>
    end_start_invs n (L, v, c) \<Longrightarrow>
    (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p i))) \<Longrightarrow>
    (\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j)) \<Longrightarrow>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j)) \<Longrightarrow>
    (\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0) \<Longrightarrow>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n)) \<Longrightarrow>
    thesis"
  shows thesis
  using assms by (auto simp: end_start_pre_def end_start_cond_def)

lemma end_start_preD:
  assumes "end_start_pre n i (L, v, c)"
  shows "end_start_invs n (L, v, c) \<and>
    (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p i))) \<and>
    (\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j)) \<and>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j)) \<and>
    (\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0) \<and>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n))"
  using assms by (auto simp: end_start_pre_def end_start_cond_def)

lemma end_start_pre_dests:
  assumes "end_start_pre n i (L, v, c)"
  shows "end_start_invs n (L, v, c)"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p i)))"
    "(\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j))"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j))"
    "(\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0)"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n))"
  using assms by (auto dest!: end_start_preD)

lemma end_start_preI:
  assumes "x = (L, v, c)"
    "end_start_invs n x"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p i)))"
    "(\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j))"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j))"
    "(\<forall>j. j < i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0)"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n))"
  shows "end_start_pre n i x"
  using assms by (auto simp: end_start_pre_def end_start_cond_def)

lemma end_start_postE:
  assumes "end_start_post n i x"
    and "x = (L, v, c)"
    and "end_start_invs n x \<Longrightarrow>    
    (\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p (Suc i)))) \<Longrightarrow>
    (\<forall>j. j \<le> i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j)) \<Longrightarrow>
    (\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j)) \<Longrightarrow>
    (\<forall>j. j \<le> i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0) \<Longrightarrow> 
    (\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n)) \<Longrightarrow> 
    thesis"
  shows thesis
  using assms by (auto simp: end_start_post_def end_start_cond_def)

lemma end_start_post_dests:
  assumes "end_start_post n i x"
    and "x = (L, v, c)"
  shows "end_start_invs n x"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p (Suc i))))"
    "(\<forall>j. j \<le> i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j))"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j))"
    "(\<forall>j. j \<le> i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0)"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n))"
  using assms by (auto simp: end_start_post_def end_start_cond_def)

lemma end_start_postI:
  assumes "x = (L, v, c)"
    and "end_start_invs n x"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> n) p (Suc i))))"
    "(\<forall>j. j \<le> i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = EndInstant (actions ! j))"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> L ! Suc j = Running (actions ! j))"
    "(\<forall>j. j \<le> i \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> c (ActEnd (actions ! j)) = 0)"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (time_index \<pi> n) j \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! j)) (time_index \<pi> n))"
  shows "end_start_post n i x"
  using assms by (auto simp: end_start_post_def end_start_cond_def)

lemma happening_pre_end_starts_dests:
  assumes "happening_pre_end_starts n x"
      and "x = (L, v, c)"
  shows "end_start_invs n (L, v, c)"
        "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))"
        "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Running (actions ! i))" 
        "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
  using assms happening_pre_end_starts_def by auto

lemma happening_pre_end_startsI:
  assumes "x = (L, v, c)"
    "end_start_invs n (L, v, c)"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_before (time_index \<pi> n) p)))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Running (actions ! i))" 
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    shows "happening_pre_end_starts n x"
  using assms happening_pre_end_starts_def by auto

lemma happening_post_end_starts_dests:
  assumes "happening_post_end_starts n x"
    and "x = (L, v, c)"
  shows "end_start_invs n (L, v, c)"
    "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> n) p)))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = EndInstant (actions ! i))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  using assms unfolding happening_post_end_starts_def by auto


lemma happening_post_end_startsI:
  assumes  "x = (L, v, c)"
  and "end_start_invs n (L, v, c)"
      "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> n) p)))"
      "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = EndInstant (actions ! i))"
      "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  shows "happening_post_end_starts n x"
  using assms unfolding happening_post_end_starts_def by auto

lemma happening_pre_instants_dests:
  assumes "happening_pre_instants n (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms unfolding happening_pre_instants_def
    by auto

lemma happening_pre_instantsI:
  assumes "x = (L, v, c)"
    "instant_action_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_before_happ n p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  shows "happening_pre_instants n x" using assms unfolding happening_pre_instants_def Let_def prod.case by auto

lemma instant_action_invs_dests:
  assumes "instant_action_invs n (L, v, c)" 
  shows "happening_invs n (L, v, c)"
    "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> n) p))"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = EndInstant (actions ! i))"
  using assms unfolding instant_action_invs_def by auto
  
lemma instant_action_invsI:
  assumes "x = (L, v, c)"
    "happening_invs n (L, v, c)"
    "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> n) p))"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
    "(\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = EndInstant (actions ! i))"
  shows "instant_action_invs n x" 
  using assms unfolding instant_action_invs_def by auto

lemma instant_pre_dests:
  assumes "instant_pre n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_part_updated_prop_state n j p))"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
  "(\<forall>i. i < j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
  "(\<forall>i. i < j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
  "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms unfolding instant_pre_def instant_cond_def by auto

lemma instant_preI:
  assumes "x = (L, v, c)"
    "instant_action_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_part_updated_prop_state n j p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i. i < j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
    "(\<forall>i. i < j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  shows "instant_pre n j x" 
  using assms unfolding instant_pre_def instant_cond_def by fastforce

lemma instant_post_dests:
  assumes "instant_post n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_part_updated_prop_state n (Suc j) p))"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
  "(\<forall>i. i < Suc j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
  "(\<forall>i. i < Suc j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  "(\<forall>i. Suc j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
  "(\<forall>i. Suc j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))" 
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms unfolding instant_post_def comp_def instant_cond_def by auto

lemma instant_postI:
  assumes "instant_action_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_part_updated_prop_state n (Suc j) p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))" 
    "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  shows "instant_post n j (L, v, c)"
  using assms unfolding instant_post_def comp_def instant_cond_def by auto

lemma instant_starting_cond_dests:
  assumes "instant_starting_cond n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_intermediate_prop_state n j p))"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n) + 1))"
  "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
  "(\<forall>i. i < j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
  "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
  "L ! Suc j = StartInstant (actions ! j)"
  "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms unfolding instant_starting_cond_def by auto

lemma instant_starting_condI:
  assumes "instant_action_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_intermediate_prop_state n j p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n) + 1))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
    "(\<forall>i. i < j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "L ! Suc j = StartInstant (actions ! j)"
    "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  shows "instant_starting_cond n j (L, v, c)" 
  using assms unfolding instant_starting_cond_def by auto 

lemma instant_ending_cond_dests:
  assumes "instant_ending_cond n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_intermediate_prop_state n j p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n) + 1))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "L ! Suc j = EndInstant (actions ! j)"
    "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  using assms unfolding instant_ending_cond_def by auto


lemma instant_ending_condI:
  assumes "instant_action_invs n (L, v, c)"
    "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_intermediate_prop_state n j p))"
    "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n) + 1))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
    "(\<forall>i. i \<le> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! i)) (time_index \<pi> n))"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> act_clock_pre_happ_spec c (ActEnd (actions ! i)) (time_index \<pi> n))"
    "L ! Suc j = EndInstant (actions ! j)"
    "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"
  shows "instant_ending_cond n j (L, v, c)"
  using assms unfolding instant_ending_cond_def by auto


lemma Lv_conds_maintained:
  assumes "Lv_conds L v"
    and "length L = length L'"
    and "L ! 0 = L' ! 0"
    and "v' PlanningLock = v PlanningLock"
    and "bounded (map_of nta_vars) v \<Longrightarrow> bounded (map_of nta_vars) v'"
  shows "Lv_conds L' v'"
  using assms unfolding Lv_conds_def by simp

lemma happening_invs_maintained:
  assumes "happening_invs n (L, v, c)"
      and Lc: "Lv_conds L v \<Longrightarrow> Lv_conds L' v'"
      and clock: 
          "\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> c' (ActStart (actions ! i))  = c (ActStart (actions ! i))"
          "\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> c' (ActEnd (actions ! i))  = c (ActEnd (actions ! i))"
          "\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> c' (ActStart (actions ! i))  = c (ActStart (actions ! i))"
          "\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> c' (ActEnd (actions ! i))  = c (ActEnd (actions ! i))"
      and Loc: "\<forall>i<length actions. is_not_happening_index (time_index \<pi> n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
  shows "happening_invs n (L', v', c')"
  apply (insert assms(1))
  apply (rule happening_invsI)
         apply (rule HOL.refl)
        apply (drule happening_invs_dests(1))
  by (auto simp: clock Loc dest: happening_invs_dests intro: Lc)

lemma end_start_invs_maintained:
  assumes "end_start_invs n (L, v, c)"
      and happ_invs: "happening_invs n (L, v, c) \<Longrightarrow> happening_invs n (L', v', c')"
      and p: "\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropVar p) = v (PropVar p)"
      and aa: "v' ActsActive  = v ActsActive"
      and clock: 
          "\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> c' (ActStart (actions ! i))  = c (ActStart (actions ! i))"
          "\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> c' (ActStart (actions ! i))  = c (ActStart (actions ! i))"
          "\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> c' (ActEnd (actions ! i))  = c (ActEnd (actions ! i))"
      and Loc: 
          "\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
          "\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
  shows "end_start_invs n (L', v', c')"
  apply (insert assms(1))
  apply (rule end_start_invsI, simp)
  by (auto dest: end_start_invs_dests simp: happ_invs p aa clock Loc)

lemma instant_action_invs_maintained:
  assumes "instant_action_invs n (L, v, c)"
      and happ_invs: "happening_invs n (L, v, c) \<Longrightarrow> happening_invs n (L', v', c')"
      and lock: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = v (PropLock p)"
      and clock: 
          "\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> c' (ActStart (actions ! i))  = c (ActStart (actions ! i))"
          "\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> c' (ActEnd (actions ! i))  = c (ActEnd (actions ! i))"
      and Loc: 
          "\<forall>i<length actions. is_starting_index (time_index \<pi> n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
          "\<forall>i<length actions. is_ending_index (time_index \<pi> n) i \<longrightarrow> L' ! Suc i = L ! Suc i"
  shows "instant_action_invs n (L', v', c')"
  apply (insert assms(1))
  apply (rule instant_action_invsI, simp)
  by (auto dest: instant_action_invs_dests simp: happ_invs lock clock Loc)

lemma happening_post_instants_dests:
  assumes "happening_post_instants n (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_instant_happ n p))"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))"  
  using assms unfolding happening_post_instants_def by auto
  
lemma happening_post_instantsI:
  assumes "instant_action_invs n (L, v, c)"
  "(\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (prop_state_after_instant_happ n p))"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> n)))"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActStart (actions ! i)) = 0)"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> c (ActEnd (actions ! i)) = 0)"
  "(\<forall>i<length actions. is_instant_index (time_index \<pi> n) i \<longrightarrow> L ! Suc i = Off (actions ! i))" 
  shows "happening_post_instants n (L, v, c)" 
  using assms unfolding happening_post_instants_def by auto

lemma happening_pre_start_starts_dests:
  assumes "happening_pre_start_starts i (L, v, c)"
  shows "start_start_invs i (L, v, c)"
  "PropVar p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropVar p) = Some (prop_state_after_instant_happ i p)"
  "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> i)))"
  "j<length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) j \<Longrightarrow>  act_clock_pre_happ_spec c (ActStart (actions ! j)) (time_index \<pi> i)"
  "j<length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) j \<Longrightarrow>  L ! Suc j = Off (actions ! j)"
  using assms unfolding happening_pre_start_starts_def by auto

lemma happening_pre_start_startsI:
  assumes "start_start_invs i (L, v, c)"
      "\<And>p. PropVar p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropVar p) = Some (prop_state_after_instant_happ i p)"
      "v ActsActive = Some (int (planning_sem.active_before (time_index \<pi> i)))"
      "\<And>ia. ia < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) ia \<Longrightarrow> act_clock_pre_happ_spec c (ActStart (actions ! ia)) (time_index \<pi> i)"
      "\<And>ia. ia < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) ia \<Longrightarrow> L ! Suc ia = Off (actions ! ia)"
  shows "happening_pre_start_starts i (L, v, c)"
  unfolding happening_pre_start_starts_def using assms by auto

lemma start_start_invs_maintained:
  assumes "start_start_invs i (L, v, c)"
      and "happening_invs i (L, v, c) \<Longrightarrow> happening_invs i (L', v', c')"
      and "(\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = v (PropLock p))"
          "(\<forall>ia<length actions. is_ending_index (time_index \<pi> i) ia \<longrightarrow> c' (ActEnd (actions ! ia)) = c (ActEnd (actions ! ia)))"
          "(\<forall>ia<length actions. is_instant_index (time_index \<pi> i) ia \<longrightarrow> c' (ActStart (actions ! ia)) = c (ActStart (actions ! ia)))"
          "(\<forall>ia<length actions. is_instant_index (time_index \<pi> i) ia \<longrightarrow> c' (ActEnd (actions ! ia)) = c (ActEnd (actions ! ia)))"
          "(\<forall>ia<length actions. is_ending_index (time_index \<pi> i) ia \<longrightarrow> L' ! Suc ia = L ! Suc ia)"
          "(\<forall>ia<length actions. is_instant_index (time_index \<pi> i) ia \<longrightarrow> L' ! Suc ia = L ! Suc ia)"
  shows "start_start_invs i (L', v', c')"
  using assms unfolding start_start_invs_def by auto

lemma start_start_invsI:
  assumes "happening_invs i (L, v, c)"
      "\<And>p. PropLock p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> i) p))"
      "\<And>ia. ia < length actions \<Longrightarrow> is_ending_index (time_index \<pi> i) ia \<Longrightarrow> c (ActEnd (actions ! ia)) = 0"
      "\<And>ia. ia < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) ia \<Longrightarrow> c (ActStart (actions ! ia)) = 0"
      "\<And>ia. ia < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) ia \<Longrightarrow> c (ActEnd (actions ! ia)) = 0"
      "\<And>ia. ia < length actions \<Longrightarrow> is_ending_index (time_index \<pi> i) ia \<Longrightarrow> L ! Suc ia = EndInstant (actions ! ia)"
      "\<And>ia. ia < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) ia \<Longrightarrow> L ! Suc ia = Off (actions ! ia)"
  shows "start_start_invs i (L, v, c)"
  unfolding start_start_invs_def using assms by auto

lemma start_start_invs_dests:
  assumes "start_start_invs i (L, v, c)"
  shows "happening_invs i (L, v, c)"
    "\<And>p. PropLock p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> i) p))"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (time_index \<pi> i) k \<Longrightarrow> c (ActEnd (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) k \<Longrightarrow> c (ActStart (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) k \<Longrightarrow> c (ActEnd (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = EndInstant (actions ! k)"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = Off (actions ! k)"
  using assms unfolding start_start_invs_def by auto

lemma start_start_preI:
  assumes "start_start_invs i (L, v, c)"
    "\<And>p. PropVar p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropVar p) = Some (starting_part_updated_prop_state i n p)"
    "v ActsActive = Some (int (updated_active_before i n))"
    "\<And>k. k < n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> c (ActStart (actions ! k)) = 0"
    "\<And>k. k < n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = StartInstant (actions ! k)"
    "\<And>k. n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = Off (actions ! k)"
  shows "start_start_pre i n (L, v, c)"
  unfolding start_start_pre_def start_start_cond_def
  using assms by auto

lemma start_start_pre_dests:
  assumes "start_start_pre i n (L, v, c)"
  shows "start_start_invs i (L, v, c)"
    "PropVar p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropVar p) = Some (starting_part_updated_prop_state i n p)"
    "v ActsActive = Some (int (updated_active_before i n))"
    "k < n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> c (ActStart (actions ! k)) = 0"
    "k < n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = StartInstant (actions ! k)"
    "n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = Off (actions ! k)"
  using assms unfolding start_start_pre_def start_start_cond_def by auto

lemma start_start_postI:
  assumes "start_start_invs i (L, v, c)"
    "\<And>p. PropVar p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropVar p) = Some (starting_part_updated_prop_state i (Suc n) p)"
    "v ActsActive = Some (int (updated_active_before i (Suc n)))"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> c (ActStart (actions ! k)) = 0"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = StartInstant (actions ! k)"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = Off (actions ! k)"
  shows "start_start_post i n (L, v, c)"
  unfolding start_start_post_def start_start_cond_def Let_def prod.case
  using assms by auto

lemma start_start_post_dests:
  assumes "start_start_post i n (L, v, c)"
  shows "start_start_invs i (L, v, c)"
    "\<And>p. PropVar p \<in> dom (map_of nta_vars) \<Longrightarrow> v (PropVar p) = Some (starting_part_updated_prop_state i (Suc n) p)"
    "v ActsActive = Some (int (updated_active_before i (Suc n)))"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> c (ActStart (actions ! k)) = 0"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = StartInstant (actions ! k)"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (time_index \<pi> i) k \<Longrightarrow> L ! Suc k = Off (actions ! k)"
  using assms unfolding start_start_post_def start_start_cond_def by auto


text \<open>The rules used to show that the composition of sequences results in a run\<close>
interpretation steps_seq: sequence_rules abs_renum.urge_bisim.A.steps
  apply standard                                 
  using abs_renum.urge_bisim.A.steps.intros(1) steps_extend .

section \<open>Properties of states\<close>
subsection \<open>The initial state\<close>



lemma initial_step_possible: "abs_renum.urge_bisim.A.steps ((ext_seq \<circ> seq_apply) [main_auto_init_edge_effect] [abs_renum.a\<^sub>0]) \<and> init_planning_state_props' (last ((ext_seq \<circ> seq_apply) [main_auto_init_edge_effect] [abs_renum.a\<^sub>0]))"
proof (rule steps_seq.ext_seq_comp_seq_apply_single_list_prop_and_post_composable[where R = init_state_props and S = init_planning_state_props])
  show "abs_renum.urge_bisim.A.steps [abs_renum.a\<^sub>0] \<and> init_state_props (last [abs_renum.a\<^sub>0])"
  proof (intro conjI, goal_cases)
    case 1
    then show ?case by rule
  next
    case 2
    then show ?case 
      apply (subst last_ConsL[OF HOL.refl])
      unfolding a\<^sub>0_alt
      apply (rule init_state_propsI)
      apply (rule HOL.refl)
      using init_vars_bounded unfolding init_vars_def
          apply simp
      apply (rule HOL.refl)
      unfolding actual_variables_correct
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
        unfolding init_planning_state_props'_def init_planning_state_props_def Let_def prod.case
        apply (elim conjE)
        apply (subst (asm) actual_variables_correct)
        apply (intro conjI allI impI)
              apply assumption
             apply assumption
            apply assumption
        subgoal for p
          apply (subst (asm) dom_map_of_conv_image_fst)
          apply (subst (asm) set_map)
          apply (cases "p \<in> set init")
           apply (subst prop_state_simps(1))
            apply assumption
           apply blast
          apply (subst prop_state_simps(2))
           apply assumption
          apply blast
          done
        subgoal for p
          apply (subst (asm) dom_map_of_conv_image_fst)
          by auto
        by blast+
      done
    done
  show "\<And>x. init_state_props x \<Longrightarrow> init_planning_state_props (main_auto_init_edge_effect x) \<and> abs_renum.urge_bisim.A.steps [x, main_auto_init_edge_effect x]"
  proof -
    fix x
    assume a: "init_state_props x"
    have x: "init_planning_state_props (main_auto_init_edge_effect x)"
      apply (rule init_state_propsE[OF a])
      subgoal for L v c
        apply (erule ssubst)
        apply (rule init_planning_state_propsI)
        unfolding main_auto_init_edge_effect_alt
               apply (rule HOL.refl)
        subgoal apply (rule Lv_condsI)
             apply simp
            apply simp
          subgoal apply (rule upds_map_bounded[where v = "v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0)"])
              apply (rule single_upd_bounded)
                 apply (erule single_upd_bounded)
                   apply (rule map_of_nta_vars_PlanningLock)
                  apply simp
                 apply simp
                apply (rule map_of_nta_vars_ActsActive)
               apply simp
              apply simp
             apply (rule HOL.refl)
            subgoal apply (rule ballI)
              subgoal for x
                apply (intro exI)
                apply (intro conjI)
                  apply (subst map_of_nta_vars_exact)
                  apply (subst map_add_find_left)
                   apply force
                  apply (subst map_add_find_left)
                   apply (rule map_of_NoneI)
                   apply force
                  apply (subst map_of_determ[of _ _ "(0, 1)"])
                    apply force
                using init_props by auto
              done
            done
          apply (subst map_upds_apply_nontin)
          by auto
        subgoal by (subst map_upds_apply_nontin) auto
            apply simp
        subgoal by (fastforce intro!: map_upds_with_map)
          apply simp
        subgoal for x
          apply (subst map_upds_apply_nontin)
          subgoal apply (rule)
            apply (frule set_mp[THEN in_actual_variablesI, rotated, of x])
            using init_props by auto
          apply (subst fun_upd_other)
           defer
           apply (subst fun_upd_other)
            defer
            apply simp
          unfolding actual_variables_exact by blast+
        by simp
      done
    moreover
    have "abs_renum.urge_bisim.A.steps [x, main_auto_init_edge_effect x]"
    proof (rule single_step_intro)
      obtain L v c where
        Lvc: "x = (L, v, c)" by (erule prod_cases3)  

      obtain L' v' c' where
        Lvc': "main_auto_init_edge_effect x = (L', v', c')" by (erule prod_cases3)

      have v': "v' = v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] map (\<lambda>x. 1) (map PropVar init))"
        using Lvc' Lvc using main_auto_init_edge_effect_alt by auto

      have "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L', v', c'\<rangle>"
      proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
        show "Simple_Network_Language.bounded (map_of nta_vars) v" 
          apply (insert a)
          apply (erule init_state_propsE)
          using Lvc by simp
        show "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L', v', c'\<rangle>"
          unfolding abs_renum.sem_def
          apply (rule step_u.step_int[where p = 0])
          unfolding TAG_def
                    apply (subst conv_trans)
                     apply (simp add: actual_autos_alt)
                    apply (subst main_auto_trans)
                    apply (rule image_eqI)
                     defer
                     apply (rule insertI1)
                    apply (rule disjI2)
                    prefer 11
                    apply (subst main_auto_init_edge_spec_def)
          apply (subst Let_def)+
                    apply (subst prod.case)+
          apply (rule HOL.refl)
          using no_committed conv_committed apply force
          subgoal apply (insert a)
            unfolding Lvc
            apply (erule init_state_propsE)
            apply simp
              apply (subst refl_True[symmetric])
              apply (rule check_bexp_is_val.intros)
               apply (rule check_bexp_is_val.intros)
               apply (subst (asm) actual_variables_exact)
               apply simp
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
      thus "(case x of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (main_auto_init_edge_effect x)"
        using Lvc Lvc' by auto
    qed
    ultimately
    show "init_planning_state_props (main_auto_init_edge_effect x) \<and> abs_renum.urge_bisim.A.steps [x, main_auto_init_edge_effect x]" by simp
  qed
qed

thm steps_seq.ext_seq'_induct_list_prop_and_post[where P = happening_pre_pre_delay and Q = happening_post and R = init_planning_state_props']

(* We need to prove these two for each happening. These are the same as the ones above *)
term "i < length (htpl \<pi>) \<Longrightarrow> happening_pre_pre_delay i s \<Longrightarrow> happening_post i (last ((map delay_and_apply [0..<length (htpl \<pi>)] ! i) s))"
term "i < length (htpl \<pi>) \<Longrightarrow> happening_pre_pre_delay i s \<Longrightarrow> abs_renum.urge_bisim.A.steps (s # (map delay_and_apply [0..<length (htpl \<pi>)] ! i) s)"

thm abs_renum.urge_bisim.A.steps.intros

(* The first function application is preceded by a delay *)

lemma apply_instant_actions_alt: "ext_seq (apply_instant_actions xs) = 
  fold (ext_seq o seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) xs) "
  unfolding apply_instant_actions_def 
  unfolding ext_seq_seq_apply'_conv_fold
  unfolding apply_snap_action_def
  by (induction xs) auto


schematic_goal action_auto_urg: "urgent ((automaton_of \<circ> conv_automaton \<circ> snd \<circ> snd) (action_to_automaton_spec a)) = ?x"
  unfolding urgent_def action_to_automaton_spec_def Let_def comp_apply fst_conv snd_conv conv_automaton_def prod.case automaton_of_def list.set ..

lemma in_setE:
  assumes "x \<in> set xs"
    and "\<And>i. i < length xs \<Longrightarrow> x = xs ! i \<Longrightarrow> thesis"
  shows thesis using assms unfolding in_set_conv_nth by blast

lemma sum_list_pos_if_ex_pos: "\<exists>x \<in> set xs. 0 < x \<Longrightarrow> (0::nat) < sum_list xs" 
  unfolding sum_list.eq_foldr apply (induction xs) apply simp
  by fastforce


lemma end_starts_possible:
  assumes "abs_renum.urge_bisim.A.steps xs \<and> happening_pre_end_starts i (last xs)"
      and end_indices: "end_indices = filter (is_ending_index (time_index \<pi> i)) [0..<length actions]"
      and i: "i < length (htpl \<pi>)"
    shows "abs_renum.urge_bisim.A.steps ((ext_seq \<circ> seq_apply) (map edge_3_effect end_indices) xs) \<and> 
          happening_pre_instants i (last ((ext_seq \<circ> seq_apply) (map edge_3_effect end_indices) xs))"
proof -
  interpret eip: filter_sorted_distinct_list "[0..<length actions]" "is_ending_index (time_index \<pi> i)" end_indices 
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
  
  have end_indices_inc_all: "\<not> is_ending_index (time_index \<pi> i) m"
    if "Suc j < length end_indices" "Suc (end_indices ! j) \<le> m" "m < end_indices ! Suc j" for j m
    apply (rule eip.ys_inc_all)
    using eij_in_act' that by auto

  have end_indices_inc_all_below: "\<not> is_ending_index (time_index \<pi> i) m"
    if "0 < length end_indices" "m < end_indices ! 0" for m
    apply (rule eip.ys_inc_all_below)
    using that eij_in_act'[OF that(1)] by auto

  have end_indices_inc_all_above: "\<not> is_ending_index (time_index \<pi> i) m"
    if "end_indices ! (length end_indices - 1) < m" "m < length actions" for m
    apply (rule eip.ys_inc_all_above)
    using that by auto

  have image_end_indices_conv_actions: "((!) actions) ` set end_indices = planning_sem.ending_actions_at (time_index \<pi> i)"
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
  
    have eij_ending: "is_ending_index (time_index \<pi> i) (end_indices ! j)"
      using set_nthI[OF j]
      apply -
      apply (subst (asm) (2) end_indices)
      by simp
  
    obtain L v c where
      s: "s = (L, v, c)" using prod_cases3 by blast


    have v_PropLock: "v (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> i) p (end_indices ! j)))"
      if p_in_vars: "PropLock p \<in> dom (map_of nta_vars)" for p
      apply (insert esp)
      unfolding s
      apply (drule end_start_preD)
      using p_in_vars by simp
  

    define v' where "v' = (v(map PropLock (over_all (actions ! (end_indices ! j))) [\<mapsto>] map (\<lambda>x. (the \<circ> v) x - 1) (map PropLock (over_all (actions ! (end_indices ! j))))))"
    
    have variables_locked_after:"v' (PropLock p) = Some (int (partially_updated_locked_before (time_index \<pi> i) p (Suc (end_indices ! j))))" 
      if p_in_vars: "PropLock p \<in> dom (map_of nta_vars)" 
      for p
    proof (cases "p \<in> set (over_all (actions ! (end_indices ! j)))")
      case True
        have v'_PropLock: "v' (PropLock p) = Some (the (v (PropLock p)) - 1)"
          unfolding v'_def
          apply (subst distinct_map_upds)
          using True eij_in_act apply simp
          apply (rule distinct_inj_map)
          apply (rule distinct_over_all[THEN bspec[of _ _ "actions ! (end_indices ! j)"]])
          using eij_in_act apply simp
          unfolding inj_def apply simp
          unfolding comp_def by simp
      
      have pudp_Suc: "partially_updated_locked_before (time_index \<pi> i) p (Suc (end_indices ! j)) = partially_updated_locked_before (time_index \<pi> i) p (end_indices ! j) - 1"
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
        apply (subst v'_PropLock)
        apply (subst pudp_Suc)
        apply (subst v_PropLock[OF p_in_vars])
        using partially_updated_locked_before_pos[OF i] True eij_in_act eij_ending i
        by fastforce
    next
      case False
      have "partially_updated_locked_before (time_index \<pi> i) p (Suc (end_indices ! j)) = partially_updated_locked_before (time_index \<pi> i) p (end_indices ! j)" 
        unfolding partially_updated_locked_before_def using False by simp
      moreover
      have "v' (PropLock p) = v (PropLock p)"
        unfolding v'_def
        apply (subst map_upds_apply_nontin)
        using False by auto
      ultimately
      show ?thesis using v_PropLock p_in_vars by presburger
    qed
    
    have bounded_after: "Simple_Network_Language.bounded (map_of nta_vars) v'"
    proof (rule updated_bounded[OF _ _ v'_def], goal_cases)
      case 1
      then show ?case 
        apply (insert esp) unfolding s 
        by (auto dest: end_start_pre_dests end_start_invs_dests happening_invs_dests Lv_conds_dests)
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
            apply (rule map_of_nta_vars_action_inv[OF eij_in_act(2)])
          using variables_locked_after map_of_nta_vars_action_inv[OF eij_in_act(2)] partially_updated_locked_before_ran by fastforce+
        done
      done
    qed 

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
                 apply (subst map_upds_apply_nontin, force)+
                apply simp
                using bounded_after
                unfolding v'_def by auto
              subgoal by simp
              subgoal
                apply (intro allI impI)
                apply (frule index_case_disj)
                using eij_ending nth_actions_unique eij_in_act 
                by (auto simp: fun_upd_other)
              subgoal 
                by simp
              subgoal 
                apply (intro allI impI)
                apply (frule index_case_disj)
                using eij_ending nth_actions_unique eij_in_act 
                by (auto simp: fun_upd_other)
              subgoal 
                apply (intro allI impI)
                apply (frule index_case_disj)
                apply (subst nth_list_update_neq)
                using eij_ending by auto
              done
            subgoal
              apply (intro allI impI)
              apply (subst map_upds_apply_nontin)
              by auto
            subgoal
              apply (subst map_upds_apply_nontin)
              by auto
            subgoal
              apply (intro allI impI)
              apply (frule index_case_disj)
              using eij_ending nth_actions_unique eij_in_act
              by (auto simp: fun_upd_other)
            subgoal 
                apply (intro allI impI)
                apply (frule index_case_disj)
              using eij_ending nth_actions_unique eij_in_act 
              by (auto simp: fun_upd_other)
            subgoal
                apply (intro allI impI)
                apply (frule index_case_disj)
              using eij_ending nth_actions_unique eij_in_act 
              by (auto simp: fun_upd_other)
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
              by (auto dest: end_start_pre_dests(3))
            done
          subgoal apply (intro allI impI)
            subgoal for k
              apply (cases "k < end_indices ! j")
              by (auto dest: end_start_pre_dests(4))
            done
          subgoal apply (intro allI impI)
            subgoal for k
              apply (cases "k < end_indices ! j")
              by (auto dest: end_start_pre_dests(5))
            done
          subgoal by (auto simp: nth_actions_unique dest: end_start_pre_dests(6))
          done
        subgoal apply (insert esp j)
          apply (rule single_step_intro)
          unfolding s prod.case edge_3_effect_alt Let_def prod.case
          apply (rule non_t_step_intro[where a="Internal (STR '''')", simplified])
           prefer 2
          subgoal by (force dest: end_start_pre_dests(1) end_start_invs_dests(1) happening_invs_dests(1) Lv_conds_dests)
          unfolding abs_renum.sem_def
          apply (rule step_u.step_int[simplified TAG_def])
                    apply (subst conv_trans[of "Suc (end_indices ! j)"])
          using eij_in_act actual_autos_alt apply simp
                    apply (rule image_eqI[of _ _ "edge_3_spec (actions ! (end_indices ! j))"])
                     apply (subst edge_3_spec_def)
                     apply simp
          using nth_auto_trans eij_in_act apply simp
          subgoal using eij_in_act length_actual_autos no_committed conv_committed by auto
          subgoal by rule
          subgoal apply (intro guard_append)
            using eij_in_act eij_ending
            apply (auto intro: ending_actions_sat_dur_const_specs dest!: end_start_pre_dests(1)  end_start_invs_dests(1)  happening_invs_dests(2) simp: is_ending_index_def)[2]
            unfolding map_map[symmetric]
            subgoal apply (rule ending_actions_sat_mutex_const_specs)
                    apply (auto intro: eij_in_act intro: eij_ending simp: is_ending_index_def[symmetric])[2]
                  apply (auto dest!: end_start_pre_dests(1) end_start_invs_dests(1) dest: happening_invs_dests(2,3,4,5) simp: index_case_defs set_conv_nth)[4]
              by (auto dest!: end_start_pre_dests(6) intro: eij_in_act eij_ending)[1]
            subgoal apply (rule ending_actions_sat_mutex_const_specs)
                    apply (auto intro: eij_in_act intro: eij_ending simp: is_ending_index_def[symmetric])[2]
                  apply (auto dest!: end_start_pre_dests(1) end_start_invs_dests(1) dest: happening_invs_dests(2,3,4,5) simp: index_case_defs set_conv_nth)[4]
              by (auto dest!: end_start_pre_dests(6) intro: eij_in_act eij_ending)[1]
            done
          subgoal using no_invs by simp
          subgoal using eij_in_act eij_ending by (blast dest: end_start_pre_dests(4))
          subgoal using eij_in_act by (auto dest!: end_start_pre_dests(1) end_start_invs_dests(1) happening_invs_dests(1) Lv_conds_dests(1))
          subgoal by blast
          subgoal by simp
          subgoal 
            apply (rule is_upds_inc_vars[rotated, rotated])
               apply (subst inc_prop_lock_ab_def) 
               apply (subst map_map[symmetric, of _ PropLock])
               apply blast
              apply (subst map_map)+
              apply (subst comp_def)+
            apply blast
             apply (rule subsetI)
            subgoal for x
              apply (drule end_start_pre_dests(2))
              apply (frule map_of_nta_vars_action_inv[rotated])
               apply (rule eij_in_act)
              by auto
            by (auto intro: distinct_inj_map simp: distinct_over_all eij_in_act inj_def)
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
        subgoal apply (drule end_start_post_dests(2), simp)
          apply (subst partially_updated_locked_before_inv[where n = "(Suc (end_indices ! i))", symmetric])
          using eip.ys_mono[rotated] apply fastforce
          using end_indices_inc_all is_ending_index_def by auto
        subgoal apply (drule end_start_post_dests(3), simp)
          apply (intro impI allI, elim conjE)
          subgoal for j
            by (cases "j \<le> end_indices ! i") (auto simp: end_indices_inc_all)
          done
        subgoal apply (drule end_start_post_dests(4), simp)
          by (auto dest: eip.ys_mono[rotated])
        subgoal apply (drule end_start_post_dests(5), simp)
          apply (intro impI allI, elim conjE)
          subgoal for j
            by (cases "j \<le> end_indices ! i") (auto simp: end_indices_inc_all)
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
        subgoal apply (drule happening_pre_end_starts_dests(2), simp)
          apply (subst partially_updated_locked_before_inv[where n = 0, symmetric], simp)
          using end_indices_inc_all_below[simplified is_ending_index_def] apply blast
          using partially_updated_locked_before_0_is_locked_before by simp
        subgoal apply (drule happening_pre_end_starts_dests(3), simp)
          by (auto simp: end_indices_inc_all_below)
        subgoal by (drule happening_pre_end_starts_dests(3), simp+)
        subgoal apply (drule happening_pre_end_starts_dests(4), simp)
          by (auto simp: end_indices_inc_all_below)
        subgoal by (drule happening_pre_end_starts_dests(4), simp+)
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
        subgoal apply (drule end_start_post_dests(2), simp)
          apply (subst partially_updated_locked_before_by_all_actions_is_locked_during[symmetric])
          apply (subst partially_updated_locked_before_inv[symmetric, where n = "Suc (end_indices ! (length end_indices - 1))"])
          subgoal using eip.nth_ys_ran by (force intro: Suc_leI)
          by (auto simp: end_indices_inc_all_above[simplified is_ending_index_def])
        subgoal apply (intro allI impI)
          subgoal for k
            by (cases "k \<le> end_indices ! (length end_indices - 1)"; 
              force dest!: end_indices_inc_all_above[rotated] end_start_post_dests(3))
          done
      subgoal apply (intro allI impI)
        subgoal for k
          by (cases "k \<le> end_indices ! (length end_indices - 1)"; 
              force dest!: end_indices_inc_all_above[rotated] end_start_post_dests(5))
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
        subgoal 
          apply (rule instant_action_invsI, simp)
          subgoal by (auto dest!: happening_post_end_starts_dests(1) dest: end_start_invs_dests)
          subgoal using happening_post_end_starts_dests(2) by auto
          subgoal by (auto dest!: happening_post_end_starts_dests(1) dest: end_start_invs_dests)
          subgoal by (force dest: happening_post_end_starts_dests)
          subgoal by (auto dest!: happening_post_end_starts_dests(1) dest: end_start_invs_dests)
          subgoal by (force simp: happening_post_end_starts_dests)
          done
        by (auto dest!: happening_post_end_starts_dests(1) dest: end_start_invs_dests)
      done
  qed
qed

lemma Suc_lessI: "n < m - 1 \<Longrightarrow> Suc n < m" by auto

lemma instant_actions_possible:
  assumes "abs_renum.urge_bisim.A.steps xs \<and> happening_pre_instants i (last xs)"
      and instant_indices: "instant_indices = filter (is_instant_index (time_index \<pi> i)) [0..<length actions]"
      and i: "i < length (htpl \<pi>)"
    shows "abs_renum.urge_bisim.A.steps (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) instant_indices) xs) 
  \<and> happening_pre_start_starts i (last (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) instant_indices) xs))"
proof -                             
  interpret iip: filter_sorted_distinct_list "[0..<length actions]" "is_instant_index (time_index \<pi> i)" instant_indices
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
  
  have instant_indices_inc_all: "\<not> is_instant_index (time_index \<pi> i) m"
    if "Suc j < length instant_indices" "Suc (instant_indices ! j) \<le> m" "m < instant_indices ! Suc j" for j m
    apply (rule iip.ys_inc_all)
    using iij_in_act' that by auto

  have instant_indices_inc_all_below: "\<not> is_instant_index (time_index \<pi> i) m"
    if "0 < length instant_indices" "m < instant_indices ! 0" for m
    apply (rule iip.ys_inc_all_below)
    using that iij_in_act'[OF that(1)] by auto

  have instant_indices_inc_all_above: "\<not> is_instant_index (time_index \<pi> i) m"
    if "instant_indices ! (length instant_indices - 1) < m" "m < length actions" for m
    apply (rule iip.ys_inc_all_above)
    using that by auto

  have image_instant_indices_conv_actions: "((!) actions) ` set instant_indices = planning_sem.instant_actions_at (time_index \<pi> i)"
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
    have "(actions ! (instant_indices ! j)) \<in> planning_sem.instant_actions_at (time_index \<pi> i)" by blast
    
    hence iij_instant: "planning_sem.is_instant_action (time_index \<pi> i) (actions ! (instant_indices ! j))"
      and iij_in_act: "actions ! (instant_indices ! j) \<in> set actions" using planning_sem.instant_actions_at_def by simp_all

    have iij_instant_index: "is_instant_index (time_index \<pi> i) (instant_indices ! j)" apply (insert iij_set) apply (subst (asm) (2) instant_indices) by simp

    have iij_ran: "instant_indices ! j < length actions" 
      apply (insert iij_set)
      apply (subst (asm) (2) instant_indices)
      by simp

    
    have v_pre_conds_sat: "Simple_Expressions.check_bexp v (bexp_and_all (map (is_prop_ab 1) (pre (at_start (actions ! (instant_indices ! j)))))) True"
      if prop_state: "\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropVar p) = Some (instant_part_updated_prop_state i (instant_indices ! j) p)" for v
    proof -
      { fix p
        assume p: "p \<in> set (pre (at_start (actions ! (instant_indices ! j))))"
        moreover
        have "PropVar p \<in> dom (map_of nta_vars)" using map_of_nta_vars_action_start_pre iij_in_act p by auto
        ultimately
        have "v (PropVar p) = Some 1" using pre_val_in_instant_part_updated_prop_state_if i  prop_state iij_ran iij_instant[simplified planning_sem.is_instant_action_def] by metis 
        hence "Simple_Expressions.check_bexp v (is_prop_ab 1 p) True" 
          unfolding is_prop_ab_def comp_def
          by (simp add: check_bexp_simps  is_val_simps)
      } 
      hence "\<forall>b\<in>set (map (is_prop_ab 1) (pre (at_start (actions ! (instant_indices ! j))))). Simple_Expressions.check_bexp v b True" by auto
      thus ?thesis using check_bexp_all by blast
    qed
    
    have v_lock_conds_sat: "Simple_Expressions.check_bexp v (bexp_and_all (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! (instant_indices ! j))))) (dels (at_start (actions ! (instant_indices ! j))))))) True"
      if locked: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> i) p))" for v
    proof -
      { fix p
        assume p: "p \<notin> set (adds (at_start (actions ! (instant_indices ! j))))"
               "p \<in> set (dels (at_start (actions ! (instant_indices ! j))))"
        hence "p \<notin> planning_sem.plan_invs_during (time_index \<pi> i)" using planning_sem.snap_does_not_delete_inv iij_instant planning_sem.action_happening_case_defs by auto
        hence "planning_sem.locked_during (time_index \<pi> i) p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
        moreover
        have "PropLock p \<in> dom (map_of nta_vars)" using map_of_nta_vars_action_start_del_lock iij_in_act p by auto
        ultimately
        have "v (PropLock p) = Some 0" using locked unfolding int_of_nat_def by simp
        hence "Simple_Expressions.check_bexp v (is_prop_lock_ab 0 p) True" 
          unfolding is_prop_lock_ab_def 
          by (simp add: check_bexp_simps  is_val_simps)
      } 
      hence "\<forall>b\<in>set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start (actions ! (instant_indices ! j))))) (dels (at_start (actions ! (instant_indices ! j)))))). Simple_Expressions.check_bexp v b True"  by auto
      thus ?thesis using check_bexp_all by blast
    qed

    have v_ending_pre_conds_sat: "Simple_Expressions.check_bexp v' (bexp_and_all (map (is_prop_ab 1) (pre (at_end (actions ! (instant_indices ! j)))))) True"
      if prop_state: "\<forall>p. PropVar p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropVar p) = Some (instant_intermediate_prop_state i (instant_indices ! j) p)" for v'
    proof -
      { fix p
        assume p: "p \<in> set (pre (at_end (actions ! (instant_indices ! j))))"
        moreover
        have "PropVar p \<in> dom (map_of nta_vars)" using  p iij_in_act p map_of_nta_vars_action_end_pre by auto
        ultimately
        have "v' (PropVar p) = Some 1" using pre_val_in_instant_intermediate_prop_state_if[OF i _ iij_instant_index] using iij_ran p prop_state by auto
    
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
      if locked: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v' (PropLock p) = Some (int (planning_sem.locked_during (time_index \<pi> i) p))" for v'
    proof -
      { fix p
        assume p: "p \<notin> set (adds (at_end (actions ! (instant_indices ! j))))"
               "p \<in> set (dels (at_end (actions ! (instant_indices ! j))))"
        hence "p \<notin> planning_sem.plan_invs_during (time_index \<pi> i)" using planning_sem.snap_does_not_delete_inv iij_instant planning_sem.action_happening_case_defs by auto
        hence "planning_sem.locked_during (time_index \<pi> i) p = 0" using planning_sem.in_invs_during_iff_locked_during by blast
        moreover
        have "PropLock p \<in> dom (map_of nta_vars)" using map_of_nta_vars_action_end_del_lock p iij_in_act by auto
        ultimately
        have "v' (PropLock p) = Some 0" using locked by simp
        
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
                 apply (((subst map_upds_apply_nontin | subst fun_upd_other), force)+, simp)
                subgoal 
            apply (rule upds_map_bounded)
              prefer 2
              apply (rule HOL.refl)
             apply (rule upds_map_bounded)
               prefer 2
               apply (rule HOL.refl)
              apply (rule single_upd_bounded)
                 apply simp
                apply (rule map_of_nta_vars_ActsActive)
                     apply (drule instant_ending_cond_dests(3)) 
                  apply simp
            subgoal using planning_sem.active_before_less_if_scheduled iij_instant iij_in_act instant_ending_cond_dests(3)
              by (fastforce simp: planning_sem.action_happening_case_defs card_action_set)
            subgoal by (force intro: map_of_nta_vars_action_end_del iij_instant iij_in_act)+
            subgoal by (force intro: map_of_nta_vars_action_end_add iij_instant iij_in_act)+
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
        apply (subst map_upds_apply_nontin, force)+
        apply (subst fun_upd_other)
        by simp_all
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
             apply force
            apply (subst map_upds_with_map)
            by simp+
          subgoal apply (subst map_upds_apply_nontin, force)+ 
            by (auto simp: instant_intermediate_prop_state_def[OF i])
          done
        done
      subgoal by (subst map_upds_apply_nontin, force)+ (use instant_ending_cond_dests(3) in fastforce)
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
      unfolding abs_renum.sem_def
       apply (rule step_u.step_int[simplified TAG_def, where p = "Suc (instant_indices ! j)"])
                 apply (subst conv_trans)
      using iij_ran length_actual_autos apply simp
                 apply (rule image_eqI[where x = "end_edge_spec (actions ! (instant_indices ! j))"])
      apply (subst end_edge_spec_def) apply simp
                 apply (subst nth_auto_trans)
      using iij_ran apply simp
                 apply simp
      using conv_committed[simplified length_map] no_committed iij_ran length_actual_autos apply simp
      subgoal apply (intro check_bexp_all_append v_ending_lock_conds_sat v_ending_pre_conds_sat)
        using instant_ending_cond_dests(1,2) instant_action_invs_dests(2) by fast+ 
      subgoal by simp
      subgoal using conv_invs no_invs by simp
      subgoal using instant_ending_cond_dests by fast
      subgoal by (fastforce dest!: instant_ending_cond_dests(1) instant_action_invs_dests(1) happening_invs_dests(1) simp: Lv_conds_dests(1) iij_ran) 
      subgoal by auto
      subgoal by auto
      subgoal apply (rule is_upds.intros)
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
        apply (subst instant_ending_cond_dests, assumption)
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
        by simp
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
          using iij_instant_index iij_ran nth_actions_unique
          by (auto dest: index_case_dests_disj intro: nth_list_update_neq)
        using iij_instant_index iij_ran nth_actions_unique 
          by (auto dest: index_case_dests_disj intro: nth_list_update_neq)
      subgoal by (auto dest: instant_starting_cond_dests(2))
      subgoal by (auto dest: instant_starting_cond_dests intro: map_upds_apply_nontin) 
      subgoal by (auto dest: index_case_dests_disj instant_starting_cond_dests)
      subgoal by (auto dest!: instant_starting_cond_dests(5) elim: nat_leE)
      subgoal by (auto dest: instant_starting_cond_dests)
      subgoal using nth_actions_unique by (auto dest!: instant_starting_cond_dests(7)) 
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
      unfolding abs_renum.sem_def
        apply (rule step_u.step_int)
      unfolding TAG_def
                  apply (subst conv_trans[of "Suc (instant_indices ! j)"])
      using length_actual_autos iij_ran apply simp
                  apply (subst nth_auto_trans)
      using iij_ran apply simp
                  apply (rule image_eqI[where x = "instant_trans_edge_spec (actions ! (instant_indices ! j))"])
                   apply (subst instant_trans_edge_spec_def)
                   apply simp
                  apply simp
      subgoal using no_committed conv_committed by auto
                apply rule
      subgoal apply (intro guard_append)
        subgoal 
          apply (rule l_dur_spec_sat_if)
          apply (rule planning_sem.instant_act_sat_dur_bounds)
          using iij_instant iij_instant_index iij_in_act
          by (auto dest!: instant_starting_cond_dests(4))
        subgoal 
          apply (rule u_dur_spec_sat_if)
          apply (rule planning_sem.instant_act_sat_dur_bounds)
          using iij_instant iij_instant_index iij_in_act
          by (auto dest!: instant_starting_cond_dests(4))
        subgoal apply (rule instant_action_sat_mutex_end)
                 apply (rule iij_in_act)
                apply (rule iij_instant)
          unfolding set_conv_nth
               apply (auto simp: index_case_defs dest!: instant_starting_cond_dests(1) instant_action_invs_dests(1) dest: happening_invs_dests)[4]
          by (auto dest!: instant_starting_cond_dests(7) simp: iij_instant_index iij_ran )
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
             apply ((subst map_upds_apply_nontin | subst fun_upd_other), fastforce)+
             apply simp
            apply (rule upds_map_bounded'[OF _ _ HOL.refl])
              apply (rule upds_map_bounded'[OF _ _ HOL.refl])
                apply (erule single_upd_bounded)
                  apply (rule map_of_nta_vars_ActsActive)
            subgoal using instant_pre_dests(3) by fastforce
            subgoal using planning_sem.active_before_less_if_scheduled iij_instant iij_in_act card_action_set planning_sem.action_happening_case_defs 
              by (fastforce dest:instant_pre_dests(3))
            using iij_instant map_of_nta_vars_action_start_del map_of_nta_vars_action_start_add iij_in_act
            by (auto dest: instant_pre_dests)
          using iij_instant_index iij_ran nth_actions_unique
          by (auto dest: index_case_dests_disj intro: nth_list_update_neq)
        subgoal by ((subst map_upds_apply_nontin | subst fun_upd_other), fastforce)+ simp
        using iij_instant_index iij_ran nth_actions_unique
        by (auto dest: index_case_dests_disj intro: nth_list_update_neq)
      subgoal apply (intro allI impI)
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
          apply fastforce
         apply (subst map_upds_with_map)
           apply simp
          apply simp
        apply simp
        apply ((subst map_upds_apply_nontin | subst fun_upd_other), force)+
        by (auto simp: instant_pre_dests(2) instant_part_updated_prop_state_def i)
      done
    subgoal 
      apply ((subst map_upds_apply_nontin | subst fun_upd_other), force)+
      by (force dest: instant_pre_dests(3))
    subgoal using instant_pre_dests iij_instant by (auto elim: nat_leE)
    subgoal by (auto dest: instant_pre_dests(5))
    subgoal using nth_actions_unique iij_instant iij_ran 
      by (auto dest: instant_pre_dests)
    subgoal by (auto dest: instant_pre_dests)
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
      unfolding abs_renum.sem_def
        apply (rule step_int[where p = "Suc (instant_indices ! j)"])
      unfolding TAG_def
                  apply (subst conv_trans)
      using iij_ran actual_autos_alt apply simp
                  apply (rule image_eqI[where x = "start_edge_spec (actions ! (instant_indices ! j))"])
                   apply (subst start_edge_spec_def)
                   apply simp
                  apply (subst nth_auto_trans)
      using iij_ran actual_autos_alt apply simp
                  apply simp
      subgoal using conv_committed no_committed by auto
      subgoal apply (rule check_bexp_all_append)
        subgoal apply (drule instant_pre_dests(1)) by (auto intro: v_pre_conds_sat v_lock_conds_sat dest: instant_action_invs_dests)
        subgoal by (auto intro: v_pre_conds_sat v_lock_conds_sat dest: instant_pre_dests)
        done
      subgoal apply (intro guard_append instant_action_sat_mutex_start[OF iij_in_act iij_instant])
        using iij_ran iij_instant_index instant_pre_dests(6)
        by (auto dest!: instant_pre_dests(1)[THEN instant_action_invs_dests(1)] dest: happening_invs_dests simp: index_case_defs set_conv_nth)
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
           apply (rule check_bexp_is_val.intros(12)[where v= "the (v ActsActive)"])
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
    hence "planning_sem.instant_actions_at (time_index \<pi> i) = {}"
      apply -
      unfolding instant_indices planning_sem.instant_actions_at_def is_instant_index_def 
      apply (subst set_conv_nth)
      by auto
    hence no_instant: "planning_sem.instant_actions_at (time_index \<pi> i) = {}"
           "planning_sem.instant_snaps_at (time_index \<pi> i) = {}" 
      using planning_sem.instant_snaps_at_def by auto

    have not_instant: "\<not>is_instant_index (time_index \<pi> i) j" if "j < length actions" for j 
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
        using not_instant  by (auto intro: happening_pre_instants_dests)
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
        subgoal using happening_pre_instants_dests instant_indices_inc_all_below by blast
        subgoal by (drule happening_pre_instants_dests(5)) (use instant_indices_inc_all_below in auto)
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
        apply (rule happening_pre_start_startsI)
        subgoal by (rule start_start_invsI) (auto dest: happening_post_instants_dests instant_action_invs_dests)
        subgoal by (auto dest: happening_post_instants_dests)
        subgoal using happening_post_instants_dests by simp
        by (auto dest!: happening_post_instants_dests(1) dest: instant_action_invs_dests)
      done
  qed 
qed

lemma start_starts_possible: 
  assumes "abs_renum.urge_bisim.A.steps xs \<and> happening_pre_start_starts i (last xs)"
  assumes i: "i < length (htpl \<pi>)" 
  assumes start_indices: "start_indices = filter (is_starting_index (time_index \<pi> i)) [0..<length actions]"
  shows " abs_renum.urge_bisim.A.steps ((ext_seq \<circ> seq_apply) (map start_edge_effect start_indices) xs) \<and>  happening_pre_end_ends i (last ((ext_seq \<circ> seq_apply) (map start_edge_effect start_indices) xs))"
proof -
  interpret sip: filter_sorted_distinct_list "[0..<length actions]" "is_starting_index (time_index \<pi> i)" start_indices
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
  
  have start_indices_inc_all: "\<not> is_starting_index (time_index \<pi> i) m"
    if "Suc j < length start_indices" "Suc (start_indices ! j) \<le> m" "m < start_indices ! Suc j" for j m
    apply (rule sip.ys_inc_all)
    using sij_in_act' that by auto

  have start_indices_inc_all_below: "\<not> is_starting_index (time_index \<pi> i) m"
    if "0 < length start_indices" "m < start_indices ! 0" for m
    apply (rule sip.ys_inc_all_below)
    using that sij_in_act'[OF that(1)] by auto

  have start_indices_inc_all_above: "\<not> is_starting_index (time_index \<pi> i) m"
    if "start_indices ! (length start_indices - 1) < m" "m < length actions" for m
    apply (rule sip.ys_inc_all_above)
    using that by auto

  have image_start_indices_conv_actions: "((!) actions) ` set start_indices = planning_sem.starting_actions_at (time_index \<pi> i)"
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
      have *: "(actions ! (start_indices ! j)) \<in> planning_sem.starting_actions_at (time_index \<pi> i)" using j by blast
      
      hence sij_starting: "planning_sem.is_starting_action (time_index \<pi> i) (actions ! (start_indices ! j))"  
        and sij_in_act[intro]: "actions ! (start_indices ! j) \<in> set actions"  using * planning_sem.starting_actions_at_def j by auto
  
      have sij_starting_index: "is_starting_index (time_index \<pi> i) (start_indices ! j)" apply (insert sij_set) apply (subst (asm) (2) start_indices) by simp
  
      have sij_ran: "start_indices ! j < length actions" 
        apply (insert sij_set)
        apply (subst (asm) (2) start_indices)
        by simp

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
                 apply (((subst map_upds_apply_nontin | subst fun_upd_other), force)+, simp)
              subgoal apply (rule upds_map_bounded[rotated])
                 apply (subst comp_def[of "\<lambda>x. 1" PropVar, symmetric])
                  apply (subst map_map[symmetric])
                  apply (rule HOL.refl)
                using map_of_nta_vars_action_start_add apply fastforce
                apply (rule upds_map_bounded[rotated])
                  apply (subst comp_def[of "\<lambda>x. 0" PropVar, symmetric])
                  apply (subst map_map[symmetric])
                  apply (rule HOL.refl)
                using map_of_nta_vars_action_start_del apply fastforce
                apply (erule single_upd_bounded)
                  apply (rule map_of_nta_vars_ActsActive)
                 apply (fastforce simp: start_start_pre_dests)
                apply (subst start_start_pre_dests, assumption)
                using updated_active_before_less_if_starting[OF i sij_starting_index sij_ran] by simp
              done
            by ((intro strip, (subst nth_list_update_neq)?, (frule index_case_dests_disj)?); (use nth_actions_unique[OF sij_ran] sij_starting_index in force))+
          subgoal apply (intro strip)
            apply ((subst map_upds_apply_nontin|subst fun_upd_other), force)+
            by simp
          by ((intro strip, (subst nth_list_update_neq)?, (frule index_case_dests_disj)?); (use nth_actions_unique[OF sij_ran] sij_starting_index in force))+
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
           apply force
          apply (cases "p \<in> set (dels (at_start (actions ! (start_indices ! j))))")
           apply (subst map_upds_with_map)
             apply simp
            apply simp
           apply simp
          apply (subst map_upds_apply_nontin)
           apply force
          apply (subst fun_upd_other)
           apply simp
          apply (drule start_start_pre_dests(2), assumption)
          unfolding starting_part_updated_prop_state_def[OF i] prop_state_def starting_part_updated_state_seq_def[OF i]
          by simp
      next
        case 3
        then show ?case 
          apply -
          apply (subst updated_active_before_Suc)
          using i sij_starting_index sij_ran apply auto[3]
          apply (subst map_upds_apply_nontin, force)+
          by (auto simp: start_start_pre_dests)
      next
        case (4 k)
        then show ?case 
          apply (cases "k = start_indices ! j")
          using sij_L start_start_pre_dests by auto
      next
        case (5 k)
        then show ?case 
          apply (cases "k = start_indices ! j")
          using sij_L start_start_pre_dests by auto
      next
        case (6 k)
        then show ?case 
          apply (cases "k = start_indices ! j")
          using sij_L start_start_pre_dests by auto
      qed
    next
      case (2 L v c)
      then show ?case 
        apply -
        unfolding comp_def start_edge_effect_alt
        apply (rule single_step_intro)
        unfolding prod.case
        apply (rule non_t_step_intro[where a = "Internal (STR '''')"])
        unfolding abs_renum.sem_def
          apply (rule step_u.step_int)
        unfolding TAG_def
                    apply (subst conv_trans[where p = "Suc (start_indices ! j)"])
        using sij_ran length_actual_autos apply simp
                    apply (rule image_eqI[where x = "start_edge_spec (actions ! (start_indices ! j))"])
                     apply (simp add: start_edge_spec_def)
                    apply (simp add: sij_ran nth_auto_trans)
                   apply (use conv_committed no_committed in simp)
    qed
    
  next
    case (2 j s)
    then show ?case sorry
  next
    case (3 x)
    then show ?case sorry
  next
    case (4 x)
    then show ?case sorry
  next
    case (5 x)
    then show ?case sorry
  next
    case (6 x)
    then show ?case sorry
  qed
qed

lemma happening_steps_possible:
  assumes i: "i < length (htpl \<pi>)" 
      and pres: "happening_pre_pre_delay i s"
  shows "abs_renum.urge_bisim.A.steps (s#delay_and_apply i s) \<and> happening_post i (last (delay_and_apply i s))" 
proof -
  let ?seq = "(ext_seq \<circ> seq_apply) (map edge_2_effect (filter (is_starting_index (time_index \<pi> i)) [0..<length actions]))
           ((ext_seq \<circ> seq_apply) (map end_edge_effect (filter (is_ending_index (time_index \<pi> i)) [0..<length actions]))
             ((ext_seq \<circ> seq_apply) (map start_edge_effect (filter (is_starting_index (time_index \<pi> i)) [0..<length actions]))
               (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (time_index \<pi> i)) [0..<length actions])) 
                ((ext_seq \<circ> seq_apply) (map edge_3_effect (filter (is_ending_index (time_index \<pi> i)) [0..<length actions])) [delay (get_delay i) s]))))"
  presume p: "abs_renum.urge_bisim.A.steps ?seq \<and> happening_post i (last ?seq)"

  have delay_non_negative: "0 \<le> get_delay i" 
    unfolding get_delay_def
    apply (cases "i = 0")
     apply (subst if_P, simp)
    using eps_range apply simp
    apply (subst if_not_P, simp)
    using time_index_sorted_list[of "i - 1" "i"] assms(1)
    by auto

  obtain L v c where
    s: "s = (L, v, c)" using prod_cases3 by blast

  obtain c' where
    c': "c' = c \<oplus> get_delay i" 
    and Lvc': "(L, v, c') = delay (get_delay i) (L, v, c)"
    unfolding delay_def by simp

  from pres[simplified s happening_pre_pre_delay_def Let_def happening_pre_def]
  have Lv_con: "Lv_conds L v" by fastforce
  
  have no_urgent: "\<forall>p<length (fst (snd abs_renum.sem)). fst (L, v, c) ! p \<notin> urgent (fst (snd abs_renum.sem) ! p)"
  proof (intro allI impI)
    have len_L: "length L = Suc (length actions)" using Lv_con unfolding Lv_conds_def by blast

    fix p
    assume "p <length (fst (snd abs_renum.sem))"
    hence pl: "p < Suc (length actions)"
          "p < length L"
      using n_ps_conv_Suc_length_actions
      unfolding Prod_TA_Defs.n_ps_def
      unfolding sem_alt_def
      using len_L by simp+
    
    show "fst (L, v, c) ! p \<notin> urgent (fst (snd abs_renum.sem) ! p)"
    proof (cases p)
      case 0
      then have "L ! p = Planning" using Lv_con unfolding Lv_conds_def by blast
      moreover
      have "urgent (fst (snd abs_renum.sem) ! p) = {InitialLocation, GoalLocation}" 
        apply (subst sem_alt_def)
        unfolding fst_conv snd_conv
        apply (subst nth_map, simp add: pl)
        apply (subst 0)
        apply (subst nth_Cons_0)
        unfolding comp_def main_auto_spec_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
          urgent_def fst_conv by auto
      ultimately
      show ?thesis by simp
    next
      case (Suc n)
      hence a: "actions ! n \<in> set actions" using pl by simp
      consider "L ! p = Off (actions ! n)" | "L ! p = Running (actions ! n)"
        using pres unfolding s happening_pre_pre_delay_def Let_def happening_pre_def prod.case
        using pl unfolding Suc
        apply (cases rule: planning_sem.open_active_count_cases[OF a])
        by blast+
      note c = this
      have "urgent (fst (snd abs_renum.sem) ! p) = {StartInstant (actions ! n), EndInstant (actions ! n)} "
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
        apply (cases rule: c)
        by simp+
    qed
  qed
    
  have tl_not_Nil: "1 < length xs \<Longrightarrow> tl xs \<noteq> []" for xs apply (cases xs) by auto
  have last_tl_eq_last: "last(tl ?seq)= last ?seq"
  proof - 
    have 1: "0 < length (map end_edge_effect (filter (is_ending_index (time_index \<pi> i)) [0..<length actions])) +
        length (map start_edge_effect (filter (is_starting_index (time_index \<pi> i)) [0..<length actions])) +
        sum_list (map length (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (time_index \<pi> i)) [0..<length actions]))) +
        length (map end_edge_effect (filter (is_ending_index (time_index \<pi> i)) [0..<length actions])) +
        length (map edge_2_effect (filter (is_starting_index (time_index \<pi> i)) [0..<length actions]))"
      unfolding add_gr_0
      apply (rule time_index_action_index_happening_cases[OF i])
      by (fastforce intro!: length_pos_if_in_set sum_list_pos_if_ex_pos)+
    show ?thesis 
      apply (rule tl_last[symmetric], rule tl_not_Nil, (subst length_ext_seq_comp_seq_apply | subst length_fold_ext_seq_comp_seq_apply)+)
      apply (subst length_Cons)
      apply (subst length_nth_simps(1))
      using 1 by linarith
  qed

  show "abs_renum.urge_bisim.A.steps (s#delay_and_apply i s) \<and> happening_post i (last (delay_and_apply i s))" 
    apply (rule conjI)
    subgoal
      unfolding delay_and_apply_def Let_def
      unfolding s
      apply (subst apply_nth_happening_def)
      unfolding Let_def
unfolding apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def apply_instant_actions_alt
      unfolding comp_apply[of ext_seq seq_apply, symmetric]
      apply (subst ext_seq_seq_apply_append_distrib, intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst fold_ext_seq_comp_conv_foldl_append, intro ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst ext_seq_seq_apply_append_distrib, intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst ext_seq_seq_apply_append_distrib, intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst ext_seq_seq_apply_append_distrib, simp)
      apply (rule steps_delay_replace[OF _ delay_non_negative no_urgent])
      apply (subst comp_def)
      apply (subst Cons_tl_ext_seq)
      apply (subst comp_apply[of ext_seq seq_apply, symmetric])
      apply (subst ext_seq_seq_apply_append_distrib[symmetric], simp)
      apply (subst ext_seq_seq_apply_append_distrib[symmetric], intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst ext_seq_seq_apply_append_distrib[symmetric], intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst fold_ext_seq_comp_conv_foldl_append[symmetric], intro ext_seq_comp_seq_apply_not_Nil, simp)
      apply (subst ext_seq_seq_apply_append_distrib[symmetric], intro fold_ext_seq_comp_seq_apply_not_Nil ext_seq_comp_seq_apply_not_Nil, simp)
      using p s by blast
    unfolding delay_and_apply_def Let_def
    apply (subst apply_nth_happening_def)
    unfolding Let_def apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def  apply_instant_actions_alt
    unfolding comp_apply[of ext_seq seq_apply, symmetric]
    apply (subst last_tl_eq_last)
    using p by blast
  
next
let ?seq = "(ext_seq \<circ> seq_apply) (map edge_2_effect (filter (is_starting_index (time_index \<pi> i)) [0..<length actions]))
       ((ext_seq \<circ> seq_apply) (map end_edge_effect (filter (is_ending_index (time_index \<pi> i)) [0..<length actions]))
         ((ext_seq \<circ> seq_apply) (map start_edge_effect (filter (is_starting_index (time_index \<pi> i)) [0..<length actions]))
           (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) (filter (is_instant_index (time_index \<pi> i)) [0..<length actions])) 
            ((ext_seq \<circ> seq_apply) (map edge_3_effect (filter (is_ending_index (time_index \<pi> i)) [0..<length actions])) [delay (get_delay i) s]))))"

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
      subgoal by (auto dest!: happening_pre_post_delay_dests(3))
      subgoal by (auto 
            simp: planning_sem.open_active_count_1_if_ending
              index_case_defs planning_sem.action_happening_case_defs 
            dest!: happening_pre_post_delay_dests(6))
      subgoal by (auto dest!: happening_pre_post_delay_dests(8))
      done
  qed
  show "abs_renum.urge_bisim.A.steps ?seq \<and> happening_post i (last ?seq)"
    apply (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[where R = "happening_pre_start_ends i" and S = "happening_post_start_ends i"])
          apply (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[where R = "happening_pre_end_ends i" and S = "happening_post_end_ends i"])
                apply (rule steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable[where R = "happening_pre_start_starts i" and S = "happening_post_start_starts i"])
                      apply (rule instant_actions_possible)
                        apply (rule end_starts_possible)
                        apply (auto intro!: abs_renum.urge_bisim.A.steps.intros pres')[1]
                        apply simp
    using i apply simp
    sorry
qed


lemma set_foldl_append: "set (foldl (@) ys xs) = \<Union> (set ` (set xs)) \<union> (set ys)"
  apply (induction xs arbitrary: ys)
  by auto

lemma plan_steps_possible: 
  assumes "abs_renum.urge_bisim.A.steps xs \<and> init_planning_state_props' (last xs)"
  shows "abs_renum.urge_bisim.A.steps (ext_seq' (map delay_and_apply [0..<length (htpl \<pi>)]) xs) \<and> goal_trans_pre (last (ext_seq' (map delay_and_apply [0..<length (htpl \<pi>)]) xs))"
proof (rule steps_seq.ext_seq'_induct_list_prop_and_post[
      where P = happening_pre_pre_delay 
        and Q = happening_post 
        and R = init_planning_state_props' 
        and fs = "map delay_and_apply [0..<length (htpl \<pi>)]" 
        and S = goal_trans_pre, 
        OF assms,
        simplified length_map set_map length_upt minus_nat.diff_0 set_upt], 
        goal_cases)
  case (1 f x)
  have x: "delay_and_apply i x' \<noteq> []" if "i < length (htpl \<pi>)" for i x'
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
  then show ?case 
    apply -
    apply (subst nth_map, simp)+
    apply (subst nth_upt, simp)+
    unfolding add_0 sorry
next
  case (3 i s)
  then show ?case 
    apply -
    apply (erule happening_postE)
    subgoal for L v c
      apply (erule happening_pre_pre_delayI)
             apply simp
      subgoal by (auto simp: prop_state_after_happ_def prop_state_before_happ_def planning_sem.state_seq_Suc_is_upd)
      subgoal by (auto simp: planning_sem.locked_after_indexed_timepoint_is_locked_before_Suc[symmetric])
      subgoal by (auto simp: planning_sem.active_after_indexed_timepoint_is_active_before_Suc[symmetric])
      subgoal by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
      subgoal by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
      subgoal by (auto simp: planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
      subgoal by (auto simp: planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
      done
    done
next
  case (4 x)
  hence init_is_goal: "set goal \<subseteq> set init" using vp[THEN valid_plan_state_seq] by auto
  show ?case 
    apply (insert 4)
    apply (erule init_planning_state_props'E)
    apply (rule goal_trans_preI)
    using init_is_goal by auto
next
  case (5 x)
  show ?case 
    apply (insert 5)
    apply (erule init_planning_state_props'E)
    subgoal for L v c
      apply (erule happening_pre_pre_delayI)
            apply (auto simp: planning_sem.plan_state_seq_props prop_state_before_happ_def 
              int_of_nat_def planning_sem.locked_before_initial_is_0 planning_sem.active_before_initial_is_0 planning_sem.open_active_count_initial_is_0)[6]
      subgoal 
        apply (subst act_clock_pre_happ_spec.simps)
        apply (subst cval_add_def)
        apply (subst planning_sem.exec_time_at_init)
        by (auto simp: get_delay_def card_htps_len_htpl of_rat_add Rat.of_int_def)
      subgoal 
        apply (subst act_clock_pre_happ_spec.simps)
        apply (subst cval_add_def)
        apply (subst planning_sem.exec_time_at_init)
        by (auto simp: cval_add_def get_delay_def card_htps_len_htpl of_rat_add Rat.of_int_def)
      done 
    done
next
  case (6 x)
  show ?case 
    apply (insert 6)
    apply (erule happening_postE)
    subgoal for L v c
      apply (erule goal_trans_preI)
          apply simp
         apply (subst (asm) planning_sem.active_after_final_is_0)
         apply simp
      subgoal
        apply (subst list_eq_iff_nth_eq)
        apply (rule conjI)
        apply (erule Lv_condsE)
        apply simp
        apply (intro allI impI)
        subgoal for i
          apply (cases i)
          apply (erule Lv_condsE)
          apply simp
          subgoal for i'
            apply (drule spec[of _ i'])
            apply (rule ssubst[of i], assumption)
             apply (subst nth_Cons_Suc)
            apply (subst nth_map)
             apply (erule Lv_condsE, linarith)
            apply (drule mp)
             apply (erule Lv_condsE, linarith)
            apply (erule mp)
            apply (subst planning_sem.closed_active_count_final_is_0[of "actions ! i'"])
             apply (erule Lv_condsE, simp)
            by blast
          done
        done
          subgoal
            apply (rule exI[of _ "planning_sem.upd_state (length (htpl \<pi>) - 1)"])
            apply (subst planning_sem.state_seq_Suc_is_upd[symmetric], simp)+
            apply (rule conjI)
            using planning_sem.plan_state_seq_valid apply fastforce
            apply (subst (asm) prop_state_after_happ_def, simp)
            apply (subst (asm) planning_sem.state_seq_Suc_is_upd[symmetric], simp)+
            by blast
          unfolding planning_sem.locked_after_final_is_0 int_of_nat_def
          by simp
        done
    qed

lemma final_step_possible: 
  assumes "abs_renum.urge_bisim.A.steps xs \<and> goal_trans_pre (last xs)"
  shows "abs_renum.urge_bisim.A.steps ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] xs) \<and> goal_state_conds (last ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] xs))"
proof (rule steps_seq.ext_seq_comp_seq_apply_single_list_prop_and_post[where R = goal_trans_pre, OF assms], rule conjI)
  fix x::"'action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)"
  assume a: "goal_trans_pre x"
  show "goal_state_conds (main_auto_goal_edge_effect x)" 
    apply (insert a)
    apply (erule goal_trans_preE)
    subgoal for L v c
      apply (rule ssubst[of x], assumption)
      unfolding main_auto_goal_edge_effect_def Let_def prod.case
      apply (rule goal_state_condsI, rule HOL.refl)
      by (auto elim: Lv_condsE intro!: single_upd_bounded map_of_nta_vars_PlanningLock)
    done
  show "abs_renum.urge_bisim.A.steps [x, main_auto_goal_edge_effect x]"
    apply (rule single_step_intro)
    apply (cases x)
    subgoal for L v c
      apply (rule ssubst, assumption)
      unfolding main_auto_goal_edge_effect_def Let_def prod.case
      apply (insert a)
      apply (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
       apply (subst abs_renum.sem_def)
       apply (rule step_u.step_int[where p = 0])
      unfolding TAG_def
                 apply (subst conv_trans)
      using some_actual_autos apply simp
                 apply (subst main_auto_trans)
                 apply (rule image_eqI)
                  prefer 2
                  apply (rule insertI2)
                  apply (rule insertI1)
                 apply (simp add: main_auto_goal_edge_spec_def)
      using no_committed conv_committed apply simp
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
          using map_of_nta_vars_init_goal
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
      by (auto elim: goal_trans_preE Lv_condsE simp: map_of_nta_vars_PlanningLock)
    done
qed


lemma all_steps_possible: "abs_renum.urge_bisim.A.steps plan_steps \<and> goal_state_conds (last plan_steps)" 
    unfolding plan_steps_def 
    unfolding comp_apply[of ext_seq seq_apply, symmetric]         
    apply (rule final_step_possible)
     apply (rule plan_steps_possible)
    by (rule initial_step_possible)



find_theorems name: "abs_renum.urge_bisim.A.steps*"

(* delay and apply forces the delay on the first state *)
lemma "abs_renum.urge_bisim.A.steps ((L, v, c) # apply_nth_happening i (L, v, c \<oplus> real_of_rat (get_delay i)))"
  unfolding delay_and_apply_def Let_def
  apply (subst apply_nth_happening_def) 
  apply (subst Let_def)+
  sorry



(* Define the pre- and post-conditions when executing:
  - all ending transitions
  - all instant transitions
  - all starting transitions
  - all ending' transitions
  - all starting' transitions
*)

(* Define the pre- and post-conditions when executing:
  - a happening
  - a plan
*)



thm nta_vars_exact[no_vars]
thm action_vars_spec_def[no_vars]
thm snap_vars_spec_def[no_vars]

(* What happens when the ending snap-actions are applied? *)



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

find_theorems  name: "LTL*ev"

thm Graph_Defs.Ex_ev_def Graph_Defs.extend_run' Sequence_LTL.ev_alt_def

lemma "abs_renum.sem, abs_renum.a\<^sub>0 \<Turnstile> form"
proof -
  show "?thesis" unfolding form_alt 
    unfolding models_def 
    unfolding formula.case
    find_theorems name: "abs_renumEx_ev"
    apply (subst abs_renum.urge_bisim.A.Ex_ev_def)
    find_theorems (200) name: "abs_renum*run"
    find_theorems name: deadlock
    apply (intro exI conjI)
     prefer 2
    apply (subst ev_alt_def)
    find_theorems intro
     apply (coinduction rule: abs_renum.urge_bisim.A.run.coinduct) sorry
  qed

end
end
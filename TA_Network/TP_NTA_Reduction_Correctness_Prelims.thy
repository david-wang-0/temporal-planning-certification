theory TP_NTA_Reduction_Correctness_Prelims
  imports TP_NTA_Reduction_Model_Checking
          "Temporal_Planning_Common.Sequences"
          "Temporal_Planning_Common.ListMisc"
          NTA_Temp_Planning_Sem
begin

lemma fold_union:
  "fold (\<union>) S T =  \<Union> (set S) \<union> T"
  by (induction S arbitrary: T) auto

lemma fold_union':
  "fold (\<union>) S {} =  \<Union> (set S)"
  apply (subst fold_union)
  apply (subst Un_empty_right)
  ..

context tp_nta_reduction_correctness
begin
schematic_goal map_of_all_vars_exact:
  "map_of all_vars = ?x"
  unfolding all_vars_def Let_def fold_union'
  ..

lemmas map_of_net_bounds_exact = map_of_all_vars_exact

thm map_of_all_vars_exact

section \<open>Equivalence to temporal planning semantics\<close>

definition lower_sem where
"lower_sem \<equiv> (map_option (map_lower_bound rat_of_int)) o lower"

definition upper_sem where
"upper_sem \<equiv> (map_option (map_upper_bound rat_of_int)) o upper"

definition "\<pi>_sem \<equiv> map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>"

sublocale planning_sem: nta_temp_planning  
  at_start at_end "set \<circ> over_all" 
  lower_sem upper_sem
  "set \<circ> pre" "set \<circ> adds" "set \<circ> dels"
  "set init" "set goal" "rat_of_int \<epsilon>"
  \<pi>_sem "set props" "set actions"
  1
  unfolding lower_sem_def upper_sem_def \<pi>_sem_def
  apply standard 
  by auto

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
  show ?thesis using rat_impl.set_impl.at_start_inj_on_acts unfolding inj_on_def by blast
qed


lemma nth_end_unique:
  assumes "a \<in> set actions"
      and "n < length actions"
      and "at_end (actions ! n) = at_end a"
    shows "actions ! n = a"
proof -
  have "actions ! n \<in> set actions" using assms set_conv_nth by simp
  with assms
  show ?thesis using rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def by blast
qed

lemma nth_start_end_disj:
  assumes "a \<in> set actions"
      and "n < length actions"
    shows "at_start (actions ! n) \<noteq> at_end a"
  using assms in_set_conv_nth[of "actions ! n" actions] rat_impl.set_impl.end_start_disj_on_acts by blast

lemma nth_end_start_disj:
  assumes "a \<in> set actions"
      and "n < length actions"
    shows "at_end (actions ! n) \<noteq> at_start a"
  using assms in_set_conv_nth[of "actions ! n" actions] rat_impl.set_impl.end_start_disj_on_acts by blast
  

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
  using rat_impl.set_impl.at_start_inj_on_acts unfolding inj_on_def
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
  using rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def
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


lemma partially_updated_locked_before_inv_mono': 
  assumes "n \<le> m"
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
  assumes "i < length planning_sem.htpl" 
      and "(\<And>n. n < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) n \<Longrightarrow> thesis)" 
          "(\<And>n. n < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) n \<Longrightarrow> thesis)" 
          "(\<And>n. n < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) n \<Longrightarrow> thesis)"
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

lemma index_case_conv_action:
  "(\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> P (actions ! i)) = (\<forall>a \<in> set actions. planning_sem.is_not_happening_action t a \<longrightarrow> P a)"
  "(\<forall>i < length actions. is_instant_index t i \<longrightarrow> P (actions ! i)) = (\<forall>a \<in> set actions. planning_sem.is_instant_action t a \<longrightarrow> P a)"
  "(\<forall>i < length actions. is_ending_index t i \<longrightarrow> P (actions ! i)) = (\<forall>a \<in> set actions. planning_sem.is_ending_action t a \<longrightarrow> P a)"
  "(\<forall>i < length actions. is_starting_index t i \<longrightarrow> P (actions ! i)) = (\<forall>a \<in> set actions. planning_sem.is_starting_action t a \<longrightarrow> P a)"
    unfolding set_conv_nth index_case_defs
    by auto

text \<open>A lemma\<close>
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

context 
  fixes i::nat
assumes i: "i < length planning_sem.htpl"
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



(* Intermediate states *)
definition "actions_before n \<equiv>
  map ((!) actions) [0..<n]
"

(* instant actions *)
definition "instant_actions_before n \<equiv> set (filter (planning_sem.is_instant_action (planning_sem.time_index i)) (actions_before n))"

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
definition "starting_actions_before n \<equiv> set (filter (planning_sem.is_starting_action (planning_sem.time_index i)) (actions_before n))"

definition "starting_snaps_before n = at_start ` starting_actions_before n"

definition "apply_starting_snaps_before n s \<equiv> apply_snaps (starting_snaps_before n) s"

definition "starting_part_updated_state_seq n \<equiv> apply_starting_snaps_before n (planning_sem.inst_upd_state i)"

definition "starting_part_updated_prop_state n \<equiv> prop_state (starting_part_updated_state_seq n)"

definition "starting_actions_after n \<equiv> planning_sem.starting_actions_at (planning_sem.time_index i) - starting_actions_before n"

(* ending *)
definition "ending_actions_before n \<equiv> set (filter (planning_sem.is_ending_action (planning_sem.time_index i)) (actions_before n))"

definition "ending_snaps_before n = at_end ` ending_actions_before n"

definition "apply_ending_snaps_before n s \<equiv> apply_snaps (ending_snaps_before n) s"

definition "ending_part_updated_state_seq n \<equiv> apply_ending_snaps_before n (planning_sem.inst_start_upd_state i)"

definition "ending_part_updated_prop_state n \<equiv> prop_state (ending_part_updated_state_seq n)"

definition "ending_actions_after n \<equiv> planning_sem.ending_actions_at (planning_sem.time_index i) - ending_actions_before n"

(* all *)


lemma apply_snaps_is_app_effs[simp]: "apply_snaps = planning_sem.apply_effects" 
  unfolding apply_snaps_def planning_sem.apply_effects_def by blast
lemma happ_combine': 
  assumes "S \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and "T \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  shows "((apply_snaps T) o (apply_snaps S)) s = apply_snaps (S \<union> T) s"
  using planning_sem.happ_combine[of S T "planning_sem.time_index i" s]
  using assms by auto

lemma actions_before_not_include:
  assumes "n < length actions"
  shows "(actions ! n) \<notin> set (actions_before n)"
  using assms
  unfolding actions_before_def
  using nth_actions_unique by auto

lemma actions_before_in_actions:
  assumes "n < length actions"
  shows "set (actions_before n) \<subseteq> set actions"
  using assms unfolding actions_before_def by auto

(*instant*)
lemma instant_actions_before_all_is_instant_actions: "instant_actions_before (length actions) = planning_sem.instant_actions_at (planning_sem.time_index i)"
  unfolding instant_actions_before_def Let_def set_filter set_map set_upt planning_sem.instant_actions_at_def actions_before_def by simp

lemma instant_snaps_before_all_is_instant_snaps: "instant_snaps_before (length actions) = planning_sem.instant_snaps_at (planning_sem.time_index i)"
  unfolding instant_snaps_before_def planning_sem.instant_snaps_at_def instant_ends_before_def instant_starts_before_def 
  using instant_actions_before_all_is_instant_actions by simp

lemma apply_instant_snaps_before_all_is_apply_instant_snaps: "apply_instant_snaps_before (length actions) s = planning_sem.apply_effects (planning_sem.instant_snaps_at (planning_sem.time_index i)) s"
  unfolding planning_sem.apply_effects_def apply_instant_snaps_before_def Let_def instant_snaps_before_all_is_instant_snaps apply_snaps_def by blast

lemma instant_actions_before_0_is_none: "instant_actions_before 0 = {}" 
  unfolding instant_actions_before_def Let_def actions_before_def by simp

lemma instant_snaps_before_0_is_none: "instant_snaps_before 0 = {}"
  unfolding instant_snaps_before_def instant_starts_before_def instant_ends_before_def instant_actions_before_0_is_none by blast

lemma apply_instant_snaps_before_0_is_id: "apply_instant_snaps_before 0 = id"
  unfolding apply_instant_snaps_before_def instant_snaps_before_0_is_none apply_snaps_def id_def by blast

(* starting *)

lemma starting_actions_before_all_is_starting_actions: 
  "starting_actions_before (length actions) = planning_sem.starting_actions_at (planning_sem.time_index i)"
  unfolding starting_actions_before_def Let_def set_filter set_map set_upt 
    planning_sem.starting_actions_at_def actions_before_def by simp

lemma finite_starting_actions_before:
  "finite (starting_actions_before n)" 
  unfolding starting_actions_before_def by auto

lemma starting_snaps_before_all_is_starting_snaps: "starting_snaps_before (length actions) = planning_sem.starting_snaps_at (planning_sem.time_index i)"
  unfolding starting_snaps_before_def planning_sem.starting_snaps_at_def  
  using starting_actions_before_all_is_starting_actions by simp

lemma apply_starting_snaps_before_all_is_apply_starting_snaps: "apply_starting_snaps_before (length actions) s = planning_sem.apply_effects (planning_sem.starting_snaps_at (planning_sem.time_index i)) s"
  unfolding planning_sem.apply_effects_def apply_starting_snaps_before_def Let_def starting_snaps_before_all_is_starting_snaps apply_snaps_def by blast

lemma starting_actions_before_0_is_none: "starting_actions_before 0 = {}"
  using starting_actions_before_def actions_before_def by auto

lemma starting_snaps_before_0_is_none: "starting_snaps_before 0 = {}" 
  using starting_snaps_before_def starting_actions_before_0_is_none by blast

lemma apply_starting_snaps_before_0_is_id: "apply_starting_snaps_before 0 = id"
  unfolding apply_starting_snaps_before_def apply_snaps_def starting_snaps_before_0_is_none by auto

lemma starting_actions_after_0_is_starting_actions:
  "starting_actions_after 0 = planning_sem.starting_actions_at (planning_sem.time_index i)"
  unfolding starting_actions_after_def using starting_actions_before_0_is_none by auto

lemma starting_actions_after_all_is_none:
  "starting_actions_after (length actions) = {}"
  unfolding starting_actions_after_def using starting_actions_before_all_is_starting_actions by auto

lemma finite_starting_actions_after:
  "finite (starting_actions_after n)"
  using starting_actions_after_def finite_starting_actions_before 
    planning_sem.finite_starting_actions_at by auto
(* starting *)


lemma starting_actions_before_mono:
  assumes "n \<le> m"
  shows "starting_actions_before n \<subseteq> starting_actions_before m"
  using assms unfolding starting_actions_before_def actions_before_def by auto

lemma card_starting_actions_before_mono:
  assumes "n \<le> m"
  shows "card (starting_actions_before n) \<le> card (starting_actions_before m)"
  using assms unfolding starting_actions_before_def actions_before_def 
  by (auto intro: card_mono)

lemma starting_actions_before_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_starting_index (planning_sem.time_index i) j)" 
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
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
  shows "starting_actions_before (Suc n) = starting_actions_before n \<union> {actions ! n}"
  using assms
  unfolding starting_actions_before_def actions_before_def index_case_defs by simp

lemma starting_actions_before_not_include:
  assumes "n < length actions"
    shows "disjnt (starting_actions_before n) {actions ! n}"
    unfolding disjnt_def starting_actions_before_def actions_before_def
    using nth_actions_unique assms by auto

lemma card_starting_actions_before_Suc:
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (starting_actions_before (Suc n)) = card (starting_actions_before n) + 1"
  using starting_actions_before_Suc assms starting_actions_before_not_include card_Un_disjnt
    finite_starting_actions_before by auto

(* The anding actions with a greater or equal index *)

lemma card_ending_actions_and_starting_before_less:
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (planning_sem.ending_actions_at (planning_sem.time_index i)) + card (starting_actions_before n) < length actions"
proof -
  have "planning_sem.ending_actions_at (planning_sem.time_index i) \<union> planning_sem.starting_actions_at (planning_sem.time_index i) \<subseteq> set actions" using planning_sem.all_actions_at[of "planning_sem.time_index i"] by auto
  moreover
  have "disjnt (planning_sem.ending_actions_at (planning_sem.time_index i)) (planning_sem.starting_actions_at (planning_sem.time_index i))" 
    unfolding planning_sem.actions_at_defs  disjnt_def
    using planning_sem.action_happening_disj by blast
  ultimately
  have 1: "card (planning_sem.ending_actions_at (planning_sem.time_index i)) + card (planning_sem.starting_actions_at (planning_sem.time_index i)) \<le> length actions" 
    apply (subst card_action_set[symmetric])
    apply (subst card_Un_disjnt[symmetric])
    using planning_sem.finite_ending_actions_at planning_sem.finite_starting_actions_at apply auto[3]
    using card_mono by blast

  have "starting_actions_before (Suc n) \<subseteq> planning_sem.starting_actions_at (planning_sem.time_index i)" 
    using starting_actions_before_mono assms starting_actions_before_all_is_starting_actions[symmetric] by simp
  hence "card (starting_actions_before (Suc n)) \<le> card (planning_sem.starting_actions_at (planning_sem.time_index i))" 
    using planning_sem.finite_starting_actions_at card_mono by auto
  hence "card (starting_actions_before n \<union> {actions ! n}) \<le> card (planning_sem.starting_actions_at (planning_sem.time_index i))" 
    using assms starting_actions_before_Suc by simp
  hence "card (starting_actions_before n) < card (planning_sem.starting_actions_at (planning_sem.time_index i))"
    using card_Un_disjnt starting_actions_before_not_include assms finite_starting_actions_before by auto
  thus ?thesis using 1 by linarith
qed

lemma starting_actions_before_less_if_starting:
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (starting_actions_before n) < length actions"
  using card_ending_actions_and_starting_before_less assms by force

lemma starting_actions_after_pos_if_starting:
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "0 < card (starting_actions_after n)"
proof -
  have "actions ! n \<in> planning_sem.starting_actions_at (planning_sem.time_index i)"
    using assms index_case_defs planning_sem.starting_actions_at_def by auto
  hence "actions ! n \<in> starting_actions_after n" using starting_actions_after_def starting_actions_before_not_include assms by auto
  thus ?thesis using finite_starting_actions_after card_gt_0_iff by blast
qed

lemma starting_actions_after_Suc:
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "starting_actions_after (Suc n) \<union> {actions ! n} = starting_actions_after n"
proof -
  have "actions ! n \<in> planning_sem.starting_actions_at (planning_sem.time_index i)"
    using assms index_case_defs planning_sem.starting_actions_at_def by auto
  moreover
  have "starting_actions_before (Suc n) = starting_actions_before n \<union> {actions ! n}" 
    using assms starting_actions_before_Suc by auto
  moreover
  have "actions ! n \<notin> starting_actions_before n" using starting_actions_before_not_include assms by auto 
  ultimately
  show ?thesis unfolding starting_actions_after_def by blast
qed

lemma starting_actions_after_Suc_not_include:
  assumes "n < length actions"
  shows "disjnt (starting_actions_after (Suc n)) {actions ! n}"
proof (cases "is_starting_index (planning_sem.time_index i ) n")
  case True
  then show ?thesis unfolding starting_actions_after_def using starting_actions_before_Suc assms by simp
next
  case False
  then show ?thesis unfolding starting_actions_after_def planning_sem.starting_actions_at_def index_case_defs by auto
qed

lemma card_starting_actions_after_Suc:
  assumes "is_starting_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (starting_actions_after (Suc n)) + 1 = card (starting_actions_after n)"
  using starting_actions_after_Suc assms 
    card_Un_disjnt[OF finite_starting_actions_after _ starting_actions_after_Suc_not_include]
  by force

lemma starting_actions_after_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_starting_index (planning_sem.time_index i) j)" 
    shows "starting_actions_after n = starting_actions_after m"
  unfolding starting_actions_after_def
  using starting_actions_before_inv[OF assms] by simp

lemma starting_actions_after_le:
  "card (starting_actions_after n) \<le> length actions"
  unfolding starting_actions_after_def planning_sem.starting_actions_at_def card_action_set[symmetric]
  apply (rule card_mono) by auto

(* ending  *)

lemma ending_actions_before_all_is_ending_actions: 
  "ending_actions_before (length actions) = planning_sem.ending_actions_at (planning_sem.time_index i)"
  unfolding ending_actions_before_def Let_def set_filter set_map set_upt 
    planning_sem.ending_actions_at_def actions_before_def by simp

lemma ending_snaps_before_all_is_ending_snaps: "ending_snaps_before (length actions) = planning_sem.ending_snaps_at (planning_sem.time_index i)"
  unfolding ending_snaps_before_def planning_sem.ending_snaps_at_def  
  using ending_actions_before_all_is_ending_actions by simp

lemma apply_ending_snaps_before_all_is_apply_ending_snaps: "apply_ending_snaps_before (length actions) s = planning_sem.apply_effects (planning_sem.ending_snaps_at (planning_sem.time_index i)) s"
  unfolding planning_sem.apply_effects_def apply_ending_snaps_before_def Let_def ending_snaps_before_all_is_ending_snaps apply_snaps_def by blast

lemma ending_actions_before_0_is_none: "ending_actions_before 0 = {}"
  using ending_actions_before_def actions_before_def by auto

lemma finite_ending_actions_before:
  "finite (ending_actions_before n)"
  unfolding ending_actions_before_def actions_before_def by blast

lemma ending_actions_after_0_is_ending_actions:
  "ending_actions_after 0 = planning_sem.ending_actions_at (planning_sem.time_index i)"
  unfolding ending_actions_after_def using ending_actions_before_0_is_none by auto

lemma ending_actions_after_all_is_none:
  "ending_actions_after (length actions) = {}"
  unfolding ending_actions_after_def using ending_actions_before_all_is_ending_actions by auto

lemma finite_ending_actions_after:
  "finite (ending_actions_after n)"
  using ending_actions_after_def finite_ending_actions_before 
    planning_sem.finite_ending_actions_at by auto

lemma ending_snaps_before_0_is_none: "ending_snaps_before 0 = {}" 
  using ending_snaps_before_def ending_actions_before_0_is_none by blast

lemma apply_ending_snaps_before_0_is_id: "apply_ending_snaps_before 0 = id"
  unfolding apply_ending_snaps_before_def apply_snaps_def ending_snaps_before_0_is_none by auto

lemma ending_actions_before_mono:
  assumes "n \<le> m"
  shows "ending_actions_before n \<subseteq> ending_actions_before m"
  using assms unfolding ending_actions_before_def actions_before_def by auto

lemma card_ending_actions_before_mono:
  assumes "n \<le> m"
  shows "card (ending_actions_before n) \<le> card (ending_actions_before m)"
  using assms unfolding ending_actions_before_def actions_before_def 
  by (auto intro: card_mono)

lemma ending_actions_before_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_ending_index (planning_sem.time_index i) j)" 
    shows "ending_actions_before n = ending_actions_before m"
proof-
  have 1: "[0..<m] = [0..<n] @ [n..<m]" using assms by simp
  show ?thesis 
    unfolding ending_actions_before_def
    unfolding actions_before_def
    apply (subst 1)
    apply (subst map_append)
    apply (subst filter_append)
    apply (subst set_append)
    using assms index_case_defs
    by auto
qed

lemma ending_actions_before_Suc:
  assumes "is_ending_index (planning_sem.time_index i) n"
      and "n < length actions"
  shows "ending_actions_before (Suc n) = ending_actions_before n \<union> {actions ! n}"
  using assms
  unfolding ending_actions_before_def actions_before_def index_case_defs by simp

lemma ending_actions_before_not_include:
  assumes "n < length actions"
    shows "disjnt (ending_actions_before n) {actions ! n}"
    unfolding disjnt_def ending_actions_before_def actions_before_def
    using nth_actions_unique assms by auto

lemma card_ending_actions_before_Suc:
  assumes "is_ending_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (ending_actions_before (Suc n)) = card (ending_actions_before n) + 1"
  using ending_actions_before_Suc assms ending_actions_before_not_include card_Un_disjnt
    finite_ending_actions_before by auto

lemma ending_actions_before_less_if_ending:
  assumes "is_ending_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (ending_actions_before n) < length actions"
proof -
  have "ending_actions_before (Suc n) \<subseteq> planning_sem.ending_actions_at (planning_sem.time_index i)" 
    using ending_actions_before_mono assms ending_actions_before_all_is_ending_actions[symmetric] by simp
  hence "ending_actions_before (Suc n) \<subseteq> set actions" using planning_sem.all_actions_at by blast
  hence "card (ending_actions_before (Suc n)) \<le> length actions" unfolding card_action_set[symmetric]
    using card_mono finite_ending_actions_before by blast
  hence 1: "card (ending_actions_before n \<union> {actions ! n}) \<le> length actions" using assms ending_actions_before_Suc by auto
  thus ?thesis using card_Un_disjnt ending_actions_before_not_include assms finite_ending_actions_before by auto
qed

lemma ending_actions_after_pos_if_ending:
  assumes "is_ending_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "0 < card (ending_actions_after n)"
proof -
  have "actions ! n \<in> planning_sem.ending_actions_at (planning_sem.time_index i)"
    using assms index_case_defs planning_sem.ending_actions_at_def by auto
  hence "actions ! n \<in> ending_actions_after n" using ending_actions_after_def ending_actions_before_not_include assms by auto
  thus ?thesis using finite_ending_actions_after card_gt_0_iff by blast
qed

lemma ending_actions_after_Suc:
  assumes "is_ending_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "ending_actions_after (Suc n) \<union> {actions ! n} = ending_actions_after n"
proof -
  have "actions ! n \<in> planning_sem.ending_actions_at (planning_sem.time_index i)"
    using assms index_case_defs planning_sem.ending_actions_at_def by auto
  moreover
  have "ending_actions_before (Suc n) = ending_actions_before n \<union> {actions ! n}" 
    using assms ending_actions_before_Suc by auto
  moreover
  have "actions ! n \<notin> ending_actions_before n" using ending_actions_before_not_include assms by auto 
  ultimately
  show ?thesis unfolding ending_actions_after_def by blast
qed

lemma ending_actions_after_Suc_not_include:
  assumes "n < length actions"
  shows "disjnt (ending_actions_after (Suc n)) {actions ! n}"
proof (cases "is_ending_index (planning_sem.time_index i ) n")
  case True
  then show ?thesis unfolding ending_actions_after_def using ending_actions_before_Suc assms by simp
next
  case False
  then show ?thesis unfolding ending_actions_after_def planning_sem.ending_actions_at_def index_case_defs by auto
qed

lemma card_ending_actions_after_Suc:
  assumes "is_ending_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (ending_actions_after (Suc n)) + 1 = card (ending_actions_after n)"
  using ending_actions_after_Suc assms 
    card_Un_disjnt[OF finite_ending_actions_after _ ending_actions_after_Suc_not_include]
  by force

lemma ending_actions_after_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_ending_index (planning_sem.time_index i) j)" 
    shows "ending_actions_after n = ending_actions_after m"
  unfolding ending_actions_after_def
  using ending_actions_before_inv[OF assms] by simp

lemma card_ending_actions_less:
  assumes "is_instant_index (planning_sem.time_index i) n \<or> is_starting_index (planning_sem.time_index i) n \<or> is_not_happening_index (planning_sem.time_index i) n"
      and "n < length actions"
    shows "card (planning_sem.ending_actions_at (planning_sem.time_index i)) < length actions"
proof -
  from assms
  have "actions ! n \<in> planning_sem.instant_actions_at (planning_sem.time_index i) 
    \<or> actions ! n \<in> planning_sem.starting_actions_at (planning_sem.time_index i) 
    \<or> actions ! n \<in> planning_sem.not_happening_actions_at (planning_sem.time_index i)" unfolding index_case_defs planning_sem.actions_at_defs by simp
  with planning_sem.ending_actions_at_less
  have "planning_sem.ending_actions_at (planning_sem.time_index i) \<subset> set actions" by auto
  thus ?thesis 
    apply (subst card_action_set[symmetric])
    by (auto intro: psubset_card_mono)
qed

lemma ending_actions_after_inv_mono:
  assumes "n \<le> m"
  shows "ending_actions_after m \<subseteq> ending_actions_after n"
  using assms unfolding ending_actions_after_def using ending_actions_before_mono by blast

lemma card_starting_actions_and_ending_after_le:
  assumes "n \<le> length actions"
    shows "card (planning_sem.starting_actions_at (planning_sem.time_index i)) + card (ending_actions_after n) \<le> length actions"
proof -
  have 1:"ending_actions_after n \<subseteq> planning_sem.ending_actions_at (planning_sem.time_index i)" 
    using ending_actions_after_0_is_ending_actions ending_actions_after_inv_mono assms by blast

  
  have "disjnt (planning_sem.starting_actions_at (planning_sem.time_index i)) (planning_sem.ending_actions_at (planning_sem.time_index i))"
    unfolding disjnt_def planning_sem.actions_at_defs using planning_sem.action_happening_disj by blast
  hence 2: "disjnt (planning_sem.starting_actions_at (planning_sem.time_index i)) (ending_actions_after n)" using 1  disjnt_subset2 by blast
  
  have 3: "planning_sem.starting_actions_at (planning_sem.time_index i) \<union> ending_actions_after n \<subseteq> set actions"
    using 1 planning_sem.all_actions_at card_action_set by blast
  
  show ?thesis using card_Un_disjnt[OF _ _ 2] card_action_set card_mono[OF _ 3]
      planning_sem.finite_starting_actions_at finite_ending_actions_after by simp
qed
  
(* indices *)


lemma instant_snaps_before_is_in_happ_seq: 
  assumes "n < length actions"
  shows "instant_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
proof -
  have 1: "(!) actions ` {0..<n} \<subseteq> set actions" using assms by fastforce 
  { fix x
    assume "x \<in> instant_snaps_before n"
    then obtain a where
      "x = at_start a \<or> x = at_end a"
      "a \<in> set actions"
      "(planning_sem.time_index i, at_start a) \<in> planning_sem.plan_happ_seq \<and> (planning_sem.time_index i, at_end a) \<in> planning_sem.plan_happ_seq"
      unfolding instant_snaps_before_def instant_actions_before_def instant_starts_before_def instant_ends_before_def Let_def
      set_filter set_map set_upt actions_before_def planning_sem.is_instant_action_def using 1 by blast
    hence "(planning_sem.time_index i, x) \<in> planning_sem.plan_happ_seq" by blast
  } 
  thus "instant_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)" by blast
qed

lemma pre_sat_by_instant_part_updated_plan_state_seq:
  assumes t: "t = planning_sem.time_index i"
      and h: "(t, h) \<in> planning_sem.plan_happ_seq"
      and h_cases: "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and n: "n < length actions"
    shows "set (pre h) \<subseteq> instant_part_updated_plan_state_seq n"
proof (rule planning_sem.pre_sat_by_arbitrary_intermediate_state[simplified comp_apply, OF i t h])
  show "instant_part_updated_plan_state_seq n = planning_sem.apply_effects (instant_snaps_before n) (planning_sem.plan_state_seq i)"
    unfolding instant_part_updated_plan_state_seq_def apply_instant_snaps_before_def apply_snaps_def planning_sem.apply_effects_def
    by blast
  show "instant_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t"
    unfolding instant_snaps_before_def instant_starts_before_def instant_ends_before_def 
    unfolding instant_actions_before_def Let_def set_filter planning_sem.action_happening_case_defs
    unfolding t[symmetric]
    by auto
  have n_in_act: "actions ! n \<in> set actions" using n by auto
  show "h \<notin> instant_snaps_before n"
    unfolding instant_snaps_before_def instant_starts_before_def instant_ends_before_def 
    unfolding instant_actions_before_def Let_def set_filter
    apply (rule notI)
    apply (rule disjE[OF h_cases]; elim UnE imageE CollectE conjE)
    subgoal for b
      using rat_impl.set_impl.at_start_inj_on_acts[THEN inj_on_contraD, THEN notE, of "actions ! n" b]
      using actions_before_not_include n_in_act actions_before_in_actions n by auto
    using rat_impl.set_impl.end_start_disj_on_acts actions_before_in_actions n_in_act n apply blast
    using rat_impl.set_impl.end_start_disj_on_acts actions_before_in_actions n_in_act n apply blast
    subgoal for b
      using rat_impl.set_impl.at_end_inj_on_acts[THEN inj_on_contraD, THEN notE, of "actions ! n" b]
      using actions_before_not_include n_in_act actions_before_in_actions n by auto
    done
qed

lemma pre_val_in_instant_part_updated_prop_state_if:
  assumes t: "t = planning_sem.time_index i"
      and h: "(t, h) \<in> planning_sem.plan_happ_seq"
             "h = at_start (actions ! n) \<or> h = at_end (actions ! n)"
      and n: "n < length actions"
      and p: "p \<in> set (pre h)"
    shows "instant_part_updated_prop_state n p = 1"
  using assms pre_sat_by_instant_part_updated_plan_state_seq[THEN subsetD] assms
  unfolding instant_part_updated_prop_state_def by auto 

lemma instant_snaps_before_Suc:
  assumes is_instant: "is_instant_index t n"
      and t: "t = planning_sem.time_index i"
    shows "instant_snaps_before (Suc n) = instant_snaps_before n \<union> {at_start (actions ! n)} \<union>  {at_end (actions ! n)}"
proof -
  have 1: "{0..<Suc n} = {0..<n} \<union> {n}" by auto
  show ?thesis 
  unfolding instant_snaps_before_def Let_def instant_actions_before_def
    set_filter set_map set_upt  actions_before_def
    image_Un image_insert image_empty planning_sem.is_instant_action_def
    instant_starts_before_def instant_ends_before_def 1
    using is_instant unfolding planning_sem.action_happening_case_defs index_case_defs t by blast
qed

lemma apply_instant_snaps_before_Suc:
  assumes is_instant: "is_instant_index t n"
      and n: "n < length actions"
      and t: "t = planning_sem.time_index i"
    shows "apply_instant_snaps_before (Suc n) s = 
  apply_instant_snaps_before n s
  - set (dels (at_start (actions ! n)))
  \<union> set (adds (at_start (actions ! n)))
  - set (dels (at_end (actions ! n)))
  \<union> set (adds (at_end (actions ! n)))"
proof -
  have "planning_sem.apply_effects (planning_sem.snaps (actions ! n)) (planning_sem.apply_effects (instant_snaps_before n) s) = 
  planning_sem.apply_effects (instant_snaps_before n \<union> planning_sem.snaps (actions ! n)) s"
    using planning_sem.happ_combine is_instant is_instant_index_def instant_snaps_before_is_in_happ_seq[OF n] t instant_snaps_before_def planning_sem.action_happening_case_defs by auto
  hence 1: " s - \<Union> ((set \<circ> dels) ` (instant_snaps_before n \<union> planning_sem.snaps (actions ! n))) \<union> \<Union> ((set \<circ> adds) ` (instant_snaps_before n \<union> planning_sem.snaps (actions ! n))) 
    = s - \<Union> ((set \<circ> dels) ` instant_snaps_before n) \<union> \<Union> ((set \<circ> adds) ` instant_snaps_before n) - \<Union> ((set \<circ> dels) ` planning_sem.snaps (actions ! n)) \<union> \<Union> ((set \<circ> adds) ` planning_sem.snaps (actions ! n))" 
    unfolding planning_sem.apply_effects_def by argo

  have "planning_sem.apply_effects {at_end (actions ! n)} (planning_sem.apply_effects {at_start (actions ! n)} M) = planning_sem.apply_effects ({at_start (actions ! n)} \<union> {at_end (actions ! n)}) M" for M 
    using planning_sem.happ_combine[of "{at_start (actions ! n)}" "{at_end (actions ! n)}"] is_instant
    unfolding index_case_defs planning_sem.action_happening_case_defs by auto
  hence 2: "M - \<Union> ((set \<circ> dels) ` ({at_start (actions ! n), at_end (actions ! n)})) \<union> \<Union> ((set \<circ> adds) ` ({at_start (actions ! n), at_end (actions ! n)})) = 
  M - \<Union> ((set \<circ> dels) ` {at_start (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_start (actions ! n)}) - \<Union> ((set \<circ> dels) ` {at_end (actions ! n)}) \<union> \<Union> ((set \<circ> adds) ` {at_end (actions ! n)})"
    for M unfolding planning_sem.apply_effects_def by auto

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
      and t: "t = planning_sem.time_index i"
      and n: "n < length actions"
    shows "instant_part_updated_prop_state (Suc n) p = 
  (if p \<in> instant_part_updated_plan_state_seq n - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) - set (dels (at_end (actions ! n))) \<union> set (adds (at_end (actions ! n))) then 1 else 0)"
  unfolding instant_part_updated_prop_state_def instant_part_updated_plan_state_seq_def 
  apply (subst apply_instant_snaps_before_Suc)
  using assms
  by simp_all

lemma instant_intermediate_plan_state_alt:
  assumes is_instant: "is_instant_index t n"
    and t: "t = planning_sem.time_index i"
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

  have 3: "instant_part_updated_plan_state_seq n 
  - set (dels (at_start (actions ! n))) 
  \<union> set (adds (at_start (actions ! n))) 
  = apply_snaps {at_start (actions ! n)} (instant_part_updated_plan_state_seq n)"
    unfolding apply_snaps_def by auto

  have 4: "instant_starts_before (Suc n) = instant_starts_before n \<union> {at_start (actions ! n)}" using instant_starts_before_def 1 by simp

  have 5: "instant_intermediate_plan_state_seq n = apply_snaps ({at_start (actions ! n)} \<union> instant_snaps_before n) (planning_sem.plan_state_seq i)"
    unfolding instant_intermediate_plan_state_seq_def
    unfolding instant_part_updated_plan_state_seq_def 
    unfolding apply_instant_snaps_before_and_start_def
    unfolding instant_snaps_before_and_start_def
    unfolding apply_instant_snaps_before_def
    unfolding instant_snaps_before_def
    unfolding 4 by auto

  have 6: "instant_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)" 
    unfolding instant_snaps_before_def instant_starts_before_def instant_ends_before_def 
      instant_actions_before_def planning_sem.action_happening_case_defs by auto
  have 7: "{at_start (actions ! n)} \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)" 
    using is_instant unfolding index_case_defs planning_sem.action_happening_case_defs t by blast
    
  show ?thesis
    using planning_sem.happ_combine
    using 3 5 6 7
    unfolding instant_part_updated_plan_state_seq_def apply_instant_snaps_before_def 
    by auto
qed

lemma instant_intermediate_prop_state_alt:
  assumes is_instant: "is_instant_index t n"
    and t: "t = planning_sem.time_index i"
    and n: "n < length actions"
  shows "instant_intermediate_prop_state n p = (if p \<in> instant_part_updated_plan_state_seq n - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) then 1 else 0)"
  using assms by (simp add: instant_intermediate_prop_state_def prop_state_def instant_intermediate_plan_state_alt)


lemma instant_part_updated_prop_state_Suc_conv_intermediate:
  assumes is_instant: "is_instant_index t n"
    and t: "t = planning_sem.time_index i"
    and n: "n < length actions"
  shows "instant_part_updated_prop_state (Suc n) p = (if p \<in> instant_intermediate_plan_state_seq n - set (dels (at_end (actions ! n))) \<union> set (adds (at_end (actions ! n))) then 1 else 0)"
  by (simp add: instant_part_updated_prop_state_Suc[OF assms] instant_intermediate_plan_state_alt[OF assms])

lemma pre_val_in_instant_intermediate_prop_state_if:
  assumes t: "t = planning_sem.time_index i"
      and h: "is_instant_index t n"
      and n: "n < length actions"
      and p: "p \<in> set (pre (at_end (actions ! n)))"
    shows "instant_intermediate_prop_state n p = 1"
proof -
  have happening: "(t, at_start (actions ! n)) \<in> planning_sem.plan_happ_seq"
        "(t, at_end (actions ! n)) \<in> planning_sem.plan_happ_seq" 
    using index_case_defs planning_sem.action_happening_case_defs h by auto
  have is_act: "actions ! n \<in> set actions" using n by auto
  have non_int: "(set o pre) (at_end (actions ! n)) \<inter> (set o dels) (at_start (actions ! n)) = {}"
       "(set o pre) (at_end (actions ! n)) \<inter> (set o adds) (at_start (actions ! n)) = {}"
    using rat_impl.set_impl.end_start_disj_on_acts planning_sem.mutex_not_in_same_instant[OF happening] 
    unfolding planning_sem.mutex_snap_action_def 
    using is_act by fast+
  hence p': "p \<notin> (set o dels) (at_start (actions ! n)) \<union> (set o adds) (at_start (actions ! n))" using p by auto
  show ?thesis
    apply (subst instant_intermediate_prop_state_alt[OF h t n])
    using p' pre_sat_by_instant_part_updated_plan_state_seq[OF t happening(2) _ n] p by auto
qed

lemma instant_part_upd_prop_state_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<and> a = actions ! j \<longrightarrow> \<not>(planning_sem.is_instant_action (planning_sem.time_index i) a)" 
    shows "instant_part_updated_prop_state n p = instant_part_updated_prop_state m p"
proof -
  have 1: "[0..<m] = [0..<n] @ [n..<m]" using assms upt_append by auto
  have 2: "filter (planning_sem.is_instant_action (planning_sem.time_index i)) (map ((!) actions) [n..<m]) = []"
    apply (subst filter_empty_conv)
    using assms(2) by auto
  have "filter (planning_sem.is_instant_action (planning_sem.time_index i)) (map ((!) actions) [0..<n]) =
      filter (planning_sem.is_instant_action (planning_sem.time_index i)) (map ((!) actions) [0..<m])"
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
  assumes "planning_sem.instant_snaps_at (planning_sem.time_index i) = {}"
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

(* prop state for starting actions *)

lemma apply_starting_snaps_before_Suc:
  assumes is_starting: "is_starting_index t n"
      and n: "n < length actions"
      and t: "t = planning_sem.time_index i"
    shows "apply_starting_snaps_before (Suc n) s = 
  apply_starting_snaps_before n s
  - set (dels (at_start (actions ! n)))
  \<union> set (adds (at_start (actions ! n)))"
proof -
  have "at_start ` starting_actions_before n \<union> at_start ` {actions ! n} \<subseteq> at_start ` planning_sem.starting_actions_at t"
  proof -
    have "starting_actions_before (Suc n) \<subseteq> planning_sem.starting_actions_at (planning_sem.time_index i)"
      apply (subst starting_actions_before_all_is_starting_actions[symmetric])
      apply (rule starting_actions_before_mono)
      using n by auto
    with starting_actions_before_Suc assms
    show ?thesis by auto
  qed
  hence 1: "at_start ` starting_actions_before n \<union> at_start ` {actions ! n} \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t"
    unfolding planning_sem.starting_actions_at_def planning_sem.action_happening_case_defs by auto

  show ?thesis
    unfolding apply_starting_snaps_before_def
    unfolding starting_snaps_before_def
    apply (subst starting_actions_before_Suc)
    using assms apply auto[2]
    apply (subst image_Un)
    unfolding apply_snaps_def
    apply (subst planning_sem.happ_combine[simplified planning_sem.apply_effects_def, symmetric])
    using 1 
    unfolding planning_sem.apply_effects_def 
    by auto
qed

lemma starting_part_updated_prop_state_Suc:
  assumes is_starting: "is_starting_index t n"
      and n: "n < length actions"
      and t: "t = planning_sem.time_index i"
  shows "starting_part_updated_prop_state (Suc n) p =  (if p \<in> apply_starting_snaps_before n (planning_sem.inst_upd_state i) - set (dels (at_start (actions ! n))) \<union> set (adds (at_start (actions ! n))) then 1 else 0)"
  unfolding starting_part_updated_prop_state_def prop_state_def starting_part_updated_state_seq_def
  using apply_starting_snaps_before_Suc
  using assms by auto

lemma pre_sat_by_starting_part_updated_state_seq:
  assumes t[simp]: "t = planning_sem.time_index i"
      and h: "(t, h) \<in> planning_sem.plan_happ_seq"
      and h_start: "h = at_start (actions ! n)"
      and n_starting: "is_starting_index t n"
      and n: "n < length actions"
    shows "set (pre h) \<subseteq> starting_part_updated_state_seq n"
proof (rule planning_sem.pre_sat_by_arbitrary_intermediate_state[simplified comp_apply, OF i t h])
  have "starting_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" 
    unfolding starting_snaps_before_def actions_before_def starting_actions_before_def planning_sem.is_starting_action_def set_filter t[symmetric] by blast
  moreover
  have "planning_sem.instant_snaps_at (planning_sem.time_index i) \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" using planning_sem.instant_snaps_happening t by blast
  ultimately
  show "planning_sem.instant_snaps_at (planning_sem.time_index i) \<union> starting_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" by blast

  thus "starting_part_updated_state_seq n = planning_sem.apply_effects (planning_sem.instant_snaps_at (planning_sem.time_index i) \<union> starting_snaps_before n) (planning_sem.plan_state_seq i)"
    unfolding starting_part_updated_state_seq_def apply_starting_snaps_before_def 
    unfolding planning_sem.inst_upd_state_def apply_snaps_is_app_effs
    using planning_sem.happ_combine by auto

  have n_in_act: "actions ! n \<in> set actions" using n by auto
  show "h \<notin> planning_sem.instant_snaps_at (planning_sem.time_index i) \<union> starting_snaps_before n"
  proof (rule notI, elim UnE)
    assume "h \<in> planning_sem.instant_snaps_at (planning_sem.time_index i)"
    thus False
      unfolding planning_sem.instant_snaps_at_def planning_sem.instant_actions_at_def
      apply -
      apply (elim UnE imageE CollectE conjE)
      subgoal for b
        apply (insert n_starting) 
        unfolding index_case_defs 
        apply (drule planning_sem.action_happening_disj)
        apply (erule conjE) 
        using h_start
        using rat_impl.set_impl.at_start_inj_on_acts[THEN inj_onD, of "actions ! n", OF _ n_in_act] by auto
      unfolding h_start 
      using rat_impl.set_impl.end_start_disj_on_acts n_in_act by blast
  next
    assume "h \<in> starting_snaps_before n"
    thus False 
      apply -
      apply (insert h_start)
      unfolding starting_snaps_before_def starting_actions_before_def set_filter actions_before_def
      using n nth_actions_unique rat_impl.set_impl.at_start_inj_on_acts[THEN inj_on_contraD]
      by force
  qed
qed

lemma pre_val_in_starting_part_updated_prop_state_if:
  assumes t[simp]: "t = planning_sem.time_index i"
      and h: "(t, h) \<in> planning_sem.plan_happ_seq"
      and h_start: "h = at_start (actions ! n)"
      and n_starting: "is_starting_index t n"
      and n: "n < length actions"
      and p: "p \<in> set (pre h)"
    shows "starting_part_updated_prop_state n p = 1"
  using assms pre_sat_by_starting_part_updated_state_seq[THEN subsetD] assms
  unfolding starting_part_updated_prop_state_def by auto

lemma starting_part_updated_prop_state_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<and> a = actions ! j \<longrightarrow> \<not>(planning_sem.is_starting_action (planning_sem.time_index i) a)" 
    shows "starting_part_updated_prop_state n p = starting_part_updated_prop_state m p"
proof -
  have 1: "[0..<m] = [0..<n] @ [n..<m]" using assms upt_append by auto
  have 2: "filter (planning_sem.is_starting_action (planning_sem.time_index i)) (map ((!) actions) [n..<m]) = []"
    apply (subst filter_empty_conv)
    using assms(2) by auto
  have "filter (planning_sem.is_starting_action (planning_sem.time_index i)) (map ((!) actions) [0..<n]) =
      filter (planning_sem.is_starting_action (planning_sem.time_index i)) (map ((!) actions) [0..<m])"
    apply (subst 1)
    using 2 by auto
  thus ?thesis 
    unfolding starting_part_updated_prop_state_def 
    unfolding starting_part_updated_state_seq_def 
    unfolding apply_starting_snaps_before_def
    unfolding starting_snaps_before_def
    unfolding starting_actions_before_def
    unfolding actions_before_def by argo
qed

lemma starting_part_updated_prop_state_0_is_prop_state_after_instant_happ:
  "starting_part_updated_prop_state 0 = prop_state_after_instant_happ"
  unfolding starting_part_updated_prop_state_def starting_part_updated_state_seq_def 
    apply_starting_snaps_before_0_is_id
  unfolding prop_state_after_instant_happ_def by auto

lemma starting_part_updated_prop_state_all_is_prop_state_after_instant_start_happ:
  "starting_part_updated_prop_state (length actions) = prop_state_after_instant_start_happ"
 unfolding starting_part_updated_prop_state_def starting_part_updated_state_seq_def 
    apply_starting_snaps_before_all_is_apply_starting_snaps
  unfolding prop_state_after_instant_start_happ_def
  apply (subst planning_sem.inst_start_upd_state_def)
  apply (subst planning_sem.inst_upd_state_def)
  by simp

lemma prop_state_after_instant_start_happ_is_prop_state_after_instant_happ_if_no_start:
  assumes "planning_sem.starting_actions_at (planning_sem.time_index i) = {}"
  shows "prop_state_after_instant_start_happ = prop_state_after_instant_happ"
  unfolding prop_state_after_instant_happ_def prop_state_after_instant_start_happ_def
  unfolding planning_sem.inst_start_upd_state_def planning_sem.inst_upd_state_def planning_sem.apply_effects_def
  unfolding planning_sem.starting_snaps_at_def assms
  by simp

(* ending *)


lemma apply_ending_snaps_before_Suc:
  assumes is_ending: "is_ending_index t n"
      and n: "n < length actions"
      and t: "t = planning_sem.time_index i"
    shows "apply_ending_snaps_before (Suc n) s = 
  apply_ending_snaps_before n s
  - set (dels (at_end (actions ! n)))
  \<union> set (adds (at_end (actions ! n)))"
proof -
  have "at_end ` ending_actions_before n \<union> at_end ` {actions ! n} \<subseteq> at_end ` planning_sem.ending_actions_at t"
  proof -
    have "ending_actions_before (Suc n) \<subseteq> planning_sem.ending_actions_at (planning_sem.time_index i)"
      apply (subst ending_actions_before_all_is_ending_actions[symmetric])
      apply (rule ending_actions_before_mono)
      using n by auto
    with ending_actions_before_Suc assms
    show ?thesis by auto
  qed
  hence 1: "at_end ` ending_actions_before n \<union> at_end ` {actions ! n} \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t"
    unfolding planning_sem.ending_actions_at_def planning_sem.action_happening_case_defs by auto

  show ?thesis
    unfolding apply_ending_snaps_before_def
    unfolding ending_snaps_before_def
    apply (subst ending_actions_before_Suc)
    using assms apply auto[2]
    apply (subst image_Un)
    unfolding apply_snaps_def
    apply (subst planning_sem.happ_combine[simplified planning_sem.apply_effects_def, symmetric])
    using 1 
    unfolding planning_sem.apply_effects_def 
    by auto
qed

lemma ending_part_updated_prop_state_Suc:
  assumes is_ending: "is_ending_index t n"
      and n: "n < length actions"
      and t: "t = planning_sem.time_index i"
  shows "ending_part_updated_prop_state (Suc n) p =  (if p \<in> apply_ending_snaps_before n (planning_sem.inst_start_upd_state i) - set (dels (at_end (actions ! n))) \<union> set (adds (at_end (actions ! n))) then 1 else 0)"
  unfolding ending_part_updated_prop_state_def prop_state_def ending_part_updated_state_seq_def
  using apply_ending_snaps_before_Suc
  using assms by auto

lemma pre_sat_by_ending_part_updated_state_seq:
  assumes t[simp]: "t = planning_sem.time_index i"
      and h: "(t, h) \<in> planning_sem.plan_happ_seq"
      and h_end: "h = at_end (actions ! n)"
      and n_ending: "is_ending_index t n"
      and n: "n < length actions"
    shows "set (pre h) \<subseteq> ending_part_updated_state_seq n"
proof (rule planning_sem.pre_sat_by_arbitrary_intermediate_state[simplified comp_apply, OF i t h])
  have "ending_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" 
    unfolding ending_snaps_before_def actions_before_def ending_actions_before_def planning_sem.is_ending_action_def set_filter t[symmetric] by blast
  moreover
  have "planning_sem.instant_snaps_at t \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" using planning_sem.instant_snaps_happening t by blast
  moreover
  have "planning_sem.starting_snaps_at t \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" using planning_sem.starting_snaps_happening t by blast
  ultimately
  show "planning_sem.instant_snaps_at t \<union> planning_sem.starting_snaps_at t \<union> ending_snaps_before n \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq t" by blast

  thus "ending_part_updated_state_seq n = planning_sem.apply_effects (planning_sem.instant_snaps_at t \<union> planning_sem.starting_snaps_at t \<union> ending_snaps_before n) (planning_sem.plan_state_seq i)"
    unfolding ending_part_updated_state_seq_def apply_ending_snaps_before_def 
    unfolding planning_sem.inst_start_upd_state_def apply_snaps_is_app_effs
    unfolding planning_sem.inst_upd_state_def apply_snaps_is_app_effs
    using planning_sem.happ_combine by auto

  have n_in_act: "actions ! n \<in> set actions" using n by auto

  show "h \<notin> planning_sem.instant_snaps_at t \<union> planning_sem.starting_snaps_at t  \<union> ending_snaps_before n"
  proof (rule notI, elim UnE)
    assume "h \<in> planning_sem.instant_snaps_at t"
    thus False
      unfolding planning_sem.instant_snaps_at_def planning_sem.instant_actions_at_def
      apply -
      apply (elim UnE imageE CollectE conjE)
      unfolding h_end
      subgoal using rat_impl.set_impl.end_start_disj_on_acts n_in_act by blast
      subgoal for b
        apply (insert n_ending) 
        unfolding index_case_defs 
        apply (drule planning_sem.action_happening_disj)
        apply (erule conjE) 
        using rat_impl.set_impl.at_end_inj_on_acts[THEN inj_onD, of "actions ! n", OF _ n_in_act] by auto
      done
  next
    assume "h \<in> planning_sem.starting_snaps_at t"
    thus False 
      unfolding planning_sem.starting_snaps_at_def planning_sem.starting_actions_at_def
      unfolding h_end using rat_impl.set_impl.end_start_disj_on_acts n_in_act by blast
  next
    assume "h \<in> ending_snaps_before n"
    thus False 
      unfolding h_end
      unfolding ending_snaps_before_def ending_actions_before_def set_filter actions_before_def
      using n nth_actions_unique rat_impl.set_impl.at_end_inj_on_acts[THEN inj_on_contraD]
      by force
  qed
qed

lemma pre_val_in_ending_part_updated_prop_state_if:
  assumes t[simp]: "t = planning_sem.time_index i"
      and h: "(t, h) \<in> planning_sem.plan_happ_seq"
      and h_end: "h = at_end (actions ! n)"
      and n_ending: "is_ending_index t n"
      and n: "n < length actions"
      and p: "p \<in> set (pre h)"
    shows "ending_part_updated_prop_state n p = 1"
  using assms pre_sat_by_ending_part_updated_state_seq[THEN subsetD] assms
  unfolding ending_part_updated_prop_state_def by auto

lemma ending_part_updated_prop_state_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<and> a = actions ! j \<longrightarrow> \<not>(planning_sem.is_ending_action (planning_sem.time_index i) a)" 
    shows "ending_part_updated_prop_state n p = ending_part_updated_prop_state m p"
proof -
  have 1: "[0..<m] = [0..<n] @ [n..<m]" using assms upt_append by auto
  have 2: "filter (planning_sem.is_ending_action (planning_sem.time_index i)) (map ((!) actions) [n..<m]) = []"
    apply (subst filter_empty_conv)
    using assms(2) by auto
  have "filter (planning_sem.is_ending_action (planning_sem.time_index i)) (map ((!) actions) [0..<n]) =
      filter (planning_sem.is_ending_action (planning_sem.time_index i)) (map ((!) actions) [0..<m])"
    apply (subst 1)
    using 2 by auto
  thus ?thesis 
    unfolding ending_part_updated_prop_state_def 
    unfolding ending_part_updated_state_seq_def 
    unfolding apply_ending_snaps_before_def
    unfolding ending_snaps_before_def
    unfolding ending_actions_before_def
    unfolding actions_before_def by argo
qed

lemma ending_part_updated_prop_state_0_is_prop_state_after_instant_start_happ:
  "ending_part_updated_prop_state 0 = prop_state_after_instant_start_happ"
  unfolding ending_part_updated_prop_state_def ending_part_updated_state_seq_def 
    apply_ending_snaps_before_0_is_id
  unfolding prop_state_after_instant_start_happ_def by auto

lemma ending_part_updated_prop_state_all_is_prop_state_after_happ:
  "ending_part_updated_prop_state (length actions) = prop_state_after_happ"
 unfolding ending_part_updated_prop_state_def ending_part_updated_state_seq_def 
    apply_ending_snaps_before_all_is_apply_ending_snaps
  unfolding prop_state_after_happ_def
  using planning_sem.upd_state_conv_inst_start_upd_state
  by simp

lemma prop_state_after_instant_start_happ_is_prop_state_after_happ_if_no_end:
  assumes "planning_sem.ending_actions_at (planning_sem.time_index i) = {}"
  shows "prop_state_after_instant_start_happ = prop_state_after_happ"
  unfolding prop_state_after_happ_def prop_state_after_instant_start_happ_def
  unfolding planning_sem.upd_state_conv_inst_start_upd_state
  unfolding planning_sem.apply_effects_def
  unfolding planning_sem.ending_snaps_at_def assms
  by simp

subsubsection \<open>Active actions\<close>
(* active actions for starting actions *)
definition "updated_active_before n \<equiv> 
  planning_sem.active_before (planning_sem.time_index i) + card (starting_actions_before n) 
"

lemma updated_active_before_0_is_active_before: "updated_active_before 0 = planning_sem.active_before (planning_sem.time_index i)"
  using updated_active_before_def starting_actions_before_0_is_none by auto

lemma updated_active_before_all_is_active_during: 
   "updated_active_before (length actions) = planning_sem.active_during (planning_sem.time_index i)"
  using updated_active_before_def starting_actions_before_all_is_starting_actions
    planning_sem.active_during_conv_active_before by auto

lemma updated_active_before_mono:
  assumes "n \<le> m"
  shows "updated_active_before n \<le> updated_active_before m"
  using assms card_starting_actions_before_mono updated_active_before_def by simp

lemma updated_active_before_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_starting_index (planning_sem.time_index i) j)" 
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
  assumes "is_starting_index (planning_sem.time_index i) n"
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
  assumes "is_starting_index (planning_sem.time_index i) n"
    and "n < length actions"
    shows "updated_active_before n < length actions"
proof -
  have"updated_active_before (Suc n) = updated_active_before n + 1"
    using updated_active_before_Suc assms by blast
  thus ?thesis using updated_active_before_ran[of "Suc n"] assms(2) by simp
qed

lemma active_before_is_active_during_if_no_start:
  assumes "planning_sem.starting_actions_at (planning_sem.time_index i) = {}"
  shows "planning_sem.active_before (planning_sem.time_index i) = planning_sem.active_during (planning_sem.time_index i)"
  using planning_sem.active_during_conv_active_before assms by simp


(* ending actions *)

definition "updated_active_during n \<equiv>
  planning_sem.active_during (planning_sem.time_index i) - card (ending_actions_before n)
"

lemma updated_active_during_0_is_active_during: "updated_active_during 0 = planning_sem.active_during (planning_sem.time_index i)"
  using updated_active_during_def ending_actions_before_0_is_none by auto

lemma updated_active_during_all_is_active_during_minus_ended: 
   "updated_active_during (length actions) = planning_sem.active_during_minus_ended (planning_sem.time_index i)"
  using updated_active_during_def ending_actions_before_all_is_ending_actions
    planning_sem.active_during_conv_active_during_minus_ended by auto


lemma updated_active_during_inv_mono:
  assumes "n \<le> m"
  shows "updated_active_during n \<ge> updated_active_during m"
  using assms card_ending_actions_before_mono updated_active_during_def by fastforce

lemma updated_active_during_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_ending_index (planning_sem.time_index i) j)" 
    shows "updated_active_during n = updated_active_during m"
  using assms ending_actions_before_inv updated_active_during_def by auto

lemma updated_active_during_ran:
  shows "updated_active_during n \<le> length actions"
  using updated_active_during_inv_mono[of 0 n]
  using updated_active_during_0_is_active_during 
  using planning_sem.active_during_ran card_action_set 
  using order.trans by auto

lemma updated_active_during_Suc:
  assumes "is_ending_index (planning_sem.time_index i) n"
    and "n < length actions"
  shows "updated_active_during (Suc n) = updated_active_during n - 1"
proof -
  have "disjnt (ending_actions_before n) {actions ! n}"
    unfolding disjnt_def ending_actions_before_def actions_before_def
    using nth_actions_unique assms(2) by auto
  thus "updated_active_during (Suc n) = updated_active_during n - 1"
    unfolding updated_active_during_def 
    using ending_actions_before_Suc[OF assms]
    using card_Un_disjnt finite_ending_actions_before by auto
qed

lemma updated_active_during_pos_if_ending:
  assumes "is_ending_index (planning_sem.time_index i) n"
    and "n < length actions"
  shows "0 < updated_active_during n"
proof -
  have 1: "planning_sem.active_during (planning_sem.time_index i) = planning_sem.active_during_minus_ended (planning_sem.time_index i) + card (planning_sem.ending_actions_at (planning_sem.time_index i))" 
    using planning_sem.active_during_conv_active_during_minus_ended by auto

  have 2: "card (ending_actions_before n) < card (planning_sem.ending_actions_at (planning_sem.time_index i))" 
  proof -
    have "Suc n \<le> length actions" using assms(2) by auto
    hence "ending_actions_before (Suc n) \<subseteq> ending_actions_before (length actions)" using ending_actions_before_mono by simp
    hence "(ending_actions_before n) \<union> {actions ! n} \<subseteq> planning_sem.ending_actions_at (planning_sem.time_index i)" using ending_actions_before_Suc ending_actions_before_all_is_ending_actions assms by blast
    hence "(ending_actions_before n) \<subset> planning_sem.ending_actions_at (planning_sem.time_index i)" 
    proof -
      have "disjnt (ending_actions_before n) {actions ! n}"
        unfolding disjnt_def ending_actions_before_def actions_before_def
        using nth_actions_unique assms(2) by auto
      thus "ending_actions_before n \<union> {actions ! n} \<subseteq> planning_sem.ending_actions_at (planning_sem.time_index i) 
        \<Longrightarrow> ending_actions_before n \<subset> planning_sem.ending_actions_at (planning_sem.time_index i)" by auto
    qed
    thus ?thesis using planning_sem.finite_ending_actions_at 
      by (intro psubset_card_mono)
  qed
  show ?thesis
    unfolding updated_active_during_def
    apply (subst 1)
    using 2 by auto
qed
  

lemma active_during_minus_ended_is_active_during_if_no_end:
  assumes "planning_sem.ending_actions_at (planning_sem.time_index i) = {}"
  shows "planning_sem.active_during_minus_ended (planning_sem.time_index i) = planning_sem.active_during (planning_sem.time_index i)"
  using planning_sem.active_during_conv_active_during_minus_ended assms by simp

subsubsection \<open>Updated lock variables for propositions\<close>

definition "updated_locked_during n p = planning_sem.locked_during (planning_sem.time_index i) p + 
  card {a. a \<in> starting_actions_before n \<and> p \<in> (set o over_all) a}"

lemma updated_locked_during_all_is_locked_after:
  "updated_locked_during (length actions) p = planning_sem.locked_after (planning_sem.time_index i) p"
proof -
  have "sum_list (map (\<lambda>a. if planning_sem.is_starting_action (planning_sem.time_index i) a then (1::nat) else 0) (filter (\<lambda>a. p \<in> (set \<circ> over_all) a) planning_sem.action_list))
  = (\<Sum>a\<leftarrow>filter (\<lambda>a. planning_sem.is_starting_action (planning_sem.time_index i) a) (filter (\<lambda>a. p \<in> (set \<circ> over_all) a) planning_sem.action_list). 1)
  + (\<Sum>a\<leftarrow>filter (\<lambda>a. \<not>planning_sem.is_starting_action (planning_sem.time_index i) a) (filter (\<lambda>a. p \<in> (set \<circ> over_all) a) planning_sem.action_list). 0)" 
    using  sum_list_map_if'[where P = "(planning_sem.is_starting_action (planning_sem.time_index i))"]
    by blast
  also have "... = (\<Sum>a\<leftarrow>filter (\<lambda>a. planning_sem.is_starting_action (planning_sem.time_index i) a \<and> p \<in> (set \<circ> over_all) a) planning_sem.action_list. 1)" apply (subst sum_list_0) apply (subst filter_filter) apply (subst conj_commute) by simp
  also have "... = card {x \<in> set actions. planning_sem.is_starting_action (planning_sem.time_index i) x \<and> p \<in> (set \<circ> over_all) x}" 
    apply (subst distinct_sum_list_1_conv_card_set)
    using planning_sem.distinct_action_list planning_sem.set_action_list by auto
  also have "... = card {a. a \<in> starting_actions_before (length actions) \<and> p \<in> (set o over_all) a}"
    using starting_actions_before_all_is_starting_actions
    using planning_sem.starting_actions_at_def by force
  finally have 1: "(\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> (set \<circ> over_all) a) planning_sem.action_list. if planning_sem.is_starting_action (planning_sem.time_index i) a then 1 else 0) = card {a \<in> starting_actions_before (length actions). p \<in> (set \<circ> over_all) a}" by simp
  show ?thesis unfolding updated_locked_during_def planning_sem.locked_after_and_during planning_sem.locked_by_def 1 by blast
qed

lemma updated_locked_during_0_is_locked_during:
  "updated_locked_during 0 p = planning_sem.locked_during (planning_sem.time_index i) p"
  unfolding updated_locked_during_def starting_actions_before_0_is_none by simp

lemma updated_locked_during_mono:
  assumes "n \<le> m"
  shows "updated_locked_during n p \<le> updated_locked_during m p"
proof -
  have "card {a \<in> starting_actions_before n. p \<in> (set \<circ> over_all) a} \<le> card {a \<in> starting_actions_before m. p \<in> (set \<circ> over_all) a}"
    apply (rule card_mono)
    using finite_starting_actions_before starting_actions_before_mono assms by auto
  thus ?thesis unfolding updated_locked_during_def by auto
qed


lemma updated_locked_during_Suc:
  assumes starting: "is_starting_index (planning_sem.time_index i) n"
    and n: "n < length actions"
    and p: "p \<in> set (over_all (actions ! n))" 
  shows "updated_locked_during (Suc n) p = updated_locked_during n p + 1"
proof -
  have "starting_actions_before (Suc n) = starting_actions_before n \<union> {actions ! n}"
    using n starting_actions_before_Suc starting by blast
  with p
  have 1: "{a \<in> starting_actions_before (Suc n). p \<in> (set \<circ> over_all) a} = {a \<in> starting_actions_before n. p \<in> (set \<circ> over_all) a} \<union> {actions ! n}" by auto

  have "card {a \<in> starting_actions_before (Suc n). p \<in> (set \<circ> over_all) a} = card {a \<in> starting_actions_before n. p \<in> (set \<circ> over_all) a} + card {actions ! n}" 
  proof -
    have "disjnt (starting_actions_before n) {actions ! n}"
        unfolding disjnt_def starting_actions_before_def actions_before_def
        using nth_actions_unique starting n by auto
    hence " {a \<in> starting_actions_before n. p \<in> (set \<circ> over_all) a} \<inter> {actions ! n} = {}" by auto
    thus ?thesis
      apply (subst 1) 
      apply (subst card_Un_disjoint)
      using finite_starting_actions_before by auto
  qed
  thus ?thesis unfolding updated_locked_during_def by simp
qed

lemma updated_locked_during_Suc_inv:
  assumes starting: "is_starting_index (planning_sem.time_index i) n"
    and n: "n < length actions"
    and p: "p \<notin> set (over_all (actions ! n))" 
  shows "updated_locked_during (Suc n) p = updated_locked_during n p"
proof -
  have "starting_actions_before (Suc n) = starting_actions_before n \<union> {actions ! n}"
    using n starting_actions_before_Suc starting by blast
  hence "{a \<in> starting_actions_before (Suc n). p \<in> (set \<circ> over_all) a} = {a \<in> starting_actions_before n. p \<in> (set \<circ> over_all) a}"
    using p by auto
  thus ?thesis unfolding updated_locked_during_def by auto
qed
  

lemma updated_locked_during_ran:
  assumes n: "n \<le> length actions"
  shows "updated_locked_during n p \<le> length actions"
  using updated_locked_during_mono[OF assms] 
  using planning_sem.locked_after_ran 
  unfolding updated_locked_during_all_is_locked_after
  unfolding card_action_set 
  by (rule order.trans)

lemma updated_locked_during_ran_if_starting:
  assumes starting: "is_starting_index (planning_sem.time_index i) n"
    and n: "n < length actions"
    and p: "p \<in> set (over_all (actions ! n))" 
  shows "updated_locked_during n p < length actions"
proof -
  have "updated_locked_during (Suc n) p \<le> length actions" 
    using updated_locked_during_ran[of "Suc n"] assms 
    by fastforce
  moreover
  have "updated_locked_during (Suc n) p = updated_locked_during n p + 1" 
    using updated_locked_during_Suc[OF assms] by auto
  ultimately
  show ?thesis by linarith
qed

lemma updated_locked_during_inv:
  assumes "n \<le> m"
      and "\<forall>j a. n \<le> j \<and> j < m \<longrightarrow> \<not>(is_starting_index (planning_sem.time_index i) j)" 
    shows "updated_locked_during n p = updated_locked_during m p"
  unfolding updated_locked_during_def 
  using starting_actions_before_inv[OF assms]
  by auto

end

end
end

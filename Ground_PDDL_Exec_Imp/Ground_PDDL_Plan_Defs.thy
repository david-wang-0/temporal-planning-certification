theory Ground_PDDL_Plan_Defs
  imports Ground_PDDL_Problem_Defs
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics_Alt"
begin
  
locale ground_plan_defs = 
  ground_ast_problem_defs P 
  for P::ast_problem +
  fixes tp::"(rat \<times> plan_action) list"
begin

fun timed_plan_action_to_ref_plan_action::"rat \<times> plan_action \<Rightarrow> ast_action_schema \<times> int \<times> int" where
"timed_plan_action_to_ref_plan_action (t, Simple_Plan_Action n as) = (the (resolve_action_schema n), floor t, 0)" |
"timed_plan_action_to_ref_plan_action (t, Durative_Plan_Action n as d) = (the (resolve_action_schema n), floor t, floor d)"

definition ref_plan where
"ref_plan \<equiv> (map timed_plan_action_to_ref_plan_action tp)"


definition plan_imp where
"plan_imp \<equiv> 
  ref_plan
  |> nth_opt"

text \<open>Simple properties\<close>

lemma dom_plan_imp: 
  "dom plan_imp = {i. i < length tp}"
  unfolding plan_imp_def dom_nth_opt ref_plan_def by auto

lemma ran_plan_imp:
  "ran plan_imp = timed_plan_action_to_ref_plan_action ` set tp"
  unfolding plan_imp_def ran_nth_opt ref_plan_def by auto

lemma in_set_ref_planE:
  assumes "(a, t, d) \<in> set ref_plan"
      and "\<And>t n as. (t, Simple_Plan_Action n as) \<in> set tp \<Longrightarrow> Q (the (resolve_action_schema n)) (floor t) 0"
      and "\<And>t n as d. (t, Durative_Plan_Action n as d) \<in> set tp \<Longrightarrow> Q (the (resolve_action_schema n)) (floor t) (floor d)"
  shows "Q a t d"
  using assms(1) unfolding ref_plan_def set_map
  apply (elim imageE)
  subgoal for x
    apply (cases x)
    subgoal for t' b
      apply (cases b)
      using assms(2, 3)
      by auto
    done
  done

lemma ref_plan_pairwise_if:
  assumes "list_pairwise (\<lambda>a b. Q (timed_plan_action_to_ref_plan_action a) (timed_plan_action_to_ref_plan_action b)) tp"
  shows "list_pairwise Q ref_plan"
  using assms unfolding ref_plan_def 
  using list_pairwise_map by blast
                            
text \<open>Properties specific to later proofs\<close>
fun plan_act_no_args where
"plan_act_no_args (Simple_Plan_Action n []) = True" |
"plan_act_no_args (Durative_Plan_Action n [] d) = True" |
"plan_act_no_args _ = False"

fun timed_plan_action_durs_integer::"rat \<times> plan_action \<Rightarrow> bool" where
"timed_plan_action_durs_integer (t, Simple_Plan_Action n as) = (is_integer t)" |
"timed_plan_action_durs_integer (t, Durative_Plan_Action n as d) = (is_integer t \<and> is_integer d)"

fun PDDL_no_self_overlap::"(rat \<times> plan_action) \<Rightarrow> (rat \<times> plan_action) \<Rightarrow> bool" where
"PDDL_no_self_overlap (t, Simple_Plan_Action x _) (u, Simple_Plan_Action y _) = (x = y \<longrightarrow> t \<noteq> u)" |
"PDDL_no_self_overlap (_, Simple_Plan_Action _ _) (_, Durative_Plan_Action _ _ _) = True" |
"PDDL_no_self_overlap (_, Durative_Plan_Action _ _ _) (_, Simple_Plan_Action _ _) = True" |
"PDDL_no_self_overlap (t, Durative_Plan_Action x _ d) (u, Durative_Plan_Action y _ e) =
  (x = y \<longrightarrow> \<not>((t \<le> u \<and> u \<le> t + d) \<or> (u \<le> t \<and> t \<le> u + e)))"

definition "PDDL_plan_no_self_overlap \<equiv> list_pairwise PDDL_no_self_overlap tp"

fun ref_no_self_overlap::"(ast_action_schema \<times> int \<times> int) \<Rightarrow> (ast_action_schema \<times> int \<times> int) \<Rightarrow> bool" where
"ref_no_self_overlap (a, t, d) (b, u, e) = ((a = b) \<longrightarrow> \<not>((t \<le> u \<and> u \<le> t + d) \<or> (u \<le> t \<and> t \<le> u + e)))"

definition "ref_plan_no_self_overlap \<equiv> list_pairwise ref_no_self_overlap ref_plan"

lemma ref_no_self_overlap_refl:
  "\<forall>x y. ref_no_self_overlap x y \<longleftrightarrow> ref_no_self_overlap y x"
  by auto


text \<open>The abstract plan that can be obtained from this plan\<close>
sublocale imp_defs: temp_plan_for_problem_list_defs_int
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  init_spec goal_spec 0 props_spec actions_spec plan_imp  
  by unfold_locales simp

definition "abstr_plan \<equiv> (map_option (map_prod id (map_prod rat_of_int rat_of_int))) o plan_imp"

lemma ran_abstr_plan_ref_planE:
  assumes "(a, t, d) \<in> ran abstr_plan"
      and "\<And>a t d. (a, t, d) \<in> set ref_plan \<Longrightarrow> Q a (rat_of_int t) (rat_of_int d)"
    shows "Q a t d"
  using assms unfolding abstr_plan_def plan_imp_def ran_map_option comp_def ran_nth_opt 
  by auto

lemma abstr_plan_binary_prop:
  assumes secondary:
    "i \<in> dom abstr_plan" 
    "j \<in> dom abstr_plan" 
    "i \<noteq> j"
    "abstr_plan i = Some (a, ta, da)"
    "abstr_plan j = Some (b, tb, db)"
  and refl:
    "\<forall>a ta da b tb db. Q a ta da b tb db = Q b tb db a ta da"
  and primary: "list_pairwise (\<lambda>(a, ta, da) (b, tb, db). Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)) ref_plan"
shows "Q a ta da b tb db"
proof -
  have "list_pairwise (\<lambda>(a, ta, da) (b, tb, db). Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)) ref_plan =
     (\<forall>i j. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j \<longrightarrow> 
      (case ref_plan ! i of (a, ta, da) \<Rightarrow> \<lambda>(b, tb, db). 
      Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)) (ref_plan ! j))" 
    using list_pairwise_nth_refl[of "\<lambda>(a, ta, da) (b, tb, db). Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)",
        where xs = ref_plan] using refl by simp
  hence 1: "(\<forall>i j a ta da b tb db. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j 
      \<longrightarrow> (ref_plan ! i) = (a, ta, da) \<longrightarrow> (ref_plan ! j) = (b, tb, db)
      \<longrightarrow> Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db))"
    using primary by fastforce
  show ?thesis
    using secondary 
    unfolding abstr_plan_def plan_imp_def 
    unfolding ran_map_option comp_def ran_nth_opt 
    unfolding dom_map_option comp_def dom_nth_opt
    unfolding map_option_eq_Some
    apply -
    apply (elim exE conjE)
    subgoal for x y
      apply (drule nth_opt_Some)+
      apply (induction x; induction y)
      unfolding map_prod_simp using 1 by auto
    done
qed

(* --- *)
lemma duration_matches_imp_sat_lb: 
  assumes "duration_matches d dc ps as"
      and "\<not>is_Func_Const dc"
  shows "imp_defs.rat_impl.satisfies_lower_bound (dc_to_lb dc) d"
  using assms
  apply (cases dc)
  subgoal by auto
  subgoal for op ps by (cases op) auto
  by auto

lemma durations_match_imp_sat_lb:
  assumes "durations_match d dcs ps as"
      and "list_all (\<lambda>x. \<not>is_Func_Const x) dcs"
    shows "imp_defs.rat_impl.satisfies_lower_bound (dc_list_lower dcs) d"
  apply (rule dc_list_lower_propI)
  using assms duration_matches_imp_sat_lb unfolding durations_match_def list_all_iff by auto  

lemma duration_matches_imp_sat_ub: 
  assumes "duration_matches d dc ps as"
      and "\<not>is_Func_Const dc"
  shows "imp_defs.rat_impl.satisfies_upper_bound (dc_to_ub dc) d"
  using assms
  apply (cases dc)
  subgoal by auto
  subgoal for op ps by (cases op) auto
  by auto

lemma durations_match_imp_sat_ub:
  assumes "durations_match d dcs ps as"
      and "list_all (\<lambda>x. \<not>is_Func_Const x) dcs"
    shows "imp_defs.rat_impl.satisfies_upper_bound (dc_list_upper dcs) d"
  apply (rule dc_list_upper_propI)
  using assms duration_matches_imp_sat_ub unfolding durations_match_def list_all_iff by auto  

lemma integers_sat_lower_bounds:
  assumes "imp_defs.rat_impl.satisfies_lower_bound x d"
      and "pred_option (pred_lower_bound is_integer) x"
      and "is_integer d"
    shows "imp_defs.rat_impl.satisfies_lower_bound (map_option (map_lower_bound (\<lambda>x. rat_of_int \<lfloor>x\<rfloor>)) x) (rat_of_int \<lfloor>d\<rfloor>)"
  using assms apply (cases x)
   apply simp
  subgoal for a
    apply (cases a)
    using is_integer_floor_less Archimedean_Field.floor_mono
    by auto
  done

lemma integers_sat_upper_bounds:
  assumes "imp_defs.rat_impl.satisfies_upper_bound x d"
      and "pred_option (pred_upper_bound is_integer) x"
      and "is_integer d"
    shows "imp_defs.rat_impl.satisfies_upper_bound (map_option (map_upper_bound (\<lambda>x. rat_of_int \<lfloor>x\<rfloor>)) x) (rat_of_int \<lfloor>d\<rfloor>)"
  using assms apply (cases x)
   apply simp
  subgoal for a
    apply (cases a)
    using is_integer_floor_less Archimedean_Field.floor_mono
    by auto
  done

lemmas integers_sat_bounds = integers_sat_lower_bounds integers_sat_upper_bounds

lemma ground_act_pres_conv_pre_spec:
  assumes "ground_act_pres_pos a"
  shows "to_predicate ` Atom `(atoms (ground_action.precondition a)) = set (pre_spec a)"
  using assms
proof (induction a)
  case (Ground_Action n anno pre eff)
  hence "is_pos_conj pre" by simp
  then show ?case using is_pos_conj_predicates by simp
qed

lemma add_preds: "to_predicate ` set (adds (ground_action.effect a)) = set (adds_spec a)"
  apply (cases a) by simp

lemma del_preds: "to_predicate ` set (dels (ground_action.effect a)) = set (dels_spec a)"
  apply (cases a) by simp


lemma acts_non_intrf_imp_mutex_snap_action:
  assumes non_int: "acts_non_intrf a b"
      and pres_pos: "ground_act_pres_pos a" "ground_act_pres_pos b"
  shows "\<not> imp_defs.rat_impl.set_impl.mutex_snap_action a b"
proof -
  have "to_predicate ` Atom `(atoms (ground_action.precondition a)) = set (pre_spec a)"
    using ground_act_pres_conv_pre_spec pres_pos by auto
  moreover
  have "to_predicate ` set (adds (ground_action.effect a)) = set (adds_spec a)"
    using add_preds by simp
  moreover
  have "to_predicate ` set (dels (ground_action.effect a)) = set (dels_spec a)"
    using del_preds by simp
  moreover
  have "to_predicate ` Atom `(atoms (ground_action.precondition b)) = set (pre_spec b)"
    using ground_act_pres_conv_pre_spec pres_pos by auto
  moreover
  have "to_predicate ` set (adds (ground_action.effect b)) = set (adds_spec b)"
    using add_preds by simp
  moreover
  have "to_predicate ` set (dels (ground_action.effect b)) = set (dels_spec b)"
    using del_preds by simp
  moreover

  have x: "(\<not> x \<noteq> y) = (x = y)" for x y by simp

  find_theorems "?f ` ?x \<inter> ?f ` ?y"
  have inj_to_predicate: "inj_on to_predicate {x. is_pos_lit x \<and> form_preds_no_args x}"
    apply (rule inj_onI)
    apply (elim CollectE conjE is_pos_lit.elims)
       apply simp
    
    apply (elim Collect_is_pos_litE)
    subgoal for x

  show ?thesis
    unfolding imp_defs.rat_impl.set_impl.mutex_snap_action_def
    unfolding comp_def calculation[symmetric]
    unfolding de_Morgan_disj x 
    unfolding image_Un[symmetric]
    apply (intro conjI)
    using non_int 
    unfolding acts_non_intrf_def Let_def
qed

end

locale valid_ground_plan =
  ground_ast_problem P +
  ground_plan_defs P tp
  for P::ast_problem 
  and tp::"(rat \<times> plan_action) list" +
assumes valid_plan: "valid_plan tp"
    and pddl_nso: "PDDL_plan_no_self_overlap"
    and plan_acts_durs_integer: "list_all (timed_plan_action_durs_integer) tp"
begin

text \<open>We obtain some other constants\<close>
definition "htps_and_final_state \<equiv> 
  let
    (htps, final_state) = (SOME hm. (\<lambda>(htps, M'). htps_seq tp htps \<and> valid_state_seq I htps tp M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)) hm)
  in
  (htps, final_state)"

thm Hilbert_Choice.someI

definition "htps = fst htps_and_final_state"
definition "final_state = snd htps_and_final_state"

lemma htps_seq_htps: "htps_seq tp htps"
  and valid_state_seq_final_state: "valid_state_seq I htps tp final_state" 
  and final_state_sat_goal: "final_state \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
proof -
  let ?P = "(\<lambda>(htps, M'). htps_seq tp htps \<and> valid_state_seq I htps tp M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P))"
  have P: "\<exists>x. (\<lambda>(htps, M'). htps_seq tp htps \<and> valid_state_seq I htps tp M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)) x"
    using valid_plan unfolding valid_plan_def valid_plan_from_def by auto
  have "?P htps_and_final_state" using Hilbert_Choice.someI_ex[of ?P, OF P]  htps_and_final_state_def by auto
  thus "htps_seq tp htps"
       "valid_state_seq I htps tp final_state"
       "final_state \<^sup>c\<TTurnstile>\<^sub>= goal P"
    unfolding htps_def final_state_def by auto
qed

lemma all_htps_acts_non_intrf:
  assumes "A\<^sub>i = acts_of_plan_at t\<^sub>i tp"
      and "t\<^sub>i \<in> set htps"
    shows "(\<forall>a \<in> A\<^sub>i. \<forall>b \<in> A\<^sub>i. a \<noteq> b \<longrightarrow> acts_non_intrf a b)"
proof -
  have "(\<forall>a \<in> A. \<forall>b \<in> A. a \<noteq> b \<longrightarrow> acts_non_intrf a b)" 
    if "A = acts_of_plan_at t \<pi>" 
    and "t \<in> set ts"
    and "\<exists>M M'. valid_state_seq M ts \<pi> M'"
    for A t ts \<pi>
    using that
    apply (induction ts)
     apply simp
    by force
  thus ?thesis using assms valid_state_seq_final_state by blast
qed

(* Needs an assumption that durations are integers. *)

lemma wf_plan_actions:
  assumes "(t, a) \<in> set tp"
  shows "wf_plan_action a" 
  using assms valid_plan unfolding valid_plan_def valid_plan_from_def wf_plan_def by blast

lemma durative_plan_action_durs:
  assumes "wf_plan_action (Durative_Plan_Action n as d)"
  shows "0 \<le> d"
  using durative_plan_action_schema_type1 assms by force


lemma plan_acts_no_args: "list_all (snd #> plan_act_no_args) tp"
proof -
  { fix t a 
    assume "(t, a) \<in> set tp"
    hence wf: "wf_plan_action a" using wf_plan_actions by auto
    have "plan_act_no_args a"
    proof (cases a)
      case a: (Simple_Plan_Action n ps)
      hence wf: "wf_plan_action (Simple_Plan_Action n ps)" using wf by auto
      then obtain pre eff as  where
        res: "resolve_action_schema n = Some (Simple_Action_Schema n as pre eff)"
        using simple_plan_action_schema_type1 by blast
      have pm: "action_params_match (Simple_Action_Schema n as pre eff) ps" using wf res by auto
      have "as = []" using resolve_action_schema_def index_by_eq_SomeD acts_no_args res
        unfolding list_all_iff by fastforce
      then show ?thesis using pm a action_params_match_def by simp
    next
      case a: (Durative_Plan_Action n ps d)
      hence wf: "wf_plan_action (Durative_Plan_Action n ps d)" using wf by auto
      then obtain pre eff as dcs where
        res: "resolve_action_schema n = Some (Durative_Action_Schema n as pre eff dcs)"
        using durative_plan_action_schema_type1 by blast
      have pm: "action_params_match (Durative_Action_Schema n as pre eff dcs) ps" using wf res by auto
      have "as = []" using resolve_action_schema_def index_by_eq_SomeD acts_no_args res
        unfolding list_all_iff by fastforce
      then show ?thesis using pm a action_params_match_def by simp
    qed
  }
  thus ?thesis unfolding list_all_iff by fastforce
qed


lemma simple_action_in_ref_plan:
  assumes "(Simple_Action_Schema n ps pre eff, t, d) \<in> set ref_plan"
  shows "\<exists>as. (rat_of_int t, Simple_Plan_Action n as) \<in> set tp \<and> resolve_action_schema n = Some (Simple_Action_Schema n ps pre eff)"
proof -
  obtain t' a where
    a: "(t', a) \<in> set tp"
    "timed_plan_action_to_ref_plan_action (t', a) = (Simple_Action_Schema n ps pre eff, t, d)"
    "wf_plan_action a"
    using assms wf_plan_actions unfolding ref_plan_def set_map by auto
  hence "\<exists>as'. a = Simple_Plan_Action n as' \<and> resolve_action_schema n = Some (Simple_Action_Schema n ps pre eff)"
  proof (cases a)
    case x: (Simple_Plan_Action n' as)
    have "n' = n" using a unfolding x using simple_plan_action_schema_type1 by fastforce
    then show ?thesis using x a using simple_plan_action_schema_type1 by fastforce
  next
    case (Durative_Plan_Action n' as d')
    then show ?thesis using durative_plan_action_schema_type1 a by fastforce
  qed
  moreover
  { have "is_integer t'" using plan_acts_durs_integer using a apply (cases a) unfolding list_all_iff by auto
    moreover
    have "t = floor t'" using a apply (cases a) by auto
    ultimately
    have "rat_of_int t = t'" using is_integer_of_int by blast
  }
  ultimately
  show ?thesis using a(1) by fast
qed

lemma durative_action_in_ref_plan:
  assumes "(Durative_Action_Schema n ps dcs pre eff, t, d) \<in> set ref_plan"
  shows "\<exists>as. (rat_of_int t, Durative_Plan_Action n as (rat_of_int d)) \<in> set tp 
        \<and> resolve_action_schema n = Some (Durative_Action_Schema n ps dcs pre eff)"
proof -
  obtain t' a where
    a: "(t', a) \<in> set tp"
    "timed_plan_action_to_ref_plan_action (t', a) = (Durative_Action_Schema n ps dcs pre eff, t, d)"
    "wf_plan_action a"
    using assms wf_plan_actions unfolding ref_plan_def set_map by auto
  hence "\<exists>as' d'. a = Durative_Plan_Action n as' d' \<and> resolve_action_schema n = Some (Durative_Action_Schema n ps dcs pre eff)"
  proof (cases a)
    case x: (Simple_Plan_Action n' as)
    have "n' = n" using a unfolding x using simple_plan_action_schema_type1 by fastforce
    then show ?thesis using x a using simple_plan_action_schema_type1 by fastforce
  next
    case x: (Durative_Plan_Action n' as d')
    have "n' = n" using a unfolding x using durative_plan_action_schema_type1 by fastforce
    then show ?thesis using durative_plan_action_schema_type1 a x by fastforce
  qed
  then obtain as' d' where
    wit: "a = Durative_Plan_Action n as' d'" 
    "resolve_action_schema n = Some (Durative_Action_Schema n ps dcs pre eff)" by auto
  moreover
  { have "is_integer t'" using plan_acts_durs_integer using a apply (cases a) unfolding list_all_iff by auto
    moreover
    have "t = floor t'" using a apply (cases a) by auto
    ultimately
    have "rat_of_int t = t'" using is_integer_of_int by blast
  }
  moreover
  { have "is_integer d'" using plan_acts_durs_integer using wit a apply (cases a) unfolding list_all_iff by auto
    moreover
    have "d = floor d'" using wit a apply (cases a) by auto
    ultimately
    have "rat_of_int d = d'" using is_integer_of_int by blast
  }
  ultimately
  show ?thesis using a(1) by fast
qed

lemma resolve_action_schema_inj_on_dom:
  assumes "resolve_action_schema x = resolve_action_schema y"
      and "resolve_action_schema x = Some a"
      and "resolve_action_schema y = Some b"
  shows "x = y"
proof (cases a; cases b)
  fix l as pre eff n bs ore fff
  assume a: "a = Simple_Action_Schema l as pre eff" 
     and b: "b = Simple_Action_Schema n bs ore fff"
  have dist: "distinct (map ast_action_schema.name (actions D))" using wf_domain wf_domain_def by blast
  have "x = l" using index_by_eq_Some_eq[OF dist] a assms(2) unfolding resolve_action_schema_def by simp
  moreover
  have "y = n" using index_by_eq_Some_eq[OF dist] b assms(3) unfolding resolve_action_schema_def by simp
  ultimately 
  show "x = y" using assms a b by simp
next 
  fix l as pre eff n bs ore fff d
  assume a: "a = Simple_Action_Schema l as pre eff" 
     and b: "b = Durative_Action_Schema n bs d ore fff"
  show "x = y" using assms a b by simp
next 
  fix l as pre eff n bs ore fff d
  assume a: "a = Durative_Action_Schema l as d pre eff" 
     and b: "b = Simple_Action_Schema n bs ore fff"
  show "x = y" using assms a b by simp
next 
  fix l as pre eff n bs ore fff d e
  assume a: "a = Durative_Action_Schema l as d pre eff" 
     and b: "b = Durative_Action_Schema n bs e ore fff"
  have dist: "distinct (map ast_action_schema.name (actions D))" using wf_domain wf_domain_def by blast
  have "x = l" using index_by_eq_Some_eq[OF dist] a assms(2) unfolding resolve_action_schema_def by simp
  moreover
  have "y = n" using index_by_eq_Some_eq[OF dist] b assms(3) unfolding resolve_action_schema_def by simp
  ultimately 
  show "x = y" using assms a b by simp
qed

text \<open>Well-formedness and properties of the refined plan.\<close>
(* 
- Every action in the refined plan belongs to the set of actions. 
- The duration of every action in the refined plan is greater than or equal to 0.
- The actions' starts and ends are pairwise non-interfering
- The actions' 
*)

lemma ref_plan_acts_in_actions:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "a \<in> set actions_spec"
  apply (rule in_set_ref_planE[OF assms])
  using simple_plan_action_schema_type1 resolve_action_in_actions  wf_plan_actions
   apply fastforce
  using durative_plan_action_schema_type1 resolve_action_in_actions wf_plan_actions
  by fastforce

lemma ref_plan_acts_wf:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "wf_action_schema a" 
  apply (cases a)
  using assms simple_action_in_ref_plan durative_action_in_ref_plan resolve_action_wf 
  by blast+

lemma ref_plan_durs:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "0 \<le> d"
  apply (rule in_set_ref_planE[OF assms])
  using durative_plan_action_durs wf_plan_actions 
  by fastforce+ 

lemma ref_plan_start_is_htp:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "is_htp tp (rat_of_int t)"
  apply (cases a)
  using assms simple_action_in_ref_plan durative_action_in_ref_plan resolve_action_wf 
  unfolding is_htp_def by blast+

lemma ref_plan_end_is_htp_if_durative:
  assumes "(Durative_Action_Schema n ps dcs pre eff, t, d) \<in> set ref_plan"
  shows "is_htp tp (rat_of_int (t + d))"
  using durative_action_in_ref_plan[OF assms]
  unfolding is_htp_def durative_acts_def is_act_simple_def by fastforce

lemma ref_plan_start_in_htps:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "(rat_of_int t) \<in> set htps"
  using ref_plan_start_is_htp[OF assms] htps_seq_htps htps_seq_def by blast

lemma ref_plan_end_in_htps_if_durative:
  assumes "(Durative_Action_Schema n ps dcs pre eff, t, d) \<in> set ref_plan"
  shows "rat_of_int (t + d) \<in> set htps"
  using ref_plan_end_is_htp_if_durative[OF assms] 
    htps_seq_htps htps_seq_def by blast

(* Hence, we know that the starts and ends are well-formed *)

lemma ref_plan_snaps_wf:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "wf_ground_action (at_start_spec a)"
        "wf_ground_action (at_end_spec a)"
        "wf_ground_action (over_all_snap a)"
  using assms ref_plan_acts_in_actions 
  by (blast intro: start_snaps_wf end_snaps_wf over_all_snap_wf)+

(* Prove that these are in the acts_of_plan_at *)


(* acts_of_plan_at are only guaranteed not to interfere, if they are not equal, but
equality is asserted on the ground action, which means that a can interfere with b
if dels b = {x}, pre b = {x}, adds b = {}, dels a = {x}, pre a = {x}, adds a = {x}. *)


lemma at_start_snap_at_t:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "at_start_spec a \<in> acts_of_plan_at (rat_of_int t) tp"
  using assms 
proof (induction a)
  case 1: (Simple_Action_Schema n ps pre eff)
  then obtain as where
    x: "(rat_of_int t, Simple_Plan_Action n as) \<in> set tp" 
    and y: "resolve_action_schema n = Some (Simple_Action_Schema n ps pre eff)"
    using simple_action_in_ref_plan by blast
  hence z: "Simple_Action_Schema n ps pre eff = the (resolve_action_schema n)" by simp
  have as_Nil: "as = []" using x plan_acts_no_args unfolding list_all_iff by (cases as) auto
  have "at_start_spec (Simple_Action_Schema n ps pre eff)
    \<in> {a\<^sub>\<pi>. \<exists>\<pi>. (rat_of_int t, \<pi>) \<in> simple_acts tp \<and> Some a\<^sub>\<pi> = res_inst \<pi> At_Start}"
    apply (rule CollectI)
    apply (intro exI)
    using x 
    unfolding simple_acts_def is_act_simple_def comp_def set_filter
    unfolding res_inst.simps at_start_spec.simps unfolding z as_Nil by auto
  thus ?case unfolding acts_of_plan_at_def by simp
next
  case (Durative_Action_Schema n ps dcs pre eff)
  then obtain as d where
    x: "(rat_of_int t, Durative_Plan_Action n as d) \<in> set tp" 
    and y: "resolve_action_schema n = Some (Durative_Action_Schema n ps dcs pre eff)"
    using durative_action_in_ref_plan by blast
  hence z: "Durative_Action_Schema n ps dcs pre eff = the (resolve_action_schema n)" by simp
  have as_Nil: "as = []" using x plan_acts_no_args unfolding list_all_iff by (cases as) auto
  have "at_start_spec (Durative_Action_Schema n ps dcs pre eff)
    \<in> {a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t. \<exists>\<pi>. (rat_of_int t,\<pi>) \<in> durative_acts tp \<and> Some a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t = res_inst_snap_action \<pi> At_Start}"
    apply (rule CollectI)
    apply (intro exI conjI)
    using x
    unfolding durative_acts_def is_act_simple_def comp_def set_filter apply auto[1] 
    unfolding res_inst.simps at_start_spec.simps unfolding z as_Nil by simp
  thus ?case unfolding acts_of_plan_at_def by simp
qed

lemma at_end_snap_at_t_if_durative:
  assumes "((Durative_Action_Schema n ps dcs pre eff), t, d) \<in> set ref_plan"
  shows "at_end_spec (Durative_Action_Schema n ps dcs pre eff) \<in> acts_of_plan_at (rat_of_int (t + d)) tp"
proof -
  obtain as where
    x: "(rat_of_int t, Durative_Plan_Action n as (rat_of_int d)) \<in> set tp"
    and y: "resolve_action_schema n = Some (Durative_Action_Schema n ps dcs pre eff)"
    using assms durative_action_in_ref_plan by blast
  hence z: "Durative_Action_Schema n ps dcs pre eff = the (resolve_action_schema n)" by simp
  have as_Nil: "as = []" using x plan_acts_no_args unfolding list_all_iff by (cases as) auto
  have "at_end_spec (Durative_Action_Schema n ps dcs pre eff)
    \<in> {a\<^sub>e\<^sub>n\<^sub>d. \<exists>t' \<pi>. (t',\<pi>) \<in> durative_acts tp \<and> rat_of_int (t + d) = t' + duration \<pi> \<and> Some a\<^sub>e\<^sub>n\<^sub>d = res_inst_snap_action \<pi> At_End}"
    apply (rule CollectI)
    apply (intro exI conjI)
    using x
    unfolding durative_acts_def is_act_simple_def comp_def set_filter apply auto[2]
    unfolding res_inst.simps at_end_spec.simps unfolding z as_Nil by simp
  thus ?thesis unfolding acts_of_plan_at_def by simp
qed

(* The above is needed for non-interference of starting snaps.
Ending snaps for durative (but not simple actions) actions need a similar one.
Simple actions' ends need to be considered separately *)

find_theorems "inst_of_plan_action"

text \<open>We obtain a placeholder for the valid state_sequence\<close>
term inst_of_plan_action

(* We must know that these are *)

lemma PDDL_no_self_overlap_imp_ref_no_self_overlap:
  assumes "PDDL_no_self_overlap a b"
      and "wf_plan_action (snd a)"
      and "wf_plan_action (snd b)"
      and "plan_act_no_args (snd a)"
      and "plan_act_no_args (snd b)"
      and "timed_plan_action_durs_integer a"
      and "timed_plan_action_durs_integer b"
  shows "ref_no_self_overlap (timed_plan_action_to_ref_plan_action a) (timed_plan_action_to_ref_plan_action b)"
  using assms
proof (induction rule: PDDL_no_self_overlap.induct)
  case (1 t x as u y bs)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" using 1 by auto

  have a: "x = y \<longrightarrow> t \<noteq> u" using 1 unfolding PDDL_no_self_overlap.simps by auto

  have wf_acts: 
    "wf_plan_action (Simple_Plan_Action x as)"
    "wf_plan_action (Simple_Plan_Action y bs)" using 1 by auto

  hence res_some: 
    "\<exists>a. resolve_action_schema x = Some a"
    "\<exists>b. resolve_action_schema y = Some b" using simple_plan_action_schema_type1 by blast+

  have res_iff: "the (resolve_action_schema x) = the (resolve_action_schema y) \<longleftrightarrow> x = y"
    using res_some resolve_action_schema_inj_on_dom by auto 

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    apply (subst res_iff)
    using a is_integer_floor_ne t_integer u_integer 
    by auto
next
  case (2 t x as u y d bs)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" using 2 by auto


  have wf_acts: 
    "wf_plan_action (Simple_Plan_Action x as)"
    "wf_plan_action (Durative_Plan_Action y d bs)" using 2 by auto

  hence res_some: 
    "\<exists>a. resolve_action_schema x = Some a"
    "\<exists>b. resolve_action_schema y = Some b" 
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 by blast+

  have res_neq: "the (resolve_action_schema x) \<noteq> the (resolve_action_schema y)"
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 wf_acts by fastforce

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    using res_neq by auto
next
  case (3 t x d as u y bs)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" using 3 by auto

  have wf_acts: 
    "wf_plan_action (Durative_Plan_Action x d as)"
    "wf_plan_action (Simple_Plan_Action y bs)" using 3 by auto

  hence res_some: 
    "\<exists>a. resolve_action_schema x = Some a"
    "\<exists>b. resolve_action_schema y = Some b" 
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 by blast+

  have res_neq: "the (resolve_action_schema x) \<noteq> the (resolve_action_schema y)"
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 wf_acts by fastforce

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    using res_neq by auto
next
  case (4 t x as d u y bs e)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" 
   and d_integer: "is_integer d"
   and e_integer: "is_integer e" using 4 by auto

  note vs_integer = t_integer u_integer d_integer e_integer
  
  have wf_acts: 
    "wf_plan_action (Durative_Plan_Action x as d)"
    "wf_plan_action (Durative_Plan_Action y bs e)" using 4 by auto

  have res_iff: "the (resolve_action_schema x) = the (resolve_action_schema y) \<longleftrightarrow> x = y"
    using durative_plan_action_schema_type1[OF wf_acts(1)] durative_plan_action_schema_type1[OF wf_acts(2)]
    by auto

  {
    assume "x = y"
    hence " \<not> (t \<le> u \<and> u \<le> t + d \<or> u \<le> t \<and> t \<le> u + e)" using 4 by simp
    hence "(u < t \<or> t + d < u) \<and> (t < u \<or> u + e < t)" by linarith
    moreover
    { assume "u < t"
      hence "floor u < floor t" using vs_integer is_integer_floor_less by auto
    }
    moreover
    { assume "t + d < u"
      hence "floor (t + d) < floor u" 
        by (intro vs_integer is_integer_floor_less is_integer_add)
      hence "floor t + floor d < floor u" by linarith
    }
    moreover
    { assume "t < u"
      hence "floor t < floor u" using vs_integer is_integer_floor_less by auto
    }
    moreover
    { assume "u + e < t"
      hence "floor (u + e) < floor t" 
        by (intro vs_integer is_integer_floor_less is_integer_add)
      hence "floor u + floor e < floor t" by linarith 
    }
    ultimately
    have " \<not> (\<lfloor>t\<rfloor> \<le> \<lfloor>u\<rfloor> \<and> \<lfloor>u\<rfloor> \<le> plus_int \<lfloor>t\<rfloor> \<lfloor>d\<rfloor> \<or> \<lfloor>u\<rfloor> \<le> \<lfloor>t\<rfloor> \<and> \<lfloor>t\<rfloor> \<le> plus_int \<lfloor>u\<rfloor> \<lfloor>e\<rfloor>)" 
      unfolding de_Morgan_disj de_Morgan_conj not_le by linarith
  } note r = this

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    apply (subst res_iff) 
    using r
    by blast
qed 


lemma ref_plan_no_self_overlap: "ref_plan_no_self_overlap"
proof -
  have "wf_plan tp" using valid_plan unfolding valid_plan_def valid_plan_from_def by blast
  hence "list_all (snd #> wf_plan_action) tp" unfolding wf_plan_def list_all_iff by auto
  thus ?thesis
    using pddl_nso plan_acts_no_args plan_acts_durs_integer
    unfolding PDDL_plan_no_self_overlap_def ref_plan_no_self_overlap_def ref_plan_def
  proof (induction tp)
    case Nil
    then show ?case by simp
  next
    case (Cons pa pas)
    have 1: "list_pairwise ref_no_self_overlap (map timed_plan_action_to_ref_plan_action pas)" using Cons by simp

    have nso: "list_all (PDDL_no_self_overlap pa) pas" using Cons by simp
    have wf: "list_all (\<lambda>x. wf_plan_action (snd x)) (pa # pas)" using Cons by blast
    have no_args: "list_all (\<lambda>x. plan_act_no_args (snd x)) (pa # pas)" using Cons by blast
    have are_integer: "list_all timed_plan_action_durs_integer (pa # pas)" using Cons by blast

    have 2: "list_all (ref_no_self_overlap (timed_plan_action_to_ref_plan_action pa)) (map timed_plan_action_to_ref_plan_action pas)"
      using nso wf no_args are_integer PDDL_no_self_overlap_imp_ref_no_self_overlap unfolding list_all_iff by simp

    show ?case using 1 2 by simp
  qed
qed

lemma ref_plan_actions_in_actions:
  "set (map fst ref_plan) \<subseteq> set actions_spec"
proof -
  have "\<forall>a \<in> fst ` set ref_plan. a \<in> set actions_spec"
  proof (rule ballI)
    fix a 
    assume a: "a \<in> fst ` set ref_plan" 
    obtain t d where
      t: "(a, t, d) \<in> set ref_plan"  using a by auto
    then obtain t' a' where
      t': "(t', a') \<in> set tp"
          "(a, t, d) = timed_plan_action_to_ref_plan_action (t', a')" 
      using t unfolding ref_plan_def by auto
    have wf: "wf_plan_action a'" using t' valid_plan unfolding valid_plan_def valid_plan_from_def wf_plan_def list_all_iff by auto
    show "a \<in> set actions_spec" 
    proof (cases a')
      case (Simple_Plan_Action n as)
      thus "a \<in> set actions_spec" using t' wf unfolding actions_spec_def
        apply (cases "resolve_action_schema n")
         apply simp (* apply simp *)
        (* unfolding *) using resolve_action_schema_def
        by (auto dest: index_by_eq_SomeD)
    next
      case (Durative_Plan_Action n as d)
      thus ?thesis using t' wf unfolding actions_spec_def
        apply (cases "resolve_action_schema n")
        by (auto dest: index_by_eq_SomeD simp: resolve_action_schema_def)
    qed
  qed
  thus ?thesis by auto
qed


text \<open>Properties of the abstract plan used for the proof\<close>

lemma temp_plan_no_self_overlap:
  "imp_defs.rat_impl.no_self_overlap"
proof -
  define \<pi> where "\<pi> \<equiv> (map_option (map_prod id (map_prod rat_of_int rat_of_int))) o plan_imp"
  have "list_pairwise ref_no_self_overlap ref_plan" 
    using ref_plan_no_self_overlap unfolding ref_plan_no_self_overlap_def by simp
  hence "(\<forall>i j. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j 
    \<longrightarrow> ref_no_self_overlap (ref_plan ! i) (ref_plan ! j))" 
    using list_pairwise_nth_refl ref_no_self_overlap_refl by blast
  hence "(\<forall>i j. i \<in> dom plan_imp \<longrightarrow> j \<in> dom plan_imp \<longrightarrow> i \<noteq> j 
    \<longrightarrow> ref_no_self_overlap (ref_plan ! i) (ref_plan ! j))" 
    unfolding plan_imp_def dom_nth_opt by blast
  hence "(\<forall>i j a t d b u e. i \<in> dom plan_imp \<longrightarrow> j \<in> dom plan_imp \<longrightarrow> i \<noteq> j 
    \<longrightarrow> Some (a, t, d) = plan_imp i \<longrightarrow> Some (b, u, e) = plan_imp j
    \<longrightarrow> ref_no_self_overlap (a, t, d) (b, u, e))" unfolding plan_imp_def 
    apply (intro strip)
    apply (drule nth_opt_Some)+
    by simp
  hence "\<forall>i j a t d u e.  i \<noteq> j \<and> i \<in> dom \<pi> \<and> j \<in> dom \<pi> 
    \<and> Some (a, t, d) = \<pi> i \<and> Some (a, u, e) = \<pi> j 
    \<longrightarrow> \<not>(t \<le> u \<and> u \<le> t + d)"
    unfolding \<pi>_def by fastforce
  thus ?thesis 
    unfolding imp_defs.rat_impl.no_self_overlap_def \<pi>_def by blast
qed

lemma temp_plan_actions_in_actions:
  "imp_defs.rat_impl.plan_actions_in_problem"
proof -
  have "ran (nth_opt ref_plan) = set ref_plan" using ran_nth_opt by fast
  hence 1: "ran ((map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ>\<circ> nth_opt) ref_plan) = 
      (map_prod id (map_prod rat_of_int rat_of_int)) ` set ref_plan" 
    unfolding comp_def ran_map_option  by simp
  show ?thesis
  unfolding imp_defs.rat_impl.plan_actions_in_problem_def
  unfolding imp_defs.rat_impl.plan_actions_def
  unfolding plan_imp_def 
  apply (rule subsetI)
  apply (elim CollectE exE conjE)
  apply simp
  apply (subst (asm) 1)
  using ref_plan_actions_in_actions by force
qed

find_theorems happ_enabled name: local
find_theorems happ_non_intrf name: local
find_theorems acts_non_intrf name: local

lemma temp_plan_valid:
  "imp_defs.rat_impl.valid_plan"
proof -
  have "\<exists>M. imp_defs.rat_impl.valid_state_sequence M \<and> M 0 = set init_spec \<and> set goal_spec \<subseteq> M (length imp_defs.rat_impl.htpl)" sorry
  have "imp_defs.rat_impl.durations_ge_0"
  proof -
    have "\<forall>a t d. (a, t, d) \<in> ran abstr_plan \<longrightarrow> 0 \<le> d"
    proof (intro strip, elim ran_abstr_plan_ref_planE in_set_ref_planE)
      fix t n as 
      show "(t, Simple_Plan_Action n as) \<in> set tp \<Longrightarrow> 0 \<le> rat_of_int 0" by simp
    next
      fix t n as d
      assume "(t, Durative_Plan_Action n as d) \<in> set tp"
      hence "wf_plan_action (Durative_Plan_Action n as d)" using wf_plan_actions by fast
      thus "0 \<le> rat_of_int \<lfloor>d\<rfloor>" by (auto split: option.splits ast_action_schema.splits)
    qed
    thus ?thesis unfolding imp_defs.rat_impl.durations_ge_0_def abstr_plan_def by simp
  qed
  have "imp_defs.rat_impl.durations_valid"
  proof -
    have "\<forall>a t d. (a, t, d) \<in> ran abstr_plan \<longrightarrow> imp_defs.rat_impl.satisfies_duration_bounds a d"
    proof (intro strip, elim ran_abstr_plan_ref_planE in_set_ref_planE)
      fix t n as
      assume "(t, Simple_Plan_Action n as) \<in> set tp"
      hence "wf_plan_action (Simple_Plan_Action n as)" using wf_plan_actions by fast
      then obtain ps pre eff where
        res: "resolve_action_schema n = Some (Simple_Action_Schema n ps pre eff)"
        using simple_plan_action_schema_type1 by blast
      show "imp_defs.rat_impl.satisfies_duration_bounds (the (resolve_action_schema n)) (rat_of_int 0)"
        unfolding imp_defs.rat_impl.satisfies_duration_bounds_def Let_def res option.sel 
        unfolding comp_def lower_spec.simps upper_spec.simps
        unfolding option.map
        by simp
    next 
      fix t n as d
      assume a: "(t, Durative_Plan_Action n as d) \<in> set tp"
      hence wfp: "wf_plan_action (Durative_Plan_Action n as d)" using wf_plan_actions by fast
      then obtain ps pre eff dcs where
        res: "resolve_action_schema n = Some (Durative_Action_Schema n ps dcs pre eff)" and 
        wfs: "wf_action_schema (Durative_Action_Schema n ps dcs pre eff)"
        using durative_plan_action_schema_type1 resolve_action_wf by blast+
      have dms: "durations_match d dcs ps as" using wfp unfolding wf_plan_action.simps res by simp
      have no_func_dcs: "list_all (\<lambda>d. \<not> is_Func_Const d) dcs" 
        using acts_no_func_dcs resolve_action_in_actions[OF res]
        unfolding actions_spec_def list_all_iff
        apply -
        apply (drule bspec, assumption)
        unfolding list_all_iff[symmetric] by simp
      have sat: "imp_defs.rat_impl.satisfies_lower_bound (dc_list_lower dcs) d"
           "imp_defs.rat_impl.satisfies_upper_bound (dc_list_upper dcs) d"
        using durations_match_imp_sat_lb durations_match_imp_sat_ub dms no_func_dcs by simp+

      have d_integer: "is_integer d" using plan_acts_durs_integer a unfolding list_all_iff by auto

      have dcs_integer: "list_all duration_constraint_integer dcs"
        using resolve_action_in_actions[OF res] acts_dcs_integers 
        unfolding actions_spec_def 
        by (auto simp: list_all_iff)

      have lbs_integer: "pred_option (pred_lower_bound is_integer) (dc_list_lower dcs)" 
        apply (rule dc_list_lower_propI)
        using dcs_integer no_func_dcs
         apply (induction dcs)
        using dc_integer_imp_lb_integer by auto
  
      have ubs_integer: "pred_option (pred_upper_bound is_integer) (dc_list_upper dcs)" 
        apply (rule dc_list_upper_propI)
        using dcs_integer no_func_dcs
         apply (induction dcs)
        using dc_integer_imp_ub_integer by auto

      show "imp_defs.rat_impl.satisfies_duration_bounds (the (resolve_action_schema n)) (rat_of_int \<lfloor>d\<rfloor>)" 
        unfolding imp_defs.rat_impl.satisfies_duration_bounds_def Let_def res option.sel 
        unfolding comp_def lower_spec.simps upper_spec.simps
        unfolding option.map_comp comp_def lower_bound.map_comp upper_bound.map_comp
        using sat integers_sat_bounds lbs_integer ubs_integer d_integer by simp
    qed
    thus ?thesis unfolding imp_defs.rat_impl.durations_valid_def abstr_plan_def by simp
  qed
  have "imp_defs.rat_impl.mutex_valid_plan"
  proof -
    show ?thesis 
      unfolding imp_defs.rat_impl.mutex_valid_plan_eq
      imp_defs.rat_impl.mutex_valid_plan_alt_def
      unfolding abstr_plan_def[symmetric]
    proof (intro conjI)
      show "\<forall>i j a ta da b tb db. i \<in> dom abstr_plan \<and> j \<in> dom abstr_plan \<and> i \<noteq> j 
          \<and> abstr_plan i = Some (a, ta, da) \<and> abstr_plan j = Some (b, tb, db) 
        \<longrightarrow> imp_defs.rat_impl.mutex_sched a ta da b tb db" 
        unfolding imp_defs.rat_impl.mutex_sched_def 
        apply (intro strip | elim conjE disjE)+
               apply (linarith)
        sorry
      show "\<forall>(a, t, d)\<in>ran abstr_plan. d = 0 \<or> d < rat_of_int 0 
        \<longrightarrow> \<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a) (at_end_spec a)"
      proof -
        { fix a' t' d'
          assume "(a', t', d') \<in> ran abstr_plan"
          hence "(d' = 0 \<or> d' < rat_of_int 0) \<longrightarrow> \<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a') (at_end_spec a')"
          proof (elim ran_abstr_plan_ref_planE; intro strip)
            fix a t d
            assume a: "(a, t, d) \<in> set ref_plan"
              and d: "rat_of_int d = 0 \<or> rat_of_int d < rat_of_int 0" 
            have d[simp]: "d = 0" using a d ref_plan_durs by fastforce
            show "\<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a) (at_end_spec a)"
            proof (cases a)
              case (Simple_Action_Schema n ps pre eff)
              thus ?thesis unfolding imp_defs.rat_impl.set_impl.mutex_snap_action_def 
                  using non_ground_action_def by simp
            next
              case x: (Durative_Action_Schema n ps dcs pre eff)
              have
                "at_start_spec a \<in> acts_of_plan_at (rat_of_int t) tp"
                "at_end_spec a \<in> acts_of_plan_at (rat_of_int t) tp"
                using a d x at_start_snap_at_t at_end_snap_at_t_if_durative by fastforce+
              hence "acts_non_intrf (at_start_spec a) (at_end_spec a)"
                using all_htps_acts_non_intrf
                using ref_plan_start_in_htps[OF a]
                using start_spec_end_spec_neq by auto
              thus ?thesis 
                unfolding imp_defs.rat_impl.set_impl.mutex_snap_action_def 
                acts_non_intrf_def Let_def 
            qed
          qed
        } thus ?thesis by blast
      qed
    qed
  qed
  have "imp_defs.rat_impl.finite_plan" 
    unfolding imp_defs.rat_impl.finite_plan_def
    unfolding dom_map_option comp_def
    using dom_plan_imp by simp
qed

sublocale red_corr: tp_nta_reduction_correctness' init_spec goal_spec 
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  0 
  props_spec actions_spec plan_imp  
  act_to_name_spec prop_to_name_spec
  apply unfold_locales
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry

end

end
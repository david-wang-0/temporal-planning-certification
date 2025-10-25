theory Ground_PDDL_Plan_Defs
  imports Ground_PDDL_Problem_Defs
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics_Alt"
begin
                         
instantiation real::infinity
begin
instance ..
end
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

lemma in_set_ref_planI:
  "(t, Simple_Plan_Action n as) \<in> set tp \<Longrightarrow> (the (resolve_action_schema n), floor t, 0) \<in> set ref_plan"
  "(t, Durative_Plan_Action n as d) \<in> set tp \<Longrightarrow> (the (resolve_action_schema n), floor t, floor d) \<in> set ref_plan"
  unfolding ref_plan_def by force+

lemma ref_plan_pairwise_if:
  assumes "list_pairwise (\<lambda>a b. Q (timed_plan_action_to_ref_plan_action a) (timed_plan_action_to_ref_plan_action b)) tp"
  shows "list_pairwise Q ref_plan"
  using assms unfolding ref_plan_def 
  using list_pairwise_map by blast
                            
text \<open>Properties specific to later proofs\<close>
fun plan_act_no_params where
"plan_act_no_params (Simple_Plan_Action n []) = True" |
"plan_act_no_params (Durative_Plan_Action n [] d) = True" |
"plan_act_no_params _ = False"

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

(* leaky abstraction? 
To do (low prio): move into other locale that converts a plan from a list into a function. *)
sublocale temp_plan_finite at_start_spec at_end_spec "set o over_all_spec"
  "(map_option (map_lower_bound rat_of_int)) o lower_spec" 
  "(map_option (map_upper_bound rat_of_int)) o upper_spec" 
  "set o pre_spec" "set o adds_spec" "set o dels_spec"
  "set init_spec" "set goal_spec" "rat_of_int 0" 
  "map_option (map_prod id (map_prod rat_of_int rat_of_int)) o plan_imp"
  apply unfold_locales 
  unfolding imp_defs.rat_impl.finite_plan_def
  unfolding comp_def
  unfolding dom_map_option
  unfolding plan_imp_def
  unfolding dom_nth_opt
  by blast
  

definition "abstr_plan \<equiv> (map_option (map_prod id (map_prod rat_of_int rat_of_int))) o plan_imp"

lemma ran_abstr_plan_ref_planE:
  assumes "(a, t, d) \<in> ran abstr_plan"
      and "\<And>a t d. (a, t, d) \<in> set ref_plan \<Longrightarrow> Q a (rat_of_int t) (rat_of_int d)"
    shows "Q a t d"
  using assms unfolding abstr_plan_def plan_imp_def ran_map_option comp_def ran_nth_opt 
  by auto

lemma ran_abstr_planI:
  "(a, t, d) \<in> set ref_plan \<Longrightarrow> (a, rat_of_int t, rat_of_int d) \<in> ran abstr_plan"
  unfolding abstr_plan_def plan_imp_def ran_map_option comp_def ran_nth_opt by force

lemma abstr_plan_binary_prop':
  assumes secondary:
    "i \<in> dom abstr_plan" 
    "j \<in> dom abstr_plan" 
    "i \<noteq> j"
    "abstr_plan i = Some (a, ta, da)"
    "abstr_plan j = Some (b, tb, db)"
  and refl:
    "\<forall>a ta da b tb db. Q a ta da b tb db = Q b tb db a ta da"
  and primary: "(\<forall>i j a ta da b tb db. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j 
      \<longrightarrow> (ref_plan ! i) = (a, ta, da) \<longrightarrow> (ref_plan ! j) = (b, tb, db)
      \<longrightarrow> Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db))"
shows "Q a ta da b tb db"
proof -
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
      unfolding map_prod_simp using primary by auto
    done
qed

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
  show ?thesis using assms abstr_plan_binary_prop' 1 by blast
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
      and wf: "wf_ground_action a" "wf_ground_action b"
      and no_args: "ground_act_no_args a" "ground_act_no_args b"
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
  note pad_alt = calculation[symmetric]
  
  ultimately have True by simp (* clearing calculation *)

  have x: "(\<not> x \<noteq> y) = (x = y)" for x y by simp (* SMT.smt_arith_simplify(277) *)
                           
  have inj_to_predicate: "inj_on to_predicate {x. is_predAtom x \<and> form_preds_no_args x}" (is "inj_on to_predicate ?S")
    apply (rule inj_onI)
    apply (elim CollectE conjE is_predAtom.elims)
    unfolding form_preds_no_args_def 
    apply (drule bspec, simp)+
    apply (erule atom_no_args.elims)+
    by auto
    
  have "Atom ` atoms (ground_action.precondition a) \<subseteq> ?S" 
    using is_pos_conj_atoms_preds pres_pos no_args
    apply (induction a)
    using form_preds_no_args_imp_atoms_no_args by auto
  moreover
  have "set (adds (ground_action.effect a)) \<subseteq> ?S" 
    using no_args wf apply (induction a)
    unfolding ground_action.sel
    subgoal for n anno pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  have "set (dels (ground_action.effect a)) \<subseteq> ?S" 
    using no_args wf apply (induction a)
    unfolding ground_action.sel
    subgoal for n anno pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  have "Atom ` atoms (ground_action.precondition b) \<subseteq> ?S" 
    using is_pos_conj_atoms_preds pres_pos no_args
    apply (induction b)
    using form_preds_no_args_imp_atoms_no_args by auto
  moreover
  have "set (adds (ground_action.effect b)) \<subseteq> ?S" 
    using no_args wf apply (induction b)
    unfolding ground_action.sel
    subgoal for n anno pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  have "set (dels (ground_action.effect b)) \<subseteq> ?S" 
    using no_args wf apply (induction b)
    unfolding ground_action.sel
    subgoal for n anno pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  note in_set = calculation
  ultimately have True by simp (* clearing calculation *)

  

  show ?thesis
    unfolding imp_defs.rat_impl.set_impl.mutex_snap_action_def
    unfolding comp_def pad_alt
    unfolding de_Morgan_disj x 
    unfolding image_Un[symmetric]
    apply (intro conjI)
    using non_int 
    unfolding acts_non_intrf_def Let_def
    using inj_on_image_Int[symmetric, OF inj_to_predicate] in_set 
    by simp+
qed

lemma ground_non_action_not_mutex:
  shows "\<not>imp_defs.rat_impl.set_impl.mutex_snap_action (ground_non_action a anno) b"
        "\<not>imp_defs.rat_impl.set_impl.mutex_snap_action b (ground_non_action a anno)"
  unfolding ground_non_action_def imp_defs.rat_impl.set_impl.mutex_snap_action_def by simp+

lemma ground_non_action_non_intrf:
  shows "acts_non_intrf (ground_non_action a anno) b"
        "acts_non_intrf b (ground_non_action a anno)"
  unfolding ground_non_action_def acts_non_intrf_def by simp+


lemma ground_non_action_no_effs:
  assumes "T \<subseteq> {ground_non_action n anno|n anno. True}"
  shows "imp_defs.rat_impl.apply_effects (S \<union> T) q = imp_defs.rat_impl.apply_effects S q"
proof -
  have "(\<Union>x\<in>T. set (dels_spec x)) = {}"
    using assms ground_non_action_dels by fastforce
  moreover
  have "(\<Union>x\<in>T. set (adds_spec x)) = {}"  
    using assms ground_non_action_adds by fastforce
  ultimately
  show ?thesis unfolding imp_defs.rat_impl.apply_effects_def
    unfolding comp_def unfolding UN_Un by blast
qed

lemma ground_non_action_no_pres:
  assumes "T \<subseteq> {ground_non_action n anno|n anno. True}"
  shows "\<Union> ((set \<circ> pre_spec) ` (S \<union> T)) = \<Union> ((set \<circ> pre_spec) ` S)"
proof -
  have "(\<Union>x\<in>T. set (pre_spec x)) = {}"
    using assms ground_non_action_pre by fastforce
  thus ?thesis 
    unfolding comp_def unfolding UN_Un 
    by blast
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

lemma all_htps_acts_non_intrf':
  assumes "t\<^sub>i \<in> set htps" "a \<in> acts_of_plan_at t\<^sub>i tp" "b \<in> acts_of_plan_at t\<^sub>i tp" "a \<noteq> b"
  shows "acts_non_intrf a b"
  using all_htps_acts_non_intrf assms by simp

(* Needs an assumption that durations are integers. *)

lemma wf_plan_actions:
  assumes "(t, a) \<in> set tp"
  shows "wf_plan_action a" 
  using assms valid_plan unfolding valid_plan_def valid_plan_from_def wf_plan_def by blast

lemma simple_acts_in_plan:  
  assumes "(t, a) \<in> simple_acts tp"
  shows "(t, a) \<in> set tp" using assms unfolding simple_acts_def by simp

lemma durative_acts_in_plan:
  assumes "(t, a) \<in> durative_acts tp"
  shows "(t, a) \<in> set tp" using assms unfolding durative_acts_def by simp

lemma durative_plan_action_durs:
  assumes "wf_plan_action (Durative_Plan_Action n as d)"
  shows "0 \<le> d"
  using durative_plan_action_schema_type1 assms by force

lemma simple_act_ex_simple_plan_act:
  assumes "(t, a) \<in> simple_acts tp"
  shows "\<exists>n as. a = Simple_Plan_Action n as"
  using assms unfolding simple_acts_def is_act_simple_alt apply (cases a) by auto

lemma res_simple_act_name:
  assumes "(t, a) \<in> simple_acts tp"
  shows "\<exists>n ps pre eff. resolve_action_schema (plan_action.name a) = Some (Simple_Action_Schema n ps pre eff)"
  using assms[THEN simple_act_ex_simple_plan_act]
  using assms[THEN simple_acts_in_plan] 
  using wf_plan_actions
  using simple_plan_action_schema_type1 
  by fastforce 

lemma durative_act_ex_durative_plan_act:
  assumes "(t, a) \<in> durative_acts tp"
  shows "\<exists>n as d. a = Durative_Plan_Action n as d"
  using assms unfolding durative_acts_def is_act_simple_alt 
  apply (cases a) by auto

lemma res_durative_act_name:
  assumes "(t, a) \<in> durative_acts tp"
  shows "\<exists>n ps dcs pre eff. resolve_action_schema (plan_action.name a) = Some (Durative_Action_Schema n ps dcs pre eff)"
  using assms[THEN durative_act_ex_durative_plan_act]
  using assms[THEN durative_acts_in_plan] 
  using wf_plan_actions
  using durative_plan_action_schema_type1 
  by fastforce 

lemma plan_acts_no_args: "list_all (snd #> plan_act_no_params) tp"
proof -
  { fix t a 
    assume "(t, a) \<in> set tp"
    hence wf: "wf_plan_action a" using wf_plan_actions by auto
    have "plan_act_no_params a"
    proof (cases a)
      case a: (Simple_Plan_Action n ps)
      hence wf: "wf_plan_action (Simple_Plan_Action n ps)" using wf by auto
      then obtain pre eff as  where
        res: "resolve_action_schema n = Some (Simple_Action_Schema n as pre eff)"
        using simple_plan_action_schema_type1 by blast
      have pm: "action_params_match (Simple_Action_Schema n as pre eff) ps" using wf res by auto
      have "as = []" using resolve_action_schema_def index_by_eq_SomeD acts_no_params res
        unfolding list_all_iff by fastforce
      then show ?thesis using pm a action_params_match_def by simp
    next
      case a: (Durative_Plan_Action n ps d)
      hence wf: "wf_plan_action (Durative_Plan_Action n ps d)" using wf by auto
      then obtain pre eff as dcs where
        res: "resolve_action_schema n = Some (Durative_Action_Schema n as pre eff dcs)"
        using durative_plan_action_schema_type1 by blast
      have pm: "action_params_match (Durative_Action_Schema n as pre eff dcs) ps" using wf res by auto
      have "as = []" using resolve_action_schema_def index_by_eq_SomeD acts_no_params res
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


(* To do: remove the name *)

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
Ending snaps for durative (but not simple) actions need a similar one.
Simple actions' ends need to be considered separately *)

lemma simple_act_in_ref_plan_durs:
  assumes "(Simple_Action_Schema n as pre eff, t, d) \<in> set ref_plan"
  shows "d = 0"using assms unfolding ref_plan_def set_map
    apply -
    apply (erule imageE)
    subgoal for x
      apply (cases x)
      subgoal for a b apply (cases b)
         apply simp
        using durative_plan_action_schema_type1[OF wf_plan_actions]
        by fastforce
      done
    done

find_theorems "inst_of_plan_action"

text \<open>We obtain a placeholder for the valid state_sequence\<close>
term inst_of_plan_action

(* We must know that these are *)

lemma PDDL_no_self_overlap_imp_ref_no_self_overlap:
  assumes "PDDL_no_self_overlap a b"
      and "wf_plan_action (snd a)"
      and "wf_plan_action (snd b)"
      and "plan_act_no_params (snd a)"
      and "plan_act_no_params (snd b)"
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
    have no_args: "list_all (\<lambda>x. plan_act_no_params (snd x)) (pa # pas)" using Cons by blast
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


definition "is_state_at \<pi> ts initial final t M \<equiv> 
  valid_state_seq initial (takeWhile (\<lambda>x. x < t) ts) \<pi> M 
  \<and> valid_state_seq M (dropWhile (\<lambda>x. x < t) ts) \<pi> final"

definition "state_at \<pi> ts initial final t \<equiv> SOME M. is_state_at \<pi> ts initial final t M"

definition "time_after_all ts \<equiv> SOME t. \<forall>t' \<in> set ts. t' < t"

definition "add_final_time_point ts \<equiv> ts @ [time_after_all ts]" 

definition "abstr_state_list \<equiv> (map (state_at tp htps I final_state) (add_final_time_point htps))"

definition "plan_state_list \<equiv> abstr_state_list 
  |> map (\<lambda>atomic_formulas. \<Union>((to_literals #> map to_predicate #> set) ` atomic_formulas))"


lemma length_add_final_time_point:
  "length (add_final_time_point ts) = Suc (length ts)"
  unfolding add_final_time_point_def by auto

lemma length_abstr_state_list:
  "length abstr_state_list = Suc (length htps)"
  unfolding abstr_state_list_def length_map
  using length_add_final_time_point by blast

lemma length_plan_state_list:
  "length plan_state_list = Suc (length htps)"
  unfolding plan_state_list_def 
  using length_abstr_state_list by simp

lemma plan_state_list_nth_conv_abstr_state_list_nth:
  assumes "n < length plan_state_list"
  shows "plan_state_list ! n = (\<Union>x\<in>abstr_state_list ! n. to_predicate ` set (to_literals x))"
  using assms unfolding plan_state_list_def
  by auto

lemma time_after_all_is_after_all:
  "\<forall>t \<in> set ts. t < time_after_all (ts::rat list)"
  unfolding time_after_all_def
  apply (rule someI_ex)
  apply (induction ts)
   apply simp
  subgoal for t ts
    apply (erule exE)
    subgoal for x
      apply (cases "x < t")
       apply (intro exI[of _ "t+1"] ballI)
       apply auto[1]
      apply (intro exI[of _ "x + 1"])
      by auto
    done
  done
      


lemma nth_add_final_time_point_length:
  "add_final_time_point ts ! (length ts) = (time_after_all ts)"
  unfolding add_final_time_point_def by simp

lemma nth_add_final_time_point:
  assumes "n < length ts"
  shows "add_final_time_point ts ! n = ts ! n"
  using assms
  unfolding add_final_time_point_def by auto


lemma strict_sorted_add_final_time_point:
  assumes "strict_sorted (ts::rat list)"
  shows "strict_sorted (add_final_time_point ts)"
  unfolding add_final_time_point_def
  apply (rule sorted_wrt_append)
  using assms time_after_all_is_after_all[of ts] by auto

lemma abstr_state_list_nth_length:
  "abstr_state_list ! length htps = (state_at tp htps I final_state (time_after_all htps))" 
  unfolding abstr_state_list_def apply (subst nth_map, subst length_add_final_time_point, blast)
  apply (subst nth_add_final_time_point_length)
  by simp

lemma state_at_is_state_at:
  assumes "valid_state_seq M ts \<pi> M'"
      and "strict_sorted ts"
  shows "is_state_at \<pi> ts M M' t (state_at \<pi> ts M M' t)"
proof -
  show ?thesis
    unfolding state_at_def
    apply (rule someI_ex)
    unfolding is_state_at_def 
    apply (subst valid_state_seq_app_iff[symmetric])
    using assms by auto
qed

lemma is_state_at_unique:
  fixes X Y
  assumes "is_state_at \<pi> ts M M' t X"
     and "is_state_at \<pi> ts M M' t Y"
  shows "X = Y" 
  using assms valid_state_seq_state_unique is_state_at_def by blast


lemma abstr_state_list_nth_valid:
  assumes "n \<le> length htps"
  shows "is_state_at tp htps I final_state ((add_final_time_point htps) ! n) (abstr_state_list ! n)"
  unfolding abstr_state_list_def
   apply (subst nth_map)
    apply (subst length_add_final_time_point)
  using assms apply simp
   apply (rule state_at_is_state_at)
  using valid_state_seq_final_state 
  using htps_seq_htps unfolding htps_seq_def 
  by blast+

lemma abstr_state_list_nth_Suc:
  assumes "n < length htps"
  shows "(abstr_state_list ! (Suc n)) = apply_eff (acts_of_plan_at (htps ! n) tp) (abstr_state_list ! n)"
proof -
  have 1: "sorted_wrt (<) htps" using htps_seq_htps unfolding htps_seq_def by blast

  have take_Sn: "take (Suc n) htps = take n htps @ [htps ! n]" using take_Suc_conv_app_nth assms by auto
  
  
  have sn: "is_state_at tp htps I final_state ((add_final_time_point htps) ! (Suc n)) (abstr_state_list ! (Suc n))" 
    using assms 1 abstr_state_list_nth_valid by auto
  hence 2: "valid_state_seq I (takeWhile (\<lambda>x. x < add_final_time_point htps ! Suc n) htps) tp (abstr_state_list ! Suc n)" 
    unfolding is_state_at_def by simp
  have "valid_state_seq I (take (Suc n) htps) tp (abstr_state_list ! Suc n)" 
  proof (cases "Suc n < length htps")
    case True
    show ?thesis 
      apply (insert 2 True)
      apply (subst (asm) nth_add_final_time_point, simp)
     apply (subst (asm) strict_sorted_takeWhile_nth)
    using 1 by simp+
  next
    case False
    hence n': "Suc n = length htps" using assms by simp
    show ?thesis
      apply (insert 2)
      unfolding n' 
      apply (subst (asm) nth_add_final_time_point_length)
      apply (subst (asm) takeWhile_all)
      using time_after_all_is_after_all
      by auto
  qed 
  hence "\<exists>Mj. valid_state_seq I (take n htps) tp Mj \<and> valid_state_seq Mj [htps ! n] tp (abstr_state_list ! Suc n)" 
    unfolding take_Sn valid_state_seq_app_iff by auto
  then obtain Mj where
    Ij: "valid_state_seq I (take n htps) tp Mj" 
    and jSn: "valid_state_seq Mj [htps ! n] tp (abstr_state_list ! Suc n)" by auto

  have Mj_eff_Sn: "apply_eff (acts_of_plan_at (htps ! n) tp) Mj = abstr_state_list ! Suc n" 
    using jSn unfolding valid_state_seq.simps Let_def by auto

  have n: "is_state_at tp htps I final_state ((add_final_time_point htps) ! n) (abstr_state_list ! n)" 
    using assms 1 abstr_state_list_nth_valid by auto
  hence "valid_state_seq I (takeWhile (\<lambda>x. x < add_final_time_point htps ! n) htps) tp (abstr_state_list ! n)" 
    unfolding is_state_at_def by blast
  hence In: "valid_state_seq I (take n htps) tp (abstr_state_list ! n)"
    apply (subst (asm) nth_add_final_time_point)
    using assms apply simp
    using strict_sorted_takeWhile_nth[OF assms 1] by simp 

  have eq: "Mj = (abstr_state_list ! n)" using Ij In valid_state_seq_state_unique by blast

  show ?thesis using Mj_eff_Sn eq by blast
qed

text \<open>\<close>

find_theorems name: "ran*map_op"

lemma ref_htpl_eq_htps: "imp_defs.rat_impl.htpl = htps"
proof (rule strict_sorted_equal)
  have "htps_seq tp htps" using htps_seq_htps by blast
  hence htps_prop: "(\<forall>t. (t \<in> set htps) = ((\<exists>\<pi>. (t, \<pi>) \<in> set tp) \<or> (\<exists>(t\<^sub>\<pi>, \<pi>)\<in>durative_acts tp. t = t\<^sub>\<pi> + duration \<pi>)))"
    unfolding htps_seq_def is_htp_def by argo

  show "strict_sorted htps"
    using htps_seq_htps htps_seq_def by blast
  show "strict_sorted imp_defs.rat_impl.htpl" 
    using imp_defs.rat_impl.sorted_htpl by simp
  show "set imp_defs.rat_impl.htpl = set htps"
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> set imp_defs.rat_impl.htpl"
    hence "x \<in> imp_defs.rat_impl.htps" using htps_set_htpl by simp
    thus "x \<in> set htps" 
      apply (elim imp_defs.rat_impl.htpsE ssubst)
      unfolding abstr_plan_def[symmetric]
    proof goal_cases
      fix a t d
      assume "(a, t, d) \<in> ran abstr_plan"
      thus "t + d \<in> set htps" 
      proof (elim ran_abstr_plan_ref_planE)
        fix a t d
        assume "(a, t, d) \<in> set ref_plan" 
        thus "rat_of_int t + rat_of_int d \<in> set htps"
        proof (elim in_set_ref_planE)
          fix t n as
          assume a: "(t, Simple_Plan_Action n as) \<in> set tp" 
          have "is_integer t" using plan_acts_durs_integer a unfolding list_all_iff by fastforce
          moreover
          have "t \<in> set htps" using a htps_prop by blast
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> + rat_of_int 0 \<in> set htps" 
            using is_integer_of_int by fastforce
        next
          fix t n as d
          assume a: "(t, Durative_Plan_Action n as d) \<in> set tp"
          have "is_integer t" "is_integer d" using plan_acts_durs_integer a 
            unfolding list_all_iff by fastforce+
          moreover
          {
            have "(t, Durative_Plan_Action n as d) \<in> (durative_acts tp)" using a 
              unfolding durative_acts_def comp_def set_filter is_act_simple_alt by auto
            hence "t + d \<in> set htps" using htps_prop by fastforce
          }
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> + rat_of_int \<lfloor>d\<rfloor> \<in> set htps" 
            by(fastforce simp: is_integer_of_int)
        qed
      qed
    next
      fix a t d
      assume "(a, t, d) \<in> ran abstr_plan"
      thus "t \<in> set htps"
      proof (elim ran_abstr_plan_ref_planE)
        fix a t d
        assume "(a, t, d) \<in> set ref_plan" 
        thus "rat_of_int t \<in> set htps"
        proof (elim in_set_ref_planE)
          fix t n as
          assume a: "(t, Simple_Plan_Action n as) \<in> set tp" 
          have "is_integer t" using plan_acts_durs_integer a unfolding list_all_iff by fastforce
          moreover
          have "t \<in> set htps" using a htps_prop by blast
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> \<in> set htps" 
            using is_integer_of_int by fastforce
        next
          fix t n as d
          assume a: "(t, Durative_Plan_Action n as d) \<in> set tp"
          have "is_integer t"  using plan_acts_durs_integer a 
            unfolding list_all_iff by fastforce+
          moreover
          have "t \<in> set htps" using htps_prop a by fastforce
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> \<in> set htps" 
            by (fastforce simp: is_integer_of_int)
        qed
      qed
    qed
  next
    fix x
    assume "x \<in> set htps" 
    hence "((\<exists>\<pi>. (x, \<pi>) \<in> set tp) \<or> (\<exists>(t\<^sub>\<pi>, \<pi>)\<in>durative_acts tp. x = t\<^sub>\<pi> + duration \<pi>))"
      using htps_prop by blast
    then consider 
          a where "(x, a) \<in> set tp" 
      | t a where "(t, a) \<in> durative_acts tp" "x = t + duration a"
      by blast
    then consider
        n as  where "(x, (Simple_Plan_Action n as)) \<in> set tp" 
      | n as d where "(x, (Durative_Plan_Action n as d)) \<in> set tp" 
      | t n as d where "(t, (Durative_Plan_Action n as d)) \<in> set tp" 
        "x = t + d"
      apply cases
      subgoal for a apply (cases a)
        by auto
      subgoal for t a
        apply (cases a)
        unfolding durative_acts_def is_act_simple_alt 
        by auto
      done
    hence "x \<in> imp_defs.rat_impl.htps"
    proof (cases)
      case 1
      have 2: "(the (resolve_action_schema n), \<lfloor>x\<rfloor>, 0) \<in> set ref_plan" 
        using in_set_ref_planI 1 by simp
      {
        have "(the (resolve_action_schema n), rat_of_int \<lfloor>x\<rfloor>, rat_of_int 0) \<in> ran abstr_plan" 
          using ran_abstr_planI 2 by blast
        moreover
        have "is_integer x" using plan_acts_durs_integer 1
            unfolding list_all_iff by fastforce+
        ultimately
        have "(the (resolve_action_schema n), x, rat_of_int 0) \<in> ran abstr_plan" 
          using is_integer_of_int by fastforce
      }
      then show ?thesis using imp_defs.rat_impl.htpsI 
        unfolding abstr_plan_def by auto
    next
      case 2
      have 3: "(the (resolve_action_schema n), \<lfloor>x\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
        using in_set_ref_planI 2 by blast
      {
        have "(the (resolve_action_schema n), rat_of_int \<lfloor>x\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
          using ran_abstr_planI 3 by blast
        moreover
        have "is_integer x" "is_integer d" using plan_acts_durs_integer 2
            unfolding list_all_iff by fastforce+
        ultimately
        have "(the (resolve_action_schema n), x, d) \<in> ran abstr_plan" 
          using is_integer_of_int by fastforce
      }
      then show ?thesis using imp_defs.rat_impl.htpsI 
        unfolding abstr_plan_def by auto
    next
      case 3
      have 4: "(the (resolve_action_schema n), \<lfloor>t\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
        using in_set_ref_planI 3 by blast
      {
        have "(the (resolve_action_schema n), rat_of_int \<lfloor>t\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
          using ran_abstr_planI 4 by blast
        moreover
        have "is_integer t" "is_integer d" using plan_acts_durs_integer 3
            unfolding list_all_iff by fastforce+
        ultimately
        have "(the (resolve_action_schema n), t, d) \<in> ran abstr_plan" 
          using is_integer_of_int by fastforce
      }
      then show ?thesis using imp_defs.rat_impl.htpsI 
        unfolding abstr_plan_def 3 by auto
    qed
    thus "x \<in> set imp_defs.rat_impl.htpl" using htps_set_htpl by simp
  qed
qed


(* What needs to be added to the actions of the plan at a time_point to include all snap actions? *)
(* Every instantaneous action (simple action) needs an empty snap action paired with its start *)

definition "missing_ends t \<pi> \<equiv> {s. \<exists>a. (t,a) \<in> simple_acts \<pi> \<and> Some s = map_option at_end_spec (resolve_action_schema (name a))}"  

lemma plan_happ_seq_alt': "\<forall>s. s \<in> (imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq t)  \<longleftrightarrow> 
  ((s \<in> acts_of_plan_at t tp) 
    \<or> s \<in> missing_ends t tp)"
  unfolding missing_ends_def
proof (intro strip iffI CollectI; (elim disjE CollectE exE conjE)?)
  fix s
  assume a: "(t, s) \<in> imp_defs.rat_impl.plan_happ_seq" 
  show "s \<in> acts_of_plan_at t tp \<or> s \<in> {s. \<exists>a. (t, a) \<in> simple_acts tp \<and> Some s = map_option at_end_spec (resolve_action_schema (plan_action.name a))}"
  proof ((rule imp_defs.rat_impl.in_happ_seq_propE[OF a]; subst (asm) abstr_plan_def[symmetric]); elim ran_abstr_plan_ref_planE)
    show "\<And>a t d aa ta da. (aa, ta, da) \<in> set ref_plan 
      \<Longrightarrow> at_start_spec aa \<in> acts_of_plan_at (rat_of_int ta) tp \<or> 
          at_start_spec aa \<in> {s. \<exists>a. (rat_of_int ta, a) \<in> simple_acts tp 
            \<and> Some s = map_option at_end_spec (resolve_action_schema (plan_action.name a))}"
      using at_start_snap_at_t by simp
  next
    fix a t d
    assume a: "(a, t, d) \<in> set ref_plan"
    thus "at_end_spec a \<in> acts_of_plan_at (rat_of_int t + rat_of_int d) tp 
            \<or> at_end_spec a \<in> {s. \<exists>a. (rat_of_int t + rat_of_int d, a) \<in> simple_acts tp 
              \<and> Some s = map_option at_end_spec (resolve_action_schema (plan_action.name a))}"
    proof (cases a)
      case b: (Simple_Action_Schema n ps pre eff)
      have d: "d = 0" using a b simple_act_in_ref_plan_durs by auto
      obtain as where
        as: "(rat_of_int t, Simple_Plan_Action n as) \<in> set tp \<and> resolve_action_schema n = Some (Simple_Action_Schema n ps pre eff)" using simple_action_in_ref_plan a b by blast
      have "at_end_spec a \<in> {s. \<exists>a. (rat_of_int t + rat_of_int d, a) \<in> simple_acts tp \<and> Some s = map_option at_end_spec (resolve_action_schema (plan_action.name a))}"
      proof -
        have "(rat_of_int t + rat_of_int d, Simple_Plan_Action n as) \<in> simple_acts tp" using as d 
          unfolding simple_acts_def is_act_simple_alt by simp
        moreover
        have "Some (at_end_spec a) = map_option at_end_spec (resolve_action_schema n)" using as b by simp
        ultimately
        show ?thesis by auto
      qed
      then show ?thesis by auto
    next
      case (Durative_Action_Schema x21 x22 x23 x24 x25)
      then show ?thesis 
        using at_end_snap_at_t_if_durative a by simp
    qed
  qed
next
  fix s
  assume s: "s \<in> acts_of_plan_at t tp"
  consider pa where "(t, pa) \<in> simple_acts tp" "Some s = res_inst pa At_Start"
    | pa where "(t, pa) \<in> durative_acts tp" "Some s = res_inst_snap_action pa At_Start"
    | t' pa where "(t', pa) \<in> durative_acts tp" "t = t' + duration pa" "Some s = res_inst_snap_action pa At_End"
    using s unfolding acts_of_plan_at_def by auto
  note c = this

  thus "(t, s) \<in> imp_defs.rat_impl.plan_happ_seq" 
  proof (cases rule: c)
    case a: 1
    obtain n as where
      pa: "pa = Simple_Plan_Action n as" using a by (cases pa) auto
    have ref: "(the (resolve_action_schema n), \<lfloor>t\<rfloor>, 0) \<in> set ref_plan" 
      apply (rule in_set_ref_planI(1))
      using a unfolding simple_acts_def pa by auto

    obtain ps pre eff where 
      res: "the (resolve_action_schema n) = Simple_Action_Schema n ps pre eff" 
      using a pa simple_plan_action_schema_type1 wf_plan_actions simple_acts_in_plan by fastforce

    have as_Nil: "as = []" 
      using plan_acts_no_args
          simple_acts_in_plan
          a(1) pa 
      unfolding list_all_iff
      apply (cases as) 
      by fastforce+

    have abstr: "(the (resolve_action_schema n), rat_of_int \<lfloor>t\<rfloor>, rat_of_int 0) \<in> ran abstr_plan" 
      using ran_abstr_planI ref by blast
    have s: "s = at_start_spec (the (resolve_action_schema n))"
      using a unfolding pa res_inst.simps res at_start_spec.simps as_Nil by blast
      
    have "is_integer t" using a(1) plan_acts_durs_integer simple_acts_in_plan 
      unfolding pa list_all_iff by fastforce
    hence t: "rat_of_int (floor t) = t" using is_integer_of_int by blast

    show ?thesis using imp_defs.rat_impl.in_happ_seqI(1)[OF abstr[simplified abstr_plan_def]] 
      unfolding s t by blast
  next
    case a: 2
    obtain n as d where
      pa: "pa = Durative_Plan_Action n as d" using a by (cases pa) auto
    have ref: "(the (resolve_action_schema n), \<lfloor>t\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
      apply (rule in_set_ref_planI(2))
      using a unfolding pa using durative_acts_in_plan by auto

    obtain ps dcs pre eff where 
      res: "the (resolve_action_schema n) = Durative_Action_Schema n ps dcs pre eff" 
      using a pa durative_plan_action_schema_type1 wf_plan_actions durative_acts_in_plan by fastforce

    have as_Nil: "as = []" 
      using plan_acts_no_args
          durative_acts_in_plan
          a(1) pa 
      unfolding list_all_iff
      apply (cases as) 
      by fastforce+

    have abstr: "(the (resolve_action_schema n), rat_of_int \<lfloor>t\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
      using ran_abstr_planI ref by blast
    have s: "s = at_start_spec (the (resolve_action_schema n))"
      using a unfolding pa res_inst_snap_action.simps res at_start_spec.simps as_Nil by blast
      
    have "is_integer t" "is_integer d" using a(1) plan_acts_durs_integer durative_acts_in_plan 
      unfolding pa list_all_iff by fastforce+
    hence td: "rat_of_int (floor t) = t" "rat_of_int (floor d) = d" using is_integer_of_int by blast+

    show ?thesis using imp_defs.rat_impl.in_happ_seqI(1)[OF abstr[simplified abstr_plan_def]] 
      unfolding s td by blast
  next
    case a: 3
    obtain n as d where
      pa: "pa = Durative_Plan_Action n as d" using a by (cases pa) auto
    have ref: "(the (resolve_action_schema n), \<lfloor>t'\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
      apply (rule in_set_ref_planI(2))
      using a unfolding pa using durative_acts_in_plan by blast

    obtain ps dcs pre eff where 
      res: "the (resolve_action_schema n) = Durative_Action_Schema n ps dcs pre eff" 
      using a pa durative_plan_action_schema_type1 wf_plan_actions durative_acts_in_plan by fastforce

    have as_Nil: "as = []" 
      using plan_acts_no_args
          durative_acts_in_plan
          a(1) pa 
      unfolding list_all_iff
      apply (cases as) 
      by fastforce+

    have abstr: "(the (resolve_action_schema n), rat_of_int \<lfloor>t'\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
      using ran_abstr_planI ref by blast
    have s: "s = at_end_spec (the (resolve_action_schema n))"
      using a unfolding pa res_inst_snap_action.simps res at_end_spec.simps as_Nil by blast
      
    have "is_integer t'" "is_integer d" using a(1) plan_acts_durs_integer durative_acts_in_plan 
      unfolding pa list_all_iff by fastforce+
    hence td: "rat_of_int (floor t') = t'" "rat_of_int (floor d) = d" using is_integer_of_int by blast+

    show ?thesis using imp_defs.rat_impl.in_happ_seqI(2)[OF abstr[simplified abstr_plan_def]] 
      unfolding s td a pa plan_action.sel by auto
  qed
next
  fix s a
  assume x: "(t, a) \<in> simple_acts tp" 
    and s: "Some s = map_option at_end_spec (resolve_action_schema (plan_action.name a))"

  obtain n as where
    a: "a = Simple_Plan_Action n as" using x(1) unfolding simple_acts_def is_act_simple_alt 
    by (cases a) auto

  obtain ps pre eff where 
    res: "the (resolve_action_schema n) = Simple_Action_Schema n ps pre eff" 
    using a x simple_plan_action_schema_type1 wf_plan_actions simple_acts_in_plan by fastforce

  have s: "s = at_end_spec (Simple_Action_Schema n ps pre eff)"  using s res a by auto

  have ref: "(the (resolve_action_schema n), \<lfloor>t\<rfloor>, 0) \<in> set ref_plan"
    apply (rule in_set_ref_planI)
    using x a simple_acts_in_plan by auto

  have abstr: "(Simple_Action_Schema n ps pre eff, rat_of_int \<lfloor>t\<rfloor>, rat_of_int 0) \<in> ran abstr_plan" 
    using ran_abstr_planI ref res by fastforce

  have t: "rat_of_int (floor t) = t" 
    apply (rule is_integer_of_int)
    using plan_acts_durs_integer x 
      simple_acts_in_plan a unfolding list_all_iff by fastforce
  
  show "(t, s) \<in> imp_defs.rat_impl.plan_happ_seq" 
    using imp_defs.rat_impl.in_happ_seqI(2)[folded abstr_plan_def, OF abstr] unfolding abstr_plan_def
    unfolding s t by simp
qed

lemma plan_happ_seq_alt: "imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq t =
  acts_of_plan_at t tp \<union> missing_ends t tp"
  using plan_happ_seq_alt' by blast


lemma missing_ends_ground_non_actions:
  "missing_ends t tp \<subseteq> {ground_non_action n anno|n anno. True}"
proof (rule subsetI)
  fix x
  assume "x \<in> missing_ends t tp"
  then obtain a where
    "(t, a) \<in> simple_acts tp" 
    "Some x = map_option at_end_spec (resolve_action_schema (plan_action.name a))"
    unfolding missing_ends_def by auto
  then obtain n ps pre eff where
    x: "x = at_end_spec (Simple_Action_Schema n ps pre eff)" 
    using res_simple_act_name by fastforce
  show "x \<in> {ground_non_action n anno |n anno. True}" unfolding x
    by auto
qed

lemma
  assumes "S - (\<Union>x\<in>h. set (dels (ground_action.effect x))) \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))) = T"
     and S_props: "S \<subseteq> {x. form_preds_no_args x \<and> is_predAtom x}"
     and "h \<subseteq> {x. ground_act_no_args x \<and> wf_ground_action x}" (* From where do we deduce that effects are predAtoms? wf_effect 
                From where to we deduce that effects have no args? Definition of locale *)
  shows "(\<Union>x\<in>S. set (map to_predicate (to_literals x))) - (\<Union>x\<in>h. set (dels_spec x)) \<union> (\<Union>x\<in>h. set (adds_spec x)) 
    = (\<Union>x\<in>T. set (map to_predicate (to_literals x)))"
proof -
  thm del_preds


  have 2: "(\<Union>x \<in> S. set (to_literals x)) = S" 
    apply (intro equalityI subsetI)
    subgoal for x
      apply (erule UnionE)
      apply (erule imageE)
      subgoal for x' x''
        apply (frule preds[THEN bspec])
        apply (erule is_predAtom.elims)
        by auto
      done
    apply (frule preds[THEN bspec])
    apply (erule is_predAtom.elims)
    by fastforce

      
  have "(\<Union>x\<in>S. to_predicate ` set (to_literals x)) - (\<Union>x\<in>h. to_predicate ` set (dels (ground_action.effect x))) \<union> (\<Union>x\<in>h. to_predicate ` set (adds (ground_action.effect x))) =
    to_predicate ` ((\<Union>x\<in>S. set (to_literals x)) - (\<Union>x\<in>h. set (dels (ground_action.effect x))) \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))))"
    unfolding image_UN[symmetric]
    apply (subst inj_on_image_set_diff[symmetric])
       apply (rule i)
    using 2 apply simp
    
    
  have "(\<Union>x\<in>S. set (map to_predicate (to_literals x))) - (\<Union>x\<in>h. set (dels_spec x)) \<union> (\<Union>x\<in>h. set (adds_spec x)) 
    = (\<Union>x\<in>S - (\<Union>x\<in>h. set (dels (ground_action.effect x))) \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))). set (map to_predicate (to_literals x)))" 
  unfolding del_preds[symmetric] add_preds[symmetric] set_map 
  show ?thesis
    unfolding assms[symmetric]
  qed
lemma 
  assumes "i < length imp_defs.rat_impl.htpl" 
  shows "imp_defs.rat_impl.apply_effects 
      (imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq (imp_defs.rat_impl.time_index i)) 
      (plan_state_list ! i) = plan_state_list ! Suc i"
proof -
  have i': "i < length htps" using assms ref_htpl_eq_htps by argo
  hence Sia: "Suc i < length abstr_state_list" 
    and Sip: "Suc i < length plan_state_list" 
      using length_abstr_state_list length_plan_state_list by simp+
  hence ia: "i < length abstr_state_list" 
    and ip: "i < length plan_state_list" by simp+

  have x: "apply_eff (acts_of_plan_at (htps ! i) tp) (abstr_state_list ! i) = abstr_state_list ! Suc i"
    using abstr_state_list_nth_Suc i' by blast
  have "imp_defs.rat_impl.apply_effects (acts_of_plan_at (htps ! i) tp) (plan_state_list ! i) = plan_state_list ! Suc i"
    using x
    unfolding apply_eff.simps imp_defs.rat_impl.apply_effects_def
    unfolding comp_def image_image[symmetric]
    unfolding plan_state_list_nth_conv_abstr_state_list_nth[OF ip]
    unfolding plan_state_list_nth_conv_abstr_state_list_nth[OF Sip]
    unfolding image_image image_set
    using dels_spec.simps
  thus ?thesis
    unfolding plan_happ_seq_alt
    apply (subst ground_non_action_no_effs)
     apply (rule missing_ends_ground_non_actions)
    unfolding imp_defs.rat_impl.time_index_def ref_htpl_eq_htps 
    by blast
qed



lemma temp_plan_valid:
  "imp_defs.rat_impl.valid_plan"
proof -
  have vss: "\<exists>M. imp_defs.rat_impl.valid_state_sequence M \<and> M 0 = set init_spec \<and> set goal_spec \<subseteq> M (length imp_defs.rat_impl.htpl)" 
  proof (intro exI conjI)
    show "imp_defs.rat_impl.valid_state_sequence ((!) plan_state_list)"
    proof (rule imp_defs.rat_impl.valid_state_sequenceI)

    qed
  qed                                              
  moreover
  have durs_ge_0: "imp_defs.rat_impl.durations_ge_0"
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
  moreover
  have durs_valid: "imp_defs.rat_impl.durations_valid"
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
  moreover
  have mutex_valid: "imp_defs.rat_impl.mutex_valid_plan"
  proof -
    show ?thesis 
      unfolding imp_defs.rat_impl.mutex_valid_plan_eq
      imp_defs.rat_impl.mutex_valid_plan_alt_def
      unfolding abstr_plan_def[symmetric]
    proof (intro conjI)
      show "\<forall>i j a ta da b tb db. i \<in> dom abstr_plan \<and> j \<in> dom abstr_plan \<and> i \<noteq> j 
          \<and> abstr_plan i = Some (a, ta, da) \<and> abstr_plan j = Some (b, tb, db) 
        \<longrightarrow> imp_defs.rat_impl.mutex_sched a ta da b tb db" 
      proof -
        have 1: "\<forall>i j a ta da b tb db. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j \<longrightarrow> ref_plan ! i = (a, ta, da) \<longrightarrow> ref_plan ! j = (b, tb, db) \<longrightarrow> imp_defs.rat_impl.mutex_sched a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)"
        proof (intro strip)
          fix i j a ta da b tb db
          assume i:   "i < length ref_plan"
            and j:    "j < length ref_plan" 
            and ij:   "i \<noteq> j" 
            and atd:  "ref_plan ! i = (a, ta, da)"
            and btd:  "ref_plan ! j = (b, tb, db)"


          have in_ref_plan: "(a, ta, da) \<in> set ref_plan" 
            "(b, tb, db) \<in> set ref_plan"
            using nth_mem[OF i] nth_mem[OF j] unfolding atd btd by simp+

          
          have durs_ge0: "0 \<le> da"
                         "0 \<le> db" 
            using in_ref_plan ref_plan_durs by blast+

          have nso_cond: "ref_no_self_overlap (a, ta, da) (b, tb, db)" 
            using ref_plan_no_self_overlap unfolding ref_plan_no_self_overlap_def
            unfolding list_pairwise_nth_refl[OF ref_no_self_overlap_refl]
            using i j ij atd[symmetric] btd[symmetric]
            by auto
            

          have a_start: "at_start_spec a \<in> acts_of_plan_at (rat_of_int ta) tp"
            using at_start_snap_at_t in_ref_plan by simp

          have "at_end_spec a \<in> acts_of_plan_at (rat_of_int (ta + da)) tp \<or> (\<exists>n anno. at_end_spec a = ground_non_action n anno)"
            apply (cases a)
            using at_end_snap_at_t_if_durative in_ref_plan by auto
          then
          consider "at_end_spec a \<in> acts_of_plan_at (rat_of_int (ta + da)) tp" 
            | "\<exists>n anno. at_end_spec a = ground_non_action n anno"
            by blast
          note a_end = this
            

          have b_start: "at_start_spec b \<in> acts_of_plan_at (rat_of_int tb) tp"
            using btd at_start_snap_at_t nth_mem[OF j] by simp
          have "at_end_spec b \<in> acts_of_plan_at (rat_of_int (tb + db)) tp \<or> (\<exists>n anno. at_end_spec b = ground_non_action n anno)"
            apply (cases b)
            using at_end_snap_at_t_if_durative in_ref_plan by auto
          then
          consider "at_end_spec b \<in> acts_of_plan_at (rat_of_int (tb + db)) tp" 
            | "(\<exists>n anno. at_end_spec b = ground_non_action n anno)"
            by blast
          note b_end = this

          have a_in_acts: "a \<in> set actions_spec" 
           and b_in_acts: "b \<in> set actions_spec" 
            using in_ref_plan
            using ref_plan_acts_in_actions by auto
          note ab_in_acts = this

          have acts_pres_pos: 
                "ground_act_pres_pos (at_start_spec a)"
                "ground_act_pres_pos (at_start_spec b)" 
                "ground_act_pres_pos (at_end_spec a)"
                "ground_act_pres_pos (at_end_spec b)"
            using ab_in_acts start_snap_pre_pos_conj end_snap_pre_pos_conj by blast+
          have acts_no_args: 
                "ground_act_no_args (at_start_spec a)"
                "ground_act_no_args (at_start_spec b)"
                "ground_act_no_args (at_end_spec a)"
                "ground_act_no_args (at_end_spec b)"
            using ab_in_acts start_snap_no_args end_snap_no_args by blast+
          have acts_wf:
                "wf_ground_action (at_start_spec a)"
                "wf_ground_action (at_start_spec b)"
                "wf_ground_action (at_end_spec a)"
                "wf_ground_action (at_end_spec b)"
            using ab_in_acts start_snaps_wf end_snaps_wf by blast+

          have start_times_in_htps: 
            "rat_of_int ta \<in> set htps" 
            "rat_of_int tb \<in> set htps" 
            using ref_plan_start_in_htps in_ref_plan by force+

          have "rat_of_int (ta + da) \<in> set htps \<or> (\<exists>n anno. at_end_spec a = ground_non_action n anno)" 
            apply (cases a)
            using ref_plan_end_in_htps_if_durative in_ref_plan
            by auto
          then
          consider "rat_of_int (ta + da) \<in> set htps" 
            | "(\<exists>n anno. at_end_spec a = ground_non_action n anno)"
            by blast+
          note a_end_time = this

          have "rat_of_int (tb + db) \<in> set htps \<or> (\<exists>n anno. at_end_spec b = ground_non_action n anno)" 
            apply (cases b)
            using ref_plan_end_in_htps_if_durative in_ref_plan
            by auto
          then
          consider "rat_of_int (tb + db) \<in> set htps" 
            | "(\<exists>n anno. at_end_spec b = ground_non_action n anno)"
            by blast+
          note b_end_time = this

          show "imp_defs.rat_impl.mutex_sched a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)" 
          proof (intro imp_defs.rat_impl.mutex_sched_zero_sepI acts_non_intrf_imp_mutex_snap_action acts_pres_pos acts_no_args acts_wf)
            show "rat_of_int 0 = 0" by simp
          next 
            assume t: "rat_of_int ta = rat_of_int tb"

            have "a \<noteq> b"
              apply (rule notI)
              using t nso_cond durs_ge0 by auto
            hence ne: "at_start_spec a \<noteq> at_start_spec b" 
              using inj_on_at_start_spec a_in_acts b_in_acts by (force dest: inj_on_contraD)
            

            show "acts_non_intrf (at_start_spec a) (at_start_spec b)" 
              apply (rule all_htps_acts_non_intrf')
              using start_times_in_htps(1)
              using a_start b_start t[symmetric] ne by auto 

          next
            assume t: "rat_of_int ta = rat_of_int tb + rat_of_int db" 
            { assume b_end: "at_end_spec b \<in> acts_of_plan_at (rat_of_int (tb + db)) tp"
              
              have "a \<noteq> b"
                apply (rule notI)
                using t nso_cond durs_ge0 by auto
              hence ne: "at_start_spec a \<noteq> at_end_spec b" 
                using at_start_spec_at_end_spec_disj a_in_acts b_in_acts by auto
            
              have "acts_non_intrf (at_start_spec a) (at_end_spec b)" 
                apply (rule all_htps_acts_non_intrf')
                using start_times_in_htps(1)
                using a_start b_end ne t by auto
            }
            thus " acts_non_intrf (at_start_spec a) (at_end_spec b)" 
              apply (cases rule: b_end)
              using ground_non_action_non_intrf by auto
          next 
            assume t: "rat_of_int ta + rat_of_int da = rat_of_int tb" 
            { assume a_end: "at_end_spec a \<in> acts_of_plan_at (rat_of_int (ta + da)) tp"
              have "a \<noteq> b"
                apply (rule notI)
                using t nso_cond durs_ge0 by auto
              hence ne: "at_end_spec a \<noteq> at_start_spec b" 
                using at_start_spec_at_end_spec_disj a_in_acts b_in_acts by auto
            
              have  "acts_non_intrf (at_end_spec a) (at_start_spec b)" 
                apply (rule all_htps_acts_non_intrf')
                using start_times_in_htps(2)
                using a_end b_start ne t by auto
            }
            thus "acts_non_intrf (at_end_spec a) (at_start_spec b)" 
              apply (cases rule: a_end)
              using ground_non_action_non_intrf by auto
          next 
            assume t: "rat_of_int ta + rat_of_int da = rat_of_int tb + rat_of_int db" 
            { assume a_end: "at_end_spec a \<in> acts_of_plan_at (rat_of_int (ta + da)) tp"
              assume b_end: "at_end_spec b \<in> acts_of_plan_at (rat_of_int (tb + db)) tp"
              assume a_end_time: "rat_of_int (plus_int ta da) \<in> set htps"
              have "a \<noteq> b"
                apply (rule notI)
                using t nso_cond durs_ge0 by auto
              hence ne: "at_end_spec a \<noteq> at_end_spec b" 
                using inj_on_at_end_spec a_in_acts b_in_acts by (force dest: inj_on_contraD)
            
              have "acts_non_intrf (at_end_spec a) (at_end_spec b)" 
                apply (rule all_htps_acts_non_intrf')
                using a_end_time
                using a_end b_end ne t by auto
            }
            thus "acts_non_intrf (at_end_spec a) (at_end_spec b)" 
              apply (cases rule: a_end; cases rule: b_end; cases rule: a_end_time)
              using ground_non_action_non_intrf by auto
          qed
        qed
        show ?thesis
        apply (intro strip, elim conjE)
        subgoal
          apply (rule abstr_plan_binary_prop')
          using imp_defs.rat_impl.mutex_sched_refl 
          using 1 by blast+
        done
      qed
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
  
            have a_in_acts: "a \<in> set actions_spec" using a ref_plan_acts_in_actions by simp
            
            show "\<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a) (at_end_spec a)"
            proof (cases a)
              case (Simple_Action_Schema n ps pre eff)
              thus ?thesis unfolding imp_defs.rat_impl.set_impl.mutex_snap_action_def 
                  using ground_non_action_def by simp
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
                apply (rule acts_non_intrf_imp_mutex_snap_action)
                using start_snap_pre_pos_conj start_snaps_wf start_snap_no_args
                using end_snap_pre_pos_conj end_snaps_wf end_snap_no_args
                using a_in_acts by blast+
            qed
          qed
        }
        thus ?thesis by auto
      qed
    qed
  qed
  moreover
  have finite: "imp_defs.rat_impl.finite_plan" 
    unfolding imp_defs.rat_impl.finite_plan_def
    unfolding dom_map_option comp_def
    using dom_plan_imp by simp
  ultimately
  show "imp_defs.rat_impl.valid_plan" 
    unfolding imp_defs.rat_impl.valid_plan_def
    by simp
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
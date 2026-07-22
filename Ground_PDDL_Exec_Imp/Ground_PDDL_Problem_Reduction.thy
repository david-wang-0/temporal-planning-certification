theory Ground_PDDL_Problem_Reduction
  imports Ground_PDDL_Problem_Defs
begin

context ground_ast_problem_base
begin

sublocale abstr_model_checking: tp_nta_reduction_model_checking'
  init_spec goal_spec at_start_spec at_end_spec 
  over_all_spec 
  lower_spec upper_spec 
  pre_spec adds_spec dels_spec
  0
  props_spec actions_spec
  act_to_name_spec prop_to_name_spec
proof 
  show "distinct props_spec"
    using wf_domain_signature
    unfolding wf_domain_signature_def props_spec_def 
    by simp
  show "distinct actions_spec"
  proof -
    have "distinct (map ast_temporal_action_schema_name actions_spec)"
      using distinct_act_names .
    thus ?thesis
      using distinct_map by blast
  qed                                         
  show "\<forall>a\<in>set actions_spec. distinct (over_all_spec a)"
    by (simp add: pre_spec_alt)
  show "set goal_spec - set props_spec \<subseteq> set init_spec - set props_spec"
    \<comment> \<open>@{text goal_in_props} makes the LHS empty; @{text init_in_props} is no longer needed (and is a
        @{text no_functions}-leaf lemma, unavailable in @{text ground_ast_problem_core}).\<close>
    using goal_in_props by auto
  show "\<forall>a\<in>set actions_spec. action_and_prop_set.act_mod_props at_start_spec at_end_spec (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) a"
  proof (rule ballI)
    fix a
    assume "a \<in> set actions_spec" 
    thus "action_and_prop_set.act_mod_props at_start_spec at_end_spec (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) a"
      by (intro action_and_prop_set.act_mod_propsI action_and_prop_set.snap_mod_propsI 
          wf_ground_action_adds_in_props wf_ground_action_dels_in_props start_snaps_wf end_snaps_wf)
  qed
  show "action_set_and_props.action_consts at_start_spec at_end_spec (set \<circ> over_all_spec) (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (set actions_spec) \<subseteq> set init_spec - set props_spec"
  proof (rule subsetI)
    fix x
    assume "x \<in> action_set_and_props.action_consts at_start_spec at_end_spec (set \<circ> over_all_spec) (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (set actions_spec)"
    then obtain a where
      a: "x \<in> action_and_prop_set.act_consts at_start_spec at_end_spec (set \<circ> over_all_spec) (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) a" 
      and a_in_acts: "a \<in> set actions_spec" unfolding action_set_and_props.action_consts_def by blast
    then consider "x \<in> action_and_prop_set.snap_consts (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (at_start_spec a)"
      | "x \<in> action_and_prop_set.snap_consts (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (at_end_spec a)"
      | "x \<in> ((set \<circ> over_all_spec) a - set props_spec)" unfolding action_and_prop_set.act_consts_def by auto
    hence "x \<in> {}" 
    proof (cases)
      case 1
      have a': "wf_ground_action (at_start_spec a)" using start_snaps_wf[OF a_in_acts] .
      have "(set \<circ> pre_spec) (at_start_spec a) \<union> (set \<circ> adds_spec) (at_start_spec a) \<union> (set \<circ> dels_spec) (at_start_spec a) \<subseteq> set props_spec"
        using wf_ground_action_pres_in_props wf_ground_action_dels_in_props wf_ground_action_adds_in_props
        using a' by simp
      then show ?thesis using 1 unfolding action_and_prop_set.snap_consts_def by blast
    next
      case 2
      have a': "wf_ground_action (at_end_spec a)" using end_snaps_wf[OF a_in_acts] .
      have "(set \<circ> pre_spec) (at_end_spec a) \<union> (set \<circ> adds_spec) (at_end_spec a) \<union> (set \<circ> dels_spec) (at_end_spec a) \<subseteq> set props_spec"
        using wf_ground_action_pres_in_props wf_ground_action_dels_in_props wf_ground_action_adds_in_props
        using a' by simp
      then show ?thesis using 2 unfolding action_and_prop_set.snap_consts_def by blast
    next
      case 3
      then show ?thesis using a_in_acts over_all_in_props by auto
    qed
    thus "x \<in> set init_spec - set props_spec" by simp \<comment> \<open>ex-falso from @{text \<open>x \<in> {}\<close>}\<close>
  qed
  show "inj_on act_to_name_spec (set actions_spec)"
  proof -
    have "distinct (map act_to_name_spec actions_spec)" 
      using distinct_act_names unfolding act_to_name_spec_def .
    thus ?thesis unfolding distinct_map by blast
  qed                                       
  show "inj_on prop_to_name_spec (set props_spec)"
  proof -
    have "distinct (map pred (predicates local.D))"
      using wf_domain_signature unfolding wf_domain_signature_def by auto
    hence "distinct (map predicate.name (map pred (predicates local.D)))"
      apply (rule distinct_inj_map)
      apply (rule injI)
      using predicate.expand by simp
    thus ?thesis
      unfolding prop_to_name_spec_def props_spec_def
      unfolding distinct_map by blast
  qed
qed
end (* context ground_ast_problem *)

end
theory Ground_PDDL_Problem_Defs
  imports Ground_PDDL_Problem_Base
begin
text \<open>Numeric-free / integer-duration assumptions for the (numeric-free) NTA reduction phase that
  the grounder's grounded/positive locales do not cover: no numeric functions, duration constraints
  are function-free and integer-valued. Bundled with the grounder's grounded_temporal_problem
  + positive_temporal_problem by ground_ast_problem below.\<close>
locale integer_duration_problem = wf_ast_temporal_problem P
  for P :: ast_temporal_problem +
  assumes no_functions: "functions D = []"
      and acts_no_func_dcs: "list_all act_no_func_dcs (actions D)"
      and acts_dcs_integers: "list_all act_dcs_integers (actions D)"

locale ground_ast_problem_core =
    ground_ast_problem_base P
  for P :: ast_temporal_problem +
  assumes conds_no_args: "list_all act_conds_no_args (actions D)"
      and init_no_args: "list_all form_preds_no_args (init P)"

begin

lemma act_conds_no_args_spec:
  assumes "a \<in> set actions_spec"
  shows "act_conds_no_args a"
  using assms unfolding actions_spec_def using conds_no_args unfolding list_all_iff
  by simp

text \<open>In the classical (predAtm-only) core the numeric-tolerant base positivity
  @{const act_pres_pos_num} upgrades to strict @{const act_pres_pos} -- there are no numeric
  condition atoms to differ on -- so the classical no-args/pos-conj lemmas below (which take
  @{const act_pres_pos}) are fed unchanged.\<close>
lemma act_pres_pos_spec:
  assumes "a \<in> set actions_spec"
  shows "act_pres_pos a"
  using act_pres_pos_num_spec[OF assms] act_conds_no_args_spec[OF assms]
  by (cases a rule: act_pres_pos.cases)
     (auto simp: is_pos_conj_num_no_args list_all_iff)

lemma instantiate_action_schema_no_params:
  assumes "act_no_params (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "wf_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "act_conds_no_args (SimpleActionSchema h (SimpleActionBody pre eff))"
    shows "ground_act_no_args (instantiate_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff)) as)"
proof -
  have ps: "parameters h = []" using assms(1) by simp
  have p: "wf_fmla (ty_term (map_of []) constT) pre" 
   and e: "wf_effect (ty_term (map_of []) constT) eff" 
    using assms(2) ps unfolding wf_temporal_action_schema.simps wf_simple_action_body.simps Let_def by auto

  have pre_no_args: "form_preds_no_args pre" using assms(4) by simp

  have eff_adds_no_args: "list_all form_preds_no_args (adds eff)"
    apply (cases eff) 
    using wf_fmla_atom_no_args e unfolding list_all_iff
    by auto

  have eff_dels_no_args: "list_all form_preds_no_args (dels eff)"
    apply (cases eff) 
    using wf_fmla_atom_no_args e unfolding list_all_iff
    by auto

  show ?thesis
    unfolding instantiate_temporal_action_schema.simps instantiate_simple_body.simps Let_def
    unfolding ground_act_no_args.simps ground_action.sel
    using pre_no_args eff_adds_no_args eff_dels_no_args 
    using map_formula_no_args map_effect_adds_no_args map_effect_dels_no_args by fastforce
qed


lemma inst_snap_action_no_params:
  assumes "act_no_params (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
      and "wf_temporal_action_schema (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
      and "act_pres_pos (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
      and "act_conds_no_args (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
    shows "ground_act_no_args (inst_snap_action_body_elements [] cond deff (tsubst h args) dur ta)"
proof -
  have ps: "parameters h = []" using assms(1) by simp
  have p: "\<forall>(t, pre) \<in> set cond. wf_fmla (ty_term (map_of []) constT) pre" 
   and e: "\<forall>(t, eff) \<in> set deff. wf_effect (ty_term (map_of []) constT) eff" 
    using assms(2) ps unfolding wf_temporal_action_schema.simps wf_temporal_durative_action_body.simps Let_def by auto
  
  have pre_no_args: "\<forall>(t, pre) \<in> set cond. form_preds_no_args pre"
    using assms(4) unfolding act_conds_no_args.simps list_all_iff by auto

  have eff_adds_no_args: "\<forall>(t, eff) \<in> set deff. list_all form_preds_no_args (adds eff)"
    using wf_fmla_atom_no_args e unfolding list_all_iff
    apply (intro ballI)
    subgoal for x
      apply (cases x)
      subgoal for t eff
        apply (cases eff)
        by auto
      done
    done

  have eff_dels_no_args: "\<forall>(t, eff) \<in> set deff. list_all form_preds_no_args (dels eff)"
    using wf_fmla_atom_no_args e unfolding list_all_iff
    apply (intro ballI)
    subgoal for x
      apply (cases x)
      subgoal for t eff
        apply (cases eff)
        by auto
      done
    done

  have adds_eq: "adds (inst_duration_in_ast_effect e dur) = adds e" for e
    by (cases e) auto
  have dels_eq: "dels (inst_duration_in_ast_effect e dur) = dels e" for e
    by (cases e) auto

  show ?thesis unfolding inst_snap_action_body_elements.simps Let_def inst_formula.simps
    unfolding ground_act_no_args.simps ground_action.sel
    unfolding adds_eq dels_eq
    apply (intro conjI)
      apply (rule map_formula_no_args_gen)
       apply (rule form_preds_no_args_Big_And)
       apply (subst filter_time_spec_def)
       apply (subst list_all_iff)
    using pre_no_args apply auto[1]
      apply simp
     apply (rule map_effect_adds_no_args)
     apply (rule eff_adds_no_args_conjunct_effect)
     apply (subst filter_time_spec_def)
    using eff_adds_no_args apply auto[1]
     apply (rule map_effect_dels_no_args)
     apply (rule eff_dels_no_args_conjunct_effect)
     apply (subst filter_time_spec_def)
    using eff_dels_no_args by auto
qed

lemma start_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (at_start_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  obtain pre eff where
    b: "b = SimpleActionBody pre eff" by (cases b)
  show ?case 
    unfolding at_start_spec.simps b
    apply (rule instantiate_action_schema_no_params[where as = "[]", unfolded b])
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec SimpleActionSchema b by blast+
next
  case (DurativeActionSchema h b)
  obtain dcs cond deff where
    b: "b = DurativeActionBody dcs cond deff" by (cases b)
  show ?case 
    unfolding at_start_spec.simps b
    apply (rule inst_snap_action_no_params)
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec DurativeActionSchema b by blast+
qed

lemma end_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (at_end_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case 
    unfolding at_end_spec.simps ground_non_action_def
    by (simp add: form_preds_no_args_def)
next
  case (DurativeActionSchema h b)
  obtain dcs cond deff where
    b: "b = DurativeActionBody dcs cond deff" by (cases b)
  show ?case 
    unfolding at_end_spec.simps b
    apply (rule inst_snap_action_no_params)
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec DurativeActionSchema b by blast+
qed

text \<open>The over-all condition is obtained by first instantiating the action.\<close>

lemma over_all_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (over_all_snap a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case 
    unfolding over_all_snap.simps ground_non_action_def
    by (simp add: form_preds_no_args_def)
next
  case (DurativeActionSchema h b)
  obtain dcs cond deff where
    b: "b = DurativeActionBody dcs cond deff" by (cases b)
  show ?case 
    unfolding over_all_snap.simps b
    apply (rule inst_snap_action_no_params)
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec DurativeActionSchema b by blast+
qed

text \<open>Conditions\<close>
lemma start_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (at_start_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  obtain pre eff where b: "b = SimpleActionBody pre eff" by (cases b)
  have p: "act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff))"
    using act_pres_pos_spec SimpleActionSchema unfolding b by blast
  have n: "form_preds_no_args pre"
    using SimpleActionSchema conds_no_args unfolding actions_spec_def list_all_iff b by auto
  show ?case unfolding at_start_spec.simps b
    using instantiate_action_schema_pres_pos[OF p n, where as = "[]"] by simp
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where b: "b = DurativeActionBody dc cond deff" by (cases b)
  have p: "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using act_pres_pos_spec DurativeActionSchema unfolding b by blast
  have n: "list_all form_preds_no_args (map snd cond)"
    using act_conds_no_args_spec[OF DurativeActionSchema] unfolding b by simp
  from inst_snap_act_pres_pos[OF p n] show ?case unfolding at_start_spec.simps b by blast
qed

lemma end_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (at_end_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case unfolding at_end_spec.simps ground_non_action_def by (simp add: pos_conj_form_def)
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where b: "b = DurativeActionBody dc cond deff" by (cases b)
  have p: "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using act_pres_pos_spec DurativeActionSchema unfolding b by blast
  have n: "list_all form_preds_no_args (map snd cond)"
    using act_conds_no_args_spec[OF DurativeActionSchema] unfolding b by simp
  from inst_snap_act_pres_pos[OF p n] show ?case unfolding at_end_spec.simps b by blast
qed

lemma over_all_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (over_all_snap a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case unfolding over_all_snap.simps ground_non_action_def by (simp add: pos_conj_form_def)
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where b: "b = DurativeActionBody dc cond deff" by (cases b)
  have p: "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using act_pres_pos_spec DurativeActionSchema unfolding b by blast
  have n: "list_all form_preds_no_args (map snd cond)"
    using act_conds_no_args_spec[OF DurativeActionSchema] unfolding b by simp
  from inst_snap_act_pres_pos[OF p n] show ?case unfolding over_all_snap.simps b by blast
qed

end (* locale ground_ast_problem_core *)

text \<open>Numeric-freeness is an \<^emph>\<open>orthogonal leaf\<close> off the shared @{text ground_ast_problem_core}
  (grounder idiom: cf. the grounder's @{text numeric_free_problem}), \<^bold>\<open>not\<close> part of the core: the
  classical admission bundle @{text ground_ast_problem} is \<open>core\<close> + @{text no_functions}; the numeric
  admission bundle @{text numeric_ground_ast_problem} (in @{text Ground_PDDL_Numeric_Problem_Defs}) is
  \<open>core\<close> + the numeric-fragment well-formedness. The core stays numeric-inclusive so both leaves share it.\<close>

locale ground_ast_problem =
    ground_ast_problem_core P
  for P :: ast_temporal_problem +
  assumes no_functions: "functions D = []"
begin

text \<open>The initial state facts are in the props.\<close>

text \<open>In the numeric-free setting the domain declares no functions, so the function signature is
  empty and no initialisation fact can be a (well-formed) function assignment. Hence the
  well-formedness alternative \<open>wf_fmla_atom objT f \<or> wf_func_assign f\<close> of @{const wf_temporal_problem}
  collapses to the predicate-atom case.\<close>
lemma no_functions_no_wf_func_assign:
  "\<not> wf_func_assign f"
proof (rule notI)
  assume "wf_func_assign f"
  then obtain l r where
    f: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
   and wf: "wf_primitive_numeric_expression objT l"
    by (cases f rule: wf_func_assign.cases) auto
  obtain g args where l: "l = PNE g args" by (cases l)
  have "func_sig g = Some (the (func_sig g))"
    using wf unfolding l wf_primitive_numeric_expression.simps wf_func_args.simps
    by (cases "func_sig g") auto
  thus False
    using no_functions unfolding func_sig_def by simp
qed

lemma init_wf_fmla_atoms:
  "\<forall>f\<in>set (init P). wf_fmla_atom objT f"
proof -
  have 1: "\<forall>f\<in>set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    using wf_temporal_problem unfolding wf_temporal_problem_def by auto
  show "\<forall>f\<in>set (init P). wf_fmla_atom objT f" 
    using 1 no_functions_no_wf_func_assign by blast
qed

lemma init_in_props: "set init_spec \<subseteq> set props_spec"
  using init_wf_fmla_atoms wf_fmla_atom_in_props init_spec_def by auto

end (* locale ground_ast_problem *)
end
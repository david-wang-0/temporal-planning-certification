theory Ground_PDDL_NTA_Reduction_Correctness
imports Ground_PDDL_Plan_Reduction "TP_NTA_Reduction.TP_NTA_Reduction_Correctness"
begin

context valid_ground_plan
begin
  lemmas valid_plan_imp_form_holds = local.red_corr.valid_plan_imp_form_holds
end

context ground_ast_problem
begin

  lemma valid_ground_plan_imp_form_holds:
    assumes "\<exists>tp. valid_ground_plan P tp"
    shows "abstr_model_checking.ref_model_checking.net_impl.sem,
      abstr_model_checking.ref_model_checking.a\<^sub>0 
      \<Turnstile> abstr_model_checking.reduction_ref_impl.reach_formula"
  proof -
    from assms obtain tp where "valid_ground_plan P tp" by blast
    then interpret x: valid_ground_plan P tp by auto
    have "temp_plan_for_problem_list_impl_int' 
      at_start_spec at_end_spec over_all_spec 
      lower_spec upper_spec 
      pre_spec adds_spec dels_spec 
      init_spec goal_spec 0 props_spec actions_spec x.plan_imp"
      using x.red_corr.temp_plan_for_problem_list_impl_int'_axioms by simp
    show ?thesis using x.valid_plan_imp_form_holds by blast
  qed
  
  corollary form_not_sat_imp_no_valid_ground_plan:
    assumes "\<not>(abstr_model_checking.ref_model_checking.net_impl.sem,
      abstr_model_checking.ref_model_checking.a\<^sub>0 
    \<Turnstile> abstr_model_checking.reduction_ref_impl.reach_formula)"
    shows "\<not>(\<exists>tp. valid_ground_plan P tp)"
    using valid_ground_plan_imp_form_holds assms by auto

end



end
theory Ground_PDDL_Plan_Reduction
  imports Ground_PDDL_Plan_Defs Ground_PDDL_Problem_Reduction
begin

context valid_ground_plan
begin
sublocale red_corr: tp_nta_reduction_correctness' init_spec goal_spec 
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  0 
  props_spec actions_spec plan_imp  
  act_to_name_spec prop_to_name_spec
  apply unfold_locales
  using temp_plan_valid apply simp
  using temp_plan_no_self_overlap apply blast
  using temp_plan_actions_in_actions apply blast
  done
end

end
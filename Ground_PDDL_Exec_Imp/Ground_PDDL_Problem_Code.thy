theory Ground_PDDL_Problem_Code
  imports Ground_PDDL_Problem_Defs
begin

(* fun at_start_spec::"ast_action_schema \<Rightarrow> ground_action" where
"at_start_spec (Simple_Action_Schema n ps pre eff) = instantiate_action_schema (Simple_Action_Schema n ps pre eff) [] At_Start" |
"at_start_spec (Durative_Action_Schema n ps d cond eff) = inst_snap_action (Durative_Action_Schema n ps d cond eff) [] At_Start"

fun at_end_spec::"ast_action_schema \<Rightarrow> ground_action" where
"at_end_spec (Simple_Action_Schema n ps pre eff) = ground_non_action n At_End" |
"at_end_spec (Durative_Action_Schema n ps d cond eff) = inst_snap_action (Durative_Action_Schema n ps d cond eff) [] At_End"

fun over_all_snap::"ast_action_schema \<Rightarrow> ground_action" where
"over_all_snap (Simple_Action_Schema n ps pre eff) = 
   ground_non_action n Over_All" |
"over_all_snap (Durative_Action_Schema n ps d cond eff) = 
  inst_snap_action (Durative_Action_Schema n ps d cond eff) [] Over_All"

fun pre_spec::"ground_action \<Rightarrow> predicate list" where
"pre_spec (Ground_Action n anno form eff) = 
  form
  |> to_literals
  |> map to_predicate
  |> remdups"

fun over_all_spec::"ast_action_schema \<Rightarrow> predicate list" where
"over_all_spec x =
  x
  |> over_all_snap
  |> pre_spec"

fun adds_spec::"ground_action \<Rightarrow> predicate list" where
"adds_spec (Ground_Action n anno form eff) =
  eff
  |> ast_effect.adds
  |> map to_predicate
  |> remdups
"

fun dels_spec::"ground_action \<Rightarrow> predicate list" where
"dels_spec (Ground_Action n anno form eff) =
  eff
  |> ast_effect.dels
  |> map to_predicate
  |> remdups
"

fun dc_to_lb::"term duration_constraint \<Rightarrow> rat lower_bound option" where
"dc_to_lb No_Const = None" |
"dc_to_lb (Time_Const duration_op.EQ x) = Some (lower_bound.GE x)" |
"dc_to_lb (Time_Const duration_op.GEQ x) = Some (lower_bound.GE x)" |
"dc_to_lb (Time_Const duration_op.LEQ x) = None"


definition dc_list_lower::"term duration_constraint list \<Rightarrow> rat lower_bound option" where
"dc_list_lower xs \<equiv> map dc_to_lb xs |> (\<lambda>xs. max_lb_opt xs None)" 


fun dc_to_ub::"term duration_constraint \<Rightarrow> rat upper_bound option" where
"dc_to_ub No_Const = None" |
"dc_to_ub (Time_Const duration_op.EQ x) = Some (upper_bound.LE  x)" |
"dc_to_ub (Time_Const duration_op.GEQ x) = None" |
"dc_to_ub (Time_Const duration_op.LEQ x) = Some (upper_bound.LE x)"

definition dc_list_upper::"term duration_constraint list \<Rightarrow> rat upper_bound option" where
"dc_list_upper xs = map dc_to_ub xs |> (\<lambda>xs. min_ub_opt xs None)" 

fun lower_spec::"ast_action_schema \<Rightarrow> _" where
"lower_spec (Simple_Action_Schema n ps pre eff) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec (Durative_Action_Schema n ps d cond eff) = map_option (map_lower_bound floor) (dc_list_lower d)"

fun upper_spec::"ast_action_schema \<Rightarrow> _" where
"upper_spec (Simple_Action_Schema n ps pre eff) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec (Durative_Action_Schema n ps d cond eff) = map_option (map_upper_bound floor) (dc_list_upper d)"

 *)


 
end
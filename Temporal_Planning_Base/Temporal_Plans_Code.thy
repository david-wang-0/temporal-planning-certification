theory Temporal_Plans_Code
imports Temporal_Plans_Instances
begin

lemma [code]: "action_defs.mutex_snap_action = (\<lambda> pre adds dels a b. 
  (pre a \<inter> (adds b \<union> dels b) \<noteq> {} \<or> 
  adds a \<inter> dels b \<noteq> {} \<or> 
  pre b \<inter> (adds a \<union> dels a) \<noteq> {} \<or> 
  adds b \<inter> dels a \<noteq> {}))"
  apply (intro ext)
  apply (subst action_defs.mutex_snap_action_def)
  by blast


lemma [code]: "temp_planning_problem_list_defs.pre_imp_list = 
  (\<lambda>pre at_start at_end a. action_defs.app_snap pre at_start at_end a)"
  apply (intro ext)
  apply (subst temp_planning_problem_list_defs.pre_imp_list_def)
   apply (intro temp_planning_problem_list_defs.intro)
   apply blast
  by simp

lemma [code]: "temp_planning_problem_list_defs.add_imp_list = 
  (\<lambda>add at_start at_end a. action_defs.app_snap add at_start at_end a)"
  apply (intro ext)
  apply (subst temp_planning_problem_list_defs.add_imp_list_def)
   apply (intro temp_planning_problem_list_defs.intro)
   apply blast
  by simp

lemma [code]: "temp_planning_problem_list_defs.del_imp_list = 
  (\<lambda>del at_start at_end a. action_defs.app_snap del at_start at_end a)"
  apply (intro ext)
  apply (subst temp_planning_problem_list_defs.del_imp_list_def)
   apply (intro temp_planning_problem_list_defs.intro)
   apply blast
  by simp

code_thms "action_defs.mutex_snap_action"
end
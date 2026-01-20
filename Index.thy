theory Index
  imports "PDDL_TP_Reduction.Check_Unsolvability"
          "Munta_Model_Checker.Simple_Network_Language_Impl"
begin

subsection \<open>Locales\<close>
text \<open>Our locales are:\<close>
text \<open>\<open>\<Pi>\<close>:\<close>
term temp_planning_problem_set_impl
text \<open>\<open>\<Pi>a:\<close>\<close>
term temp_planning_problem_set_impl'
text \<open>\<open>\<pi>:\<close>\<close>
term temp_plan_for_problem_impl
text \<open>\<open>\<pi>a:\<close>\<close>
term temp_plan_for_problem_impl'
text \<open>\<open>\<Pi>li:\<close>\<close>
term temp_planning_problem_list_impl_int
text \<open>\<open>\<Pi>ali:\<close>\<close>
term temp_planning_problem_list_impl_int'
text \<open>\<open>\<pi>li:\<close>\<close>
term temp_plan_for_problem_list_impl_int
text \<open>\<open>\<pi>ali:\<close>\<close>
term temp_plan_for_problem_list_impl_int'
text \<open>\<open>\<Pi>liN:\<close>\<close>
term tp_nta_reduction_model_checking
text \<open>\<open>\<Pi>aliN:\<close>\<close>
term tp_nta_reduction_model_checking'
text \<open>\<open>\<pi>liN:\<close>\<close>
term tp_nta_reduction_correctness
text \<open>\<open>\<pi>aliN:\<close>\<close>
term tp_nta_reduction_correctness'
text \<open>\<open>\<T>:\<close>\<close>
term Simple_Network_Impl_nat
(* This is found as 
Actually Simple_Network_Impl, but the definition cannot be navigated to from here.
sublocale net_impl: Simple_Network_Impl automata_spec broadcast_spec bounds_spec .
*)
text \<open>\<open>\<Pi>Sg:\<close>\<close>
term ground_ast_problem
text \<open>\<open>\<Pi>Sg:\<close>\<close>
term valid_ground_plan
text \<open>\<open>\<Pi>SgD:\<close>\<close>
term ground_ast_problem
text \<open>\<open>\<Pi>S:\<close>\<close>
term TEMPORAL_PDDL_Semantics.wf_ast_problem

find_theorems name: "Simple_Network_Language_Model"

subsection \<open>Theorems\<close>
text\<open>Theorem 1:\<close>
thm tp_nta_reduction_correctness.valid_plan_imp_form_holds
text\<open>Lemma 1:\<close>
thm tp_nta_reduction_correctness.plan_steps_possible
text\<open>Lemma 2:\<close>
thm tp_nta_reduction_correctness.initial_step_possible
text\<open>Lemma 3:\<close>
thm tp_nta_reduction_correctness.final_step_possible
end
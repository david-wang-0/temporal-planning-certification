theory Ground_PDDL_Numeric_NTA_Reduction_Bounds
  imports
    Ground_PDDL_Numeric_NTA_Reduction_Correctness
    "TP_NTA_Reduction.TP_NTA_Reduction_Numeric_Bounds"
begin

text \<open>\<^bold>\<open>NUMERIC_EXEC_PLAN WP-D INTEGRATION\<close> -- discharge the soundness-critical @{text num_seq_in_bounds}
  plug at the ground problem from the static, eval-checkable interval certificate
  @{text \<open>is_gbound_inv'\<close>} (theory @{text TP_NTA_Reduction_Numeric_Bounds}).

  WP-A (@{text Ground_PDDL_Numeric_NTA_Reduction_Correctness}) carried
  @{text num_seq_in_bounds} as a per-plan locale assumption of @{locale numeric_valid_ground_plan}.
  Here it is \<^emph>\<open>derived\<close>: the plan-free static certificate @{text \<open>nred.is_gbound_inv'\<close>} (init in the
  fluent box; every relaxed snap update lands in bounds under interval evaluation of the guard-refined
  box) implies the reduction-native @{text \<open>nred.num_bound_inv\<close>} via
  @{text is_gbound_inv'_imp_num_bound_inv}, and the abstract discharge
  locale @{locale numeric_tp_nta_reduction_bounds} turns that certificate into
  @{locale numeric_tp_nta_reduction_correctness} (via @{text num_seq_in_bounds_derived}).

  So the ground plan predicate here (@{text numeric_valid_ground_plan_cert}) no longer bundles the
  soundness-critical reachability invariant: it is a genuinely valid numeric plan, with boundedness
  supplied once, statically, at the problem level.\<close>

subsection \<open>The static bound certificate at the ground problem (plan-free)\<close>

text \<open>The eval-checkable certificate @{text \<open>nred.is_gbound_inv'\<close>} is a property of the plan-free
  ground data (the inferred finite @{text fluent_lo}/@{text fluent_hi} box, @{text num_init}, and every
  relaxed snap's updates/guards). We assume it here and derive the reduction-native certificate
  @{text \<open>nred.num_bound_inv\<close>}.\<close>

locale numeric_ground_ast_problem_cert =
    numeric_ground_ast_problem P fluent_lo fluent_hi
  for P :: ast_temporal_problem
    and fluent_lo :: "func \<Rightarrow> int"
    and fluent_hi :: "func \<Rightarrow> int" +
  assumes gbound_inv: "nred.is_gbound_inv'"
begin

text \<open>The static, eval-decidable interval certificate discharges the reduction-native
  @{term \<open>nred.num_bound_inv\<close>} (still plan-free).\<close>
lemma num_bound_inv: "nred.num_bound_inv"
  using gbound_inv by (rule nred.is_gbound_inv'_imp_num_bound_inv)

end

subsection \<open>The numeric plan-carrying locale, @{text num_seq_in_bounds} DISCHARGED\<close>

text \<open>The twin of @{locale numeric_valid_ground_plan}, but WITHOUT the @{text num_seq_in_bounds}
  assumption: it extends the certificate leaf @{locale numeric_ground_ast_problem_cert} (which supplies
  @{thm [source] numeric_ground_ast_problem_cert.num_bound_inv}) together with the UNPRIMED numeric
  plan-carrying locale @{locale numeric_temp_plan_for_problem_list_impl_int}, and interprets the abstract
  discharge locale @{locale numeric_tp_nta_reduction_bounds} -- which re-derives
  @{locale numeric_tp_nta_reduction_correctness} from the certificate.\<close>

locale numeric_valid_ground_plan_cert =
    numeric_ground_ast_problem_cert P fluent_lo fluent_hi +
    num_plan: numeric_temp_plan_for_problem_list_impl_int
      at_start_spec at_end_spec over_all_spec lower_spec upper_spec
      pre_spec adds_spec dels_spec init_spec goal_spec 0 props_spec actions_spec \<pi>
      "set o n_pre" "set o n_inv" "set o upds"
      "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
  for P :: ast_temporal_problem
    and fluent_lo :: "func \<Rightarrow> int"
    and fluent_hi :: "func \<Rightarrow> int"
    and \<pi> :: "(nat, ast_temporal_action_schema, int) temp_plan" +
  assumes num_valid_plan: "num_plan.num_rat_impl.num_valid_plan"

begin

text \<open>Interpret the abstract discharge locale @{locale numeric_tp_nta_reduction_bounds} at the raw ground
  parameters + the numeric plan \<open>\<pi>\<close>.  Its ancestors are present: @{locale numeric_tp_nta_reduction}
  (via @{text nred}), the UNPRIMED numeric plan locale (via @{text num_plan}), and the UNPRIMED
  @{locale tp_nta_reduction_correctness} (the propositional plan + the leaf's @{text unique_names}
  discharges).  Its three own assumptions are @{text num_valid} (from @{thm num_valid_plan}),
  @{text num_bound_inv} (the derived certificate, @{thm num_bound_inv}), and @{text num_goal_comp_ok}
  (a leaf assumption).\<close>

sublocale nbnd: numeric_tp_nta_reduction_bounds
  init_spec goal_spec at_start_spec at_end_spec over_all_spec lower_spec upper_spec
  pre_spec adds_spec dels_spec 0 props_spec actions_spec \<pi> act_to_name_spec prop_to_name_spec
  n_pre n_inv upds num_init num_goal nfluents fluent_to_name_spec fluent_lo fluent_hi const_to_int
  apply unfold_locales
  subgoal using num_valid_plan .
  subgoal using num_bound_inv .
  subgoal using num_goal_comp_ok .
  done

text \<open>The hypothesis-free abstract capstone, re-exported at this ground interpretation.\<close>
lemmas num_valid_plan_imp_form_holds = nbnd.num_valid_plan_imp_form_holds

end

subsection \<open>Rung 4 (discharged): the numeric-net lift and its contrapositive\<close>

context numeric_ground_ast_problem_cert
begin

text \<open>The numeric twin of @{thm [source] ground_ast_problem.valid_ground_plan_imp_form_holds}, over the
  \<^emph>\<open>numeric\<close> net @{term num_net_impl.sem}, with the boundedness plug now discharged from the static
  certificate: from a valid numeric plan for the ground problem the numeric Munta net reaches the goal
  formula.  No per-plan @{text num_seq_in_bounds} assumption.\<close>

lemma num_valid_ground_plan_imp_num_form_holds:
  assumes "\<exists>\<pi>. numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi>"
  shows "num_net_impl.sem, num_a\<^sub>0 \<Turnstile> ndefs.reach_formula"
proof -
  obtain \<pi> where "numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi>"
    using assms by blast
  then interpret x: numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi> .
  show ?thesis
    using x.num_valid_plan_imp_form_holds
    unfolding num_a\<^sub>0_def x.nbnd.num_a\<^sub>0_def by simp
qed

corollary num_net_form_not_sat_imp_no_valid_ground_plan:
  assumes "\<not>(num_net_impl.sem, num_a\<^sub>0 \<Turnstile> ndefs.reach_formula)"
  shows "\<not>(\<exists>\<pi>. numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi>)"
  using num_valid_ground_plan_imp_num_form_holds assms by blast

end

end

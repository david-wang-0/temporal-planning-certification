theory Ground_PDDL_Numeric_NTA_Reduction_Correctness
  imports
    Ground_PDDL_NTA_Reduction_Correctness
    Ground_PDDL_Numeric_Problem_Defs
    "TP_NTA_Reduction.TP_NTA_Reduction_Correctness_Numeric"
begin

text \<open>\<^bold>\<open>NUMERIC_EXEC_PLAN WP-A\<close> -- Rung 4 over the \<^emph>\<open>numeric\<close> net. The numeric twin of
  @{text ground_ast_problem.valid_ground_plan_imp_form_holds}
  (theory @{text Ground_PDDL_NTA_Reduction_Correctness}): interpret
  @{text numeric_tp_nta_reduction_correctness} at the ground numeric problem (via the numeric leaf
  @{text numeric_ground_ast_problem}) and lift the abstract, hypothesis-free capstone
  @{text numeric_tp_nta_reduction_correctness.num_valid_plan_imp_form_holds} to a ground-level
  corollary over @{text num_net_impl}, under a \<open>\<exists>\<pi>. numeric_valid_ground_plan \<dots> \<pi>\<close> hypothesis.

  Three steps: (1) discharge @{locale numeric_tp_nta_reduction} at the raw ground parameters from the
  leaf's static assumptions (@{text nred}), and hoist the plan-free numeric net @{text num_net_impl} /
  pre-init config @{term num_a\<^sub>0} into the leaf; (2) a plan-carrying locale
  @{text numeric_valid_ground_plan} (twin of @{text valid_ground_plan}) that interprets
  @{text numeric_tp_nta_reduction_correctness}; (3) the Rung-4 lemma
  @{text num_valid_ground_plan_imp_num_form_holds} and its contrapositive
  @{text num_net_form_not_sat_imp_no_valid_ground_plan}.\<close>

subsection \<open>The numeric static reduction, discharged from the leaf assumptions\<close>

text \<open>The numeric leaf @{locale numeric_ground_ast_problem} restates -- one-for-one, over the DEFINED
  ground data -- exactly the @{locale numeric_tp_nta_reduction} static assumptions.  We package them as
  a @{command sublocale} interpretation over the raw ground parameters, so the numeric net
  @{const numeric_tp_nta_reduction_defs.num_timed_automaton_net} and the grounder-match well-formedness
  are in scope at the ground level.\<close>

context numeric_ground_ast_problem
begin

text \<open>The numeric network's Munta semantics and pre-init configuration are functions of \<^emph>\<open>plan-free\<close>
  data only (the augmented automata @{const numeric_tp_nta_reduction_defs.num_timed_automaton_net} and
  variable bounds @{const numeric_tp_nta_reduction_defs.num_all_vars}, both from @{text nred}).  We hoist
  the @{locale Simple_Network_Impl} interpretation and the pre-init config @{term num_a\<^sub>0} into the
  plan-free leaf context, mirroring @{locale numeric_tp_nta_reduction_correctness} (lines 80/88); the
  plan-carrying interpretation's @{text ncorr.num_net_impl}/@{text ncorr.num_a\<^sub>0} coincide with these
  definitionally (same plan-free arguments).\<close>

sublocale num_net_impl: Simple_Network_Impl
  ndefs.num_timed_automaton_net ndefs.net_broadcast ndefs.num_net_bounds .

definition "num_a\<^sub>0 = (ndefs.init_locs, map_of ndefs.num_init_vars, (\<lambda>_::String.literal. 0::real))"

end

subsection \<open>The numeric plan-carrying locale\<close>

text \<open>The numeric twin of @{locale valid_ground_plan}: the numeric admission leaf plus a numeric plan
  \<open>\<pi>\<close> (a reduction-level @{typ \<open>(nat, ast_temporal_action_schema, int) temp_plan\<close>}) and the numeric
  plan-validity facts.  It extends the numeric admission leaf @{locale numeric_ground_ast_problem}
  together with the UNPRIMED numeric plan-carrying locale
  @{locale numeric_temp_plan_for_problem_list_impl_int} at the raw ground parameters -- which yields the
  propositional plan-validity fixes @{text vp} / @{text nso} / @{text pap} as locale assumptions
  (mirroring @{locale temp_plan_for_problem_list_impl_int}) and brings the @{text num_plan.num_rat_impl}
  refinement and @{text num_plan.rat_impl.htpl} into the header scope so the @{text num_seq_in_bounds}
  plug can be stated.

  \<^bold>\<open>WP-E plug (@{text num_seq_in_bounds}), supplied by the boundedness analysis; assumption here.\<close> It is
  the range-boundedness reachability invariant and is soundness-critical -- reserved for the human WP-E
  boundedness design, NOT discharged from anything.  @{text num_valid} (numeric plan validity) is carried
  as the assumption @{text num_valid_plan}; at the Rung-4 lift it is supplied by the existential plan
  hypothesis, exactly as @{text valid_ground_plan} supplies propositional validity.\<close>

locale numeric_valid_ground_plan =
    numeric_ground_ast_problem P fluent_lo fluent_hi +
    num_plan: numeric_temp_plan_for_problem_list_impl_int'
      at_start_spec at_end_spec over_all_spec lower_spec upper_spec
      pre_spec adds_spec dels_spec init_spec goal_spec 0 props_spec actions_spec \<pi>
      "set o n_pre" "set o n_inv" "set o upds"
      "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
  for P :: ast_temporal_problem
    and fluent_lo :: "func \<Rightarrow> int"
    and fluent_hi :: "func \<Rightarrow> int"
    and \<pi> :: "(nat, ast_temporal_action_schema, int) temp_plan" +
  assumes num_valid_plan: "num_plan.num_rat_impl.num_valid_plan"
      \<comment> \<open>WP-E plug (num_seq_in_bounds), supplied by the boundedness analysis; assumption here.\<close>
      and num_seq_in_bounds:
            "\<And>M i. num_plan.num_rat_impl.num_valid_state_sequence M
               \<Longrightarrow> snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)
               \<Longrightarrow> i \<le> length num_plan.rat_impl.htpl
               \<Longrightarrow> ndefs.fluent_in_bounds (snd (M i))"

begin

text \<open>Interpret the abstract numeric correctness locale @{locale numeric_tp_nta_reduction_correctness}
  at the raw ground parameters + the numeric plan \<open>\<pi>\<close>.  Its three ancestor layers are already present:
  @{locale numeric_tp_nta_reduction} (via @{text nred}), the UNPRIMED numeric plan locale (via
  @{text num_plan}), and the UNPRIMED @{locale tp_nta_reduction_correctness} (the propositional plan +
  the leaf's @{text unique_names} discharges).  Its three own assumptions are @{text num_valid} (from
  @{thm num_valid_plan}), @{text num_seq_in_bounds} (the WP-E plug), and @{text num_goal_comp_ok}
  (a leaf assumption); @{text const_to_int_of_int} (a leaf lemma) is now inherited from the base
  @{locale numeric_tp_nta_reduction} and already discharged there via @{text nred}.\<close>

sublocale ncorr: numeric_tp_nta_reduction_correctness'
  init_spec goal_spec at_start_spec at_end_spec over_all_spec lower_spec upper_spec
  pre_spec adds_spec dels_spec 0 props_spec actions_spec \<pi> act_to_name_spec prop_to_name_spec
  n_pre n_inv upds num_init num_goal nfluents fluent_to_name_spec fluent_lo fluent_hi const_to_int
  by unfold_locales
     (fact num_plan.vp num_plan.nso num_plan.pap
           upds_functional_start upds_functional_end
           upds_no_cross_read_start upds_no_cross_read_end fluent_bounds_valid
           snap_upds_nexp_ok_start snap_upds_nexp_ok_end
           snap_pre_comp_ok_start snap_pre_comp_ok_end snap_inv_comp_ok
           num_init_val_ok const_to_int_of_int
           snap_writes_nfluents_start snap_writes_nfluents_end
           num_valid_plan num_seq_in_bounds num_goal_comp_ok
           fluent_to_name_spec_inj)+

text \<open>The hypothesis-free abstract capstone, re-exported at this ground interpretation.\<close>
lemmas num_valid_plan_imp_form_holds = ncorr.ref_correctness.num_valid_plan_imp_form_holds

end

subsection \<open>Rung 4: the numeric-net lift and its contrapositive\<close>

context numeric_ground_ast_problem
begin

text \<open>The numeric twin of @{thm [source] ground_ast_problem.valid_ground_plan_imp_form_holds}, over the
  \<^emph>\<open>numeric\<close> net @{term num_net_impl.sem} (not the additive-tracking propositional shortcut): from the
  existence of a valid, bounded numeric plan for the ground problem the numeric Munta net reaches the
  goal formula.  Proved by @{command interpret}ing the plan-carrying locale
  @{locale numeric_valid_ground_plan} on the obtained plan and firing the abstract capstone
  @{thm [source] numeric_tp_nta_reduction_correctness.num_valid_plan_imp_form_holds}; the interpretation's
  @{text ncorr} net/config/formula coincide definitionally with the plan-free leaf
  @{term num_net_impl.sem} / @{term num_a\<^sub>0} / @{term ndefs.reach_formula}.

  The @{term num_seq_in_bounds} WP-E plug is threaded through the plan predicate's locale assumption
  (see @{locale numeric_valid_ground_plan}).\<close>

lemma num_valid_ground_plan_imp_num_form_holds:
  assumes "\<exists>\<pi>. numeric_valid_ground_plan P fluent_lo fluent_hi \<pi>"
  shows "num_net_impl.sem, num_a\<^sub>0 \<Turnstile> ndefs.reach_formula"
proof -
  obtain \<pi> where "numeric_valid_ground_plan P fluent_lo fluent_hi \<pi>"
    using assms by blast
  then interpret x: numeric_valid_ground_plan P fluent_lo fluent_hi \<pi> .
  show ?thesis
    using x.num_valid_plan_imp_form_holds
    unfolding num_a\<^sub>0_def x.ncorr.ref_correctness.num_a\<^sub>0_def by simp
qed

corollary num_net_form_not_sat_imp_no_valid_ground_plan:
  assumes "\<not>(num_net_impl.sem, num_a\<^sub>0 \<Turnstile> ndefs.reach_formula)"
  shows "\<not>(\<exists>\<pi>. numeric_valid_ground_plan P fluent_lo fluent_hi \<pi>)"
  using num_valid_ground_plan_imp_num_form_holds assms by blast

end

end

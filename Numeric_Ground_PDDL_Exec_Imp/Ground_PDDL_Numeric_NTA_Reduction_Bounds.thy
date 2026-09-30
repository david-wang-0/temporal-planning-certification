theory Ground_PDDL_Numeric_NTA_Reduction_Bounds
  imports
    Ground_PDDL_Numeric_NTA_Reduction_Correctness
    "TP_NTA_Reduction_Numeric.TP_NTA_Reduction_Numeric_Inference"
begin

text \<open>\<^bold>\<open>NUMERIC_EXEC_PLAN WP-D INTEGRATION\<close> -- discharge the soundness-critical @{text num_seq_in_bounds}
  plug at the ground problem from the VERIFIED interval bound inference
  (@{text \<open>ndefs.reduction_ref_impl.inferred_box\<close>}, theory @{text TP_NTA_Reduction_Numeric_Inference}): the inference's own
  result is the certificate.

  WP-A (@{text Ground_PDDL_Numeric_NTA_Reduction_Correctness}) carried
  @{text num_seq_in_bounds} as a per-plan locale assumption of @{locale numeric_valid_ground_plan}.
  Here it is \<^emph>\<open>derived\<close>: when the inference run over the plan-free ground data returns the declared
  fluent box (@{text \<open>ndefs.reduction_ref_impl.inferred_box = Some (\<lambda>f. (fluent_lo f, fluent_hi f))\<close>}), the reduction-native
  @{text \<open>nred'.num_bound_inv\<close>} follows via @{text inferred_box_imp_num_bound_inv}, and the abstract
  discharge locale @{locale numeric_tp_nta_reduction_bounds'} turns that certificate into
  @{locale numeric_tp_nta_reduction_correctness} (via @{text num_seq_in_bounds_derived}).
  (The eval-checkable re-check @{text \<open>is_gbound_inv'\<close>} of theory @{text TP_NTA_Reduction_Numeric_Bounds}
  stays in the abstract layer; it is no longer used here.)

  So the ground plan predicate here (@{text numeric_valid_ground_plan_cert}) no longer bundles the
  soundness-critical reachability invariant: it is a genuinely valid numeric plan, with boundedness
  supplied once, statically, at the problem level.\<close>

subsection \<open>The inferred bound certificate at the ground problem (plan-free)\<close>

text \<open>The certificate @{text \<open>ndefs.reduction_ref_impl.inferred_box = Some (\<lambda>f. (fluent_lo f, fluent_hi f))\<close>} is a property of
  the plan-free ground data (@{text num_init}, every relaxed snap's updates/guards, the declared fluents):
  the verified inference computes the box, and the leaf's @{text fluent_lo}/@{text fluent_hi} are exactly
  its components.  We assume it here and derive the reduction-native certificate
  @{text \<open>nred'.num_bound_inv\<close>}.\<close>

text \<open>Interpret the AXIOM numeric reduction @{locale numeric_tp_nta_reduction} at the injective
  @{const AtStart}/@{const AtEnd} snaps -- the SAME parameters at which the leaf's
  @{text ndefs.reduction_ref_impl} (a @{locale numeric_tp_nta_reduction_defs}) is instantiated -- so the
  inference @{text inferred_box} and its discharge @{text inferred_box_imp_num_bound_inv} /
  @{text num_bound_inv} (the latter two live only in the axiom locale @{locale numeric_tp_nta_reduction})
  are in scope at the ground level.  The propositional
  injective base (incl. \<open>snaps_disj\<close>) is inherited from @{text ndefs.reduction_ref_impl}; the 14
  numeric-wf assumptions are discharged from the leaf assumptions (the raw-snap facts \<open>upds (at_start_spec a)\<close>
  bridge to the injective \<open>app_snap upds (AtStart a)\<close> by \<open>app_snap.simps\<close>), and the
  \<open>unique_names fluent_to_name_spec\<close> obligation from \<open>fluent_to_name_spec_inj\<close>.\<close>
context numeric_ground_ast_problem
begin

sublocale nred': numeric_tp_nta_reduction
  "imp_defs.rat_impl.list_inter props_spec init_spec" "imp_defs.rat_impl.list_inter props_spec goal_spec"
  AtStart AtEnd imp_defs.rat_impl.over_all_restr_list lower_spec upper_spec
  imp_defs.rat_impl.pre_imp_restr_list imp_defs.rat_impl.add_imp_list imp_defs.rat_impl.del_imp_list
  0 props_spec actions_spec act_to_name_spec prop_to_name_spec
  "imp_defs.rat_impl.set_impl.app_snap n_pre" n_inv "imp_defs.rat_impl.set_impl.app_snap upds"
  num_init num_goal nfluents fluent_to_name_spec fluent_lo fluent_hi const_to_int
  apply unfold_locales
  apply (simp_all add: upds_functional_start upds_functional_end
      upds_no_cross_read_start upds_no_cross_read_end fluent_bounds_valid
      num_init_val_ok const_to_int_of_int
      snap_writes_nfluents_start snap_writes_nfluents_end
      snap_upds_nexp_ok_start snap_upds_nexp_ok_end
      snap_pre_comp_ok_start snap_pre_comp_ok_end snap_inv_comp_ok
      fluent_to_name_spec_inj)
  done

end

text \<open>The inference @{text inferred_box} is a constant of the NO-assumption locale
  @{locale numeric_tp_nta_reduction_defs}, whose instance at these parameters was registered first as
  @{text ndefs.reduction_ref_impl}; so its ground name is @{text ndefs.reduction_ref_impl.inferred_box}
  (the @{text nred'} registration adds names only for the axiom locale's own constants and facts, e.g.
  @{text \<open>nred'.num_bound_inv\<close>} and @{text \<open>nred'.inferred_box_imp_num_bound_inv\<close>}).\<close>

locale numeric_ground_ast_problem_cert =
    numeric_ground_ast_problem P fluent_lo fluent_hi
  for P :: ast_temporal_problem
    and fluent_lo :: "func \<Rightarrow> int"
    and fluent_hi :: "func \<Rightarrow> int" +
  assumes box_inferred: "ndefs.reduction_ref_impl.inferred_box = Some (\<lambda>f. (fluent_lo f, fluent_hi f))"
begin

text \<open>The verified inference's own result discharges the reduction-native
  @{term \<open>nred'.num_bound_inv\<close>} (still plan-free): the declared bounds are exactly the components
  of the inferred box.\<close>
lemma num_bound_inv: "nred'.num_bound_inv"
  by (rule nred'.inferred_box_imp_num_bound_inv[OF box_inferred]) simp_all
end

subsection \<open>The numeric plan-carrying locale, @{text num_seq_in_bounds} DISCHARGED\<close>
text \<open>The twin of @{locale numeric_valid_ground_plan}, but WITHOUT the @{text num_seq_in_bounds}
  assumption: it extends the certificate leaf @{locale numeric_ground_ast_problem_cert} (which supplies
  @{thm [source] numeric_ground_ast_problem_cert.num_bound_inv}) together with the PRIMED numeric
  plan-carrying locale @{locale numeric_temp_plan_for_problem_list_impl_int'}, and interprets the abstract
  discharge locale @{locale numeric_tp_nta_reduction_bounds'} -- which re-derives
  @{locale numeric_tp_nta_reduction_correctness} from the certificate.\<close>

locale numeric_valid_ground_plan_cert =
    numeric_ground_ast_problem_cert P fluent_lo fluent_hi +
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

begin

text \<open>Interpret the abstract discharge locale @{locale numeric_tp_nta_reduction_bounds'} at the raw ground
  parameters + the numeric plan \<open>\<pi>\<close>.  Its ancestors are present: the PRIMED @{locale tp_nta_reduction_correctness'}
  and the PRIMED numeric plan locale (via @{text num_plan}).  Its own assumptions are the leaf numeric-wf,
  @{text num_valid} (from @{thm num_valid_plan}), @{text bound_inv} (the derived certificate
  @{thm num_bound_inv}, i.e. @{text \<open>nred'.num_bound_inv\<close>}), and @{text num_goal_comp_ok} (a leaf
  assumption).  Discharged order-independently, exactly as the committed correctness re-point discharges
  @{text ncorr}, but with @{text num_seq_in_bounds} replaced by @{text num_bound_inv}.\<close>

sublocale nbnd: numeric_tp_nta_reduction_bounds'
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
           num_valid_plan num_bound_inv num_goal_comp_ok
           fluent_to_name_spec_inj)+

text \<open>The hypothesis-free abstract capstone, re-exported at this ground interpretation.\<close>
lemmas num_valid_plan_imp_form_holds = nbnd.ref_bounds.num_valid_plan_imp_form_holds

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
    unfolding num_a\<^sub>0_def x.nbnd.ref_bounds.num_a\<^sub>0_def by simp
qed

corollary num_net_form_not_sat_imp_no_valid_ground_plan:
  assumes "\<not>(num_net_impl.sem, num_a\<^sub>0 \<Turnstile> ndefs.reach_formula)"
  shows "\<not>(\<exists>\<pi>. numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi>)"
  using num_valid_ground_plan_imp_num_form_holds assms by blast

end

end

theory Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl
  imports
    "PDDL_TP_Reduction.Ground_PDDL_Numeric_NTA_Reduction_Impl"
    Ground_PDDL_Numeric_NTA_Reduction_Bounds
begin

text \<open>\<^bold>\<open>WP-D (no per-plan bounds).\<close> Compose the executable numeric net refinement (WP-C,
  @{thm [source] numeric_ground_ast_problem.num_model_checking_problem_refine}) with the
  \<^emph>\<open>bounds-discharged\<close> capstone (WP-D integration,
  @{thm [source] numeric_ground_ast_problem_cert.num_net_form_not_sat_imp_no_valid_ground_plan}) so the
  \<^emph>\<open>executable\<close> soundness concludes over @{text numeric_valid_ground_plan_cert} -- a genuinely valid
  numeric plan, with boundedness supplied ONCE, statically, by the @{text \<open>is_gbound_inv'\<close>} certificate
  (bundled in @{locale numeric_ground_ast_problem_cert}), NOT as a per-plan @{text num_seq_in_bounds}
  assumption.

  The two ingredients live in separate theories (the exec net + its refines in
  @{theory PDDL_TP_Reduction.Ground_PDDL_Numeric_NTA_Reduction_Impl}; the cert locale + capstone in
  @{theory bound_inference.Ground_PDDL_Numeric_NTA_Reduction_Bounds}); this theory imports both.\<close>

subsection \<open>The cert-level model-checking refinement\<close>

context numeric_ground_ast_problem_cert
begin

text \<open>The numeric twin of @{thm [source] numeric_ground_ast_problem.num_model_checking_problem_refine},
  but firing the bounds-discharged @{text \<open>_cert\<close>} capstone: if the Munta semantics of the executable
  numeric net does not reach the goal formula, then the ground problem has no valid numeric plan
  \<^emph>\<open>at all\<close> (no residual @{text num_seq_in_bounds} obligation).  Proved exactly like the WP-C refinement
  (rewrite the executable net / bounds / initial configuration / formula to the abstract @{text ndefs}
  net via the inherited refines), but the capstone in scope is
  @{locale numeric_ground_ast_problem_cert}'s own @{text num_net_form_not_sat_imp_no_valid_ground_plan}
  (shadowing the inherited @{locale numeric_ground_ast_problem} one).\<close>

lemma num_model_checking_problem_refine_cert:
  "\<not> Simple_Network_Impl.sem num_net_automata' ndefs.net_broadcast
        (num_net_bounds' fluent_lo fluent_hi),
      (num_init_locs', map_of (num_init_vars' fluent_lo fluent_hi), (\<lambda>_. 0))
      \<Turnstile> num_reach_formula'
   \<Longrightarrow> \<not>(\<exists>\<pi>. numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi>)"
  using num_net_form_not_sat_imp_no_valid_ground_plan
  unfolding num_net_automata_refine num_net_bounds_refine
  unfolding num_init_locs_refine num_init_vars_refine num_reach_formula_refine
  unfolding num_a\<^sub>0_def[symmetric]
  by blast

end

subsection \<open>The cert-level network-assembly soundness\<close>

text \<open>The numeric twin of @{thm [source] check_and_make_numeric_network_and_plan}, but with the
  \<^bold>\<open>per-plan boundedness assumption removed\<close>: given (a) the executable admission check + network builder
  succeed and (b) the problem passes the static boundedness certificate (@{locale numeric_ground_ast_problem_cert}
  = the numeric admission leaf plus @{text \<open>is_gbound_inv'\<close>}), a Munta-unreachable executable numeric net
  proves there is \<^emph>\<open>no\<close> valid numeric plan for the ground problem -- the numeric-net certificate the whole
  pipeline aims at.\<close>

lemma check_and_make_numeric_network_and_plan_cert:
  assumes A: "check_and_make_numeric_network P fluent_lo fluent_hi
       = Inr (clocks, autos, ids_to_names, process_names_to_index,
              broadcast, automata, bounds, formula, init_locs, init_vars)"
      and cert: "numeric_ground_ast_problem_cert P fluent_lo fluent_hi"
  shows "\<not> (Simple_Network_Impl.sem automata broadcast bounds,
             (init_locs, map_of init_vars, (\<lambda>_. 0)) \<Turnstile> formula)
         \<longrightarrow> \<not>(\<exists>\<pi>. numeric_valid_ground_plan_cert P fluent_lo fluent_hi \<pi>)"
proof -
  have chk: "numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi = Inr ()"
    by (cases "numeric_ground_ast_problem_defs.check_numeric_ground_problem P fluent_lo fluent_hi")
       (use A in \<open>auto simp: check_and_make_numeric_network_def\<close>)
  have cdef: "check_and_make_numeric_network P fluent_lo fluent_hi = num_make_network_impl P fluent_lo fluent_hi"
    unfolding check_and_make_numeric_network_def chk by simp
  note mk = A[unfolded cdef]
  have eqs: "automata = numeric_ground_ast_problem_defs.num_net_automata' P"
      "broadcast = ground_ast_problem_defs.net_broadcast'"
      "bounds = numeric_ground_ast_problem_defs.num_net_bounds' P fluent_lo fluent_hi"
      "formula = numeric_ground_ast_problem_defs.num_reach_formula'"
      "init_locs = numeric_ground_ast_problem_defs.num_init_locs' P"
      "init_vars = numeric_ground_ast_problem_defs.num_init_vars' P fluent_lo fluent_hi"
    using mk by (simp_all add: num_make_network_impl_return_iff)
  interpret C: numeric_ground_ast_problem_cert P fluent_lo fluent_hi by (rule cert)
  have bc: "ground_ast_problem_defs.net_broadcast' = tp_nta_reduction_defs.net_broadcast"
    unfolding ground_ast_problem_defs.net_broadcast'_def C.ndefs.net_broadcast_def ..
  show ?thesis
    unfolding eqs bc
    using C.num_model_checking_problem_refine_cert
    by blast
qed

end

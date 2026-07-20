(* VENDORED Analysis-free slice of
   Formal-PDDL-Semantics/Temporal_Planning/Temporal_Continuous_Reduction.thy.
   Contains only the Analysis-free part the net builder needs: the syntactic temporal->continuous
   translation functions and the well-formedness equivalences (wf_ast_cont_problem_equiv etc.).
   The ODE/euclidean lemmas (upstream from line ~169, in locale list_of_pnes_vector_type) and the
   plan-embedding functions (temporal_to_continuous_plan / continuous_to_temporal_plan /
   intermediate_states) are intentionally omitted -- the reduction reasons via the discrete
   state-sequence semantics, not the continuous-plan validity reduction.
   TODO: upstream into an Analysis-free FPS session. *)
theory Temporal_Continuous_Reduction_Free
  imports Temporal_Planning_Discrete.Temporal_Happening_Semantics
    Temporal_Planning_Discrete.Temporal_Utils
    PDDL_Checker_Common
begin


fun temporal_to_continuous_action_body :: "ast_temporal_durative_action_body \<Rightarrow> ast_cont_change_action_body" where
"temporal_to_continuous_action_body (DurativeActionBody d c e) = ContChangeActionBody d c e []"

fun temporal_to_continuous_action_schema :: "ast_temporal_action_schema \<Rightarrow> ast_cont_action_schema" where
"temporal_to_continuous_action_schema (SimpleActionSchema h b) = ast_cont_action_schema.SimpleActionSchema h b" |
"temporal_to_continuous_action_schema (DurativeActionSchema h b) = ast_cont_action_schema.ContChangeActionSchema h (temporal_to_continuous_action_body b)"

definition temporal_to_continuous_domain :: "ast_temporal_domain \<Rightarrow> ast_cont_domain" where
"temporal_to_continuous_domain = ast_domain.map_ast_domain temporal_to_continuous_action_schema"

definition temporal_to_continuous_problem :: "ast_temporal_problem \<Rightarrow> ast_cont_problem" where
"temporal_to_continuous_problem = ast_problem.map_ast_problem temporal_to_continuous_action_schema"

lemma name_of_temporal_to_continuous_action_schema[simp]:
  "ast_cont_action_schema_name \<circ> temporal_to_continuous_action_schema = ast_temporal_action_schema_name"
  unfolding fun_eq_iff
  apply simp
  by (metis ast_cont_action_schema.sel(1,2) ast_temporal_action_schema.exhaust_sel temporal_to_continuous_action_schema.simps(1,2))

lemmas temporal_to_continuous_domain_sel =
  ast_domain.map_sel[
    where f = temporal_to_continuous_action_schema,
          folded temporal_to_continuous_domain_def]

lemmas temporal_to_continuous_problem_sel =
  ast_problem.map_sel[
    where f = temporal_to_continuous_action_schema,
    folded temporal_to_continuous_problem_def
    temporal_to_continuous_domain_def
  ]


context ast_temporal_domain
begin
sublocale ast_cont_domain: ast_cont_domain "temporal_to_continuous_domain D"
  .

end

context ast_temporal_domain
begin


lemma wf_temporal_action_schema_temporal_continuous[simp]:
   "wf_cont_action_schema (temporal_to_continuous_action_schema a) = wf_temporal_action_schema a"
proof(cases a)
  case (SimpleActionSchema x11 x12)
  then show ?thesis
    by (cases x12) (auto simp: Let_def)
next
  case (DurativeActionSchema x21 x22)
  then show ?thesis
    by (cases x22) (auto simp: Let_def)
qed

lemma wf_domain_signature_temporal_continuous[simp]:
  "ast_cont_domain.wf_domain_signature  = wf_domain_signature"
  by (cases D) (auto simp: temporal_to_continuous_domain_def)

lemma wf_ast_cont_domain_equiv: "ast_cont_domain.wf_cont_domain = wf_temporal_domain"
  unfolding ast_temporal_domain.wf_temporal_domain_def ast_cont_domain.wf_cont_domain_def
  unfolding temporal_to_continuous_domain_sel
  by simp
end

context ast_temporal_problem
begin
sublocale ast_cont_problem: ast_cont_problem "temporal_to_continuous_problem P"
  .

lemma wf_ast_cont_problem_equiv: "ast_cont_problem.wf_cont_problem \<longleftrightarrow> wf_temporal_problem"
  unfolding wf_temporal_problem_def ast_cont_problem.wf_cont_problem_def
  using wf_ast_cont_domain_equiv temporal_to_continuous_problem_sel temporal_to_continuous_domain_sel
  by presburger

lemma I_equiv: "I = ast_cont_problem.I"
  unfolding I_def ast_cont_problem.I_def
  unfolding temporal_to_continuous_problem_sel by simp

end

context wf_ast_temporal_problem
begin

sublocale wf_ast_cont_problem: wf_ast_cont_problem "temporal_to_continuous_problem P"
  using wf_ast_cont_problem_equiv
  unfolding wf_ast_cont_problem_def
  using wf_temporal_problem
  by simp
end

end

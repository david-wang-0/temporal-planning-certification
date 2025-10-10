theory PDDL_TP_Reduction
  imports "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics_Alt"
    "TP_NTA_Reduction.TP_NTA_Reduction_Model_Checking"
begin

context ast_problem
begin

definition "prop_spec = map pred (predicates D)"

definition "act_spec = actions D"

fun to_object::"object atom Formulas.formula \<Rightarrow> predicate" where
"to_object (Atom (predAtm x _)) = x"

definition "init_spec = I"

end

locale ground_ast_problem = ast_problem P 
  for P :: ast_problem
begin

sublocale tp_nta_reduction_model_checking' 
proof 

qed
end
end
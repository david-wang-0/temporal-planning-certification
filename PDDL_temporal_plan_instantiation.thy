theory PDDL_temporal_plan_instantiation
  imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
    Temporal_Plans
    Containers.Containers
begin

derive (linorder) compare rat

derive (eq) ceq predicate func atom object formula 
derive ccompare predicate func atom object formula
derive (no) cenum atom object formula
derive (rbt) set_impl func atom object formula

derive (rbt) mapping_impl object

derive linorder predicate func object atom "object atom formula"

context wf_ast_problem
begin
definition "objs \<equiv>  set (map fst (consts D @ objects P))"

definition "tos = {(ty, obj). obj \<in> objs \<and> is_obj_of_type obj ty}"

definition "ltos \<equiv> {(tys, objs). list_all2 (\<lambda>ty ob. (ty, ob) \<in> tos) tys objs}"

definition "preds \<equiv> {(predAtm n os)| n os ts. PredDecl n ts \<in> set (predicates D) \<and> (ts, os) \<in> ltos}"

definition "pddl_actions \<equiv> {(inst_snap_action a args At_Start, inst_snap_action a args Over_All, inst_snap_action a args At_End, inst_duration_const a)
          |a args. a \<in> set (actions D)}"

sublocale temp_planning_problem sorry
end

end
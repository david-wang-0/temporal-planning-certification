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

end
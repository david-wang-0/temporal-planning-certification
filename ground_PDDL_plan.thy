theory ground_PDDL_plan
imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
    Compilation                    
    Containers.Containers
begin

fun set_theoretic_formula::"'ent formula \<Rightarrow> bool" where
"set_theoretic_formula (Atom x) = True" |
"set_theoretic_formula (Not (Atom x)) = True" |
"set_theoretic_formula _ = False"

text \<open>This is the type of propositions\<close>
type_synonym pr = "object atom"

text \<open>Note, that this is not the type we will use as @{typ \<open>'snap_action\<close>}}, because we would
have to implement \<open>at_start\<close> as @{term \<open>fst\<close>}, which would make it violate injectivity.\<close>
datatype 'pr snap = 
  Snap (pre: "'pr list")
       (adds: "'pr list")
       (dels: "'pr list")

type_synonym ('t) dc = "duration_op \<times> 't"

text \<open>This is the actual type of action\<close>
datatype ('pr, 't) action = GroundAction
    (name: "string") 
    (s_snap: "'pr snap") 
    (oc: "'pr list") 
    (e_snap: "'pr snap")
    (d_const: "('t dc) option")

text \<open>These orderings are necessary for proofs\<close>
derive (linorder) compare rat 

derive (eq) ceq predicate func atom object formula 
derive ccompare predicate func atom object formula
derive (no) cenum atom object formula
derive (rbt) set_impl func atom object formula

derive (rbt) mapping_impl object

derive linorder predicate func object atom 
  "object atom formula"
  prod list ast_effect duration_op snap action

instantiation rat :: time
begin
instance apply standard
  apply (rule dense_order_class.dense, assumption)
  using zero_neq_one[symmetric] by (rule exI)
end

subsection \<open>Plan to problem\<close>


text \<open>A restriction of planning to a finite domain of actions and propositions. It should also be 
possible to derive the formulation of planning used for the compilation to timed automata from this. 
The the representations of the state is not necessarily finite, because the initial and final, and 
thus all states can be infinite in size.\<close>


locale ground_PDDL_planning =
  fixes props::   "('proposition::linorder) set"
    and actions:: "('proposition, rat) action set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
  assumes some_props:       "card props > 0"
      and some_actions:     "card actions > 0"
      and finite_props:     "finite props"
      and finite_actions:   "finite actions"
begin
                              

  definition lower_imp::"('proposition, rat) action \<rightharpoonup> rat lower_bound" where
  "lower_imp a \<equiv> (case d_const a of 
    (Some (duration_op.EQ, n)) \<Rightarrow> Some (lower_bound.GE n)
  | (Some (duration_op.GEQ, n)) \<Rightarrow> Some (lower_bound.GE n)
  | (Some (duration_op.LEQ, n)) \<Rightarrow> None
  | None \<Rightarrow> None)"
  
  definition upper_imp::"('proposition, rat) action \<rightharpoonup> rat upper_bound" where
  "upper_imp a \<equiv> (case d_const a of 
    (Some (duration_op.EQ, n)) \<Rightarrow> Some (upper_bound.LE n)
  | (Some (duration_op.GEQ, n)) \<Rightarrow> None
  | (Some (duration_op.LEQ, n)) \<Rightarrow> Some (upper_bound.LE n)
  | None \<Rightarrow> None)"

sublocale basic_temp_planning_problem props actions init goal s_snap e_snap "set o oc" 
  lower_imp upper_imp "set o pre" "set o adds" "set o dels" 0
  apply standard
  using some_props some_actions finite_props finite_actions by auto



end
end
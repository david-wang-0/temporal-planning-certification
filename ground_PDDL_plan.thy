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

datatype (act: 'a) snap_action = 
  AtStart 'a |
  AtEnd 'a

text \<open>A restriction of planning to a finite domain of actions and propositions. It should also be 
possible to derive the formulation of planning used for the compilation to timed automata from this. 
The the representations of the state is not necessarily finite, because the initial and final, and 
thus all states can be infinite in size.\<close>
locale finite_domain_planning =
  fixes props::   "('proposition::linorder) set"
    and acts::    "('action::linorder) set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and \<epsilon>::       "'time"
  assumes some_props:       "card props > 0"
      and some_actions:     "card acts > 0"
      and finite_props:     "finite props"
      and finite_actions:   "finite acts"
      and eps_range:        "0 \<le> \<epsilon>"
begin

  definition "init_imp = init \<inter> props"
  definition "goal_imp = goal \<inter> props"
  
  fun app_snap::"('snap_action \<Rightarrow> 'proposition set) \<Rightarrow> 'action snap_action \<Rightarrow> 'proposition set" where
  "app_snap f (AtStart a) = f (at_start a)" |
  "app_snap f (AtEnd a) = f (at_end a)"
  
  definition pre_imp::"'action snap_action \<Rightarrow> 'proposition set" where
  "pre_imp = (\<inter>) props o app_snap pre"
  
  definition add_imp::"'action snap_action \<Rightarrow> 'proposition set" where
  "add_imp = app_snap adds"
  
  definition del_imp::"'action snap_action \<Rightarrow> 'proposition set" where
  "del_imp = app_snap dels"

  definition over_all_imp::"'action \<Rightarrow> 'proposition set" where
  "over_all_imp = (\<inter>) props o over_all"

  sublocale temp_planning_problem props acts init_imp goal_imp AtStart AtEnd over_all_imp lower upper pre_imp add_imp del_imp \<epsilon>
  proof
    show "init_imp \<subseteq> props" "goal_imp \<subseteq> props" unfolding init_imp_def goal_imp_def by simp+
    show "inj_on AtStart acts" "inj_on AtEnd acts" unfolding inj_on_def by blast+
    show "AtStart ` acts \<inter> AtEnd ` acts = {}" by blast
    show "0 < card props" by (rule some_props)
    show "0 < card acts" by (rule some_actions)
    show "finite props" by (rule finite_props)
    show "finite acts" by (rule finite_actions)
    show "0 \<le> \<epsilon>" by (rule eps_range)
  qed 

  context 
    fixes \<pi>::"('i, 'action, 'time) temp_plan"
  begin
    (* PDDL plans must not modify equalities, but can use them in preconditions. *)
    definition act_mod_props where
      "act_mod_props a \<equiv> (
        let sp = (\<lambda>s. adds s \<union> dels s)
        in sp (at_start a) \<subseteq> props \<and> sp (at_end a) \<subseteq> props
       )"
  
    definition plan_acts_mod_props where
      "plan_acts_mod_props = (\<forall>(a, t, d) \<in> ran \<pi>. act_mod_props a)"
  
    (* If equalities are not modified, is there an equivalent plan which does not check equalities? Seems so. *)
    term "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon>"
  end
end

locale ground_PDDL_planning =
  fixes props::   "('proposition::linorder) set"
    and acts::    "('action::linorder) set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and \<epsilon>::       "'time"
  assumes some_props:       "card props > 0"
      and some_actions:     "card acts > 0"
      and finite_props:     "finite props"
      and finite_actions:   "finite acts"
begin


  definition lower_imp::"'pr action \<rightharpoonup> 'time lower_bound" where
  "lower_imp a \<equiv> (case d_const a of 
    (Some (duration_op.EQ, n)) \<Rightarrow> Some (lower_bound.GE n)
  | (Some (duration_op.GEQ, n)) \<Rightarrow> Some (lower_bound.GE n)
  | (Some (duration_op.LEQ, n)) \<Rightarrow> None
  | None \<Rightarrow> None)"
  
  definition upper_imp::"'pr action \<rightharpoonup> 'time upper_bound" where
  "upper_imp a \<equiv> (case d_const a of 
    (Some (duration_op.EQ, n)) \<Rightarrow> Some (upper_bound.LE n)
  | (Some (duration_op.GEQ, n)) \<Rightarrow> None
  | (Some (duration_op.LEQ, n)) \<Rightarrow> Some (upper_bound.LE n)
  | None \<Rightarrow> None)"
end
end
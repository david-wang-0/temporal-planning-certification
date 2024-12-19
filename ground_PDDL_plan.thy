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

type_synonym dc = "duration_op \<times> rat"

text \<open>This is the actual type of action\<close>
datatype 'pr action = GroundAction
    (name: "string") 
    (s_snap: "'pr snap") 
    (oc: "'pr list") 
    (e_snap: "'pr snap")
    (d_const: "dc option")

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

text \<open>Some additional definitions\<close>

text \<open>A plan is defined \<close>

definition mutex_snap_action::"pr snap \<Rightarrow> pr snap \<Rightarrow> bool" where
"mutex_snap_action a b = (
set (pre a) \<inter> (set (adds b) \<union> set (dels b)) \<noteq> {} \<or>
(set (adds a) \<inter> set (dels b)) \<noteq> {} \<or>
set (pre b) \<inter> (set (adds a) \<union> set (dels a)) \<noteq> {} \<or>
set (adds b) \<inter> set (dels a) \<noteq> {}
)"

definition apply_effects::"pr set \<Rightarrow> pr snap set \<Rightarrow> pr set" where
"apply_effects M S \<equiv> (M - \<Union>(set ` dels ` S)) \<union> \<Union>(set ` adds ` S)"

text \<open>This is one formulation of a plan. Thinking about the plan is our 
main goal, so we lift this out of the context of the problem. A plan is valid with respect to
an initial state and a goal and nothing else. A plan could be infinite.\<close>
type_synonym ('i, 'a, 't) temp_plan = "'i \<rightharpoonup> ('a \<times> 't \<times> 't)"
context
fixes \<pi>::"(nat, pr action, rat) temp_plan"
begin

definition htps::"rat set" where
"htps \<equiv> {t |a t d. (a, t, d) \<in> ran \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> ran \<pi>}"

definition htpl::"rat list" where
"htpl = sorted_list_of_set htps"

abbreviation time_index::"nat \<Rightarrow> rat" where
"time_index \<equiv> ((!) htpl)"

text \<open>Happening Sequences\<close>

definition plan_happ_seq::"(rat \<times> pr snap) set" where
"plan_happ_seq \<equiv> 
    {(t, s_snap a) | a t d. (a, t, d) \<in> ran \<pi>} 
  \<union> {(t + d, e_snap a) | a t d. (a, t, d) \<in> ran \<pi>}"

definition happ_at::"(rat \<times> pr snap) set \<Rightarrow> rat \<Rightarrow> pr snap set" where
"happ_at B t \<equiv> {s. (t, s) \<in> B}"

text \<open>Invariants\<close>
definition plan_inv_seq::"(pr, rat) invariant_sequence" where
"plan_inv_seq \<equiv>
  {(t', set (oc a)) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"(pr, rat) invariant_sequence \<Rightarrow> rat \<Rightarrow> pr set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"

subsubsection \<open>Non-mutex happening sequence\<close>

text \<open>This definition arose from the statement in \<^cite>\<open>Gigante2020\<close>, that every at-start 
snap-action interferes with itself for self-overlap. Therefore, we can assume the same for at-end
snap-actions. Moreover, in their definition of a planning problem, the assumption is made that 
no two actions share snap-actions. at-start(a) \<noteq> at-start(b) and at-start(a) \<noteq> at_end(b) and at-start(a) \<noteq> at-end(a).\<close>
definition nm_happ_seq::"(rat \<times> pr snap) set \<Rightarrow> rat \<Rightarrow> bool" where
"nm_happ_seq B \<epsilon>\<equiv> 
  (\<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> ((a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b) 
    \<and> (a = b \<longrightarrow> t = u)))
  \<and> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"

subsubsection \<open>Valid state sequence\<close>

definition valid_state_sequence::"pr state_sequence \<Rightarrow> bool" where
"valid_state_sequence M \<equiv> (
  let 
    t = time_index;
    Inv = plan_inv_seq;
    B = plan_happ_seq
  in
    (\<forall>i. i < length htpl \<longrightarrow> (
      let 
        S = happ_at B (t i);
        pres = \<Union>(set ` pre ` S);
        invs = invs_at Inv (t i)
      in
        apply_effects (M i) S = (M (Suc i))
        \<and> invs \<subseteq> (M i)
        \<and> pres \<subseteq> (M i)))
)"


definition no_self_overlap::"bool" where
"no_self_overlap \<equiv> \<not>(\<exists>i j a t d u e. i \<noteq> j
  \<and> i \<in> dom \<pi>
  \<and> j \<in> dom \<pi>
  \<and> Some (a, t, d) = \<pi> i
  \<and> Some (a, u, e) = \<pi> j
  \<and> t \<le> u \<and> u \<le> t + d)"

definition satisfies_duration_bounds::"pr action \<Rightarrow> rat \<Rightarrow> bool" where
"satisfies_duration_bounds a t \<equiv> (
  case (d_const a) of 
    Some (duration_op.EQ, v) \<Rightarrow> (t = v)
  | Some (LEQ, v) \<Rightarrow> (t \<le> v)
  | Some (GEQ, v) \<Rightarrow> (t \<ge> v)
  | None \<Rightarrow> True)"

definition durations_positive::bool where
"durations_positive \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> 0 < d"

definition durations_valid::bool where
"durations_valid \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> satisfies_duration_bounds a d"

definition valid_plan::"pr set \<Rightarrow> pr set \<Rightarrow> rat \<Rightarrow> bool" where
"valid_plan initial_state goal_cond \<epsilon> \<equiv> \<exists>M. 
    valid_state_sequence M
    \<and> no_self_overlap
    \<and> M 0 = initial_state
    \<and> goal_cond \<subseteq> M (length htpl)
    \<and> durations_positive
    \<and> durations_valid
    \<and> nm_happ_seq plan_happ_seq \<epsilon>"
end

datatype (act: 'a) snap_action = 
  AtStart 'a |
  AtEnd 'a

text \<open>A finite restriction \<close>
locale propositional_temporal_problem =
  fixes props::         "pr set"
    and acts::          "pr action set"
    and initial_state:: "pr set"
    and goal_cond::     "pr set"
    and \<epsilon>::             "rat"
  assumes some_props:     "card props > 0"
    and some_actions:     "card acts > 0"
    and finite_props:     "finite props"
    and finite_actions:   "finite acts"
begin

definition plan_actions_in_problem::"(pr action \<times> rat \<times> rat) list \<Rightarrow> bool" where
"plan_actions_in_problem \<pi> \<equiv> \<forall>a t d. (a, t, d) \<in> set \<pi> \<longrightarrow> a \<in> acts"

fun app_snap::"('pr snap \<Rightarrow> 'pr set) \<Rightarrow> 'pr action snap_action \<Rightarrow> 'pr set" where
"app_snap f (AtStart a) = f (s_snap a)" |
"app_snap f (AtEnd a) = f (e_snap a)"

definition over_all_imp::"'pr action \<Rightarrow> 'pr set" where
"over_all_imp = set o oc"

definition lower_imp::"'pr action \<rightharpoonup> rat lower_bound" where
"lower_imp a \<equiv> (case d_const a of 
  (Some (duration_op.EQ, n)) \<Rightarrow> Some (lower_bound.GE n)
| (Some (duration_op.GEQ, n)) \<Rightarrow> Some (lower_bound.GE n)
| (Some (duration_op.LEQ, n)) \<Rightarrow> None
| None \<Rightarrow> None)"


definition upper_imp::"'pr action \<rightharpoonup> rat upper_bound" where
"upper_imp a \<equiv> (case d_const a of 
  (Some (duration_op.EQ, n)) \<Rightarrow> Some (upper_bound.LE n)
| (Some (duration_op.GEQ, n)) \<Rightarrow> None
| (Some (duration_op.LEQ, n)) \<Rightarrow> Some (upper_bound.LE n)
| None \<Rightarrow> None)"

definition pre_imp::"'pr action snap_action \<Rightarrow> 'pr set" where
"pre_imp = app_snap (set o pre)"

definition add_imp::"'pr action snap_action \<Rightarrow> 'pr set" where
"add_imp = app_snap (set o adds)"

definition del_imp::"'pr action snap_action \<Rightarrow> 'pr set" where
"del_imp = app_snap (set o dels)"

sublocale temp_planning_problem 
  props 
  actions 
  initial_state 
  goal_cond 
  AtStart 
  AtEnd 
  over_all_imp 
  lower_imp
  upper_imp
  pre_imp
  add_imp
  del_imp
  \<epsilon>
 
end
end
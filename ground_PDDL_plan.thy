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
    (d_const: "'t dc option")

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

abbreviation "snap_pre \<equiv> set o pre"
abbreviation "snap_adds \<equiv> set o adds"
abbreviation "snap_dels \<equiv> set o dels"


locale ground_PDDL_planning =
  fixes props::   "('proposition::linorder) set"
    and actions:: "('proposition, rat) action set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
  assumes some_props:       "card props > 0"
      and some_actions:     "card actions > 0"
      and finite_props:     "finite props"
      and finite_actions:   "finite actions"
      and act_mod_fluents:  "const_valid_domain props s_snap e_snap snap_adds snap_dels actions"
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


  abbreviation pre_imp'::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
  "pre_imp' \<equiv> \<lambda>x. (pre_imp s_snap e_snap snap_pre x \<inter> props)"

  abbreviation add_imp'::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
  "add_imp' \<equiv> add_imp s_snap e_snap snap_adds"
  
  abbreviation del_imp'::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
  "del_imp' \<equiv> del_imp s_snap e_snap snap_dels"

  abbreviation "init' \<equiv> init \<inter> props"
  
  abbreviation "goal' \<equiv> goal \<inter> props"                 
  
  abbreviation "over_all' \<equiv> (\<lambda>a. (set o oc) a \<inter> props)"

  sublocale finite_props_temp_planning_problem 
    init' goal' AtStart AtEnd over_all' lower_imp upper_imp 
    pre_imp' add_imp' del_imp' 0 props actions
    apply standard
    using finite_props some_props some_actions finite_actions act_mod_fluents 
    unfolding add_imp_def del_imp_def fluent_domain_def act_ref_fluents_def pre_imp_def 
      const_valid_domain_def act_mod_fluents_def inj_on_def by auto

  context
    fixes \<pi>::"('i, ('proposition, rat) action, 'time) temp_plan"
    assumes plan_actions_in_problem: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
        and actions_wf: "\<forall>a \<in> actions. act_consts props AtStart AtEnd over_all' pre_imp add_imp del_imp' a \<subseteq> init - props"
        and dom_wf: "goal - props \<subseteq> init - props" 
  begin
  lemma valid_plan_alt:
    "valid_plan \<pi> init goal AtStart AtEnd over_all' pre_imp' add_imp del_imp \<epsilon>
      \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd over_all' lower_imp upper_imp pre_imp' del_imp' del_imp' \<epsilon>"
  proof -
    have "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon> 
    \<longleftrightarrow> valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>"
      using valid_plan_in_finite_props plan_actions_in_problem actions_wf dom_wf by blast
    moreover
    have "valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>
    \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd over_all' lower upper pre_imp' (add_imp at_start at_end adds) (del_imp at_start at_end dels) \<epsilon>"
      apply (rule valid_plan_equiv_if_snaps_functionally_equiv)
      unfolding pre_imp_def add_imp_def del_imp_def by simp+
    ultimately
    show ?thesis by simp
  qed
end
sublocale finite_fluent_temp_planning_problem' init goal s_snap e_snap "set o oc" 
  lower_imp upper_imp snap_pre snap_adds snap_dels 0 props actions 
  apply unfold_locales
  using some_props some_actions finite_props finite_actions act_mod_fluents by auto
text \<open>The above locale is a superlocale of the locale below. Now, we can obtain the timed automaton\<close>

sublocale ta_temp_planning 
    init' goal' AtStart AtEnd over_all' lower_imp upper_imp
    pre_imp' add_imp' del_imp' 0 props actions 
  apply standard
  unfolding inj_on_def by auto
end


context
  fixes ty_ent::  "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
    and of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
    and sig::     "predicate \<rightharpoonup> type list"
begin
  definition is_of_type :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
    "is_of_type v T \<longleftrightarrow> (
      case ty_ent v of
        Some vT \<Rightarrow> of_type vT T
      | None \<Rightarrow> False)"
  
  fun wf_pred_atom :: "predicate \<times> 'ent list \<Rightarrow> bool" where
    "wf_pred_atom (p,vs) \<longleftrightarrow> (
      case sig p of
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

  fun wf_pred :: "'ent atom \<Rightarrow> bool" where
    "wf_pred (predAtm p vs) \<longleftrightarrow> wf_pred_atom (p,vs)"
  | "wf_pred (eqAtm a b) \<longleftrightarrow> False"

  fun wf_atom :: "'ent atom \<Rightarrow> bool" where
    "wf_atom (predAtm p vs) \<longleftrightarrow> wf_pred_atom (p,vs)"
  | "wf_atom (eqAtm a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

  fun wf_snap::"'ent atom snap \<Rightarrow> bool" where
    "wf_snap (Snap ps as ds) = (list_all wf_atom ps \<and> list_all wf_pred as \<and> list_all wf_pred ds)"

  fun wf_action::"('ent atom, 'time::time) action \<Rightarrow> bool" where
    "wf_action (GroundAction n as over_all_cond es dc) = (wf_snap as \<and> list_all wf_atom over_all_cond \<and> wf_snap es)"
end

locale ground_PDDL_planning_with_equality = 
  ground_PDDL_planning fluent_preds actions init goal 
    for fluent_preds::   "('ent::linorder) atom set"
    and actions:: "('ent atom, rat) action set"
    and init::    "'ent atom set"
    and goal::    "'ent atom set"
   (* fixes ty_ent::  "'ent \<rightharpoonup> type"
    and of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
    and sig::     "predicate \<rightharpoonup> type list" *)
     (*  assumes wf_preds:         "\<forall>p \<in> preds. wf_pred ty_ent of_type sig p"
      and wf_init:          "\<forall>p \<in> init. wf_pred ty_ent of_type sig p"
      and wf_goal:          "\<forall>p \<in> goal. wf_pred ty_ent of_type sig p"
      and wf_actions:       "\<forall>a \<in> actions. wf_action ty_ent of_type sig a" *)
begin

end


abbreviation "person_on_floor \<equiv> Pred ''person_on_floor''"
abbreviation "elevator_on_floor \<equiv> Pred ''elevator_on_floor''"
abbreviation "stopped \<equiv> Pred ''stopped''"
abbreviation "person_in_elevator \<equiv> Pred ''person_in_elevator''"

abbreviation "person1 \<equiv> Obj ''person1''"

abbreviation "floor1 \<equiv> Obj ''floor1''"
abbreviation "floor2 \<equiv> Obj ''floor2''"
abbreviation "floor3 \<equiv> Obj ''floor3''"

abbreviation "elevator1 \<equiv> Obj ''elevator1''"

abbreviation "person_locations \<equiv> {
  predAtm person_on_floor [floor1, person1],
  predAtm person_on_floor [floor2, person1],
  predAtm person_on_floor [floor3, person1]
}"

abbreviation "elevator_locations \<equiv> {
  predAtm elevator_on_floor [floor1, elevator1],
  predAtm elevator_on_floor [floor2, elevator1],
  predAtm elevator_on_floor [floor3, elevator1]
}"

abbreviation "elevator_stopped \<equiv> {
  predAtm stopped [elevator1]
}"

abbreviation "in_elevator \<equiv> {
  predAtm person_in_elevator [person1, elevator1]
}"

definition preds::"object atom set" where
"preds \<equiv> person_locations \<union> elevator_locations \<union> elevator_stopped \<union> in_elevator"


text \<open>Move people into elevators\<close>
abbreviation "mpe111 \<equiv> 
GroundAction ''mpe111'' 
  (Snap [predAtm person_on_floor [floor1, person1]] [] [predAtm person_on_floor [floor1, person1]])
  [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]]
  (Snap [] [predAtm person_in_elevator [person1, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "mpe112 \<equiv> 
GroundAction ''mpe112'' 
  (Snap [predAtm person_on_floor [floor2, person1]] [] [predAtm person_on_floor [floor2, person1]])
  [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]]
  (Snap [] [predAtm person_in_elevator [person1, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "mpe113 \<equiv> 
GroundAction ''mpe113'' 
  (Snap [predAtm person_on_floor [floor3, person1]] [] [predAtm person_on_floor [floor3, person1]])
  [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]]
  (Snap [] [predAtm person_in_elevator [person1, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

text \<open>Move people out of elevators\<close>
abbreviation "mpf111 \<equiv> 
GroundAction ''mpf111'' 
  (Snap [predAtm person_in_elevator [person1, elevator1]] [] [predAtm person_in_elevator [person1, elevator1]])
  [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]]
  (Snap [] [predAtm person_on_floor [floor1, person1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "mpf112 \<equiv> 
GroundAction ''mpf112'' 
  (Snap [predAtm person_in_elevator [person1, elevator1]] [] [predAtm person_in_elevator [person1, elevator1]])
  [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]]
  (Snap [] [predAtm person_on_floor [floor2, person1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "mpf113 \<equiv> 
GroundAction ''mpf113'' 
  (Snap [predAtm person_in_elevator [person1, elevator1]] [] [predAtm person_in_elevator [person1, elevator1]])
  [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]]
  (Snap [] [predAtm person_on_floor [floor3, person1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

text \<open>Move elevators\<close>
abbreviation "me112 \<equiv> 
GroundAction ''me112'' 
  (Snap [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]] [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]])
  []
  (Snap [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "me113 \<equiv> 
GroundAction ''me113'' 
  (Snap [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]] [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]])
  []
  (Snap [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "me121 \<equiv> 
GroundAction ''me121'' 
  (Snap [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]] [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]])
  []
  (Snap [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "me123 \<equiv> 
GroundAction ''me123'' 
  (Snap [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]] [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]])
  []
  (Snap [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "me131 \<equiv> 
GroundAction ''me131'' 
  (Snap [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]] [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]])
  []
  (Snap [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor1, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

abbreviation "me132 \<equiv> 
GroundAction ''me132'' 
  (Snap [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]] [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor3, elevator1]])
  []
  (Snap [] [predAtm stopped [elevator1], predAtm elevator_on_floor [floor2, elevator1]] [])
  (Some (duration_op.EQ, (4::rat)))
"

definition actions::"(object atom, rat) action set" where
"actions \<equiv> {mpe111, mpe112, mpe113, mpf111, mpf112, mpf113, me112, me113, me121, me123, me131, me132}"

definition init::"object atom set" where
"init \<equiv> {predAtm person_on_floor [floor1, person1]}"

definition goal::"object atom set" where
"goal \<equiv> {predAtm person_on_floor [floor3, person1]}"


global_interpretation ground_PDDL_planning_with_equality preds actions init goal
proof
  show "finite preds" unfolding preds_def by blast
  moreover 
  have "\<exists>x. x \<in> preds" unfolding preds_def by blast
  ultimately
  show "0 < card preds" using card_gt_0_iff by blast

  show "finite actions" unfolding actions_def by blast
  moreover
  have "\<exists>x. x \<in> actions" unfolding actions_def by blast
  ultimately
  show "0 < card actions" using card_gt_0_iff by blast

  show "const_valid_domain preds s_snap e_snap snap_adds snap_dels actions"
    unfolding const_valid_domain_def act_mod_fluents_def
  proof (intro ballI; intro conjI)
    fix a
    assume a: "a \<in> actions"
    consider "a = mpe111" | "a = mpe112" | "a = mpe113" 
      | "a = mpf111" | "a = mpf112" | "a = mpf113" 
      | "a = me112" | "a = me113" | "a = me121" 
      | "a = me123" | "a = me131" | "a = me132" 
      by (insert a[simplified actions_def, simplified], elim disjE, assumption+) 
    note ac = this
    show "snap_mod_fluents preds snap_adds snap_dels (s_snap a)" 
      by (cases rule: ac; simp add: preds_def)
    show "snap_mod_fluents preds snap_adds snap_dels (e_snap a)"
      by (cases rule: ac; simp add: preds_def)
  qed
qed


ML \<open>\<close>
      
end
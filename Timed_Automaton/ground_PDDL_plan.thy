theory ground_PDDL_plan
imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
    ExecutableCompilation                    
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

derive (eq) ceq predicate func atom object formula action RefinedLocation dconstraint
derive ccompare predicate func atom object formula duration_op snap action rat RefinedLocation
derive (no) cenum atom object formula
derive (rbt) set_impl func atom object formula action

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


text \<open>To sets\<close>
abbreviation "snap_over_all \<equiv> set o oc"
abbreviation "snap_pres \<equiv> set o pre"
abbreviation "snap_adds \<equiv> set o adds"
abbreviation "snap_dels \<equiv> set o dels"


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

locale ground_PDDL_planning =
  fixes props::   "('proposition::linorder) set"
    and actions:: "('proposition, rat) action set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
  assumes some_props':       "card props > 0" (* TODO: fix locale hierarchy and naming collisions *)
      and some_actions':     "card actions > 0"
      and finite_props':     "finite props"
      and finite_actions':   "finite actions"
      and act_mod_fluents:  "const_valid_domain props s_snap e_snap snap_adds snap_dels actions"
begin
  text \<open>Removing constants\<close>
  abbreviation "fluent_over_all x \<equiv> snap_over_all x \<inter> props"
  abbreviation "fluent_pres x \<equiv> snap_pres x \<inter> props"

  text \<open>Replacing snap actions with annotated actions\<close>
  definition pre_imp'::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
  "pre_imp' \<equiv> \<lambda>x. (pre_imp s_snap e_snap snap_pres x \<inter> props)"

  definition add_imp'::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
  "add_imp' \<equiv> add_imp s_snap e_snap snap_adds"

  definition del_imp'::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
  "del_imp' \<equiv> del_imp s_snap e_snap snap_dels"

  fun pre_imp''::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
    "pre_imp'' (AtStart x) = set (pre (s_snap x)) \<inter> props" |
    "pre_imp'' (AtEnd x) = set (pre (e_snap x)) \<inter> props"


  lemma pre_imp''_eq': "pre_imp'' = pre_imp'" unfolding pre_imp_def 
    apply (rule ext)
    subgoal for x by (cases x; auto simp: pre_imp'_def pre_imp_def)
    done


lemma [code]: "pre_imp' (AtStart x) = set (pre (s_snap x)) \<inter> props"
    "pre_imp' (AtEnd x) = set (pre (e_snap x)) \<inter> props" 
  using pre_imp''_eq'[symmetric] by auto
  
  fun del_imp''::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
    "del_imp'' (AtStart x) = set (dels (s_snap x))" |
    "del_imp'' (AtEnd x) = set (dels (e_snap x))"

  lemma del_imp''_eq': "del_imp'' = del_imp'" unfolding del_imp_def 
    apply (rule ext)
    subgoal for x by (cases x; auto simp: del_imp'_def del_imp_def)
    done
  
  fun add_imp''::"('proposition, rat) action snap_action \<Rightarrow> 'proposition set" where
    "add_imp'' (AtStart x) = set (adds (s_snap x))" |
    "add_imp'' (AtEnd x) = set (adds (e_snap x))"
  
  lemma add_imp''_eq': "add_imp'' = add_imp'" unfolding add_imp_def 
    apply (rule ext)
    subgoal for x by (cases x; auto simp: add_imp'_def add_imp_def)
    done
    
  abbreviation "init' \<equiv> init \<inter> props"
  
  abbreviation "goal' \<equiv> goal \<inter> props"

  sublocale finite_props_temp_planning_problem 
    init' goal' AtStart AtEnd fluent_over_all lower_imp upper_imp 
    pre_imp' add_imp' del_imp' 0 props actions
  proof unfold_locales
    show "fluent_domain props AtStart AtEnd fluent_over_all pre_imp' add_imp' del_imp' actions"
    proof(subst fluent_domain_def, rule ballI)
      fix x
      assume "x \<in> actions"
      hence "snap_mod_fluents props snap_adds snap_dels (s_snap x)" 
            "snap_mod_fluents props snap_adds snap_dels (e_snap x)" 
        using act_mod_fluents unfolding const_valid_domain_def unfolding act_mod_fluents_def by blast+
      hence "snap_mod_fluents props add_imp' del_imp' (AtStart x)" 
            "snap_mod_fluents props add_imp' del_imp' (AtEnd x)" 
        unfolding add_imp_def del_imp_def add_imp'_def del_imp'_def by simp+
      hence "snap_ref_fluents props pre_imp' add_imp' del_imp' (AtStart x)" 
            "snap_ref_fluents props pre_imp' add_imp' del_imp' (AtEnd x)" 
        unfolding pre_imp'_def by simp+
      thus "act_ref_fluents props AtStart AtEnd fluent_over_all pre_imp' add_imp' del_imp' x"
        unfolding act_ref_fluents_def by blast
    qed
  qed (auto simp: finite_props' some_props' finite_actions' some_actions')

  sublocale unique_snaps_temp_planning_problem
      init' goal' AtStart AtEnd fluent_over_all lower_imp upper_imp 
      pre_imp' add_imp' del_imp' 0 props actions
    apply unfold_locales
    unfolding inj_on_def by auto

  sublocale ta: ta_temp_planning
        init' goal' AtStart AtEnd fluent_over_all lower_imp upper_imp 
        pre_imp' add_imp' del_imp' 0 props actions
      by standard

    find_consts name: "refined"

  context
    fixes \<pi>::"('i, ('proposition, rat) action, rat) temp_plan"
    assumes plan_actions_in_problem: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
        and actions_wf: "\<forall>a \<in> actions. act_consts props s_snap e_snap snap_over_all snap_pres snap_adds snap_dels a \<subseteq> init - props"
        and dom_wf: "goal - props \<subseteq> init - props"
  begin
    lemma valid_plan_alt:
      "valid_plan \<pi> init goal s_snap e_snap snap_over_all lower_imp upper_imp snap_pres snap_adds snap_dels \<epsilon>
        \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd fluent_over_all lower_imp upper_imp pre_imp' add_imp' del_imp' \<epsilon>"
    proof -
      have 1: "valid_plan \<pi> init goal s_snap e_snap snap_over_all lower_imp upper_imp snap_pres snap_adds snap_dels \<epsilon> 
      \<longleftrightarrow> valid_plan \<pi> init' goal' s_snap e_snap fluent_over_all lower_imp upper_imp fluent_pres snap_adds snap_dels \<epsilon>"
      proof (subst const_plan_equiv[where over_all' = fluent_over_all and pre' = fluent_pres]) 
        show "const_valid_plan \<pi> props s_snap e_snap snap_adds snap_dels" 
          using act_mod_fluents plan_actions_in_problem unfolding const_valid_plan_def const_valid_domain_def by auto
        show "fluent_over_all = fluent_over_all" by simp
        show "fluent_pres = fluent_pres" by simp
        show "goal - props \<subseteq> init - props" using dom_wf by simp
        show "plan_consts \<pi> props s_snap e_snap snap_over_all snap_pres snap_adds snap_dels \<subseteq> init - props" 
          using plan_actions_in_problem actions_wf unfolding plan_consts_def by blast
        show "valid_plan \<pi> (fluent_state props init) (fluent_state props goal) s_snap e_snap fluent_over_all lower_imp upper_imp fluent_pres snap_adds snap_dels \<epsilon> =
        valid_plan \<pi> init' goal' s_snap e_snap fluent_over_all lower_imp upper_imp fluent_pres snap_adds snap_dels \<epsilon>" unfolding fluent_state_def by simp
      qed 
      have 2: "valid_plan \<pi> init' goal' s_snap e_snap fluent_over_all lower_imp upper_imp fluent_pres snap_adds snap_dels \<epsilon>
      \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd fluent_over_all lower_imp upper_imp pre_imp' add_imp' del_imp' \<epsilon>"
        apply (rule valid_plan_equiv_if_snaps_functionally_equiv)
        unfolding pre_imp_def add_imp_def del_imp_def pre_imp'_def add_imp'_def del_imp'_def by simp+
      
      show "valid_plan \<pi> init goal s_snap e_snap snap_over_all lower_imp upper_imp snap_pres snap_adds snap_dels \<epsilon>
        \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd fluent_over_all lower_imp upper_imp pre_imp' add_imp' del_imp' \<epsilon>" apply (subst 1)
        apply (subst 2) by simp
    qed
  end
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

global_interpretation gPp: ground_PDDL_planning_with_equality preds actions init goal
  defines g_pre_imp = gPp.pre_imp'
      and g_add_imp = gPp.add_imp'
      and g_del_imp = gPp.del_imp'
      and g_ref_inv = gPp.ta.refined_invs
      and g_ref_act_list = gPp.ta.action_list'
      and g_ref_prop_list = gPp.ta.prop_list'
      and g_ref_M = gPp.ta.M'
      and g_ref_N = gPp.ta.N'
      and g_ref_pn = gPp.ta.refined_prop_numbers
      and g_ref_an = gPp.ta.refined_act_numbers
      and g_ref_ap = gPp.ta.refined_all_props
      and g_ref_aa = gPp.ta.refined_all_acts
      and g_ref_act = gPp.ta.refined_act
      and g_ref_init = gPp.ta.refined_init_asmt
      and g_ref_init_t = gPp.ta.refined_initial_transition
      and g_ref_m_d_t = gPp.ta.refined_main_to_decoding
      and g_ref_pd = gPp.ta.refined_prop_decoding
      and g_ref_pd_ed = gPp.ta.refined_prop_decoding_to_exec_decoding
      and g_ref_ed = gPp.ta.refined_exec_decoding
      and g_ref_ed_dm = gPp.ta.refined_exec_decoding_to_decision_making
      and g_ref_ssl = gPp.ta.start_snap_list
      and g_ref_esl = gPp.ta.end_snap_list
      and g_ref_ssi = gPp.ta.s_snap_s_int
      and g_ref_sei = gPp.ta.s_snap_e_int
      and g_ref_esi = gPp.ta.e_snap_s_int
      and g_ref_eei = gPp.ta.e_snap_e_int
      and g_ref_ssc = gPp.ta.refined_start_start_consts
      and g_ref_sec = gPp.ta.refined_start_end_consts
      and g_ref_esc = gPp.ta.refined_end_start_consts
      and g_ref_eec = gPp.ta.refined_end_end_consts
      and g_ref_sc = gPp.ta.refined_start_constraints
      and g_ref_ec = gPp.ta.refined_end_constraints
      and g_ref_pre_clocks = gPp.ta.refined_pre_clocks
      and g_ref_pre_const = gPp.ta.refined_pre_constraints
      and g_ref_sg = gPp.ta.refined_start_guard
      and g_ref_eg = gPp.ta.refined_end_guard
      and g_ref_gs = gPp.ta.refined_guard_at_start
      and g_ref_cdb = gPp.ta.refined_clock_duration_bounds
      and g_ref_ge = gPp.ta.refined_guard_at_end
      and g_ref_dm = gPp.ta.refined_decision_making
      and g_ref_dm_ex = gPp.ta.refined_dm_to_exec
      and g_ref_ae = gPp.ta.refined_add_effects
      and g_ref_de = gPp.ta.refined_del_effects
      and g_ref_eff = gPp.ta.refined_effects
      and g_ref_ase = gPp.ta.refined_at_start_effects
      and g_ref_aee = gPp.ta.refined_at_end_effects
      and g_ref_exec = gPp.ta.refined_execution
      and g_ref_anl = gPp.ta.refined_action_number_list
      and g_ref_oaclocks = gPp.ta.refined_over_all_clocks
      and g_ref_actoa = gPp.ta.refined_action_over_all
      and g_ref_oaconds = gPp.ta.refined_over_all_conds
      and g_ref_exm = gPp.ta.refined_exec_to_main
      and g_ref_nr = gPp.ta.refined_none_running
      and g_ref_gp = gPp.ta.refined_goal_props
      and g_ref_goal_sat = gPp.ta.refined_goal_satisfied
      and g_ref_goal_const = gPp.ta.refined_goal_constraint
      and g_ref_goal_trans = gPp.ta.refined_goal_trans
      and autom = gPp.ta.refined_prob_automaton
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


find_consts name: "pre_imp"


value "length (sorted_list_of_set {me113, me112})"


value "nth (sorted_list_of_set {me113, me112}) 0"

find_consts name: "ta_temp_planning*pre"

find_theorems name: "ground_PDDL_planning"

derive compare dconstraint RefinedClock
derive (compare) ccompare dconstraint RefinedClock
derive ceq alpha 
derive ccompare alpha
derive (eq) ceq RefinedClock rat
derive (rbt) set_impl RefinedClock RefinedLocation dconstraint alpha


find_theorems name: "refined_prob_automaton"

term add_imp 


find_theorems "ground_PDDL_planning preds"

lemmas [code] = add_imp_def del_imp_def pre_imp_def gPp.ta.refined_invs.simps
lemmas [code] = ground_PDDL_planning.pre_imp'_def[OF gPp.ground_PDDL_planning_axioms]

lemma g_pre_imp_code [code]: "g_pre_imp (AtStart x) = set (pre (s_snap x)) \<inter> preds" 
  "g_pre_imp (AtEnd x) = set (pre (e_snap x)) \<inter> preds"
  unfolding pre_imp_def gPp.pre_imp'_def by simp+

lemma g_add_imp_code [code]: "g_add_imp (AtStart x) = set (adds (s_snap x))" 
  "g_add_imp (AtEnd x) = set (adds (e_snap x))" 
  using gPp.add_imp''.simps gPp.add_imp''_eq' g_add_imp_def by auto

lemma g_del_imp_code [code]: "g_del_imp (AtStart x) = set (dels (s_snap x))" 
  "g_del_imp (AtEnd x) = set (dels (e_snap x))" 
  using gPp.del_imp''.simps gPp.del_imp''_eq' g_del_imp_def by auto

lemma g_ref_inv_code [code]: "g_ref_inv x = (if x = Main then GE Stop 0 else EQ Stop 0)" 
  apply (cases x) by simp+

lemma g_ref_pre_clocks_code [code]: "g_ref_pre_clocks a = map PropClock (g_ref_pn (g_pre_imp a))"
  using gPp.ta.refined_pre_clocks_def g_pre_imp_def g_ref_pn_def g_ref_pre_clocks_def by simp

lemma g_ref_pre_const_code [code]: "g_ref_pre_const a = (map (\<lambda>c. EQ c 1) (g_ref_pre_clocks a))"
  using gPp.ta.refined_pre_constraints_def g_pre_imp_def g_ref_pre_clocks_def g_ref_pre_const_def by force

lemma g_add_del_unions:
  "g_add_imp (AtStart a) \<union> g_del_imp (AtStart b) = set (adds (s_snap a) @ dels (s_snap b))"
  "g_add_imp (AtStart a) \<union> g_del_imp (AtEnd b) = set (adds (s_snap a) @ dels (e_snap b))"
  "g_add_imp (AtEnd a) \<union> g_del_imp (AtStart b) = set (adds (e_snap a) @ dels (s_snap b))"
  "g_add_imp (AtEnd a) \<union> g_del_imp (AtEnd b) = set (adds (e_snap a) @ dels (e_snap b))"
  unfolding g_add_imp_code g_del_imp_code by auto

lemma g_inters_1: "(g_pre_imp (AtStart a)) \<inter> ((g_add_imp (AtStart b)) \<union> (g_del_imp (AtStart b))) \<noteq> {} 
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (pre (s_snap a)) \<inter> preds) (adds (s_snap b) @ dels (s_snap b)) \<noteq> []"
  "(g_pre_imp (AtStart a)) \<inter> ((g_add_imp (AtEnd b)) \<union> (g_del_imp (AtEnd b))) \<noteq> {} 
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (pre (s_snap a)) \<inter> preds) (adds (e_snap b) @ dels (e_snap b)) \<noteq> []"
  "(g_pre_imp (AtEnd a)) \<inter> ((g_add_imp (AtStart b)) \<union> (g_del_imp (AtStart b))) \<noteq> {} 
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (pre (e_snap a)) \<inter> preds) (adds (s_snap b) @ dels (s_snap b)) \<noteq> []"
  "(g_pre_imp (AtEnd a)) \<inter> ((g_add_imp (AtEnd b)) \<union> (g_del_imp (AtEnd b))) \<noteq> {} 
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (pre (e_snap a)) \<inter> preds) (adds (e_snap b) @ dels (e_snap b)) \<noteq> []"
  by (subst g_add_del_unions, subst inter_set_filter, subst g_pre_imp_code, blast)+

lemma g_inters_2: 
"((g_add_imp (AtStart a)) \<inter> (g_del_imp (AtStart b))) \<noteq> {}
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (adds (s_snap a))) (dels (s_snap b)) \<noteq> []" 
"((g_add_imp (AtStart a)) \<inter> (g_del_imp (AtEnd b))) \<noteq> {}
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (adds (s_snap a))) (dels (e_snap b)) \<noteq> []" 
"((g_add_imp (AtEnd a)) \<inter> (g_del_imp (AtStart b))) \<noteq> {}
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (adds (e_snap a))) (dels (s_snap b)) \<noteq> []" 
"((g_add_imp (AtEnd a)) \<inter> (g_del_imp (AtEnd b))) \<noteq> {}
  \<longleftrightarrow> filter (\<lambda>x. x \<in> set (adds (e_snap a))) (dels (e_snap b)) \<noteq> []" 
  by (subst g_add_imp_code, subst g_del_imp_code, subst inter_set_filter, blast)+

fun msa_imp::"(object atom, rat) action snap_action \<Rightarrow> (object atom, rat) action snap_action \<Rightarrow> bool" where
"msa_imp (AtStart a) (AtStart b) = (
  filter (\<lambda>x. x \<in> set (pre (s_snap a)) \<inter> preds) (adds (s_snap b) @ dels (s_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (s_snap a))) (dels (s_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (pre (s_snap b)) \<inter> preds) (adds (s_snap a) @ dels (s_snap a)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (s_snap b))) (dels (s_snap a)) \<noteq> [])" |
"msa_imp (AtStart a) (AtEnd b) = (
  filter (\<lambda>x. x \<in> set (pre (s_snap a)) \<inter> preds) (adds (e_snap b) @ dels (e_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (s_snap a))) (dels (e_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (pre (e_snap b)) \<inter> preds) (adds (s_snap a) @ dels (s_snap a)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (e_snap b))) (dels (s_snap a)) \<noteq> [])" |
"msa_imp (AtEnd a) (AtStart b) = (
  filter (\<lambda>x. x \<in> set (pre (e_snap a)) \<inter> preds) (adds (s_snap b) @ dels (s_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (e_snap a))) (dels (s_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (pre (s_snap b)) \<inter> preds) (adds (e_snap a) @ dels (e_snap a)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (s_snap b))) (dels (e_snap a)) \<noteq> [])" |
"msa_imp (AtEnd a) (AtEnd b) = (
  filter (\<lambda>x. x \<in> set (pre (e_snap a)) \<inter> preds) (adds (e_snap b) @ dels (e_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (e_snap a))) (dels (e_snap b)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (pre (e_snap b)) \<inter> preds) (adds (e_snap a) @ dels (e_snap a)) \<noteq> [] \<or>
  filter (\<lambda>x. x \<in> set (adds (e_snap b))) (dels (e_snap a)) \<noteq> [])" 

lemma mutex_snap_action_imp:
"mutex_snap_action g_pre_imp g_add_imp g_del_imp a b = msa_imp a b"
   apply (induction a; induction b)
  by (subst msa_imp.simps, subst mutex_snap_action_def, (subst g_inters_1)+, (subst g_inters_2)+, blast)+

lemmas [code] = numbers_find.simps double_filter.simps mutex_snap_action_def msa_imp.simps

lemma g_ref_ssi_code [code]: "g_ref_ssi sn = (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 g_ref_ssl;
    P = (\<lambda>n' sn'. n' < n \<and> msa_imp sn sn')
  in
    double_filter P 0 g_ref_ssl []
)" unfolding mutex_snap_action_imp[symmetric] 
  using gPp.ta.s_snap_s_int_def g_add_imp_def g_del_imp_def g_pre_imp_def 
  g_ref_ssi_def by simp

lemma g_ref_sei_code [code]: "g_ref_sei sn = (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 g_ref_ssl;
    P = (\<lambda>n' sn'. n' \<le> n \<and> msa_imp sn sn')
  in
    double_filter P 0 g_ref_esl []
)" unfolding mutex_snap_action_imp[symmetric]
  using gPp.ta.s_snap_e_int_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_sei_def by auto

lemma g_ref_eei_code [code]: "g_ref_eei sn \<equiv> (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 g_ref_esl;
    P = (\<lambda>n' sn'. n' < n \<and> msa_imp sn sn')
  in
    double_filter P 0 g_ref_esl []
)" unfolding mutex_snap_action_imp[symmetric]
  using gPp.ta.e_snap_e_int_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_eei_def by auto

lemma g_ref_esi_code [code]: "g_ref_esi sn \<equiv> (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 g_ref_esl;
    P = (\<lambda>n' sn'. n' \<le> n \<and> msa_imp sn sn')
  in
    double_filter P 0 g_ref_ssl []
)" unfolding mutex_snap_action_imp[symmetric] 
  using gPp.ta.e_snap_s_int_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_esi_def by force
(* To do: is there a way to unfold visually? *)
lemma g_ref_ssc_code [code]: "g_ref_ssc sn \<equiv> map (\<lambda>b. GE (StartDur (fst  b)) 0) (g_ref_ssi sn)"
  using gPp.ta.refined_start_start_consts_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_ssc_def g_ref_ssi_def by force

lemma g_ref_sec_code [code]: "g_ref_sec sn = map (\<lambda>b. GE (EndDur (fst  b)) 0) (g_ref_sei sn)"
  using gPp.ta.refined_start_end_consts_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_sec_def g_ref_sei_def by force

lemma g_ref_esc_code [code]: "g_ref_esc sn = map (\<lambda>b. GE (StartDur (fst  b)) 0) (g_ref_esi sn)"
  using gPp.ta.refined_end_start_consts_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_esc_def g_ref_esi_def by force


lemma g_ref_eec_code [code]: "g_ref_eec sn = map (\<lambda>b. GE (EndDur (fst  b)) 0) (g_ref_eei sn)"
  using gPp.ta.refined_end_end_consts_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_eec_def g_ref_eei_def by force

lemma g_ref_sc_code [code]: "g_ref_sc sn = g_ref_ssc sn @ g_ref_sec sn"
  using gPp.ta.refined_start_constraints_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_sc_def g_ref_sec_def g_ref_ssc_def by force

lemma g_ref_ec_code [code]: "g_ref_ec sn = g_ref_esc sn @ g_ref_eec sn"
  using gPp.ta.refined_end_constraints_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_ec_def g_ref_eec_def g_ref_esc_def by force

lemma g_ref_sg_code [code]: "g_ref_sg sn = g_ref_sc sn @ g_ref_pre_const sn"
  using gPp.ta.refined_start_guard_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_pre_const_def g_ref_sc_def g_ref_sg_def by force

lemma g_ref_eg_code [code]: "g_ref_eg sn = g_ref_ec sn @ g_ref_pre_const sn"
  using gPp.ta.refined_end_guard_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_ec_def g_ref_eg_def g_ref_pre_const_def by force

fun AND_ALL_imp::"(RefinedClock, rat) dconstraint list \<Rightarrow> (RefinedClock, rat) dconstraint" where
"AND_ALL_imp [] = GE Stop 0" |
"AND_ALL_imp (c#cs) = AND c (AND_ALL_imp cs)"

lemma refined_AND_ALL_imp_lol: "refined_AND_ALL = AND_ALL_imp" 
  apply (rule ext)
  subgoal for xs apply (induction xs) by auto
  done

lemma g_ref_gs_code [code]: "g_ref_gs n = 
  AND_ALL_imp ((EQ (Running n) 0)#(g_ref_sg (AtStart (g_ref_act n))))"
  using gPp.ta.refined_guard_at_start_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_gs_def g_ref_sg_def refined_AND_ALL_imp_lol by force

lemma g_ref_ge_code [code]: "g_ref_ge n = 
  AND_ALL_imp ((EQ (Running n) 1)#g_ref_cdb n#(g_ref_eg (AtEnd (g_ref_act n))))"
  using gPp.ta.refined_guard_at_end_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_eg_def g_ref_ge_def refined_AND_ALL_imp_lol by force

lemma set_map_distrib: "set a \<union> set b = set (a @ b)"
  by auto

lemma g_ref_dm_code [code]: "g_ref_dm = 
  set ((map (\<lambda>m. (DecAtStart m, g_ref_gs m, Unit, [(SchedStartSnap m, 1)], DecAtEnd m)) g_ref_anl)
  @ (map (\<lambda>m. (DecAtStart m, GE Stop 0, Unit, [(SchedStartSnap m, 0)], DecAtEnd m)) g_ref_anl)
  @ (map (\<lambda>m. (DecAtEnd m, g_ref_ge m, Unit, [(SchedEndSnap m, 1)], DecAtStart (Suc m))) g_ref_anl)
  @ (map (\<lambda>m. (DecAtEnd m, GE Stop 0, Unit, [(SchedEndSnap m, 0)], DecAtStart (Suc m))) g_ref_anl))"
  apply (subst set_map_distrib[symmetric])+
  apply (subst gPp.ta.act_number_set_alt)+
  by (metis (no_types, lifting) Un_assoc gPp.ta.refined_decision_making_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_dm_def g_ref_ge_def g_ref_gs_def image_cong)
  
lemma g_ref_ae_code [code]: "g_ref_ae sn = map (\<lambda>p. (PropClock p, 1)) (g_ref_pn (g_add_imp sn))"
  using gPp.ta.refined_add_effects_def g_add_imp_def g_ref_ae_def by force

lemma g_ref_de_code [code]: "g_ref_de sn = 
  (let P = (\<lambda>p. p \<in> g_del_imp sn \<and> p \<notin> g_add_imp sn)
  in map (\<lambda>p. (PropClock p, 0)) (numbers_gather P 0 g_ref_prop_list))"
  using gPp.ta.refined_del_effects_def g_add_imp_def g_del_imp_def g_ref_de_def by fastforce

lemma g_ref_eff_code [code]: "g_ref_eff sn = g_ref_de sn @ g_ref_ae sn"
  using gPp.ta.refined_del_effects_def gPp.ta.refined_effects_def g_add_imp_def g_del_imp_def g_ref_ae_def g_ref_de_code g_ref_eff_def by auto

lemma g_ref_ase_code [code]: "g_ref_ase n = (Running n, 1) # (StartDur n, 0) # g_ref_eff (AtStart (g_ref_act n))"
  using gPp.ta.act_def gPp.ta.action_list'_def gPp.ta.refined_act_def gPp.ta.refined_at_start_effects_def g_add_imp_def g_del_imp_def g_ref_ase_def g_ref_eff_def by force

lemma g_ref_aee_code [code]: "g_ref_aee n = (Running n, 0) # (EndDur n, 0) # g_ref_eff (AtEnd (g_ref_act n))"
  using gPp.ta.act_def gPp.ta.action_list'_def gPp.ta.refined_act_def gPp.ta.refined_at_end_effects_def g_add_imp_def g_del_imp_def g_ref_aee_def g_ref_eff_def by force


lemma g_ref_exec_code [code]: "g_ref_exec =
set ((map (\<lambda>m. (ExecAtStart m, EQ (SchedStartSnap m) 1, Unit, g_ref_ase m, ExecAtEnd m)) g_ref_anl)
  @ (map (\<lambda>m. (ExecAtStart m, EQ (SchedStartSnap m) 0, Unit, [], ExecAtEnd m)) g_ref_anl)
  @ (map (\<lambda>m. (ExecAtEnd m, EQ (SchedEndSnap m) 1, Unit, g_ref_aee m, ExecAtStart (Suc m))) g_ref_anl)
  @ (map (\<lambda>m. (ExecAtEnd m, EQ (SchedEndSnap m) 0, Unit, [], ExecAtStart (Suc m))) g_ref_anl))"
  apply (subst set_map_distrib[symmetric])+
  apply (subst gPp.ta.act_number_set_alt)+
  by (metis (no_types, lifting) Un_assoc gPp.ta.refined_execution_def g_add_imp_def g_del_imp_def g_ref_aee_def g_ref_ase_def g_ref_exec_def image_cong)
  

lemma autom [code]: "autom = ({g_ref_init_t} \<union> {g_ref_m_d_t} \<union> g_ref_pd 
  \<union> {g_ref_pd_ed} \<union> g_ref_ed \<union> {g_ref_ed_dm}
  \<union> g_ref_dm \<union> {g_ref_dm_ex} \<union> g_ref_exec \<union> {g_ref_exm} 
  \<union> {g_ref_goal_trans}, g_ref_inv)"
  using autom_def gPp.ta.refined_prob_automaton_def g_add_imp_def g_del_imp_def g_pre_imp_def g_ref_dm_def g_ref_exec_def by argo



value "g_ref_init_t"
value "g_ref_m_d_t"
value "g_ref_pd"
value "g_ref_pd_ed"
value "g_ref_ed"
value "g_ref_ed_dm"
value "g_ref_dm"

value "autom"

end
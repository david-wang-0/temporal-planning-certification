theory Index
  imports "PDDL_TP_Reduction.Check_Unsolvability"
          "Munta_Model_Checker.Simple_Network_Language_Impl"
          "Numeric_Ground_PDDL_Exec_Imp.Ground_PDDL_Numeric_NTA_Reduction_Correctness"
          "Numeric_Ground_PDDL_Exec_Imp.Numeric_Unsolvability_Export"
          "Provenance.Provenance"
begin
provenance human


subsection \<open>Definitions\<close>
text \<open>Keyed by the paper's number and title (numbers as in the paper's note-free build).
  TODO marks a definition whose formal counterpart is still to be filled in.\<close>

text \<open>Definition 1 (Boolean expression):
  Grounded PDDL:

    number (\<open>\<D>\<close>):
      TODO

    variable/fluent:
      @{typ \<open>object primitive_numeric_expression\<close>}
    expression:
      @{typ \<open>object numeric_expression\<close>}
    comparison:
      @{typ \<open>object atom\<close>}
    logical connectives, Boolean expression:
      @{typ \<open>object atom formula\<close>}

    Note that @{const Formulas.Top} is in @{type formula} and atoms also contain propositions 
    (@{const predAtm}) from PDDL's abstract syntax.
    @{typ object} is the type of parameters of grounded/instantiated functions.
    A fluent is @{typ \<open>object primitive_numeric_expression\<close>}.
    
  Planning:
    
    variable/fluent:
      @{typ \<open>'n\<close>}
    number:
      @{typ \<open>'r\<close>}
    expression:
      @{typ \<open>('n, 'r) nexp\<close>}
    Boolean expression:
      @{typ \<open>('n, 'r) comp\<close>}
    \<open>\<top>\<close> if empty \<open>\<emptyset>\<close>, otherwise each element is a conjunct:
      @{typ \<open>('n, 'r) comp set\<close>}

  Timed Automata (Munta):
    
    variable (instantiated with @{typ String.literal}):
      @{typ \<open>'a\<close>}
    number (instantiated with @{typ rat} or @{typ int}):
      @{typ \<open>'b\<close>}
    expression:
      @{typ \<open>('a, 'b) Simple_Expressions.exp\<close>}
    Boolean expression:
      @{typ \<open>('a, 'b) Simple_Expressions.bexp\<close>}
\<close>
text \<open>Definition 2 (Variable assignment):
  PDDL:

    number (\<open>\<D>\<close>):
      TODO
    
    variable assignment:
      @{type numeric_world_model}
    expression evaluation:
      @{const numeric_expression_valuation}
    Boolean expression evaluation for atoms:
      @{const valuation}
    Boolean expression evaluation:
      @{const map_formula_semantics}
  
    Undefinedness in the \<open>\<V>\<close> is represented by a mapping to @{term None}.

    @{const valuation} hides the syntax of atoms (propositional or numeric) from formula semantics.

    This is in progress, so division by 0 currently falls back to 0 (the default in HOL's semantics).

  Planning:
  
    variable:
      @{typ \<open>'n\<close>}
    number:
      @{typ \<open>'r\<close>}
    variable assignment:
      @{typ \<open>'n \<rightharpoonup> 'r::linordered_field\<close>}
    expression evaluation:
      @{const eval_nexp}
    Boolean expression evaluation:
      @{const sat_comp}
    Boolean expression evaluation over sets:
      @{const sat_comps}

    Division by zero evaluates to @{term None}.

  Timed Automata:
    
    variable:
      @{typ \<open>'a\<close>}
    number:
      @{typ \<open>'b\<close>}
    variable assignment:
      @{typ \<open>('a \<rightharpoonup> 'b::linorder)\<close>}/@{typ \<open>'a \<Rightarrow> 'b\<close>}
    expression evaluation as relation/function:
      @{const Simple_Expressions.is_val}/@{const Simple_Network_Language_Impl_Refine.eval}
    Boolean expression evaluation as relation/function:
      @{const Simple_Expressions.check_bexp}/@{const Simple_Network_Language_Impl_Refine.bval}

    Munta can handle division, but we have not implemented it. 
    In parsed networks, it uses HOL's division, which falls back to zero on undefined values. 
    It also rounds down for inexact integer divisions.
    Our certifier rejects division, for now.
\<close>
text \<open>Definition 3 (Variable updates):
  PDDL:

    update operator:
      @{type numeric_effect_op}
    update:
      @{typ \<open>object numeric_effect\<close>}
    written variables:
      @{const numeric_effect.lhs}
      @{const lvalues}
    read variables:
      @{const ast_effect_enumerate_rhs_primitive_numeric_expressions}
      @{const additive_lvalues} (only for effects other than Assign)
      @{const rvalues}

  Planning:

    variable:
      @{typ \<open>'n\<close>}
    number:
      @{typ \<open>'r\<close>}
    update:
      @{typ \<open>('n \<times> ('n, 'r::linordered_field) nexp)\<close>}
    written variables:
      @{const numeric_action_defs.snap_writes}
    read variables:
      @{const numeric_action_defs.snap_reads}

  Timed Automata (Munta):

    variable:
      @{typ \<open>'a\<close>}
    number:
      @{typ \<open>'b\<close>}
    update:
      @{typ \<open>('a * ('a, 'b) exp)\<close>}
    written variables:
      @{term \<open>fst :: 'a \<times> ('a, 'b) exp \<Rightarrow> 'a\<close>} of each update
    read variables:
      @{const vars_of_exp} of the update's right-hand side
      (@{const vars_of_bexp} for guards; @{const Prod_TA_Defs.var_set} collects both, without
      separating reads from writes)

    Updates are applied sequentially (@{const is_upds}), so later updates read earlier writes.
    We add @{term upds_no_cress_reads} to ensure that updates do not read from the cross product of previous writes.
\<close>
text \<open>Definition 4 (Clocks):
  Timed Automata (Munta):

    clock (instantiated with @{typ String.literal}):
      @{typ \<open>'c\<close>}
    time (sort @{class time}; constants @{typ int}, semantics @{typ real}):
      @{typ \<open>'t\<close>}

    clock constraint:
      @{typ "('c, 't) acconstraint"}
      @{typ "('c, 't) cconstraint"}
    clock valuation:
      @{typ "('c, 't) cval"}
    satisfaction of clock constraints:
      @{const clock_val_a}
      and for a set @{const clock_val}
\<close>
text \<open>Definition 5 (Clock updates):
  Timed Automata (Munta):

    clock reset:
      @{const clock_set}, written @{term \<open>[r\<rightarrow>0]u\<close>}
      (resets the clocks in the list \<open>r\<close>), 
      in the ''new valuation'' premise of
      @{thm [source] step_u.step_int} (\<open>u' = [r\<rightarrow>0]u\<close>),
      etc.
\<close>
provenance ai_human
text \<open>Definition 6 (Timed Automaton):
  Now also contains the timed transition relation (the paper's former separate definition).

  Timed Automata (Munta):

    action (a name for the transition; not necessary):
      @{typ \<open>'a\<close>}
    clock:
      @{typ \<open>'c\<close>}
    time:
      @{typ \<open>'t::time\<close>} 
    location:
      @{typ \<open>'s\<close>}
    variable:
      @{typ \<open>'x\<close>}
    value (number):
      @{typ \<open>'v\<close>}

    transition \<open>\<langle>l, b, g, u, r, l'\<rangle>\<close>:
      @{typ \<open>('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.transition\<close>}
    timed transition relation \<open>\<Delta>\<close> (the set of transitions, i.e.\ syntax):
      @{typ \<open>('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.transition set\<close>},
      accessed by @{const Simple_Network_Language.trans}
    set of locations \<open>\<L>\<close>:
      the locations of automaton \<open>p\<close>: @{const Simple_Network_Impl.loc_set'}
      encoded in the transitions
    timed automaton \<open>\<langle>\<L>, \<Delta>\<rangle>\<close>:
      @{typ \<open>('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.sta\<close>}
      (also carries the committed and urgent locations and the invariant;
      \<open>\<L>\<close> is not a component, but read off the transitions as above)
\<close>
text \<open>Definition 7 (Network of Timed Automata):
  Now a tuple \<open>\<langle>automata, \<V>, \<C>, \<B>, \<langle>urg\<^sub>0, \<dots>, urg\<^sub>n\<rangle>\<rangle>\<close>; urgency and the variable
  bounds moved here from Definition 8.

  Timed Automata (Munta):

    action:
      @{typ \<open>'a\<close>}
    location:
      @{typ \<open>'s\<close>}
    clock:
      @{typ \<open>'c\<close>}
    time:
      @{typ \<open>'t::time\<close>}
    variable:
      @{typ \<open>'x\<close>}
    value (number):
      @{typ \<open>'v::linorder\<close>}

    timed automaton (committed and urgent locations, transitions, invariant):
      @{typ \<open>('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.sta\<close>}
    network of timed automata (broadcast channels, automata, variable bounds):
      @{typ \<open>('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.nta\<close>}

    list of timed automata:
      @{const Prod_TA_Defs.N}
      (already indexed)
    set of variables \<open>\<V>\<close>:
      @{const Prod_TA_Defs.var_set} (the variables read or written by the transitions)
      Same as the set of variables with an initial assignment:
      @{const Simple_Network_Language.bounded} and 
      @{thm [source] Simple_Network_Impl_nat_ceiling_start_state.s\<^sub>0_bounded}
    set of clocks \<open>\<C>\<close>:
      @{const Simple_Network_Impl.clk_set'} (the clocks in guards, invariants and resets)
    variable bounds \<open>\<B>\<close> (finite integer intervals):
      @{const Prod_TA_Defs.bounds}
      or @{const Simple_Network_Impl_nat_defs.bounds_map} (for integers)
    urgent locations \<open>urg\<^sub>i\<close>:
      @{const Simple_Network_Language.urgent}
\<close>

text \<open>Definition 8 (Network of Timed Automata Transitions):
  Timed Automata (Munta):

    configuration (passed curried to @{const step_u}):
      @{typ \<open>'s list \<times> ('x \<rightharpoonup> 'v) \<times> ('c, 't) cval\<close>}
    initial configuration:
      \<open>a\<^sub>0\<close> in @{const Simple_Network_Language_Model_Checking.models},
      written @{term \<open>A, (a\<^sub>0::('s list * ('x \<rightharpoonup> 'v::linorder) * ('c, 't::time) cval)) \<Turnstile> \<Phi>\<close>}
      This is not an inherent component of the network. 
      It's needed for CTL semantics.
    initial variable assignment within the bounds (\<open>\<V>\<^sub>I(z) \<in> \<B>\<^sub>z\<close>):
      assumption \<open>s\<^sub>0_bounded\<close> (\<open>bounded bounds (map_of s\<^sub>0)\<close>) of
      @{locale Simple_Network_Impl_nat_ceiling_start_state};
      its domain is fixed by the pre-checks (see \<open>\<V>\<close> in Definition 7)
      
    delay transition:
      @{thm [source] step_u.step_t}
    no delay while a location is urgent:
      the ''urgent'' premise of @{thm [source] step_u.step_t}
      only allows 0 delays in urgent locations.
    internal transition:
      @{thm [source] step_u.step_int}
    updated values within the bounds (\<open>eval(\<V>, e) \<in> \<B>\<^sub>z\<close>, replaces \<open>\<noteq> \<bottom>\<close>):
      the ''bounded'' premise of @{thm [source] step_u.step_t}
    reflexive-transitive closure of the transitions:
      @{const steps_u}
\<close>
provenance ai
text \<open>Definition 9 (Run):
  Timed Automata (Munta):

    finite run (list of configurations):
      @{const Graph_Defs.steps} instantiated with @{const step_u'}
      (as \<open>graph_impl\<close> in @{locale tp_nta_reduction_model_checking})
    run condition (\<open>run(cfgs)\<close>: a delay then an internal transition between consecutive
    configurations):
      @{const step_u'} (a delay, then any non-delay transition)
    infinite run:
      @{const Graph_Defs.run}
\<close>
provenance human
text \<open>Definition 10 (Valuation):
  PDDL:

    valuation:
      @{const valuation}
    model of a set of propositions:
      @{const map_formula_semantics}, written @{term \<open>\<A> \<Turnstile>\<^sub>m \<phi>\<close>}

  Planning:

    proposition:
      @{typ \<open>'p\<close>}
    valuation / propositional state:
      @{typ \<open>'p Temporal_Plans.state\<close>}
      Just check that a set is a subset of this: @{const temp_plan_defs.valid_state_sequence}
    model of a set of propositions:
      @{term \<open>(\<subseteq>)\<close>} (source: @{const temp_plan_defs.valid_state_sequence})
\<close>
provenance ai_human
text \<open>Definition 11 (Temporal planning problem):
  PDDL:

    state:
      @{typ world_model}
    durative action:
      @{const DurativeActionSchema} in @{typ ast_temporal_action_schema},
      parameter-free by @{const grounded_temporal_ac}
    snap action:
      @{typ ground_action}, obtained by @{const inst_temporal_snap_action}
    duration bounds:
      no accessor; the constraints are @{const ast_temporal_durative_action_body.duration_constraint}
      (@{typ \<open>term duration_constraint\<close>}), turned into bounds by @{const dc_list_lower} /
      @{const dc_list_upper} (per schema: @{const lower_spec_impl} / @{const upper_spec_impl})
    initial state:
      @{const ast_problem.init} (syntax), @{const ast_temporal_problem.I} (the world model)
    goal:
      @{const ast_problem.goal}
    temporal planning problem:
      @{typ ast_temporal_problem} under @{locale grounded_temporal_problem} and
      @{locale positive_temporal_problem}

    components as read by the reduction (@{locale ground_ast_problem_defs},
    @{locale numeric_ground_ast_problem_defs}):
      propositions \<open>\<P>\<close>: @{const ground_ast_problem_defs.props_spec}
      fluents \<open>\<F>\<close>: @{const numeric_ground_ast_problem_defs.nfluents}
      actions \<open>\<A>\<close>: @{const ground_ast_problem_defs.actions_spec}
      start/end snap actions: @{const ground_ast_problem_defs.at_start_spec} /
        @{const ground_ast_problem_defs.at_end_spec}
      invariants: @{const ground_ast_problem_defs.over_all_spec} (propositional),
        @{const numeric_ground_ast_problem_defs.n_inv} (numeric)
      duration bounds: @{const ground_ast_problem_defs.lower_spec} /
        @{const ground_ast_problem_defs.upper_spec}
      preconditions: @{const ground_ast_problem_defs.pre_spec} (propositional),
        @{const numeric_ground_ast_problem_defs.n_pre} (numeric)
      effects: @{const ground_ast_problem_defs.adds_spec} / @{const ground_ast_problem_defs.dels_spec}
        (propositional), @{const numeric_ground_ast_problem_defs.upds} (numeric)
      initial state: @{const ground_ast_problem_defs.init_spec},
        @{const numeric_ground_ast_problem_defs.num_init}
      goal: @{const ground_ast_problem_defs.goal_spec}, @{const numeric_ground_ast_problem_defs.num_goal}

  Planning:

    state:
      @{typ \<open>'p Temporal_Plans.state\<close>} and @{typ \<open>('p, 'n, 'r) num_state\<close>}
    durative action:
      @{typ \<open>'action\<close>} in @{locale action_defs}
    snap action:
      @{typ \<open>'snap_action\<close>} in @{locale action_defs}, via its parameters \<open>at_start\<close> / \<open>at_end\<close>
    duration bounds:
      parameters \<open>lower\<close> / \<open>upper\<close> of @{locale action_defs},
      of types @{typ \<open>'t lower_bound\<close>} / @{typ \<open>'t upper_bound\<close>}
    initial state:
      parameter \<open>init\<close> of @{locale temp_planning_problem} and \<open>num_init\<close> of
      @{locale numeric_temp_plan_defs}
    goal:
      parameter \<open>goal\<close> of @{locale temp_planning_problem} and \<open>num_goal\<close> of
      @{locale numeric_temp_plan_defs}
    temporal planning problem:
      @{locale temp_planning_problem} (just propositional)
      @{locale numeric_temp_plan_defs} (numeric addition, skipped the problem part)

    propositions \<open>\<P>\<close>:
      parameter \<open>props\<close> of @{locale action_and_prop_set}
      (a list in @{locale temp_planning_problem_list_defs})
    fluents \<open>\<F>\<close>:
      the type @{typ \<open>'n\<close>}; no explicit set
    actions \<open>\<A>\<close>:
      parameter \<open>actions\<close> of @{locale temp_planning_problem_list_defs}
    invariants:
      parameters \<open>over_all\<close> (propositional) and \<open>n_inv\<close> (numeric) of
      @{locale numeric_action_defs}
    snap action components (precondition, numeric precondition, positive and negative effects,
    numeric effects):
      parameters \<open>pre\<close>, \<open>n_pre\<close>, \<open>adds\<close>, \<open>dels\<close>, \<open>upds\<close> of @{locale numeric_action_defs}
\<close>
provenance human
text \<open>Definition 12 (MatchCellar Template): an example; decide whether it needs an entry
  example:
    @{dir \<open>examples/ground/MatchCellar-possible\<close>}:
      @{file \<open>examples/ground/MatchCellar-possible/instance_solvable_domain.pddl\<close>}
      @{file \<open>examples/ground/MatchCellar-possible/instance_solvable_problem.pddl\<close>}
\<close>
provenance ai_human
text \<open>Definition 13 (Effect application):
  PDDL:

    effect application:
      @{const apply_ground_actions}; the temporal semantics uses it under the name @{const apply_eff}

  Planning:

    effect application:
      @{const temp_plan_defs.apply_effects} (propositional),
      @{const apply_upds} (numeric, via @{const numeric_action_defs.apply_num_eff}),
      per happening @{const numeric_action_defs.happening_num_update_set}
    undefined results:
      unlike the paper (\<open>\<S>'\<close> undefined), an update evaluating to @{term None} leaves the
      fluent unassigned; later conditions on it are then not satisfied
\<close>
provenance human
text \<open>Definition 14 (Interference):
  PDDL:

    read variables of a snap action:
      @{const rvalues}
      Two snaps may both write a fluent only if both writes are additive (@{const additive_lvalues});
      within one snap, @{const numeric_effects_non_intrf} allows repeated writes of the same type
      that are not Assign.
    written variables of a snap action:
      @{const lvalues}
    interference:
      @{const acts_non_intrf} (negated)

  Planning:

    read variables of a snap action:
      @{const numeric_action_defs.snap_reads}
    written variables of a snap action:
      @{const numeric_action_defs.snap_writes}
    interference:
      @{const numeric_action_defs.num_mutex_snap_action} (numeric) and
      @{const action_defs.mutex_snap_action} (propositional)
\<close>
text \<open>Definition 15 (Plan):
  PDDL:

    plan:
      @{typ plan}
    happening time points:
      @{const htps_seq}

  Planning:

    plan:
      @{typ \<open>('i, 'action, 'time) temp_plan\<close>} (parameter \<open>\<pi>\<close> of @{locale temp_plan_defs});
      a partial map from indices, not a list as in the paper
    happening time points:
      @{const temp_plan_defs.htps}, enumerated by @{const temp_plan_defs.time_index}
\<close>
text \<open>Definition 16 (Valid state sequence):
  PDDL:

    induced parallel plan:
      @{const action_instantiations.ind_temporal_plan} (a @{typ temporal_plan})
    active invariants:
      the @{const temporal_plan.invariants} of the plan built by
      @{const action_instantiations.ind_temporal_plan},
      or @{const action_instantiations.invs_of_temporal_plan_in_interval} for the
      state-sequence based semantics
    0-separation / \<epsilon>-separation:
      hard-coded 0-separation
    valid state sequence:
      @{const valid_temporal_plan}
      or @{const action_instantiations.valid_temporal_state_seq}
      (whole plan: @{const ast_temporal_problem.valid_temporal_state_seq_plan})

    Intermediate states are not materialised, but reconstructed recursively.

  Planning:

    induced parallel plan:
      @{const temp_plan_defs.plan_happ_seq}, read at @{const temp_plan_defs.time_index}
    active invariants:
      @{const temp_plan_defs.plan_inv_seq}, read at @{const temp_plan_defs.time_index}
    0-separation / \<epsilon>-separation:
      parameter \<open>\<epsilon>\<close> of @{locale temp_plan_defs} or @{locale numeric_temp_plan_defs}
      (pass 0 or some constant)
    valid state sequence:
      @{const temp_plan_defs.valid_state_sequence}
      or @{const numeric_temp_plan_defs.num_valid_state_sequence}

    Assume that states can be accessed by index. 
    Time points can be accessed by index through @{const temp_plan_defs.time_index}.
\<close>
text \<open>Definition 17 (Valid plan):
  PDDL:

    no self-overlap:
      @{const ground_plan_defs.PDDL_no_self_overlap}
    duration constraint satisfaction:
      @{const inst_snap_action_body_elements},
      @{const inst_temporal_snap_action_body},
      @{const inst_temporal_snap_action}, passed to @{locale action_instantiations}
      
      @{const duration_constraint_as_formula} turns each duration constraint into a numeric
      comparison with \<open>DurationExpr\<close>, which @{const inst_duration_in_numeric_expression}
      replaces by the planned duration.
      These are then checked as preconditions of the starting snap action.

      bridge:
        @{const durations_match} and related lemmas
        (@{thm [source] ground_plan_defs.durations_match_imp_sat_lb},
         @{thm [source] ground_plan_defs.durations_match_imp_sat_ub},
         @{thm [source] valid_ground_plan.durations_match_of_valid}).
      
      The reduction reads the constraints as constant bounds and ignores the annotation; this
      agrees with PDDL only because the right-hand sides are constants.

    valid plan:
      @{const ast_temporal_problem.valid_temp_plan2}
      or @{const ast_temporal_problem.valid_temporal_state_seq_plan}

  Planning:

    no self-overlap:
      @{const temp_plan_defs.no_self_overlap}
    duration constraint satisfaction:
      @{const temp_plan_defs.durations_valid}
    valid plan:
      @{const temp_plan_defs.valid_plan} and @{const numeric_temp_plan_defs.num_valid_plan}
\<close>
provenance ai
text \<open>Definition 18 (Integer variables):
  Encoding:
    The bounds are passed in @{const tp_nta_reduction_defs.all_vars} and
    @{const numeric_tp_nta_reduction_defs.num_all_vars}

    proposition variables \<open>v\<^sub>p\<close> (bounds \<open>[0, 1]\<close>):
      @{const tp_nta_reduction_defs.prop_to_var}
    lock counters \<open>l\<^sub>p\<close> (bounds \<open>[0, |\<A>|]\<close>):
      @{const tp_nta_reduction_defs.prop_to_lock}
    active-action counter (bounds \<open>[0, |\<A>|]\<close>):
      @{const tp_nta_reduction_defs.acts_active}
    planning-phase variable (bounds \<open>[0, 2]\<close>):
      @{const tp_nta_reduction_defs.planning_lock}
    fluent variables:
      @{const numeric_tp_nta_reduction_defs.fluent_to_var}, bounds \<open>fluent_lo\<close> / \<open>fluent_hi\<close>
      (parameters of @{locale numeric_tp_nta_reduction_defs})
    set of variables \<open>\<V>\<close> with bounds:
      @{const tp_nta_reduction_defs.all_vars} (propositional; keeps only the proposition variables
      and locks that occur), @{const numeric_tp_nta_reduction_defs.num_all_vars} (with fluents)
    freshness w.r.t. \<open>\<F>\<close>:
      @{thm [source] numeric_tp_nta_reduction.fluent_vars_fresh} for fluents.
      @{locale unique_names} for propositions, fluents, and actions.

        Assumed as \<open>prop_names\<close>, \<open>action_names\<close> in @{locale tp_nta_reduction_correctness}
        and as \<open>fluent_names\<close> in @{locale numeric_tp_nta_reduction};

        Discharged for PDDL in @{theory PDDL_TP_Reduction.Ground_PDDL_Problem_Reduction}
        (propositions, actions: sublocale \<open>abstr_model_checking\<close>) and by
        @{thm [source] numeric_ground_ast_problem.fluent_to_name_spec_inj} (fluents).
\<close>
text \<open>Definition 19 (Action clocks):
  Encoding:

    start clock:
      @{const tp_nta_reduction_defs.act_to_start_clock}
    end clock:
      @{const tp_nta_reduction_defs.act_to_end_clock}
    clock of a snap action of unspecified kind:
      @{const tp_nta_reduction_defs.net_int_clocks} collects the start and end
      clocks of the snap actions interfering with a given one.
      No single function; represented by strings.


    not in the paper:
      @{const tp_nta_reduction_defs.urge_clock},
      the fresh clock Munta needs to encode urgency
      using resets and an invariant in urgent locations.
\<close>
text \<open>Definition 20 (Main Automaton):
  Encoding (propositional):

    main automaton:
      @{const tp_nta_reduction_defs.main_auto}
    locations:
      @{const tp_nta_reduction_defs.init_loc}, 
      @{const tp_nta_reduction_defs.planning_loc},
      @{const tp_nta_reduction_defs.goal_loc}
    initial edge:
      @{const tp_nta_reduction_defs.main_auto_init_edge}
    goal edge:
      @{const tp_nta_reduction_defs.main_auto_goal_edge}
    loop edge:
      @{const tp_nta_reduction_defs.main_auto_loop}

  Encoding (numeric extension; @{const numeric_tp_nta_reduction_defs.augment_edge} conjoins a guard
  and appends updates to a propositional edge):

    main automaton:
      @{const numeric_tp_nta_reduction_defs.num_main_auto}
    initial edge (adds the fluents' initial values,
      @{const numeric_tp_nta_reduction_defs.num_init_upd}):
      @{const numeric_tp_nta_reduction_defs.num_main_auto_init_edge}
    goal edge (adds the numeric goal, @{const numeric_tp_nta_reduction_defs.num_goal_guard}):
      @{const numeric_tp_nta_reduction_defs.num_main_auto_goal_edge}
    loop edge:
      unchanged, @{const tp_nta_reduction_defs.main_auto_loop}
\<close>
text \<open>Definition 21 (Action Automata):
  Encoding (propositional; the encodings are let-bindings inside the edges, built from the
  helpers below):

    interference guard \<open>mutex\<close>:
      the clock constraints \<open>> 0\<close> and \<open>\<ge> \<epsilon>\<close> on @{const tp_nta_reduction_defs.net_int_clocks}
    duration guard \<open>dur\<close>:
      @{const tp_nta_reduction_defs.l_dur} and 
      @{const tp_nta_reduction_defs.u_dur}
    effect encoding \<open>eff\<close>:
      @{const tp_nta_reduction_defs.set_prop_ab} (deletions then additions (respects Fox and Long))
    precondition encoding \<open>pre\<close>:
      @{const tp_nta_reduction_defs.is_prop_ab}
    invariant check \<open>inv\<close>:
      @{const tp_nta_reduction_defs.is_prop_lock_ab} on the deletions that are not also additions
    planning-phase condition \<open>(pl = 1)\<close>:
      @{const tp_nta_reduction_defs.pl_is_1}
    locations:
      @{const tp_nta_reduction_defs.off_loc}, 
      @{const tp_nta_reduction_defs.starting_loc}, 
      @{const tp_nta_reduction_defs.running_loc},
      @{const tp_nta_reduction_defs.ending_loc}
    start-start edge:
      @{const tp_nta_reduction_defs.start_edge}
    start-end edge:
      @{const tp_nta_reduction_defs.edge_2}
    end-start edge:
      @{const tp_nta_reduction_defs.edge_3}
    end-end edge:
      @{const tp_nta_reduction_defs.end_edge}
    instant edge:
      @{const tp_nta_reduction_defs.instant_trans_edge}
    action automaton:
      @{const tp_nta_reduction_defs.action_to_automaton}

  Encoding (numeric extension, via @{const numeric_tp_nta_reduction_defs.augment_edge}):

    numeric precondition:
      @{const numeric_tp_nta_reduction_defs.num_pre_guard}
    numeric invariant:
      @{const numeric_tp_nta_reduction_defs.num_inv_guard}
    numeric effects:
      @{const numeric_tp_nta_reduction_defs.num_upd}
    start-start edge (adds the numeric precondition and effects):
      @{const numeric_tp_nta_reduction_defs.num_start_edge}
    start-end edge (adds the numeric invariant):
      @{const numeric_tp_nta_reduction_defs.num_edge_2}
    end-start edge (adds the numeric invariant):
      @{const numeric_tp_nta_reduction_defs.num_edge_3}
    end-end edge (adds the numeric precondition and effects):
      @{const numeric_tp_nta_reduction_defs.num_end_edge}
    instant edge:
      unchanged, @{const tp_nta_reduction_defs.instant_trans_edge}
    action automaton:
      @{const numeric_tp_nta_reduction_defs.num_action_to_automaton}
\<close>
text \<open>Definition 22 (Network for a planning problem):
  Encoding (propositional):

    list of automata \<open>\<langle>\<A>\<^sub>M, \<A>\<^sub>1, \<dots>, \<A>\<^sub>N\<rangle>\<close>:
      automata: @{const tp_nta_reduction_defs.timed_automaton_net}:
      bounds: @{const tp_nta_reduction_defs.all_vars}
      no broadcast channels: (@{const tp_nta_reduction_defs.net_broadcast})
    initial locations \<open>\<L>\<^sub>I\<close>:
      @{const tp_nta_reduction_defs.init_locs}
    initial variable assignment (each variable at its lower bound):
      @{const tp_nta_reduction_defs.init_vars}
    initial configuration:
      @{const tp_nta_reduction_model_checking.a\<^sub>0} (clocks at 0)
    acceptance condition \<open>EF(loc(\<A>\<^sub>M) = goal)\<close>:
      @{const tp_nta_reduction_defs.reach_formula}

  Encoding (numeric extension):

    list of automata:
      automata: @{const numeric_tp_nta_reduction_defs.num_timed_automaton_net}
      bounds: @{const numeric_tp_nta_reduction_defs.num_all_vars}
    initial locations:
      unchanged, @{const tp_nta_reduction_defs.init_locs}
    initial variable assignment:
      @{const numeric_tp_nta_reduction_defs.num_init_vars}
    initial configuration:
      @{const numeric_tp_nta_reduction_correctness.num_a\<^sub>0}
    acceptance condition:
      unchanged, @{const tp_nta_reduction_defs.reach_formula} (the numeric goal is checked on the goal edge)
\<close>
provenance ai_human
text \<open>Definition 23 (Encoded states):
  Proof (propositional):

    running at, \<open>\<triangleleft>\<close> is \<open>\<le>\<close> (\<open>running_at\<close>, a count, 0 or 1 without self-overlap):
      @{const temp_plan_for_problem_impl.closed_active_count}
    running before, \<open>\<triangleleft>\<close> is \<open><\<close>:
      @{const temp_plan_for_problem_impl.open_active_count}
    time since at, \<open>\<triangleleft>\<close> is \<open>\<le>\<close> (\<open>time_since_at\<close>):
      @{const nta_temp_planning.exec_time'}
    time since before, \<open>\<triangleleft>\<close> is \<open><\<close>:
      @{const nta_temp_planning.exec_time}
      (no earlier snap: \<open>t\<^sub>i - t\<^sub>0 + \<epsilon> + c\<close>, \<open>c\<close> is the paper's \<open>d\<close>;
      TODO: check \<open>\<epsilon>\<close> in the paper; see @{const nta_temp_planning.pt})
    encoded state after (\<open>encaft\<close>):
      @{const tp_nta_reduction_correctness.happening_post}

  Proof (numeric extension):

    encoded state after (\<open>encaft\<close>), with fluents:
      @{const numeric_tp_nta_reduction_correctness.num_happening_post}
\<close>
text \<open>Definition 24 (Encoded states before):
  Proof (propositional):

    encoded state before (\<open>encbef\<close>):
      @{const tp_nta_reduction_correctness.happening_pre}
      (= @{const tp_nta_reduction_correctness.happening_pre_post_delay};
      before the delay to \<open>t\<^sub>i\<close>: @{const tp_nta_reduction_correctness.happening_pre_pre_delay})

  Proof (numeric extension):

    encoded state before (\<open>encbef\<close>), with fluents:
      @{const numeric_tp_nta_reduction_correctness.num_happening_pre}
      (before the delay: @{const numeric_tp_nta_reduction_correctness.num_happening_pre_pre_delay})
\<close>
provenance ai
text \<open>Definition 25 (Encoded initial state):
  Proof (propositional):

    encoded state after the initial edge (no happening time points needed):
      @{const tp_nta_reduction_correctness.init_planning_state_props'}
      (clocks \<open>= 0\<close>, before the first delay; the paper asks for \<open>0 <\<close>)

  Proof (numeric extension):

    encoded initial state, with fluents:
      @{const numeric_tp_nta_reduction_correctness.num_init_planning_state_props'}
\<close>

provenance ai_human
subsection \<open>Theorems\<close>
text \<open>Theorem 1 (main theorem: a valid plan implies that the goal location is reachable):
  Proof (propositional):

    main theorem:
      @{thm [source] tp_nta_reduction_correctness.valid_plan_imp_form_holds}

      contrapositive, for executable certificate checking:
        @{thm [source] make_certified_net_okay}

  Proof (numeric extension):

    main theorem:
      @{thm [source] numeric_tp_nta_reduction_correctness.num_valid_plan_imp_form_holds}

      contrapositive, for executable certificate checking:
        @{thm [source] make_certified_numeric_net_okay}
\<close>
provenance ai
text \<open>Lemma 1 (variable bounds respected): TODO (the paper's statement is still a placeholder)
  Proof (numeric extension):

    fluents of a valid state sequence stay in their bounds (candidate):
      @{thm [source] numeric_tp_nta_reduction_correctness.num_seq_fluent_in_bounds}
    the inferred bounds establish the bound invariant (candidate):
      @{thm [source] numeric_tp_nta_reduction.inferred_box_imp_num_bound_inv}
\<close>
provenance ai_human
text \<open>Lemma 2 (plan transitions possible):
  Proof (propositional):

    plan transitions:
      @{thm [source] tp_nta_reduction_correctness.plan_steps_possible}

  Proof (numeric extension):

    plan transitions:
      @{thm [source] numeric_tp_nta_reduction_correctness.num_plan_steps_possible}
\<close>
text \<open>Lemma 3 (initial transitions possible):
  Proof (propositional):

    initial transitions:
      @{thm [source] tp_nta_reduction_correctness.initial_step_possible}

  Proof (numeric extension):

    initial transitions:
      @{thm [source] numeric_tp_nta_reduction_correctness.num_initial_step_possible}
\<close>
text \<open>Lemma 4 (goal transition possible):
  Proof (propositional):

    goal transition:
      @{thm [source] tp_nta_reduction_correctness.final_step_possible}

  Proof (numeric extension):

    goal transition:
      @{thm [source] numeric_tp_nta_reduction_correctness.num_final_step_possible}
\<close>

provenance human
subsection \<open>Locales\<close>
text \<open>Our locales for the propositional part are:\<close>
text \<open>\<open>\<Pi>\<close>:\<close>
term temp_planning_problem_set_impl
text \<open>\<open>\<Pi>a:\<close>\<close>
term temp_planning_problem_set_impl'
text \<open>\<open>\<pi>:\<close>\<close>
term temp_plan_for_problem_impl
text \<open>\<open>\<pi>a:\<close>\<close>
term temp_plan_for_problem_impl'

text \<open>\<open>\<Pi>li:\<close>\<close>
term temp_planning_problem_list_impl_int
text \<open>\<open>\<Pi>ali:\<close>\<close>
term temp_planning_problem_list_impl_int'
text \<open>\<open>\<pi>li:\<close>\<close>
term temp_plan_for_problem_list_impl_int
text \<open>\<open>\<pi>ali:\<close>\<close>
term temp_plan_for_problem_list_impl_int'

text \<open>\<open>\<Pi>liN:\<close>\<close>
term tp_nta_reduction_model_checking
text \<open>\<open>\<Pi>aliN:\<close>\<close>
term tp_nta_reduction_model_checking'
text \<open>\<open>\<pi>liN:\<close>\<close>
term tp_nta_reduction_correctness
text \<open>\<open>\<pi>aliN:\<close>\<close>
term tp_nta_reduction_correctness'

text \<open>\<open>\<T>:\<close>\<close>
term Simple_Network_Impl_nat
text \<open>Or @{locale Simple_Network_Impl}\<close>

text \<open>\<open>\<Pi>Sg:\<close>\<close>
term ground_ast_problem
text \<open>\<open>\<pi>Sg:\<close>\<close>
term valid_ground_plan
text \<open>\<open>\<Pi>SgD:\<close>\<close>
term ground_ast_problem
text \<open>Or@{locale ground_ast_problem_defs}\<close>
text \<open>\<open>\<Pi>S:\<close>\<close>
term wf_ast_temporal_problem

end

theory Index
  imports "PDDL_TP_Reduction.Check_Unsolvability"
          "Munta_Model_Checker.Simple_Network_Language_Impl"
begin


subsection \<open>Definitions\<close>
text \<open>Keyed by the paper's number and title (numbers as in the paper's note-free build).
  TODO marks a definition whose formal counterpart is still to be filled in.\<close>

text \<open>Definition 1 (Boolean expression):
  Grounded PDDL:

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

    Munta can handle division, but we have not implemented it. In parsed networks, 
    it uses HOL's division, which falls back to zero on undefined values. It also
    rounds down for inexact integer divisions.
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
text \<open>Definition 4 (Valuation):
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
text \<open>Definition 5 (Temporal planning problem):
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
\<close>
text \<open>Definition 6 (MatchCellar Template): an example; decide whether it needs an entry
  example:
    @{dir \<open>examples/ground/MatchCellar-possible\<close>}:
      @{file \<open>examples/ground/MatchCellar-possible/instance_solvable_domain.pddl\<close>}
      @{file \<open>examples/ground/MatchCellar-possible/instance_solvable_problem.pddl\<close>}
\<close>
text \<open>Definition 7 (Effect application):
  PDDL:

    effect application:
      @{const apply_ground_actions}; the temporal semantics uses it under the name @{const apply_eff}

  Planning:

    effect application:
      @{const temp_plan_defs.apply_effects} (propositional),
      @{const apply_upds} (numeric, via @{const numeric_action_defs.apply_num_eff})
\<close>
text \<open>Definition 8 (Interference):
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
text \<open>Definition 9 (Plan):
  PDDL:

    plan:
      @{typ plan}
    happening time points:
      @{const htps_seq}

  Planning:

    plan:
      @{typ \<open>('i, 'action, 'time) temp_plan\<close>} (parameter \<open>\<pi>\<close> of @{locale temp_plan_defs})
    happening time points:
      @{const temp_plan_defs.htps}, enumerated by @{const temp_plan_defs.time_index}
\<close>
text \<open>Definition 10 (Valid state sequence):
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
text \<open>Definition 11 (Valid plan):
  PDDL:

    no self-overlap:
      @{const ground_plan_defs.PDDL_no_self_overlap}
    duration constraint satisfaction:
      @{const inst_snap_action_body_elements}, @{const inst_temporal_snap_action_body},
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
text \<open>Definition 12 (Clocks):
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
text \<open>Definition 13 (Clock updates):
  Timed Automata (Munta):

    clock reset:
      @{const clock_set}, written @{term \<open>[r\<rightarrow>0]u\<close>}
      (resets the clocks in the list \<open>r\<close>), 
      in the ''new valuation'' premise of
      @{thm [source] step_u.step_int} (\<open>u' = [r\<rightarrow>0]u\<close>),
      etc.
\<close>
text \<open>Definition 14 (Timed Automaton):
  Timed Automata (Munta):

    action:
      @{typ \<open>'a\<close>}
    clock:
      @{typ \<open>'c\<close>}
    time:
      @{typ \<open>'time::time\<close>} 
    location:
      @{typ \<open>'s\<close>}

    transition:
      @{typ \<open>('a, 'c, 'time, 's) Timed_Automata.transition\<close>}
    transition relation:
      @{const Timed_Automata.step_a}
    timed automaton:
      @{typ \<open>('a, 'c, 'time, 's) ta\<close>}
\<close>
text \<open>Definition 15 (Network of Timed Automata):
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
\<close>
text \<open>Definition 16 (Network of Timed Automata Transitions):
  Timed Automata (Munta):

    configuration (passed curried to @{const step_u}):
      @{typ \<open>'s list \<times> ('x \<rightharpoonup> 'v) \<times> ('c, 't) cval\<close>}
    initial configuration:
      \<open>a\<^sub>0\<close> in @{const Simple_Network_Language_Model_Checking.models},
      written @{term \<open>A, (a\<^sub>0::('s list * ('x \<rightharpoonup> 'v::linorder) * ('c, 't::time) cval)) \<Turnstile> \<Phi>\<close>}
      This is not an inherent component of the network. 
      It's needed for CTL semantics.
      
    urgent locations:
      @{const Simple_Network_Language.urgent}
    delay transition:
      @{thm [source] step_u.step_t}
    internal transition:
      @{thm [source] step_u.step_int}
    reflexive-transitive closure of the transitions:
      @{const steps_u}
\<close>
text \<open>Definition 17 (Run):
  Timed Automata (Munta):

    run:
      TODO
\<close>
text \<open>Definition 18 (Integer variables):
  Encoding:

    proposition variables:
      TODO
    lock counters:
      TODO
    active-action counter:
      TODO
    planning-phase variable:
      TODO
\<close>
text \<open>Definition 19 (Action clocks):
  Encoding:

    start clock:
      TODO
    end clock:
      TODO
\<close>
text \<open>Definition 20 (Main Automaton):
  Encoding:

    main automaton:
      TODO
    initial edge:
      TODO
    goal edge:
      TODO
    loop edge:
      TODO
\<close>
text \<open>Definition 21 (Action Automata):
  Encoding:

    interference guard:
      TODO
    duration guard:
      TODO
    effect encoding:
      TODO
    precondition encoding:
      TODO
    invariant check:
      TODO
    start-start edge:
      TODO
    start-end edge:
      TODO
    end-start edge:
      TODO
    end-end edge:
      TODO
    instant edge:
      TODO
    action automaton:
      TODO
\<close>
text \<open>Definition 22 (Network for a planning problem):
  Encoding:

    network for a planning problem:
      TODO
    initial configuration:
      TODO
    acceptance condition:
      TODO
\<close>
text \<open>Definition 23 (Encoded states):
  Proof:

    running at (\<open>running_at\<close>), TODO: re-check:
      @{const temp_plan_for_problem_impl.closed_active_count}, @{const temp_plan_for_problem_impl.open_active_count}
    time since at (\<open>time_since_at\<close>), TODO: re-check:
      @{const nta_temp_planning.exec_time'}, @{const nta_temp_planning.exec_time}
    encoded state after (\<open>encaft\<close>), TODO: re-check:
      @{const tp_nta_reduction_correctness.happening_post}
\<close>
text \<open>Definition 24 (Encoded states before):
  Proof:

    encoded state before (\<open>encbef\<close>), TODO: re-check:
      @{const tp_nta_reduction_correctness.happening_pre_post_delay}
\<close>
text \<open>Definition 25 (Encoded initial state):
  Proof:

    encoded state when there are no happening time points:
      TODO
\<close>

subsection \<open>Theorems\<close>
text \<open>Theorem 1 (main theorem: a valid plan implies that the goal location is reachable); TODO: re-check the name\<close>
thm tp_nta_reduction_correctness.valid_plan_imp_form_holds
text \<open>Contrapositive for executable certificate checking\<close>
thm make_certified_net_okay

text \<open>Lemma 1 (variable bounds respected): TODO (the paper's statement is still a placeholder)\<close>
text \<open>Lemma 2 (plan transitions possible)\<close>
thm tp_nta_reduction_correctness.plan_steps_possible
text \<open>Lemma 3 (initial transitions possible)\<close>
thm tp_nta_reduction_correctness.initial_step_possible
text \<open>Lemma 4 (goal transition possible)\<close>
thm tp_nta_reduction_correctness.final_step_possible

subsection \<open>Locales\<close>
text \<open>Our locales are:\<close>
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

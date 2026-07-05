theory TP_NTA_Reduction_Numeric_Model_Checking
  imports TP_NTA_Reduction_Correctness TP_NTA_Reduction_Numeric_Defs
begin

section \<open>Numeric reduction correctness (Layer B)\<close>

text \<open>The numeric correctness locale merges three layers at the @{emph \<open>same\<close>} propositional
parameters: the propositional reduction correctness @{locale tp_nta_reduction_correctness} (which
gives the @{emph \<open>forward\<close>} direction -- a valid plan induces a goal-reaching run via @{text plan_steps}
and the step lemmas, i.e. the soundness-of-certification direction, @{emph \<open>not\<close>} a full bisimulation),
the numeric net @{locale numeric_tp_nta_reduction} (list-valued numeric data, the numeric automata
@{text num_timed_automaton_net}, and the grounder-match well-formedness), and the abstract numeric
plan layer @{locale numeric_temp_plan_for_problem_list_impl_int} instantiated at the @{text \<open>set o _\<close>}
projection of the list numeric data (so its @{text num_rat_impl} interprets @{locale
numeric_temp_plan_defs} at the rat-refined parameters, where @{text num_valid_plan} lives). The one
genuinely new assumption -- everything else is @{emph \<open>fixes\<close>}-only over shared ancestors -- is that
the numeric plan is valid (@{text num_rat_impl.num_valid_plan}), strengthening the propositional
@{text valid_plan} the reduction already assumes.\<close>
locale numeric_tp_nta_reduction_correctness =
  tp_nta_reduction_correctness
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name +
  numeric_tp_nta_reduction
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
    n_pre n_inv upds num_init num_goal nfluents fluent_to_var fluent_lo fluent_hi const_to_int +
  num_plan: numeric_temp_plan_for_problem_list_impl_int
    at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>
    "set o n_pre" "set o n_inv" "set o upds"
    "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and \<pi> :: "('i, 'action, int) temp_plan"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
    and n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_var :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int" +
  assumes num_valid: "num_plan.num_rat_impl.num_valid_plan"
      and const_to_int_of_int: "const_to_int (Int.of_int m) = m"
      \<comment> \<open>The range-boundedness reachability invariant (grounder-match contract, complementing the
         static integrality assumptions in @{locale numeric_tp_nta_reduction}): along any valid numeric
         state sequence the per-happening valuations stay within the declared fluent variable bounds.
         A certifier checks this against the candidate plan's finite trace; PDDL supplies no bounds, and a
         global closure over all in-range valuations would be false for monotone effects. The intermediate
         partial-fold stores within a happening are derived in range from the @{term i}/@{term \<open>Suc i\<close>}
         endpoints (each fluent is written at most once, so a partial value is one of the two endpoints).
         Indexed by @{term \<open>rat_impl.htpl\<close>}, which the later \<open>rat_impl_htpl_eq\<close> equates with
         @{term \<open>planning_sem.htpl\<close>}.\<close>
      and num_seq_in_bounds:
            "\<And>M i. num_plan.num_rat_impl.num_valid_state_sequence M
               \<Longrightarrow> snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)
               \<Longrightarrow> i \<le> length rat_impl.htpl
               \<Longrightarrow> fluent_in_bounds (snd (M i))"
      and num_goal_comp_ok:
            "\<And>w. num_val_ok w \<Longrightarrow> (\<forall>c \<in> set num_goal. comp_ok w c)"
begin

text \<open>The numeric network's Munta semantics, mirroring the propositional @{text net_impl}/@{text
graph_impl}: same broadcast channels (none), the augmented automata @{const num_timed_automaton_net},
and the augmented variable bounds @{const num_net_bounds}. @{locale Simple_Network_Impl} is
assumption-free, so this is a bare interpretation.\<close>
sublocale num_net_impl: Simple_Network_Impl num_timed_automaton_net net_broadcast num_net_bounds .
sublocale num_graph_impl: Graph_Defs
  "\<lambda>(L, s, u) (L', s', u'). step_u' num_net_impl.sem L s u L' s' u'" .

text \<open>Sanity: both nets and the numeric plan-validity are in scope at the shared parameters.\<close>
lemma num_net_in_scope: "num_timed_automaton_net = num_main_auto # map num_action_to_automaton actions"
  by (simp add: num_timed_automaton_net_def)

definition "num_a\<^sub>0 = (init_locs, map_of num_init_vars, (\<lambda>_::String.literal. 0::real))"

end
end

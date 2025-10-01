theory Temporal_Plans_Instances
  imports Temporal_Plans
begin



instance rat::time 
  apply standard 
  using dense_order_class.dense apply blast
  using verit_eq_simplify(*(24) 1 \<noteq> 0 *) by blast

section \<open>Actual planning problems\<close>
text \<open>We now define the actual conditions under which we prove our results.\<close>

text \<open>Most things that we are interested in is about how plans interact with planning problems as
opposed to planning problems in isolation.
A problem is an initial state, a goal, a set of actions.\<close>


locale temp_planning_problem_set_impl = 
  temp_planning_problem +
  temp_planning_problem_and_some_props +
  temp_planning_problem_and_some_actions +
  temp_planning_problem_and_actions_with_unique_snaps +
  temp_planning_problem_with_bounded_init_and_goal +
  temp_planning_problem_and_actions_ref_props

locale temp_planning_problem_set_impl' =
  temp_planning_problem at_start at_end over_all lower upper pre adds dels init goal \<epsilon> +
  temp_planning_problem_and_some_props  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props +
  temp_planning_problem_and_some_actions  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> actions +
  temp_planning_problem_goal_consts_in_init_consts  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props +
  temp_planning_problem_and_actions_mod_props at_start at_end over_all lower upper pre adds dels init goal \<epsilon> actions props +
  temp_planning_problem_and_action_consts_in_init_consts at_start at_end over_all lower upper pre adds dels init goal \<epsilon> actions props
  for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and \<epsilon>::       "'time::time" 
    and props:: "'proposition set"
    and actions:: "'action set"
begin

sublocale prop_set_impl: 
  temp_planning_problem_set_impl AtStart AtEnd over_all_restr lower upper pre_imp_restr add_imp del_imp
  "init \<inter> props" "goal \<inter> props" \<epsilon> props actions
  apply unfold_locales
  subgoal unfolding action_defs.snaps_disj_on_def by (blast intro: inj_onI)
  subgoal by blast
  subgoal by blast
  subgoal using domain_acts_mod_props
    unfolding act_mod_props_def snap_mod_props_def
    unfolding action_and_prop_set.act_ref_props_def action_and_prop_set.snap_ref_props_def
    unfolding pre_imp_def add_imp_def del_imp_def 
    unfolding over_all_restr_def pre_imp_restr_def
    by simp
  done

end

locale temp_plan_mutex_nso_unique_snaps_dg0 =
  temp_plan_mutex + temp_plan_unique_snaps_nso_dg0
begin
sublocale temp_plan_mutex_happ_seq
  apply unfold_locales
  using mutex_valid_plan nm_anno_act_seq_eq_nm_happ_seq nso_mutex_eq_nm_anno_act_seq 
  by blast
end

locale valid_temp_plan_unique_snaps_nso_dg0 = 
  valid_temp_plan +
  temp_plan_unique_snaps_nso_dg0
begin
sublocale temp_plan_mutex_nso_unique_snaps_dg0 by unfold_locales
end

locale temp_plan_for_problem_impl =
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
  valid_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
  temp_plan_nso at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
  temp_plan_for_actions at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> actions +
  temp_planning_problem_set_impl at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::"'proposition set"
    and goal::"'proposition set"
    and \<epsilon>::"'time"
    and \<pi>::"('i, 'action, 'time::time) temp_plan" 
    and actions::"'action set"
    and props::"'proposition set"
begin

sublocale temp_plan_unique_snaps_nso_dg0 apply unfold_locales 
  using snaps_disj_on_acts snaps_disj_on_subset pap plan_actions_in_problem_def by blast

sublocale valid_temp_plan_unique_snaps_nso_dg0
  by unfold_locales

sublocale temp_plan_for_actions_with_unique_snaps_nso_dg0 
  by unfold_locales

sublocale temp_plan_nso_dg0
  by unfold_locales
end

locale plan_validity_ref =
  valid_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> + 
  plan_validity_equivalence at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
  at_start' at_end' over_all' pre' adds' dels' init' goal' 
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::"'proposition set"
    and goal::"'proposition set"
    and \<epsilon>::"'time"
    and \<pi>::"('i, 'action, 'time::time) temp_plan" 
    and at_start'::"'action \<Rightarrow> 'snap_action_1"
    and at_end'::  "'action  \<Rightarrow> 'snap_action_1"
    and over_all'::"'action  \<Rightarrow> 'proposition set"
    and pre'::     "'snap_action_1 \<Rightarrow> 'proposition set"
    and adds'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and dels'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and init':: "'proposition set"
    and goal':: "'proposition set"
begin
sublocale valid_plan2: valid_temp_plan at_start' at_end' over_all' lower upper pre' adds' dels' init' goal'
  apply unfold_locales
  using vp using valid_plan_equiv_if_snaps_functionally_equiv by blast
end

locale temp_plan_for_problem_impl' =
  temp_plan_defs +
  valid_temp_plan +
  temp_plan_nso +
  temp_plan_for_actions +
  temp_planning_problem_set_impl'
begin

(* We first replace snap actions with annotated actions*)
sublocale unique_ref: temp_plan_unique_snaps_nso_dg0 AtStart AtEnd over_all lower upper 
  pre_imp add_imp del_imp  
  apply unfold_locales 
  unfolding prop_set_impl.snaps_disj_on_def by (blast intro: inj_onI) 

sublocale valid_plan_ref: plan_validity_equivalence at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
  AtStart AtEnd over_all pre_imp add_imp del_imp init goal
  apply unfold_locales unfolding pre_imp_def add_imp_def del_imp_def by auto

sublocale valid_plan_ref_valid: plan_validity_ref at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
  AtStart AtEnd over_all pre_imp add_imp del_imp init goal by unfold_locales

(* The set of props is a superset of those that can be modified by a plan. Those propositions that
are in the preconditions of actions, are either present in this or the initial set of propositions. *)
sublocale restr_to_props: temp_plan_and_props_defs AtStart AtEnd over_all lower upper 
  pre_imp add_imp del_imp init goal by unfold_locales 

sublocale restr_to_props_ref: valid_temp_plan_restr_to_props AtStart AtEnd over_all lower upper 
  pre_imp add_imp del_imp init goal
  apply unfold_locales
  subgoal using domain_acts_mod_props unfolding restr_to_props.plan_acts_mod_props_def 
    using pap unfolding plan_actions_in_problem_def 
    unfolding prop_set_impl.act_mod_props_def act_mod_props_def 
    unfolding prop_set_impl.snap_mod_props_def snap_mod_props_def 
    unfolding pre_imp_def add_imp_def del_imp_def by auto
  subgoal using domain_action_consts_in_init_consts
    unfolding action_consts_def
    unfolding restr_to_props.plan_consts_def
    unfolding pre_imp_restr_def over_all_restr_def
    unfolding add_imp_def del_imp_def pre_imp_def
    using domain_acts_mod_props 
    using pap unfolding plan_actions_in_problem_def 
    by auto
  done


sublocale restr_to_props_valid: temp_plan_for_problem_impl AtStart AtEnd "restr_to_props.over_all_restr" lower upper 
  "restr_to_props.pre_restr" add_imp del_imp "init \<inter> props" "goal \<inter> props"
  apply unfold_locales
  apply (intro ballI)
  unfolding restr_to_props_ref.rtf.act_ref_props_def
  unfolding restr_to_props.over_all_restr_def
  unfolding restr_to_props_ref.rtf.snap_ref_props_def
  unfolding restr_to_props.pre_restr_def 
  unfolding restr_to_props.over_all_restr_def
  apply (drule domain_acts_mod_props[THEN bspec])
  unfolding act_mod_props_def snap_mod_props_def
  unfolding pre_imp_def add_imp_def del_imp_def 
  by simp
end

locale temp_planning_problem_list_defs =
  fixes at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"'time"
    and props::   "'proposition list"
    and actions:: "'action list"
  assumes eps_ran: "0 \<le> \<epsilon>"
begin
definition "over_all_restr_list = (\<lambda>a. filter (\<lambda>p. p \<in> set props) (over_all a))"
definition "pre_restr_list = (\<lambda>s. filter (\<lambda>p. p \<in> set props) (pre s))"

sublocale set_impl: temp_planning_problem_and_finite_actions at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> "set actions"
  apply unfold_locales using eps_ran finite_set by auto

sublocale set_impl: temp_planning_problem_and_finite_props at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> "set props"
  apply unfold_locales using eps_ran finite_set by auto

sublocale set_impl: action_set_and_props at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set props" "set actions"
  by unfold_locales

abbreviation "list_inter xs ys \<equiv> filter (\<lambda>p. p \<in> set (xs)) ys"

definition pre_imp_list::"'action snap_action \<Rightarrow> 'proposition list" where
"pre_imp_list x = set_impl.app_snap pre x"

definition add_imp_list::"'action snap_action \<Rightarrow> 'proposition list" where
"add_imp_list x = set_impl.app_snap adds x"

definition del_imp_list::"'action snap_action \<Rightarrow> 'proposition list" where
"del_imp_list x = set_impl.app_snap dels x"

definition "pre_imp_restr_list x = list_inter props (pre_imp_list x)"

end

locale temp_planning_problem_list_impl = temp_planning_problem_list_defs
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"'time"
    and props::   "'proposition list"
    and actions:: "'action list" +
  assumes some_actions: "0 < length actions"
      and some_props: "0 < length props"
      and distinct_props: "distinct props"
      and distinct_actions: "distinct actions"
      and distinct_over_all: "\<forall>a \<in> set actions. distinct (over_all a)"
      and snaps_disj: "set_impl.snaps_disj_on (set actions)"
      and init_in_props: "set init \<subseteq> set props"
      and goal_in_props: "set goal \<subseteq> set props"
      and acts_ref_props: "\<forall>a \<in> set actions. set_impl.act_ref_props a"
begin
sublocale set_impl: temp_planning_problem_set_impl at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> "set props" "set actions"
  apply unfold_locales
  subgoal using some_props card_gt_0_iff by blast
  subgoal using some_actions card_gt_0_iff by blast
  subgoal using snaps_disj by auto
  subgoal using init_in_props by blast
  subgoal using goal_in_props by blast
  subgoal using acts_ref_props by blast
  done
end
  
locale temp_planning_problem_list_impl' = temp_planning_problem_list_defs
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"'time"
    and props::   "'proposition list"
    and actions:: "'action list" +
  assumes some_actions: "0 < length actions"
      and some_props: "0 < length props"
      and distinct_props: "distinct props"
      and distinct_actions: "distinct actions"
      and distinct_over_all: "\<forall>a \<in> set actions. distinct (over_all a)"
      and goal_consts_in_init_consts: "set goal - set props \<subseteq> set init - set props"
      and domain_acts_mod_props: "\<forall>a \<in> set actions. act_mod_props a"
      and act_consts_in_init_consts: "action_consts \<subseteq> set init - set props"
begin

sublocale prob_list_impl: 
  temp_planning_problem_list_impl AtStart AtEnd over_all_restr_list lower upper 
  pre_imp_restr_list add_imp_list del_imp_list
  "list_inter props init" "list_inter props goal" \<epsilon> props actions
  apply unfold_locales
  using some_actions apply simp
  using some_props apply simp
  using distinct_props apply simp
  using distinct_actions apply simp
  using distinct_over_all unfolding over_all_restr_list_def apply simp
  subgoal unfolding action_defs.snaps_disj_on_def by (blast intro: inj_onI)
  subgoal by auto
  subgoal by auto
  subgoal using domain_acts_mod_props
    unfolding set_impl.act_mod_props_def set_impl.snap_mod_props_def
    unfolding action_and_prop_set.act_ref_props_def action_and_prop_set.snap_ref_props_def
    unfolding pre_imp_list_def add_imp_list_def del_imp_list_def 
    unfolding over_all_restr_list_def pre_imp_restr_list_def
    unfolding comp_def set_filter
    by auto
  done
end

locale temp_plan_for_problem_list_defs =
  temp_planning_problem_list_defs 
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"'time"
    and props::   "'proposition list"
    and actions:: "'action list" +
  fixes \<pi>:: "('i, 'action, 'time) temp_plan"
begin
sublocale temp_plan_defs at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi>
  by unfold_locales 

sublocale temp_plan_for_action_defs at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi> "set actions"
  by unfold_locales
end

locale temp_plan_for_problem_list_impl = 
  temp_plan_for_problem_list_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi> +
  temp_planning_problem_list_impl at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions 
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"'time"
    and props::   "'proposition list"
    and actions:: "'action list" 
    and \<pi>:: "('i, 'action, 'time) temp_plan" +
  assumes vp: "valid_plan"
      and nso: "no_self_overlap"
      and pap: "plan_actions_in_problem"
begin

sublocale valid_temp_plan at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi> 
  apply unfold_locales using vp by auto

sublocale temp_plan_unique_snaps_nso_dg0  at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi> 
  apply unfold_locales 
  using set_impl.snaps_disj_on_acts set_impl.snaps_disj_on_subset pap plan_actions_in_problem_def 
  using nso by auto

sublocale valid_temp_plan_unique_snaps_nso_dg0 
  at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi> 
  by unfold_locales

sublocale temp_plan_for_problem_impl
  at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi> "set actions" "set props"
   using pap by unfold_locales
end

locale temp_plan_for_problem_list_impl' =
  temp_plan_for_problem_list_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi> +
  temp_planning_problem_list_impl' at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions 
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"'time"
    and props::   "'proposition list"
    and actions:: "'action list" 
    and \<pi>:: "('i, 'action, 'time) temp_plan" +
  assumes vp:  "valid_plan"
      and nso: "no_self_overlap"
      and pap: "plan_actions_in_problem"
begin

sublocale valid_temp_plan at_start at_end "set o over_all" lower upper
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi> 
  apply unfold_locales using vp by auto

(* We first replace snap actions with annotated actions*)
sublocale unique_ref: temp_plan_unique_snaps_nso_dg0 AtStart AtEnd "set o over_all" lower upper 
  pre_imp add_imp del_imp "set init" "set goal"
  apply unfold_locales 
  unfolding prob_list_impl.set_impl.snaps_disj_on_def using nso 
  by (blast intro: inj_onI)+

sublocale valid_plan_ref: plan_validity_equivalence at_start at_end "set o over_all" lower upper 
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi>
  AtStart AtEnd "set o over_all" set_impl.pre_imp set_impl.add_imp set_impl.del_imp "set init" "set goal"
  apply unfold_locales unfolding set_impl.pre_imp_def set_impl.add_imp_def set_impl.del_imp_def by auto

sublocale valid_plan_ref_valid: plan_validity_ref at_start at_end "set o over_all" lower upper 
  "set o pre" "set o adds" "set o dels" "set init" "set goal" \<epsilon> \<pi>
  AtStart AtEnd "set o over_all" set_impl.pre_imp set_impl.add_imp set_impl.del_imp "set init" "set goal"
  by unfold_locales

(* The set of props is a superset of those that can be modified by a plan. Those propositions that
are in the preconditions of actions, are either present in this or the initial set of propositions. *)
sublocale restr_to_props: temp_plan_and_props_defs AtStart AtEnd "set o over_all" lower upper 
  set_impl.pre_imp set_impl.add_imp set_impl.del_imp "set init" "set goal" \<epsilon> \<pi> "set props" by unfold_locales 

sublocale restr_to_props_ref: valid_temp_plan_restr_to_props AtStart AtEnd "set o over_all" lower upper 
  set_impl.pre_imp set_impl.add_imp set_impl.del_imp "set init" "set goal" \<epsilon> \<pi> "set props" 
  apply unfold_locales
  subgoal using domain_acts_mod_props unfolding restr_to_props.plan_acts_mod_props_def 
    using pap unfolding plan_actions_in_problem_def 
    unfolding action_and_prop_set.act_mod_props_def set_impl.act_mod_props_def 
    unfolding action_and_prop_set.snap_mod_props_def set_impl.snap_mod_props_def 
    unfolding set_impl.pre_imp_def set_impl.add_imp_def set_impl.del_imp_def by auto
  subgoal using goal_consts_in_init_consts by auto
  subgoal using act_consts_in_init_consts
    unfolding set_impl.action_consts_def
    unfolding restr_to_props.plan_consts_def
    unfolding set_impl.pre_imp_restr_def set_impl.over_all_restr_def
    unfolding set_impl.add_imp_def set_impl.del_imp_def set_impl.pre_imp_def
    using domain_acts_mod_props 
    using pap unfolding plan_actions_in_problem_def 
    by auto
  done


sublocale valid_plan_valid_2: plan_validity_equivalence AtStart AtEnd 
  "set_impl.over_all_restr" lower upper "restr_to_props.pre_restr" set_impl.add_imp set_impl.del_imp 
  "set init \<inter> set props"
  "set goal \<inter> set props" \<epsilon> \<pi> AtStart AtEnd "set o over_all_restr_list" "set o pre_imp_restr_list" 
  "set o add_imp_list" "set o del_imp_list"  "set (list_inter props init)" "set (list_inter props goal)"
  apply unfold_locales
  unfolding restr_to_props.pre_restr_def pre_imp_restr_list_def 
  unfolding set_impl.pre_imp_def pre_imp_list_def
  unfolding set_impl.add_imp_def add_imp_list_def
  unfolding set_impl.del_imp_def del_imp_list_def
  unfolding over_all_restr_list_def unfolding set_impl.over_all_restr_def
  by auto


sublocale valid_plan_ref_valid_2: plan_validity_ref AtStart AtEnd 
  "restr_to_props.over_all_restr" lower upper "restr_to_props.pre_restr" set_impl.add_imp set_impl.del_imp  "set init \<inter> set props"
  "set goal \<inter> set props" \<epsilon> \<pi> AtStart AtEnd "set o over_all_restr_list" "set o pre_imp_restr_list" 
  "set o add_imp_list" "set o del_imp_list"  "set (list_inter props init)" "set (list_inter props goal)"
  by unfold_locales 

sublocale restr_to_props_valid: temp_plan_for_problem_list_impl AtStart AtEnd over_all_restr_list lower upper 
  pre_imp_restr_list add_imp_list del_imp_list "list_inter props init" "list_inter props goal"
  \<epsilon> props actions \<pi>
  apply unfold_locales 
  using valid_plan_ref_valid_2.valid_plan2.vp
  using nso pap by auto
end

(* global_interpretation temp_planning_problem_list_defs "fst" "fst o snd" "snd o snd"
  "\<lambda>x. Some (lower_bound.GE 0)" "\<lambda>x. Some (upper_bound.LE 2)" fst "fst o snd" "snd o snd"
   "[STR ''a'', STR ''b'']" "[c]" "1" "[STR ''a'', STR ''b'', STR ''c'']" 
   "[(([STR ''a''],[],[STR ''b'']), ([],[],[]), [STR ''a'']), (([STR ''a''],[],[STR ''b'']), ([],[],[]), [STR ''a''])]"
  sorry *)

subsection \<open>Integers as time\<close>
text \<open>Munta uses integers as inputs for clock constraints. Integers can be obtained from rationals by
multiplying by a constant.\<close>

text \<open>Define a temporal planning problem\<close>
locale temp_planning_problem_list_defs_int = 
  fixes at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::   "int"
    and props::   "'proposition list"
    and actions:: "'action list"
  assumes eps_ran: "0 \<le> \<epsilon>"
begin
sublocale rat_impl: temp_planning_problem_list_defs at_start at_end over_all 
  "(map_option (map_lower_bound rat_of_int)) o lower" "(map_option (map_upper_bound rat_of_int)) o upper"
  pre adds dels init goal "rat_of_int \<epsilon>" props actions
  apply unfold_locales using eps_ran by auto
end

text \<open>The version that is used for the compilation\<close>
locale temp_planning_problem_list_impl_int = temp_planning_problem_list_defs_int
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"int"
    and props::   "'proposition list"
    and actions:: "'action list" +
  assumes some_actions: "0 < length actions"
      and some_props: "0 < length props"
      and distinct_props: "distinct props"
      and distinct_actions: "distinct actions"
      and distinct_over_all: "\<forall>a \<in> set actions. distinct (over_all a)"
      and snaps_disj: "rat_impl.set_impl.snaps_disj_on (set actions)"
      and init_in_props: "set init \<subseteq> set props"
      and goal_in_props: "set goal \<subseteq> set props"
      and acts_ref_props: "\<forall>a \<in> set actions. rat_impl.set_impl.act_ref_props a"
begin

sublocale rat_impl: temp_planning_problem_list_impl at_start at_end over_all
  "(map_option (map_lower_bound rat_of_int)) o lower" "(map_option (map_upper_bound rat_of_int)) o upper"
  pre adds dels init goal "rat_of_int \<epsilon>" props actions
  apply unfold_locales
  using some_actions some_props distinct_actions distinct_props 
    distinct_over_all snaps_disj init_in_props goal_in_props acts_ref_props
  by auto

find_theorems name: eps_ran
end

text \<open>The version whose conditions must be satisfied. Once they are, the code from the
above version should be available. \<close>
locale temp_planning_problem_list_impl_int' = temp_planning_problem_list_defs_int
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"int"
    and props::   "'proposition list"
    and actions:: "'action list" +
  assumes some_actions: "0 < length actions"
      and some_props: "0 < length props"
      and distinct_props: "distinct props"
      and distinct_actions: "distinct actions"
      and distinct_over_all: "\<forall>a \<in> set actions. distinct (over_all a)"
      and goal_consts_in_init_consts: "set goal - set props \<subseteq> set init - set props"
      and domain_acts_mod_props: "\<forall>a \<in> set actions. act_mod_props a"
      and act_consts_in_init_consts: "action_consts \<subseteq> set init - set props"
begin

sublocale rat_imp':
  temp_planning_problem_list_impl' at_start at_end over_all
  "(map_option (map_lower_bound rat_of_int)) o lower" "(map_option (map_upper_bound rat_of_int)) o upper"
  pre adds dels init goal "rat_of_int \<epsilon>" props actions
  apply unfold_locales
  using some_actions some_props distinct_actions distinct_props 
    distinct_over_all domain_acts_mod_props goal_consts_in_init_consts act_consts_in_init_consts
  by auto 

sublocale prob_list_impl_int: 
  temp_planning_problem_list_impl_int AtStart AtEnd rat_impl.over_all_restr_list lower upper 
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  "rat_impl.list_inter props init" "rat_impl.list_inter props goal" \<epsilon> props actions
  apply unfold_locales
  using some_actions apply simp
  using some_props apply simp
  using distinct_props apply simp
  using distinct_actions apply simp
  using distinct_over_all unfolding rat_impl.over_all_restr_list_def apply simp
  subgoal unfolding action_defs.snaps_disj_on_def by (blast intro: inj_onI)
  subgoal by auto
  subgoal by auto
  subgoal using domain_acts_mod_props
    unfolding rat_impl.set_impl.act_mod_props_def rat_impl.set_impl.snap_mod_props_def
    unfolding action_and_prop_set.act_ref_props_def action_and_prop_set.snap_ref_props_def
    unfolding rat_impl.pre_imp_list_def rat_impl.add_imp_list_def rat_impl.del_imp_list_def 
    unfolding rat_impl.over_all_restr_list_def rat_impl.pre_imp_restr_list_def
    unfolding comp_def set_filter
    by auto
  done
end

locale temp_plan_for_problem_list_defs_int =
  temp_planning_problem_list_defs_int
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"int"
    and props::   "'proposition list"
    and actions:: "'action list" +
  fixes \<pi>:: "('i, 'action, int) temp_plan"
begin
sublocale rat_impl: temp_plan_for_problem_list_defs at_start at_end over_all
  "(map_option (map_lower_bound rat_of_int)) o lower" "(map_option (map_upper_bound rat_of_int)) o upper"
  pre adds dels init goal "rat_of_int \<epsilon>" props actions 
  "map_option (map_prod id (map_prod rat_of_int rat_of_int)) o \<pi>"
  by unfold_locales

end

locale temp_plan_for_problem_list_impl_int =
  temp_plan_for_problem_list_defs_int at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi> +
  temp_planning_problem_list_impl_int at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions 
    for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::   "int"
    and props::   "'proposition list"
    and actions:: "'action list"
    and \<pi>:: "('i, 'action, int) temp_plan" +
  assumes vp:  "rat_impl.valid_plan"
      and nso: "rat_impl.no_self_overlap"
      and pap: "rat_impl.plan_actions_in_problem"
begin
                                      
sublocale abstr_impl: temp_plan_for_problem_list_impl at_start at_end over_all
  "(map_option (map_lower_bound rat_of_int)) o lower" "(map_option (map_upper_bound rat_of_int)) o upper"
  pre adds dels init goal "rat_of_int \<epsilon>" props actions 
  "map_option (map_prod id (map_prod rat_of_int rat_of_int)) o \<pi>"
  apply unfold_locales using vp nso pap by auto

end

(* An instance of this should be created. *)
locale temp_plan_for_problem_list_impl_int' =
  temp_plan_for_problem_list_defs_int at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi> +
  temp_planning_problem_list_impl_int' at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions 
    for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::   "int"
    and props::   "'proposition list"
    and actions:: "'action list"
    and \<pi>:: "('i, 'action, int) temp_plan" +
  assumes vp:  "rat_impl.valid_plan"
      and nso: "rat_impl.no_self_overlap"
      and pap: "rat_impl.plan_actions_in_problem"
begin

sublocale temp_plan_for_problem_list_impl' at_start at_end over_all
  "(map_option (map_lower_bound rat_of_int)) o lower" "(map_option (map_upper_bound rat_of_int)) o upper"
  pre adds dels init goal "rat_of_int \<epsilon>" props actions 
  "map_option (map_prod id (map_prod rat_of_int rat_of_int)) o \<pi>"
  apply unfold_locales using vp nso pap by auto

(* The code in this sublocale can be called.*)
sublocale conc_ref_impl: temp_plan_for_problem_list_impl_int AtStart AtEnd rat_impl.over_all_restr_list lower upper 
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  "rat_impl.list_inter props init" "rat_impl.list_inter props goal" \<epsilon> props actions \<pi>
  apply unfold_locales
  using restr_to_props_valid.vp 
    restr_to_props_valid.nso 
    restr_to_props_valid.pap
  by auto
end


(* 
locale temp_planning_problem_list_impl_int_ex = temp_planning_problem_list_impl_int'
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition list"
    and lower::   "'action  \<rightharpoonup> int lower_bound"
    and upper::   "'action  \<rightharpoonup> int upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition list"
    and adds::    "'snap_action \<Rightarrow> 'proposition list"
    and dels::    "'snap_action \<Rightarrow> 'proposition list"
    and init::"'proposition list"
    and goal::"'proposition list"
    and \<epsilon>::"int"
    and props::   "'proposition list"
    and actions:: "'action list"
begin
context fixes \<pi>::"('i, 'action, int) temp_plan" 
begin

definition "list_impl_valid_plan \<equiv> temp_plan_defs.valid_plan at_start at_end (set o over_all) 
  ((map_option (map_lower_bound rat_of_int)) o lower) ((map_option (map_upper_bound rat_of_int)) o upper)
  (set o pre) (set o adds) (set o dels) (set init) (set goal) (rat_of_int \<epsilon>) 
  (map_option (map_prod id (map_prod rat_of_int rat_of_int)) o \<pi>)"

definition "list_impl_nso \<equiv> 
  temp_plan_defs.no_self_overlap (map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>)"

definition "list_impl_pap \<equiv> temp_plan_for_action_defs.plan_actions_in_problem 
  (map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>)
  (set actions)"

context 
  assumes vp: "list_impl_valid_plan"
      and nso: "list_impl_nso"
      and pap: "list_impl_pap"
begin
interpretation int: temp_plan_for_problem_list_impl_int'
  apply unfold_locales          
  subgoal using vp unfolding list_impl_valid_plan_def by simp
  subgoal using nso unfolding list_impl_nso_def by simp
  subgoal using pap unfolding list_impl_pap_def by simp
  done


text \<open>If a plan is valid according to the definitions used for this locale, then it is also
  valid in @{locale temp_plan_for_problem_list_impl_int}\<close>
lemma example: "int.valid_plan_valid_2.plan2.valid_plan"
  apply (rule int.conc_ref_impl.vp)
  done
end



end
end
   *)
end
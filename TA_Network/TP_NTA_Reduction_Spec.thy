theory TP_NTA_Reduction_Spec
  imports NTA_Temp_Planning_Sem
      TA_Code.Simple_Network_Language_Export_Code

begin
(* To do: implement the compilation abstractly or directly using show? *)

(* These must be replaced with arbitrary functions again *)
section \<open>Abstract definition of reduction\<close>

subsection \<open>Datatypes to identify clocks, variables and locations associated with actions and propositions\<close>
datatype 'proposition variable =
  PropVar 'proposition |
  PropLock 'proposition |
  ActsActive |
  Effecting |
  PlanningLock

datatype 'action clock =
  ActStart 'action |
  ActEnd 'action |
  Urge

datatype 'action location =
  Off 'action |
  StartInstant 'action |
  PostStart 'action |
  Running 'action |
  EndInstant 'action |
  InitialLocation |
  Planning |
  GoalLocation

lemma variable_UNIV: "(UNIV::'a variable set) = PropVar ` (UNIV::'a set) \<union> PropLock ` UNIV \<union> {ActsActive, PlanningLock, Effecting}" 
  apply (rule UNIV_eq_I)
  subgoal for x by (cases x; blast)
  done

lemma infinite_variable: "infinite (UNIV::'a set) \<Longrightarrow> infinite (UNIV::'a variable set)"
  apply (erule contrapos_nn)
  apply (subst (asm) variable_UNIV)
  apply (subst (asm) finite_Un)+
  apply (elim conjE)
  apply (erule finite_imageD)
  apply (rule injI)
  by simp

lemma clock_UNIV: "(UNIV::'a clock set) = ActStart ` (UNIV::'a set) \<union> ActEnd ` UNIV \<union> {Urge}" 
  apply (rule UNIV_eq_I)
  subgoal for x by (cases x; blast)
  done

lemma infinite_clock: "infinite (UNIV::'a set) \<Longrightarrow> infinite (UNIV::'a clock set)"
  apply (erule contrapos_nn)
  apply (subst (asm) clock_UNIV)
  apply (subst (asm) finite_Un)+
  apply (elim conjE)
  apply (erule finite_imageD)
  apply (rule injI)
  by simp

lemma location_UNIV: "(UNIV::'a location set) = 
  Off ` (UNIV::'a set) 
  \<union> StartInstant ` UNIV 
  \<union> Running ` UNIV
  \<union> EndInstant ` UNIV
  \<union> PostStart ` UNIV
  \<union> {InitialLocation, Planning, GoalLocation}" 
  apply (rule UNIV_eq_I)
  subgoal for x by (cases x; blast)
  done

lemma infinite_location: "infinite (UNIV::'a set) \<Longrightarrow> infinite (UNIV::'a location set)"
  apply (erule contrapos_nn)
  apply (subst (asm) location_UNIV)
  apply (subst (asm) finite_Un)+
  apply (elim conjE)
  apply (erule finite_imageD)
  apply (rule injI)
  by simp

instance location::(finite) finite
  apply standard
  apply (subst location_UNIV)
  apply (subst finite_Un)+
  apply (intro conjI) 
  by simp+

instance variable::(countable) countable
  by countable_datatype

instance clock::(countable) countable
  by countable_datatype

instance location::(countable) countable
  by countable_datatype

(* draft *)
(* IMPORTANT: Replace the hard-coded datatypes for equivalence of representations in the non-draft version *)
(* Time is hardcoded as int here, because this is how Simon does it. He then defines semantics w.r.t. some 
    automata obtained by replacing integers with reals (which satisfy the assumptions about the time class)
    To do: Copy the locale structure, so this extends the temporal planning locales. *)


(*  off \<rightarrow> start instant!! \<rightarrow> pass time \<rightarrow> end instant!! \<rightarrow> off
                  
                  check invariants hold!
                  increment mutex vars!
      check mutex vars!

      apply effects
      check pres

      update start clock!**
      check mutex actions**

      

                                    check lower constraint!
                                    check upper constraint!
    
                                    decrement mutex vars!
                                                  check mutex vars!

                                                  apply effects
                                                  check pres

                                    update end clock!**
                                    check mutex actions**

                                    
                                                            

    Mutual exclusivity is calculated using intersection of additions and deletions. 

    Applying effects is convenient in the same transition as checking the mutex variables, because
    only deletions "access" invariants (i.e. make them false).

    Incrementing and decrementing the must happen when transitioning out of and into the urgent 
    locations, to allow simultaneous snap-action execution
    
    Start and end clocks must be updated as the instant is entered, so that mutex conditions can be checked.
    0-separation is hardcoded into this translation.

    Items marked with ! must be scheduled in the order to be correctly applied.

    * and ** mark some relationship
    
    Checking preconditions should be done at the start of the instants. Could result in fewer transitions
    taken while model-checking.

    When the mutex variable is incremented, the invariant propositions has to be checked to be true. 
    Otherwise, it could be false and never explicitly set to false during action execution, and still not hold.
    
  *)
locale tp_nta_reduction_spec =
  fixes init :: "('proposition::countable) list"
    and goal :: "'proposition list"
    and at_start :: "('action::countable) \<Rightarrow> 'snap_action"
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
  assumes domain_ref_fluents: "fluent_domain (set props) at_start at_end
    (set o over_all) (set o pre) (set o adds) (set o dels) (set actions)"
      and init_props: "set init \<subseteq> set props"
      and goal_props: "set goal \<subseteq> set props"
      and infinite_actions: "infinite (UNIV::'action set)"
      and infinite_propositions: "infinite (UNIV::'proposition set)"
      and distinct_props: "distinct props"
      and distinct_actions: "distinct actions"
      and some_actions: "0 < length actions"
      and some_propositions: "0 < length props"
      and eps_range: "0 \<le> \<epsilon>"
      and at_start_inj: "inj_on at_start (set actions)"
      and at_end_inj: "inj_on at_end (set actions)"
      and snaps_disj: "at_start ` (set actions) \<inter> at_end ` (set actions) = {}"
      and distinct_over_all: "\<forall>a \<in> set actions. distinct (over_all a)"
begin

subsection \<open>Abbreviations for encoding propositions into clocks\<close>
abbreviation "var_is n v \<equiv> bexp.eq (exp.var v) (exp.const n)"
abbreviation "inc_var n v \<equiv> (v, exp.binop (+) (exp.var v) (exp.const n))"
abbreviation "set_var n v \<equiv> (v, exp.const n)"


fun bexp_and_all::"('a, 'b) bexp list \<Rightarrow> ('a, 'b) bexp" where
"bexp_and_all [] = bexp.true" |
"bexp_and_all (x#xs) = bexp.and x (bexp_and_all xs)"

(* To do: Reason about sets that the lists actually represent *)

definition is_prop_ab::"
   int \<Rightarrow> 'proposition
\<Rightarrow> ('proposition variable, int) bexp" where
"is_prop_ab n \<equiv> var_is n o PropVar"

definition set_prop_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"set_prop_ab n = set_var n o PropVar"

definition inc_prop_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"inc_prop_ab n \<equiv> inc_var n o PropVar"

definition is_prop_lock_ab::"
   int \<Rightarrow> 'proposition
\<Rightarrow> ('proposition variable, int) bexp" where
"is_prop_lock_ab n \<equiv> var_is n o PropLock"

definition set_prop_lock_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"set_prop_lock_ab n \<equiv> set_var n o PropLock"

definition inc_prop_lock_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"inc_prop_lock_ab n \<equiv> inc_var n o PropLock"
  


subsection \<open>Automata for individual actions\<close>
abbreviation mutex_effects_spec::"
   'snap_action 
\<Rightarrow> 'snap_action 
\<Rightarrow> bool" where
"mutex_effects_spec a b \<equiv> mutex_snap_action (set o pre) (set o adds) (set o dels) a b"

definition int_clocks_spec::"'snap_action \<Rightarrow> 'action clock list" where
"int_clocks_spec s \<equiv>
let 
  int_starts = filter (\<lambda>a. mutex_effects_spec s (at_start a)) actions;
  start_clocks = map ActStart int_starts;
  int_ends = filter (\<lambda>a. mutex_effects_spec s (at_end a)) actions;
  end_clocks = map ActEnd int_ends
in 
  start_clocks @ end_clocks
"

(* The transition from the location representing the action being inactive to the one representing
  the instant the action starts *)
definition start_edge_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"start_edge_spec a \<equiv> 
let 
  start_snap = at_start a;
  
  guard = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec start_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec start_snap);
  
  not_locked_check = map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds start_snap)) (dels start_snap));
  pre_check = map (is_prop_ab 1) (pre start_snap);
  var_check = bexp_and_all (not_locked_check @ pre_check );
  
  add_upds = map (set_prop_ab 1) (adds start_snap);
  del_upds = map (set_prop_ab 0) (dels start_snap);
  upds = (inc_var 1 ActsActive) # (inc_var 1 Effecting) # del_upds @ add_upds;

  resets = [ActStart a]
in (Off a, var_check, guard, Sil (STR ''''), upds, resets, StartInstant a)"

definition edge_2_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"edge_2_spec a \<equiv> 
let 
  check_invs = bexp_and_all (map (is_prop_ab 1) (over_all a));
  upds = (inc_var (-1) Effecting) # map (inc_prop_lock_ab 1) (over_all a)
in
  (StartInstant a, check_invs, [], Sil (STR ''''), upds, [], Running a)
"


definition leave_start_edge_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"leave_start_edge_spec a \<equiv> 
let 
  effects_applied = var_is 0 Effecting;
  check_invs = bexp_and_all (map (is_prop_ab 1) (over_all a))
in
  (PostStart a, bexp.and effects_applied check_invs, [], Sil (STR ''''), [], [], Running a)
"

definition l_dur_spec::"'action \<Rightarrow> ('action clock, int) acconstraint list" where
"l_dur_spec act \<equiv> (case lower act of 
  None \<Rightarrow> []
| Some (lower_bound.GE n) \<Rightarrow> [acconstraint.GE (ActStart act) n]
| Some (lower_bound.GT n) \<Rightarrow> [acconstraint.GT (ActStart act) n])"

definition u_dur_spec::"'action \<Rightarrow> _" where
"u_dur_spec a \<equiv> (case upper a of 
  None \<Rightarrow> []
| Some (upper_bound.LE n) \<Rightarrow> [acconstraint.LE (ActStart a) n]
| Some (upper_bound.LT n) \<Rightarrow> [acconstraint.LT (ActStart a) n])"

definition edge_3_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"edge_3_spec a \<equiv>
let
  end_snap = at_end a;
  
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec end_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec end_snap);

  guard = l_dur_spec a @ u_dur_spec a @ int_clocks;

  upds = (inc_var 1 Effecting) # map (inc_prop_lock_ab (-1)) (over_all a);
  
  resets = [ActEnd a]
in 
  (Running a, bexp.true, guard, Sil (STR ''''), upds , resets, EndInstant a)
"

(* Checking that no interfering snap-action is starting is done using the clock constraints. 
It is sufficient to check that the end does not interfere with the start, because interference is
reflexive and the start clock has been reset already *)
definition instant_trans_edge_spec::"'action 
  \<Rightarrow> 'action location 
    \<times> ('proposition variable, int) Simple_Expressions.bexp 
    \<times> ('action clock, int) acconstraint list 
    \<times> String.literal act 
    \<times> ('proposition variable \<times> ('proposition variable, int) exp) list 
    \<times> 'action clock list 
    \<times> 'action location" where
"instant_trans_edge_spec a \<equiv>
let
  end_snap = at_end a;
  start_snap = at_start a;
  
  int_clocks =  map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec end_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec end_snap);

  guard = l_dur_spec a @ u_dur_spec a @ int_clocks;

  resets = [ActEnd a]
in 
  (StartInstant a, bexp.true, guard, Sil (STR ''''), [], resets, EndInstant a)
"

(* The not-locked check should only apply to those deletions which are not immediately overwritten by additions *)
definition end_edge_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"end_edge_spec a \<equiv> 
let 
  end_instant = EndInstant a;
  off = Off a;

  end_snap = at_end a;

  not_locked_check = map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds end_snap)) (dels end_snap));
  pre_check = map (is_prop_ab 1) (pre end_snap);
  check = bexp_and_all (not_locked_check @ pre_check);
  
  add_upds = map (set_prop_ab 1) (adds end_snap);
  del_upds = map (set_prop_ab 0) (dels end_snap);
  upds = (inc_var (-1) ActsActive) # (inc_var (-1) Effecting) # del_upds @ add_upds
in
  (end_instant, check, [], Sil (STR ''''), upds, [], off)
"


definition action_to_automaton_spec::"'action \<Rightarrow> 
  'action location \<times>
    'action location list \<times>
    'action location list \<times>
    'action location list \<times>
    (
      'action location \<times>
      ('proposition variable, int) Simple_Expressions.bexp \<times>
      ('action clock, int) acconstraint list \<times> 
      String.literal act \<times> 
      (
        'proposition variable \<times> 
        ('proposition variable, int) exp
      ) list \<times> 
      'action clock list \<times> 
      'action location
    ) list \<times>
    (
      'action location \<times> 
      ('action clock, int) acconstraint list
    ) list" where 
"action_to_automaton_spec a \<equiv>
let 
  init_loc = Off a;
  locs = [Off a, StartInstant a, Running a, EndInstant a, PostStart a];
  committed_locs = (Nil::'action location list);
  urgent_locs = [StartInstant a, EndInstant a, PostStart a];
  edges = [start_edge_spec a, edge_2_spec a, edge_3_spec a, end_edge_spec a, instant_trans_edge_spec a, leave_start_edge_spec a];
  invs = []
in 
  (init_loc, locs, committed_locs, urgent_locs, edges, invs)"

subsection \<open>Main automaton to initialise problem and check goal satisfactions\<close>
definition main_auto_init_edge_spec::"'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"main_auto_init_edge_spec \<equiv>
let
  can_start = var_is 0 PlanningLock;
  
  permit_planning = set_var 1 PlanningLock;
  set_active = set_var 0 ActsActive;
  set_props = map (set_prop_ab 1) init;
  upds = permit_planning # set_active # set_props
in
  (InitialLocation, can_start, [], Sil (STR ''''), upds, [], Planning)
"

definition main_auto_goal_edge_spec::"'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"main_auto_goal_edge_spec \<equiv>
let
  can_end = [var_is 1 PlanningLock, var_is 0 ActsActive];
  goal_sat = map (is_prop_ab 1) goal;
  cond = bexp_and_all (can_end @ goal_sat);
  
  lock_plan = set_var 2 PlanningLock
in
  (Planning, cond, [], Sil (STR ''''), [lock_plan], [], GoalLocation)
"

definition main_auto_loop_spec::"'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"main_auto_loop_spec \<equiv>
  (GoalLocation, bexp.true, [], Sil (STR ''''), [], [], GoalLocation)
"

definition main_auto_spec::"
    'action location \<times>
    'action location list \<times>
    'action location list \<times>
    'action location list \<times>
    (
      'action location \<times>
      ('proposition variable, int) Simple_Expressions.bexp \<times>
      ('action clock, int) acconstraint list \<times> 
      String.literal act \<times> 
      (
        'proposition variable \<times> 
        ('proposition variable, int) exp
      ) list \<times> 
      'action clock list \<times> 
      'action location
    ) list \<times>
    (
      'action location \<times> 
      ('action clock, int) acconstraint list
    ) list" where
"main_auto_spec \<equiv> 
let
  init_loc = InitialLocation;
  locs = [InitialLocation, Planning, GoalLocation];
  committed_locs = [];
  urgent_locs = [InitialLocation, GoalLocation];
  edges = [main_auto_init_edge_spec, main_auto_goal_edge_spec, main_auto_loop_spec];
  invs = []
in
  (init_loc, locs, committed_locs, urgent_locs, edges, invs)
"

subsection \<open>The entire network\<close>


definition inv_vars_spec::"'proposition list \<Rightarrow> 'proposition variable set" where
"inv_vars_spec i \<equiv> 
let 
  vars = map PropLock i @ map PropVar i
in set vars"

definition snap_vars_spec::"'snap_action \<Rightarrow> 'proposition variable set" where
"snap_vars_spec s \<equiv>
let
  pre_vars = map PropVar (pre s);
  add_vars = map PropVar (adds s);  
  del_vars = map PropLock (filter (\<lambda>p. p \<notin> set (adds s)) (dels s)) @ map PropVar (dels s);
  vars = pre_vars @ add_vars @ del_vars
in set vars
"

definition action_vars_spec::"'action \<Rightarrow> 'proposition variable set" where
"action_vars_spec a \<equiv> 
let
  inv_vars = inv_vars_spec (over_all a);
  snap_vars = snap_vars_spec (at_start a) \<union> snap_vars_spec (at_end a)
in inv_vars \<union> snap_vars"

definition all_vars_spec::"('proposition variable \<times> int \<times> int) list" where
"all_vars_spec \<equiv>
let
  action_vars = fold (\<union>) (map action_vars_spec actions) {};
  init_vars = set (map PropVar init);
  goal_vars = set (map PropVar goal);
  vars_occ = action_vars \<union> init_vars \<union> goal_vars;

  prop_lock_var_defs = map (\<lambda>p. (PropLock p, 0::int, int (length actions))) props;
  prop_var_var_defs = map (\<lambda>p . (PropVar p, 0::int, 1::int)) props;

  prop_var_defs = (prop_lock_var_defs @ prop_var_var_defs) |> filter (\<lambda>x. fst x \<in> vars_occ);
  acts_active_var = (ActsActive, 0, int (length actions));
  effecting_var = (Effecting, 0, int (length actions));
  planning_lock_var = (PlanningLock, 0, 2::int)
in
  [acts_active_var, effecting_var, planning_lock_var] @ prop_var_defs"

definition timed_automaton_net_spec::"
  (
    nat \<times>
    'action location \<times>
    'action location list \<times>
    'action location list \<times>
    'action location list \<times>
    (
      'action location \<times>
      ('proposition variable, int) Simple_Expressions.bexp \<times>
      ('action clock, int) acconstraint list \<times> 
      String.literal act \<times> 
      (
        'proposition variable \<times> 
        ('proposition variable, int) exp
      ) list \<times> 
      'action clock list \<times> 
      'action location) list \<times>
      ('action location \<times> 
      ('action clock, int) acconstraint list
    ) list
  ) list \<times>
  'action clock list \<times> 
  ('proposition variable \<times> int \<times> int) list \<times> 
  (nat, 'action location, 'proposition variable, int) formula" where
"timed_automaton_net_spec \<equiv> 
let
  automata = main_auto_spec # (map action_to_automaton_spec actions);
  automata = zip [0..<length automata] automata;

  clocks = map ActStart actions @ map ActEnd actions;

  formula = formula.EX (loc 0 GoalLocation)
in (automata, clocks, all_vars_spec, formula)"
(* The id of the main automaton is 0 *)
end



end
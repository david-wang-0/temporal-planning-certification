theory TP_NTA_Reduction_Spec
  imports Temporal_Planning_Base.Temporal_Plans
      Simple_Networks.Simple_Network_Language_Renaming
begin
  
(* To do: implement the compilation abstractly or directly using show? *)

hide_class DBM.time

(* These must be replaced with arbitrary functions again *)

datatype 'proposition variable =
  PropVar 'proposition |
  PropLock 'proposition |
  ActsActive |
  PlanningLock

datatype 'action clock =
  ActStart 'action |
  ActEnd 'action

datatype 'action location =
  Off 'action |
  StartInstant 'action |
  Running 'action |
  EndInstant 'action |
  InitialLocation |
  Planning |
  GoalLocation

datatype 'action auto_id =
  ActAuto 'action |
  MainAuto

(* draft *)
(* IMPORTANT: Replace the hard-coded datatypes for equivalence of representations in the non-draft version *)
locale tp_nta_reduction_spec =
  fixes init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> ('time::time) lower_bound option"
    and upper :: "'action \<Rightarrow> 'time upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "'time"
    and props :: "'proposition list"
    and actions :: "'action list"
begin

abbreviation "var_is n v \<equiv> bexp.eq (exp.var v) (exp.const n)"
abbreviation "inc_var n v \<equiv> (v, exp.binop (+) (exp.var v) (exp.const n))"
abbreviation "set_var n v \<equiv> (v, exp.const n)"


fun bexp_and_all::"('a, 'b) bexp list \<Rightarrow> ('a, 'b) bexp" where
"bexp_and_all [] = bexp.true" |
"bexp_and_all (x#xs) = bexp.and x (bexp_and_all xs)"

(* To do: Reason about sets that the lists actually represent *)

(* Are variables always integers? *)
definition is_prop_ab::"
   int \<Rightarrow> 'proposition
\<Rightarrow> ('proposition variable, int) bexp" where
"is_prop_ab n prop \<equiv> var_is n (PropVar prop)"

definition set_prop_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"set_prop_ab n prop = set_var n (PropVar prop)"

definition inc_prop_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"inc_prop_ab n prop \<equiv> inc_var n (PropVar prop)"

definition is_prop_lock_ab::"
   int \<Rightarrow> 'proposition
\<Rightarrow> ('proposition variable, int) bexp" where
"is_prop_lock_ab n prop \<equiv> var_is n (PropLock prop)"

definition set_prop_lock_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"set_prop_lock_ab n prop \<equiv> set_var n (PropLock prop)"

definition inc_prop_lock_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> 'proposition variable \<times> ('proposition variable, int) exp" where
"inc_prop_lock_ab n prop \<equiv> inc_var n (PropLock prop)"
  


(* How do we handle actions with 0 duration and invariants?
  Can a start interfere with an end? Yes
  If the start and end execute in the same instance, will it allow a snap-action that is mutex with one
  of the two to execute? No, because that is excluded by the start and end clocks. *)

(* What happens when an action has a duration of 0? Should it only be able to start an infinite number
  of times when it does not interfere with itself? *)

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
definition start_edge_spec::"'action \<Rightarrow> _" where
"start_edge_spec a \<equiv> 
let 
  off = Off a;
  start_inst = StartInstant a;

  start_snap = at_start a;
  
  guard = map (\<lambda>x. acconstraint.GT x (0::'time)) (int_clocks_spec start_snap);
  
  not_locked_check = map (is_prop_lock_ab 0) (dels start_snap);
  pre_check = map (is_prop_ab 1) (pre start_snap);
  var_check = bexp_and_all (not_locked_check @ pre_check);
  
  add_upds = map (set_prop_ab 1) (adds start_snap);
  del_upds = map (set_prop_ab 0) (dels start_snap);
  upds = add_upds @ del_upds;

  resets = [AtStart a]
in (off, var_check, guard, Sil (STR ''''), upds, resets, start_inst)"

definition edge_2_spec::"'action \<Rightarrow> _" where
"edge_2_spec a \<equiv> 
let 
  start_inst = StartInstant a;
  pass_time = Running a;

  check_invs = bexp_and_all (map (is_prop_lock_ab 1) (over_all a));
  lock_invs = map (inc_prop_lock_ab 1) (over_all a)
in
  (start_inst, check_invs, [], Sil (STR ''''), lock_invs, [], pass_time)
"

find_theorems name: "Option*map"

definition l_dur_spec::"'action \<Rightarrow> _" where
"l_dur_spec a \<equiv> (case lower a of 
  None \<Rightarrow> []
| Some (lower_bound.GE n) \<Rightarrow> [acconstraint.GE (ActStart a) n]
| Some (lower_bound.GT n) \<Rightarrow> [acconstraint.GT (ActStart a) n])"

definition u_dur_spec::"'action \<Rightarrow> _" where
"u_dur_spec a \<equiv> (case upper a of 
  None \<Rightarrow> []
| Some (upper_bound.LE n) \<Rightarrow> [acconstraint.LE (ActStart a) n]
| Some (upper_bound.LT n) \<Rightarrow> [acconstraint.LT (ActStart a) n])"

definition edge_3_spec::"'action \<Rightarrow> _" where
"edge_3_spec a \<equiv>
let
  end_snap = at_end a;
  
  int_clocks = map (\<lambda>x. acconstraint.GT x (0::'time)) (int_clocks_spec end_snap);

  u_dur_const = u_dur_spec a;
  guard = l_dur_spec a @ u_dur_spec a @ int_clocks;

  unlock_invs = map (inc_prop_lock_ab (-1)) (over_all a)
in 
  (Running a, bexp.true, guard, Sil (STR ''''), [], [], EndInstant a)
"

definition end_edge_spec::"'action \<Rightarrow> _" where
"end_edge_spec a \<equiv> 
let 
  end_instant = EndInstant a;
  off = Off a;

  end_snap = at_end a;

  not_locked_check = map (is_prop_lock_ab 0) (dels end_snap);
  pre_check = map (is_prop_ab 1) (pre end_snap);
  check = bexp_and_all (not_locked_check @ pre_check);
  
  adds = map (set_prop_ab 1) (adds end_snap);
  dels = map (set_prop_ab 0) (dels end_snap)
  
in
  (end_instant, check, [], Sil (STR ''''), adds @ dels, [], off)
"

  (* To do: Implement abstract definition later *)
  (* This reduction has a different definition of no self overlap. Ends can interfere.
     Actions can also have a duration of 0, if this matters. *)
definition action_to_automaton_spec::"'action \<Rightarrow> _" where 
"action_to_automaton_spec a \<equiv>
let 
  init_loc = Off a;
  locs = [Off a, StartInstant a, Running a, EndInstant a];
  committed_locs = (Nil::'action location list);
  urgent_locs = [StartInstant a, EndInstant a];
  edges = [start_edge_spec a, edge_2_spec a, edge_3_spec a, end_edge_spec a];
  invs = ([]::('action location \<times> ('action clock, 'time) acconstraint list) list)
in 
  (ActAuto a, init_loc, locs, committed_locs, urgent_locs, edges, invs)"

(* To do: add the conditions on the planning state *)

definition main_auto_init_edge_spec::"_" where
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

definition main_auto_goal_edge_spec::"_" where
"main_auto_goal_edge_spec \<equiv>
let
  can_end = var_is 1 PlanningLock;
  goal_sat = map (is_prop_ab 1) goal;
  cond = bexp_and_all (can_end # goal_sat);
  
  lock_plan = set_var 2 PlanningLock
in
  (Planning, cond, [], Sil (STR ''''), [lock_plan], [], GoalLocation)
"

definition main_auto_spec::"_" where
"main_auto_spec \<equiv> 
let
  init_loc = InitialLocation;
  locs = [InitialLocation, Planning, GoalLocation];
  committed_locs = [];
  urgent_locs = [InitialLocation, GoalLocation];
  edges = [main_auto_init_edge_spec, main_auto_goal_edge_spec];
  invs = []
in
  (MainAuto, init_loc, locs, committed_locs, urgent_locs, edges, invs)
"

definition timed_automaton_net_spec::"_" where
"timed_automaton_net_spec _ \<equiv> 
let
  automata = main_auto_spec # (map action_to_automaton_spec actions);
  clocks = map ActStart actions @ map ActEnd actions;
  prop_lock_var_defs = map (\<lambda>p. (PropLock p, 0::int, int (length actions))) props;
  prop_var_vars_defs = map (\<lambda>p . (PropVar p, 0::int, 1::int)) props
in (automata, clocks)"

end

context tp_nta_reduction_spec
begin
sublocale Simple_Network_Rename_Formula
end

(* Functions from actions to locations and clocks, and from propositions to variables must be fixed
  later. Renamings like in Munta. *)

(* Lists are used to implement sets. Lift this to a higher level. *)

(* Do the conversion to strings later, as renamings *)
(* Right now, do the conversion using the actual types as placeholders.
Propositions and actions are not renamed in variables  *)
locale ta_net_temp_planning = ta_temp_planning init _ at_start _ _ lower
  for init::"('proposition::linorder) set"
  and at_start::"('action::linorder) \<Rightarrow> 'snap_action set"
  and lower::"'action \<Rightarrow> ('time::time) lower_bound option" +
fixes name::"'action \<Rightarrow> string"
begin

end


end
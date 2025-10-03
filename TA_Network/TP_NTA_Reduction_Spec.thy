theory TP_NTA_Reduction_Spec
  imports Temporal_Planning_Base.Temporal_Plans_Theory
      Temporal_Planning_Base.Temporal_Plans_Code
      Munta_Model_Checker.Simple_Network_Language_Export_Code

begin
section \<open>Abstract definition of reduction\<close>

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

locale tp_nta_reduction_spec = temp_planning_problem_list_impl_int
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
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
    and actions :: "'action list" +
  fixes act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
begin

find_theorems name: "local*unique_name"

(*   fixes prop_to_var prop_to_lock
    and acts_active effecting planning_lock
  fixes act_to_start_clock act_to_end_clock 
    and urge_clock
  fixes off_locct_to_starting_loc act_to_running_lock act_to_end_loc
    and init_loc planning_loc goal_loc *)
find_consts name: "implode"

definition "prop_to_var p \<equiv> STR ''var_'' + prop_to_name p"
definition "prop_to_lock p \<equiv> STR ''lock_'' + prop_to_name p"
definition "acts_active \<equiv> STR ''acts_active''"
definition "planning_lock \<equiv> STR ''planning_lock''"

definition "act_to_start_clock a \<equiv> STR ''start_'' + act_to_name a"
definition "act_to_end_clock a \<equiv> STR ''end_'' + act_to_name a"
definition "urge_clock \<equiv> STR ''urge_clock''"

definition "off_loc \<equiv> 0::nat"
definition "starting_loc \<equiv> 1::nat"
definition "running_loc \<equiv> 2::nat"
definition "ending_loc \<equiv> 3::nat"

definition "init_loc \<equiv> 0::nat"
definition "planning_loc \<equiv> 1::nat"
definition "goal_loc \<equiv> 2::nat"

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
\<Rightarrow> (String.literal, int) bexp" where
"is_prop_ab n \<equiv> var_is n o prop_to_var"

definition set_prop_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> String.literal \<times> (String.literal, int) exp" where
"set_prop_ab n = set_var n o prop_to_var"

definition inc_prop_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> String.literal \<times> (String.literal, int) exp" where
"inc_prop_ab n \<equiv> inc_var n o prop_to_var"

definition is_prop_lock_ab::"
   int \<Rightarrow> 'proposition
\<Rightarrow> (String.literal, int) bexp" where
"is_prop_lock_ab n \<equiv> var_is n o prop_to_lock"

definition set_prop_lock_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> String.literal \<times> (String.literal, int) exp" where
"set_prop_lock_ab n \<equiv> set_var n o prop_to_lock"

definition inc_prop_lock_ab::"
  int \<Rightarrow> 'proposition
\<Rightarrow> String.literal \<times> (String.literal, int) exp" where
"inc_prop_lock_ab n \<equiv> inc_var n o prop_to_lock"
  

subsection \<open>Automata for individual actions\<close>
abbreviation mutex_effects_spec::"
   'snap_action 
\<Rightarrow> 'snap_action 
\<Rightarrow> bool" where
"mutex_effects_spec a b \<equiv> rat_impl.set_impl.mutex_snap_action a b"

definition int_clocks_spec::"'snap_action \<Rightarrow> String.literal list" where
"int_clocks_spec s \<equiv>
let 
  int_starts = filter (\<lambda>a. mutex_effects_spec s (at_start a)) actions;
  start_clocks = map act_to_start_clock int_starts;
  int_ends = filter (\<lambda>a. mutex_effects_spec s (at_end a)) actions;
  end_clocks = map act_to_end_clock int_ends
in 
  start_clocks @ end_clocks
"

(* The transition from the location representing the action being inactive to the one representing
  the instant the action starts *)
definition start_edge_spec::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"start_edge_spec a \<equiv> 
let 
  start_snap = at_start a;
  
  guard = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec start_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec start_snap);
  
  not_locked_check = map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds start_snap)) (dels start_snap));
  pre_check = map (is_prop_ab 1) (pre start_snap);
  var_check = bexp_and_all (not_locked_check @ pre_check );
  
  add_upds = map (set_prop_ab 1) (adds start_snap);
  del_upds = map (set_prop_ab 0) (dels start_snap);
  upds = (inc_var 1 acts_active) # del_upds @ add_upds;

  resets = [act_to_start_clock a]
in (off_loc, var_check, guard, Sil (STR ''''), upds, resets, starting_loc)"

definition edge_2_spec::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"edge_2_spec a \<equiv> 
let 
  check_invs = bexp_and_all (map (is_prop_ab 1) (over_all a));
  upds = map (inc_prop_lock_ab 1) (over_all a)
in
  (starting_loc, check_invs, [], Sil (STR ''''), upds, [], running_loc)
"



definition l_dur_spec::"'action \<Rightarrow> (String.literal, int) acconstraint list" where
"l_dur_spec act \<equiv> (case lower act of 
  None \<Rightarrow> []
| Some (lower_bound.GE n) \<Rightarrow> [acconstraint.GE (act_to_start_clock act) n]
| Some (lower_bound.GT n) \<Rightarrow> [acconstraint.GT (act_to_start_clock act) n])"

definition u_dur_spec::"'action \<Rightarrow> _" where
"u_dur_spec a \<equiv> (case upper a of 
  None \<Rightarrow> []
| Some (upper_bound.LE n) \<Rightarrow> [acconstraint.LE (act_to_start_clock a) n]
| Some (upper_bound.LT n) \<Rightarrow> [acconstraint.LT (act_to_start_clock a) n])"

definition edge_3_spec::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"edge_3_spec a \<equiv>
let
  end_snap = at_end a;
  
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec end_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec end_snap);

  guard = l_dur_spec a @ u_dur_spec a @ int_clocks;

  upds = map (inc_prop_lock_ab (-1)) (over_all a);
  
  resets = [act_to_end_clock a]
in 
  (running_loc, bexp.true, guard, Sil (STR ''''), upds , resets, ending_loc)
"

(* Checking that no interfering snap-action is starting is done using the clock constraints. 
It is sufficient to check that the end does not interfere with the start, because interference is
reflexive and the start clock has been reset already *)
definition instant_trans_edge_spec::"'action 
  \<Rightarrow> nat 
    \<times> (String.literal, int) Simple_Expressions.bexp 
    \<times> (String.literal, int) acconstraint list 
    \<times> String.literal act 
    \<times> (String.literal \<times> (String.literal, int) exp) list 
    \<times> String.literal list 
    \<times> nat" where
"instant_trans_edge_spec a \<equiv>
let
  end_snap = at_end a;
  start_snap = at_start a;
  
  int_clocks =  map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec end_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec end_snap);

  guard = l_dur_spec a @ u_dur_spec a @ int_clocks;

  resets = [act_to_end_clock a]
in 
  (starting_loc, bexp.true, guard, Sil (STR ''''), [], resets, ending_loc)
"

(* The not-locked check should only apply to those deletions which are not immediately overwritten by additions *)
definition end_edge_spec::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"end_edge_spec a \<equiv> 
let 
  end_instant = ending_loc;
  off = off_loc;

  end_snap = at_end a;

  not_locked_check = map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds end_snap)) (dels end_snap));
  pre_check = map (is_prop_ab 1) (pre end_snap);
  check = bexp_and_all (not_locked_check @ pre_check);
  
  add_upds = map (set_prop_ab 1) (adds end_snap);
  del_upds = map (set_prop_ab 0) (dels end_snap);
  upds = (inc_var (-1) acts_active) # del_upds @ add_upds
in
  (end_instant, check, [], Sil (STR ''''), upds, [], off)
"


definition action_to_automaton_spec::"'action \<Rightarrow>
  nat list 
  \<times> nat list 
  \<times> (nat 
    \<times> (String.literal, int) Simple_Expressions.bexp 
    \<times> (String.literal, int) acconstraint list 
    \<times> String.literal act 
    \<times> (String.literal 
    \<times> (String.literal, int) exp) list 
    \<times> String.literal list 
    \<times> nat) list 
  \<times> (nat \<times> (String.literal, int) acconstraint list) list" where 
"action_to_automaton_spec a \<equiv>
let 
  committed_locs = (Nil::nat list);
  urgent_locs = [starting_loc, ending_loc];
  edges = [start_edge_spec a, edge_2_spec a, edge_3_spec a, end_edge_spec a, instant_trans_edge_spec a];
  invs = []::(nat \<times> (String.literal, int) acconstraint list) list
in 
  (committed_locs, urgent_locs, edges, invs)"

subsection \<open>Main automaton to initialise problem and check goal satisfactions\<close>
definition main_auto_init_edge_spec::"nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_init_edge_spec \<equiv>
let
  can_start = var_is 0 planning_lock;
  
  permit_planning = set_var 1 planning_lock;
  set_active = set_var 0 acts_active;
  set_props = map (set_prop_ab 1) init;
  upds = permit_planning # set_active # set_props
in
  (init_loc, can_start, [], Sil (STR ''''), upds, [], planning_loc)
"

definition main_auto_goal_edge_spec::"nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_goal_edge_spec \<equiv>
let
  can_end = [var_is 1 planning_lock, var_is 0 acts_active];
  goal_sat = map (is_prop_ab 1) goal;
  cond = bexp_and_all (can_end @ goal_sat);
  
  lock_plan = set_var 2 planning_lock
in
  (planning_loc, cond, [], Sil (STR ''''), [lock_plan], [], goal_loc)
"

definition main_auto_loop_spec::"nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_loop_spec \<equiv>
  (goal_loc, bexp.true, [], Sil (STR ''''), [], [], goal_loc)
"

definition main_auto_spec::"
  nat list 
  \<times> nat list 
  \<times> (nat 
    \<times> (String.literal, int) Simple_Expressions.bexp 
    \<times> (String.literal, int) acconstraint list 
    \<times> String.literal act 
    \<times> (String.literal 
    \<times> (String.literal, int) exp) list 
    \<times> String.literal list 
    \<times> nat) list 
  \<times> (nat \<times> (String.literal, int) acconstraint list) list" where
"main_auto_spec \<equiv> 
let
  committed_locs = [];
  urgent_locs = [init_loc, goal_loc];
  edges = [main_auto_init_edge_spec, main_auto_goal_edge_spec, main_auto_loop_spec];
  invs = []
in
  (committed_locs, urgent_locs, edges, invs)
"

subsection \<open>The entire network\<close>


definition inv_vars_spec::"'proposition list \<Rightarrow> String.literal set" where
"inv_vars_spec i \<equiv> 
let 
  vars = map prop_to_lock i @ map prop_to_var i
in set vars"

definition snap_vars_spec::"'snap_action \<Rightarrow> String.literal set" where
"snap_vars_spec s \<equiv>
let
  pre_vars = map prop_to_var (pre s);
  add_vars = map prop_to_var (adds s);  
  del_vars = map prop_to_lock (filter (\<lambda>p. p \<notin> set (adds s)) (dels s)) @ map prop_to_var (dels s);
  vars = pre_vars @ add_vars @ del_vars
in set vars
"

definition action_vars_spec::"'action \<Rightarrow> String.literal set" where
"action_vars_spec a \<equiv> 
let
  inv_vars = inv_vars_spec (over_all a);
  snap_vars = snap_vars_spec (at_start a) \<union> snap_vars_spec (at_end a)
in inv_vars \<union> snap_vars"

definition all_vars_spec::"(String.literal \<times> int \<times> int) list" where
"all_vars_spec \<equiv>
let
  action_vars = fold (\<union>) (map action_vars_spec actions) {};
  init_vars = set (map prop_to_var init);
  goal_vars = set (map prop_to_var goal);
  vars_occ = action_vars \<union> init_vars \<union> goal_vars;

  prop_lock_var_defs = map (\<lambda>p. (prop_to_lock p, 0::int, int (length actions))) props;
  prop_var_var_defs = map (\<lambda>p . (prop_to_var p, 0::int, 1::int)) props;

  prop_var_defs = (prop_lock_var_defs @ prop_var_var_defs) |> filter (\<lambda>x. fst x \<in> vars_occ);
  acts_active_var = (acts_active, 0, int (length actions));
  planning_lock_var = (planning_lock, 0, 2::int)
in
  [acts_active_var, planning_lock_var] @ prop_var_defs"


definition timed_automaton_net_spec::"
  (nat list 
  \<times> nat list 
  \<times> (nat 
    \<times> (String.literal, int) Simple_Expressions.bexp 
    \<times> (String.literal, int) acconstraint list 
    \<times> String.literal act 
    \<times> (String.literal 
    \<times> (String.literal, int) exp) list 
    \<times> String.literal list 
    \<times> nat) list 
  \<times> (nat \<times> (String.literal, int) acconstraint list) list) list" where
"timed_automaton_net_spec \<equiv> main_auto_spec # (map action_to_automaton_spec actions)"

definition "broadcast_spec::String.literal list \<equiv> []"
abbreviation "bounds_spec::(String.literal \<times> int \<times> int) list \<equiv> all_vars_spec"
abbreviation "automata_spec \<equiv> timed_automaton_net_spec"
abbreviation "urge_spec \<equiv> urge_clock"
definition "formula_spec::(nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula \<equiv> formula.EX (sexp.loc 0 goal_loc)"
definition "init_vars_spec::(String.literal \<times> int) list \<equiv> map (map_prod id fst) all_vars_spec"
definition "init_locs_spec::nat list \<equiv> init_loc # map (\<lambda>x. off_loc) actions"


(* broadcast bounds' renum_acts renum_vars renum_clocks renum_states automata urge \<Phi> s\<^sub>0 L\<^sub>0 *)
(* 
  broadcast::String.literal list
  bounds::(String.literal \<times> int \<times> int) list
  renum_acts::(String.literal \<Rightarrow> nat) (* These 4 come from the model checker *)
  renum_vars::(String.literal \<Rightarrow> nat)
  renum_clocks::(String.literal \<Rightarrow> nat)
  renum_states::(nat \<Rightarrow> nat \<Rightarrow> nat)
  automata::(nat list 
    \<times> nat list 
    \<times> (nat 
      \<times> (String.literal, int) Simple_Expressions.bexp 
      \<times> (String.literal, int) acconstraint list 
      \<times> String.literal act 
      \<times> (String.literal 
      \<times> (String.literal, int) exp) list 
      \<times> String.literal list 
      \<times> nat) list 
    \<times> (nat \<times> (String.literal, int) acconstraint list) list) list 
  urge::String.literal 
  formula::(nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula 
  init_vars::(String.literal \<times> int) list 
  init_locs::nat list *)
thm Simple_Network_Language_Export_Code.Simple_Network_Rename_Formula_String_def[no_vars]
term "Simple_Network_Rename_Formula_String"
end
(*
global_interpretation a: tp_nta_reduction_spec "[a::String.literal, b]" "[c]" "fst" "fst o snd" "snd o snd"
  "\<lambda>x. Some (lower_bound.GE 0)" "\<lambda>x. Some (upper_bound.LE 2)" fst "fst o snd" "snd o snd"
  "1" "[a, b, c]" "[(([a],[],[b]), ([],[],[]), [a]), (([a],[],[b]), ([],[],[]), [a])]"
  sorry

code_thms "action_defs.mutex_snap_action"

value "a.mutex_effects_spec ([STR ''a''],[],[STR ''b'']) ([STR ''a''],[],[STR ''b''])"
 *)

(* Implement this one.  *)
locale tp_nta_reduction_spec' = temp_planning_problem_list_impl_int'
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
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
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
begin
sublocale reduction_ref_impl: tp_nta_reduction_spec 
  "rat_impl.list_inter props init" 
  "rat_impl.list_inter props goal"
  AtStart AtEnd rat_impl.over_all_restr_list lower upper 
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  \<epsilon> props actions act_to_name prop_to_name 
  by unfold_locales
end
end
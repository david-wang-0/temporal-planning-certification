theory TP_NTA_Reduction_Defs
  imports Temporal_Planning_Semantics.Temporal_Plans_Lemmas
      Temporal_Planning_Semantics.Temporal_Plans_Code
      Munta_Model_Checker.Simple_Network_Language_Export_Code

begin
section \<open>Abstract definition of reduction\<close>

text \<open>Abstract definition of the reduction from a temporal planning problem to a Munta timed-automata
network. Time is hardcoded as \<open>int\<close> (following Wimmer, who interprets the network over the reals, which
satisfy the time-class assumptions); the locale structure mirrors the temporal-planning locales, with
\<open>tp_nta_reduction_defs\<close> extending \<open>temp_planning_problem_list_impl_int\<close>.

Each action becomes one automaton with control flow
\<open>off -> start-instant -> (running; time passes) -> end-instant -> off\<close>. At the start instant we check
the mutex variables, apply effects, check preconditions, reset the start clock and check the mutex
actions; on entering the running location we check that the invariants hold and increment the mutex
counters. At the end instant we check the lower/upper duration constraints, decrement the mutex
counters, check the mutex variables, apply effects, check preconditions, reset the end clock and check
the mutex actions.

Design notes. Mutual exclusivity is computed by intersecting additions and deletions. Applying effects
shares a transition with the mutex-variable check, because only deletions can falsify invariants.
Increment/decrement of the mutex counters happens when transitioning out of and into the urgent
locations, to allow simultaneous snap-action execution. Start and end clocks are reset as the instant
is entered, so that mutex conditions can be checked; 0-separation is hardcoded into this translation.
Order-sensitive steps must be scheduled in the right order, and preconditions are checked at the start
of the instants (which can yield fewer transitions while model-checking). When a mutex counter is
incremented, the invariant propositions must be checked true -- otherwise one could be false, never
explicitly set false during execution, and still fail to hold.\<close>

fun bexp_and_all::"('a, 'b) bexp list \<Rightarrow> ('a, 'b) bexp" where
"bexp_and_all [] = bexp.true" |
"bexp_and_all (x#xs) = bexp.and x (bexp_and_all xs)"

text \<open>Encoders from the abstract numeric syntax (NUMERIC_PLAN A.1) into the Munta expression and
boolean-expression languages (NUMERIC_PLAN A.5), parameterised by a fluent-naming map \<open>fv\<close> and a
value-to-int map \<open>ci\<close> -- the bounded-integer boundary, where rational constants land on \<open>int\<close>
(exact on the supported fragment). Pure and locale-independent.\<close>
fun nexp_to_exp :: "('n \<Rightarrow> String.literal) \<Rightarrow> ('r \<Rightarrow> int)
    \<Rightarrow> ('n, 'r) nexp \<Rightarrow> (String.literal, int) exp" where
  "nexp_to_exp fv ci (NConst c) = exp.const (ci c)"
| "nexp_to_exp fv ci (NVar f)   = exp.var (fv f)"
| "nexp_to_exp fv ci (NAdd a b) = exp.binop (+) (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "nexp_to_exp fv ci (NSub a b) = exp.binop (-) (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "nexp_to_exp fv ci (NMul a b) = exp.binop times (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "nexp_to_exp fv ci (NDiv a b) = exp.binop (div) (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"

fun comp_to_bexp :: "('n \<Rightarrow> String.literal) \<Rightarrow> ('r \<Rightarrow> int)
    \<Rightarrow> ('n, 'r) comp \<Rightarrow> (String.literal, int) bexp" where
  "comp_to_bexp fv ci (Comp Ceq a b) = bexp.eq (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "comp_to_bexp fv ci (Comp Cle a b) = bexp.le (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "comp_to_bexp fv ci (Comp Cge a b) = bexp.ge (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "comp_to_bexp fv ci (Comp Clt a b) = bexp.lt (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
| "comp_to_bexp fv ci (Comp Cgt a b) = bexp.gt (nexp_to_exp fv ci a) (nexp_to_exp fv ci b)"
locale tp_nta_reduction_defs = temp_planning_problem_list_impl_int
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

definition 
"pl_is_1 = var_is (1::int) planning_lock"
  

subsection \<open>Automata for individual actions\<close>
abbreviation mutex_effects::"
   'snap_action 
\<Rightarrow> 'snap_action 
\<Rightarrow> bool" where
"mutex_effects a b \<equiv> rat_impl.set_impl.mutex_snap_action a b"

definition net_int_clocks::"'snap_action \<Rightarrow> String.literal list" where
"net_int_clocks s \<equiv>
let 
  int_starts = filter (\<lambda>a. mutex_effects s (at_start a)) actions;
  start_clocks = map act_to_start_clock int_starts;
  int_ends = filter (\<lambda>a. mutex_effects s (at_end a)) actions;
  end_clocks = map act_to_end_clock int_ends
in 
  start_clocks @ end_clocks
"

text \<open>The transition from the \<open>off\<close> location (action inactive) to the location for the instant the
action starts.\<close>
definition start_edge::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"start_edge a \<equiv> 
let 
  start_snap = at_start a;
  
  guard = map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks start_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks start_snap);
  
  not_locked_check = map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds start_snap)) (dels start_snap));
  pre_check = map (is_prop_ab 1) (pre start_snap);
  var_check = bexp_and_all (pl_is_1 # not_locked_check @ pre_check );
  
  add_upds = map (set_prop_ab 1) (adds start_snap);
  del_upds = map (set_prop_ab 0) (dels start_snap);
  upds = (inc_var 1 acts_active) # del_upds @ add_upds;

  resets = [act_to_start_clock a]
in (off_loc, var_check, guard, Sil (STR ''''), upds, resets, starting_loc)"

definition edge_2::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"edge_2 a \<equiv> 
let 
  check_invs = (bexp_and_all (pl_is_1 # map (is_prop_ab 1) (over_all a)));
  upds = map (inc_prop_lock_ab 1) (over_all a)
in
  (starting_loc, check_invs, [], Sil (STR ''''), upds, [], running_loc)
"



definition l_dur::"'action \<Rightarrow> (String.literal, int) acconstraint list" where
"l_dur act \<equiv> (case lower act of 
  None \<Rightarrow> []
| Some (lower_bound.GE n) \<Rightarrow> [acconstraint.GE (act_to_start_clock act) n]
| Some (lower_bound.GT n) \<Rightarrow> [acconstraint.GT (act_to_start_clock act) n])"

definition u_dur::"'action \<Rightarrow> _" where
"u_dur a \<equiv> (case upper a of 
  None \<Rightarrow> []
| Some (upper_bound.LE n) \<Rightarrow> [acconstraint.LE (act_to_start_clock a) n]
| Some (upper_bound.LT n) \<Rightarrow> [acconstraint.LT (act_to_start_clock a) n])"

definition edge_3::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"edge_3 a \<equiv>
let
  end_snap = at_end a;
  
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks end_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks end_snap);

  guard = l_dur a @ u_dur a @ int_clocks;

  upds = map (inc_prop_lock_ab (-1)) (over_all a);
  
  resets = [act_to_end_clock a]
in 
  (running_loc, pl_is_1, guard, Sil (STR ''''), upds , resets, ending_loc)
"

text \<open>Checking that no interfering snap-action is starting is done with the clock constraints. It is
enough to check that the end does not interfere with the start: interference is reflexive and the start
clock has already been reset.\<close>
definition instant_trans_edge::"'action 
  \<Rightarrow> nat 
    \<times> (String.literal, int) Simple_Expressions.bexp 
    \<times> (String.literal, int) acconstraint list 
    \<times> String.literal act 
    \<times> (String.literal \<times> (String.literal, int) exp) list 
    \<times> String.literal list 
    \<times> nat" where
"instant_trans_edge a \<equiv>
let
  end_snap = at_end a;
  start_snap = at_start a;
  
  int_clocks =  map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks end_snap) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks end_snap);

  guard = l_dur a @ u_dur a @ int_clocks;

  resets = [act_to_end_clock a]
in 
  (starting_loc, pl_is_1, guard, Sil (STR ''''), [], resets, ending_loc)
"

text \<open>The not-locked check applies only to deletions that are not immediately overwritten by
additions.\<close>
definition end_edge::"'action \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"end_edge a \<equiv> 
let 
  end_instant = ending_loc;
  off = off_loc;

  end_snap = at_end a;

  not_locked_check = map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds end_snap)) (dels end_snap));
  pre_check = map (is_prop_ab 1) (pre end_snap);
  check = bexp_and_all (pl_is_1 # not_locked_check @ pre_check);
  
  add_upds = map (set_prop_ab 1) (adds end_snap);
  del_upds = map (set_prop_ab 0) (dels end_snap);
  upds = (inc_var (-1) acts_active) # del_upds @ add_upds
in
  (end_instant, check, [], Sil (STR ''''), upds, [], off)
"


definition action_to_automaton::"'action \<Rightarrow>
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
"action_to_automaton a \<equiv>
let 
  committed_locs = (Nil::nat list);
  urgent_locs = [starting_loc, ending_loc];
  edges = [start_edge a, edge_2 a, edge_3 a, end_edge a, instant_trans_edge a];
  invs = []::(nat \<times> (String.literal, int) acconstraint list) list
in 
  (committed_locs, urgent_locs, edges, invs)"

subsection \<open>Main automaton to initialise problem and check goal satisfactions\<close>
definition main_auto_init_edge::"nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_init_edge \<equiv>
let
  can_start = var_is 0 planning_lock;
  
  permit_planning = set_var 1 planning_lock;
  set_active = set_var 0 acts_active;
  set_props = map (set_prop_ab 1) init;
  upds = permit_planning # set_active # set_props
in
  (init_loc, can_start, [], Sil (STR ''''), upds, [], planning_loc)
"

definition main_auto_goal_edge::"nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_goal_edge \<equiv>
let
  can_end = [var_is 1 planning_lock, var_is 0 acts_active];
  goal_sat = map (is_prop_ab 1) goal;
  cond = bexp_and_all (can_end @ goal_sat);
  
  lock_plan = set_var 2 planning_lock
in
  (planning_loc, cond, [], Sil (STR ''''), [lock_plan], [], goal_loc)
"

definition main_auto_loop::"nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_loop \<equiv>
  (goal_loc, bexp.true, [], Sil (STR ''''), [], [], goal_loc)
"

definition main_auto::"
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
"main_auto \<equiv> 
let
  committed_locs = [];
  urgent_locs = [init_loc, goal_loc];
  edges = [main_auto_init_edge, main_auto_goal_edge, main_auto_loop];
  invs = []
in
  (committed_locs, urgent_locs, edges, invs)
"

subsection \<open>The entire network\<close>


definition inv_vars::"'proposition list \<Rightarrow> String.literal set" where
"inv_vars i \<equiv> 
let 
  vars = map prop_to_lock i @ map prop_to_var i
in set vars"

definition snap_vars::"'snap_action \<Rightarrow> String.literal set" where
"snap_vars s \<equiv>
let
  pre_vars = map prop_to_var (pre s);
  add_vars = map prop_to_var (adds s);  
  del_vars = map prop_to_lock (filter (\<lambda>p. p \<notin> set (adds s)) (dels s)) @ map prop_to_var (dels s);
  vars = pre_vars @ add_vars @ del_vars
in set vars
"

definition action_vars::"'action \<Rightarrow> String.literal set" where
"action_vars a \<equiv> 
let
  inv_vars = inv_vars (over_all a);
  snap_vars = snap_vars (at_start a) \<union> snap_vars (at_end a)
in inv_vars \<union> snap_vars"

definition all_vars::"(String.literal \<times> int \<times> int) list" where
"all_vars \<equiv>
let
  action_vars = fold (\<union>) (map action_vars actions) {};
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


definition timed_automaton_net::"
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
"timed_automaton_net \<equiv> main_auto # (map action_to_automaton actions)"

definition "net_broadcast::String.literal list \<equiv> []"
abbreviation "net_bounds::(String.literal \<times> int \<times> int) list \<equiv> all_vars"
abbreviation "net_automata \<equiv> timed_automaton_net"
abbreviation "urge \<equiv> urge_clock"
definition "reach_formula::(nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula \<equiv> formula.EX (sexp.loc 0 goal_loc)"
definition "init_vars::(String.literal \<times> int) list \<equiv> map (map_prod id fst) all_vars"
definition "init_locs::nat list \<equiv> init_loc # map (\<lambda>x. off_loc) actions"

lemma length_net_automata: "length net_automata = Suc (length actions)"
  using timed_automaton_net_def by auto


end


text \<open>The primed reduction layer (on \<open>temp_planning_problem_list_impl_int'\<close>): its
\<open>reduction_ref_impl\<close> sublocale instantiates the unprimed reduction on the restricted problem.\<close>
locale tp_nta_reduction_defs' = temp_planning_problem_list_impl_int'
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
sublocale reduction_ref_impl: tp_nta_reduction_defs 
  "rat_impl.list_inter props init" 
  "rat_impl.list_inter props goal"
  AtStart AtEnd rat_impl.over_all_restr_list lower upper 
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  \<epsilon> props actions act_to_name prop_to_name 
  by unfold_locales
end

section \<open>Numeric augmentation of the reduction (NUMERIC_PLAN Layer B)\<close>

text \<open>The numeric reduction is an ADDITIVE layer over the propositional one (NUMERIC_PLAN A.6): a
locale extending \<open>tp_nta_reduction_defs\<close> with the numeric data (\<open>n_pre\<close>/\<open>n_inv\<close>/\<open>upds\<close>/\<open>num_init\<close>/
\<open>num_goal\<close>), a fluent-naming map \<open>fluent_to_var\<close>, per-fluent integer bounds, and the value-to-int map
\<open>const_to_int\<close>. The numeric net reuses the propositional definitions and APPENDS fluent
var-declarations / numeric guards / numeric updates, so its propositional projection is the
propositional net unchanged. Numeric fields are sets/functions, so they sidestep the list-vs-set split
that \<open>pre\<close>/\<open>adds\<close>/\<open>dels\<close> carry.\<close>

locale numeric_tp_nta_reduction_defs = tp_nta_reduction_defs
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
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
    and prop_to_name :: "'proposition \<Rightarrow> String.literal" +
  fixes n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_var :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int"
begin

text \<open>One bounded \<open>int\<close> variable per declared numeric fluent, appended to the propositional
\<open>all_vars\<close> (NUMERIC_PLAN A.5).\<close>
definition num_fluent_vars :: "(String.literal \<times> int \<times> int) list" where
"num_fluent_vars = map (\<lambda>f. (fluent_to_var f, fluent_lo f, fluent_hi f)) nfluents"

definition num_all_vars :: "(String.literal \<times> int \<times> int) list" where
"num_all_vars = all_vars @ num_fluent_vars"

text \<open>Numeric guards and updates, derived from the abstract numeric data through the encoders
(NUMERIC_PLAN A.5): \<open>n_pre\<close>/\<open>n_inv\<close>/\<open>num_goal\<close> become \<open>bexp\<close> guards, \<open>upds\<close> and \<open>num_init\<close> become
\<open>(var, exp)\<close> updates.\<close>
definition num_pre_guard :: "'snap_action \<Rightarrow> (String.literal, int) bexp" where
"num_pre_guard s = bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) (n_pre s))"

definition num_inv_guard :: "'action \<Rightarrow> (String.literal, int) bexp" where
"num_inv_guard a = bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) (n_inv a))"

definition num_goal_guard :: "(String.literal, int) bexp" where
"num_goal_guard = bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) num_goal)"

definition num_upd :: "'snap_action \<Rightarrow> (String.literal \<times> (String.literal, int) exp) list" where
"num_upd s = map (\<lambda>(f, e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) (upds s)"

definition num_init_upd :: "(String.literal \<times> (String.literal, int) exp) list" where
"num_init_upd = map (\<lambda>f. (fluent_to_var f, exp.const (const_to_int (num_init f)))) nfluents"

text \<open>Faithfulness of the integer encoding on the discrete fragment (NUMERIC_PLAN A.3): a numeric
expression is @{emph \<open>ok\<close>} at a valuation when every leaf reads a declared, integer-valued fluent or an
integer constant and every division divides exactly -- the side-condition under which the truncating
Munta integer arithmetic agrees with the abstract field arithmetic. Hoisted here (into the defs locale,
above the well-formedness assumptions) so the grounder-match contract can reference it.\<close>
fun nexp_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> bool" where
  "nexp_ok w (NConst c) \<longleftrightarrow> c \<in> \<int>"
| "nexp_ok w (NVar f)   \<longleftrightarrow> f \<in> set nfluents \<and> (\<exists>r. w f = Some r \<and> r \<in> \<int>)"
| "nexp_ok w (NAdd a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NSub a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NMul a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NDiv a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b
     \<and> the (eval_nexp w b) \<noteq> 0
     \<and> const_to_int (the (eval_nexp w b)) dvd const_to_int (the (eval_nexp w a))"

text \<open>@{term \<open>comp_ok w c\<close>}: both sides of the comparison are faithful numeric expressions.\<close>
fun comp_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n, 'r) comp \<Rightarrow> bool" where
  "comp_ok w (Comp p a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"

text \<open>A valuation is @{emph \<open>integer-ok\<close>} when every declared fluent is defined and integer-valued
(the encoding @{term const_to_int} round-trips on it), and @{emph \<open>in bounds\<close>} when each fluent's
integer encoding lies within its declared variable range.\<close>
definition num_val_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> bool" where
"num_val_ok w \<longleftrightarrow> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> r \<in> \<int>)"

definition fluent_in_bounds :: "('n \<rightharpoonup> 'r) \<Rightarrow> bool" where
"fluent_in_bounds w \<longleftrightarrow> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> r \<in> \<int>
    \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f)"

text \<open>In-bounds subsumes integer-OK: the bounded valuation is in particular integer-valued.\<close>
lemma fluent_in_bounds_imp_num_val_ok: "fluent_in_bounds w \<Longrightarrow> num_val_ok w"
  unfolding fluent_in_bounds_def num_val_ok_def by blast

text \<open>Append a numeric \<open>bexp\<close> guard (conjoined) and numeric \<open>(var, exp)\<close> updates (after the
propositional ones) to a propositional edge, leaving source/target locations, clock constraints, the
action label and clock resets untouched -- so the numeric net's propositional projection is the
propositional net.\<close>
definition augment_edge where
"augment_edge g u e =
  (let (src, b, ac, act, upd, rst, tgt) = e in (src, bexp.and b g, ac, act, upd @ u, rst, tgt))"

definition "num_start_edge a =
  augment_edge (num_pre_guard (at_start a)) (num_upd (at_start a)) (start_edge a)"
definition "num_end_edge a =
  augment_edge (num_pre_guard (at_end a)) (num_upd (at_end a)) (end_edge a)"
definition "num_edge_2 a = augment_edge (num_inv_guard a) [] (edge_2 a)"

text \<open>One automaton per action: the start/end snaps carry numeric guards+updates and the running-entry
edge \<open>edge_2\<close> carries the numeric \<open>over_all\<close> invariant. The duration edge \<open>edge_3\<close> and the
instant edge \<open>instant_trans_edge\<close> are reused unchanged.\<close>
definition "num_action_to_automaton a =
(let
  committed_locs = (Nil::nat list);
  urgent_locs = [starting_loc, ending_loc];
  edges = [num_start_edge a, num_edge_2 a, edge_3 a, num_end_edge a, instant_trans_edge a];
  invs = []::(nat \<times> (String.literal, int) acconstraint list) list
in (committed_locs, urgent_locs, edges, invs))"

text \<open>The main automaton additionally sets each fluent to its initial value on the init edge and checks
the numeric goal \<open>num_goal\<close> on the goal edge.\<close>
definition "num_main_auto_init_edge = augment_edge bexp.true num_init_upd main_auto_init_edge"
definition "num_main_auto_goal_edge = augment_edge num_goal_guard [] main_auto_goal_edge"

definition "num_main_auto =
(let
  committed_locs = [];
  urgent_locs = [init_loc, goal_loc];
  edges = [num_main_auto_init_edge, num_main_auto_goal_edge, main_auto_loop];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

definition "num_timed_automaton_net = num_main_auto # (map num_action_to_automaton actions)"

text \<open>The numeric network's variable bounds and initial valuation: the propositional declarations plus
one bounded \<open>int\<close> variable per fluent (initialised to its lower bound, then set to \<open>num_init\<close> on the
init edge). Locations and the reachability \<open>reach_formula\<close> are unchanged -- the numeric goal is enforced
on the goal edge.\<close>
abbreviation "num_net_bounds::(String.literal \<times> int \<times> int) list \<equiv> num_all_vars"
definition "num_init_vars::(String.literal \<times> int) list \<equiv> map (map_prod id fst) num_all_vars"

end

section \<open>Well-formedness of the numeric data (the grounder-match contract)\<close>

text \<open>These predicates state the conditions the numeric input must satisfy for the reduction to be
sound. They are written to match, one-for-one, the guarantees the grounder produces
(NUMERIC_PLAN A.2/A.3/B).\<close>

definition upds_functional_list :: "('n \<times> ('n, 'r) nexp) list \<Rightarrow> bool" where
"upds_functional_list us \<longleftrightarrow> distinct (map fst us)"

definition upds_no_cross_read_list :: "('n \<times> ('n, 'r) nexp) list \<Rightarrow> bool" where
"upds_no_cross_read_list us \<longleftrightarrow> (\<forall>(f, e) \<in> set us. nexp_fluents e \<inter> (fst ` set us - {f}) = {})"

text \<open>The element-level fact: a fluent read by an effect's RHS that is also written by the snap can
only be that effect's own left-hand side (so a self-update reads the pre-state of its own fluent, never
another co-written fluent).\<close>
lemma upds_no_cross_read_listD:
  assumes "upds_no_cross_read_list us"
      and "(f, e) \<in> set us"
      and "g \<in> nexp_fluents e"
      and "g \<in> fst ` set us"
    shows "g = f"
  using assms unfolding upds_no_cross_read_list_def by fast

text \<open>The numeric reduction proper: the spec locale plus well-formedness. \<open>upds\<close> is functional (one
assignment per fluent, from the grounder's combination-normalisation) and cross-read-free; per-fluent
bounds are valid; the fluent variable names are injective and FRESH (disjoint from the propositional
variable names, so numeric variables never gate a propositional edge -- the keystone of the
additive-tracking architecture, NUMERIC_PLAN A.6/5.5).\<close>
locale numeric_tp_nta_reduction = numeric_tp_nta_reduction_defs
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
  n_pre n_inv upds num_init num_goal nfluents fluent_to_var fluent_lo fluent_hi const_to_int
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
  assumes upds_functional_start:   "\<forall>a \<in> set actions. upds_functional_list (upds (at_start a))"
      and upds_functional_end:     "\<forall>a \<in> set actions. upds_functional_list (upds (at_end a))"
      and upds_no_cross_read_start: "\<forall>a \<in> set actions. upds_no_cross_read_list (upds (at_start a))"
      and upds_no_cross_read_end:   "\<forall>a \<in> set actions. upds_no_cross_read_list (upds (at_end a))"
      and fluent_bounds_valid:      "\<forall>f \<in> set nfluents. fluent_lo f \<le> fluent_hi f"
      and fluent_to_var_inj:        "inj_on fluent_to_var (set nfluents)"
      and fluent_vars_fresh:        "\<forall>f \<in> set nfluents. fluent_to_var f \<notin> fst ` set all_vars"
      \<comment> \<open>Integer-encoding faithfulness, the grounder-match contract for the discrete fragment
         (NUMERIC_PLAN A.3): on any integer-valued (@{const num_val_ok}) valuation every snap's update
         RHS and pre/over_all comparison is @{const nexp_ok}/@{const comp_ok} (declared integer reads,
         exact divisions), and the initial valuation is integer-valued. These are static and
         grounder-checkable. Range-boundedness is a @{emph \<open>reachability\<close>} property (a global closure
         over all in-range valuations is false for monotone effects), so it is assumed M-scoped -- the
         certified plan's valuations stay within the declared variable bounds -- as @{text num_seq_in_bounds}
         in the \<open>numeric_tp_nta_reduction_correctness\<close> locale (where the state sequence is in scope); the
         intermediate partial-fold stores are then derived in range from the happening endpoints.\<close>
      and snap_upds_nexp_ok_start:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_start a)). nexp_ok w e)"
      and snap_upds_nexp_ok_end:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_end a)). nexp_ok w e)"
      and snap_pre_comp_ok_start:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_start a)). comp_ok w c)"
      and snap_pre_comp_ok_end:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_end a)). comp_ok w c)"
      and snap_inv_comp_ok:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_inv a). comp_ok w c)"
      and num_init_val_ok: "\<forall>f \<in> set nfluents. num_init f \<in> \<int>"
      \<comment> \<open>Snap effects write only DECLARED fluents (grounder-match): every update LHS is in
         @{term nfluents}. Needed for the integer-encoding to land on declared fluent variables.\<close>
      and snap_writes_nfluents_start:
            "\<forall>a \<in> set actions. fst ` set (upds (at_start a)) \<subseteq> set nfluents"
      and snap_writes_nfluents_end:
            "\<forall>a \<in> set actions. fst ` set (upds (at_end a)) \<subseteq> set nfluents"
      \<comment> \<open>Numeric over_all invariants: the supported fragment restricts them to EQUALITIES
         (@{term n_inv_eq}) whose fluents are never written by any snap (read-only, @{term n_inv_readonly}).
         Then an over_all comparison's value is constant along every run, hence valuation-independent, so
         @{const num_edge_2}'s entry check discharges directly from plan validity (the action's over_all
         holds while it is active, which transfers verbatim to the start instant) -- the numeric mirror of
         the propositional over_all lock, with "no update changes the value" in its strongest static form.\<close>
      and n_inv_eq:
            "\<forall>a \<in> set actions. \<forall>c \<in> set (n_inv a). \<exists>e1 e2. c = Comp Ceq e1 e2"
      and n_inv_readonly:
            "\<forall>a \<in> set actions. \<forall>b \<in> set actions.
               (fst ` set (upds (at_start a)) \<union> fst ` set (upds (at_end a)))
                 \<inter> (\<Union>c \<in> set (n_inv b). comp_fluents c) = {}"

end
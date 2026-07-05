theory TP_NTA_Reduction_Happenings
  imports TP_NTA_Reduction_Edges
begin
context tp_nta_reduction_correctness
begin
section \<open>Applying happenings\<close>
subsection \<open>Definitions for conditions\<close>
definition act_clock_pre_happ where
"act_clock_pre_happ c cons a t = (
  if (cons = act_to_start_clock) 
  then (c (act_to_start_clock a) = real_of_rat (planning_sem.exec_time (at_start a) t))
  else 
  if (cons = act_to_end_clock) 
  then (c (act_to_end_clock a) = real_of_rat (planning_sem.exec_time (at_end a) t)) 
  else undefined)"

lemma act_clock_pre_happ_simps[simp]:
  "act_clock_pre_happ c act_to_end_clock a t =  (c (act_to_end_clock a) = real_of_rat (planning_sem.exec_time (at_end a) t))"
  "act_clock_pre_happ c act_to_start_clock a t =  (c (act_to_start_clock a) = real_of_rat (planning_sem.exec_time (at_start a) t))"
  using act_clock_pre_happ_def clock_cons_unique by auto
  

subsubsection \<open>Mutex constraints\<close>

text \<open>This only works for the direction from plan to run.\<close>
(* goal cases*)
schematic_goal net_int_clocks_alt:
  shows "set (net_int_clocks h) = ?x"
  unfolding net_int_clocks_def Let_def filter_append set_append set_map set_filter ..


definition act_clock_post_happ where
"act_clock_post_happ c cons a t = (
  if (cons = act_to_start_clock) 
  then (c (act_to_start_clock a) = real_of_rat (planning_sem.exec_time' (at_start a) t))
  else 
  if (cons = act_to_end_clock) 
  then (c (act_to_end_clock a) = real_of_rat (planning_sem.exec_time' (at_end a) t))
  else undefined)"

lemma act_clock_post_happ_simps[simp]:
  "act_clock_post_happ c act_to_start_clock a t = (c (act_to_start_clock a) = real_of_rat (planning_sem.exec_time' (at_start a) t))"
  "act_clock_post_happ c act_to_end_clock a t = (c (act_to_end_clock a) = real_of_rat (planning_sem.exec_time' (at_end a) t))"
  using clock_cons_unique act_clock_post_happ_def by auto

lemma act_clock_post_happ_intros: 
  "(planning_sem.is_instant_action t a \<Longrightarrow> c (act_to_start_clock a) = 0)
\<Longrightarrow> (planning_sem.is_starting_action t a \<Longrightarrow> c (act_to_start_clock a) = 0)
\<Longrightarrow> (planning_sem.is_ending_action t a \<Longrightarrow> act_clock_pre_happ c act_to_start_clock a t)
\<Longrightarrow> (planning_sem.is_not_happening_action t a \<Longrightarrow> act_clock_pre_happ c act_to_start_clock a t)
\<Longrightarrow> act_clock_post_happ c act_to_start_clock a t"

    "(planning_sem.is_instant_action t a \<Longrightarrow> c (act_to_end_clock a) = 0) 
\<Longrightarrow> (planning_sem.is_starting_action t a \<Longrightarrow> act_clock_pre_happ c act_to_end_clock a t) 
\<Longrightarrow> (planning_sem.is_ending_action t a \<Longrightarrow> c (act_to_end_clock a) = 0) 
\<Longrightarrow> (planning_sem.is_not_happening_action t a \<Longrightarrow> act_clock_pre_happ c act_to_end_clock a t) 
\<Longrightarrow> act_clock_post_happ c act_to_end_clock a t"
  unfolding act_clock_pre_happ_def act_clock_post_happ_def
  by (rule planning_sem.action_happening_cases[of t a];
      (use planning_sem.action_happening_exec_times clock_cons_unique in simp)+)+

(* The properties of the state once the initial transition has been taken *)

text \<open>Invariants\<close>
definition "Lv_conds L v \<equiv> 
  length L = Suc (length actions) 
\<and> L ! 0 = planning_loc
\<and> bounded (map_of net_bounds) v 
\<and> v planning_lock = Some 1"

text \<open>@{const Lv_conds} as a predicate on a whole config, for carrying it as a separate conjunct
through a run (the structural invariant factored out of the per-step value predicates).\<close>
fun LvP :: "(nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool" where
  "LvP (L, v, c) = Lv_conds L v"
text \<open>Actual starting state\<close>
definition init_state_props::"(nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool" where
"init_state_props Lvc \<equiv> 
let 
  (L, v, c) = Lvc;
  bounded = bounded (map_of net_bounds) v;
  locs = (L = init_loc # map (\<lambda> x. off_loc) actions); 
  def_vars = (\<forall>x \<in> set (map fst net_bounds). v x = Some 0);
  undef_vars = (\<forall>x. x \<notin> set (map fst net_bounds) \<longrightarrow> v x = None); 
  clock_state = (c = (\<lambda>_. 0))
in bounded
\<and> locs 
\<and> def_vars
\<and> undef_vars
\<and> clock_state"

text \<open>Initial and goal state w.r.t. planning\<close>
definition "init_planning_state_props Lvc \<equiv>
let 
  (L, v, c) = Lvc;

  active = v acts_active = Some 0;

  locs = (L = planning_loc # map (\<lambda> x. off_loc) actions); 
  true_props = (\<forall>p \<in> set init. v (prop_to_var p) = Some 1);
  false_props = (\<forall>x \<in> set (map fst net_bounds) - ({planning_lock, acts_active} \<union> prop_to_var ` set init). v x = Some 0); 

  undef_vars = (\<forall>x. x \<notin> set (map fst net_bounds) \<longrightarrow> v x = None); 

  clock_state =  (c = (\<lambda>_. 0))
in 
  active
\<and> locs 
\<and> true_props 
\<and> false_props 
\<and> undef_vars 
\<and> clock_state"

definition "init_planning_state_props' Lvc \<equiv> 
let 
  (L, v, c) = Lvc;

  acts_active = v acts_active = Some 0;

  locs = (L = planning_loc # map (\<lambda> x. off_loc) actions); 

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p));
  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0);

  start_time = (\<forall>i < length actions. c (act_to_start_clock (actions ! i)) = 0);
  end_time = (\<forall>i < length actions. c (act_to_end_clock (actions ! i)) = 0)
in 
  acts_active
\<and> locs
\<and> prop_state
\<and> lock_state
\<and> start_time
\<and> end_time"


(* The final transition does not consider clock valuations as conditions *)
definition "goal_trans_pre Lvc \<equiv> 
let 
  (L, v, c) = Lvc;

  acts_active = v acts_active = Some 0;

  locs = (L = planning_loc # map (\<lambda> x. off_loc) actions); 
  prop_state = (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)));
  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)

in 
  acts_active
\<and> locs
\<and> prop_state 
\<and> lock_state"

definition "goal_state_conds Lvc \<equiv> 
let 
  (L, v, c) = Lvc;
  bounded = bounded (map_of net_bounds) v;  

  acts_active = v acts_active = Some 0;
  planning_state = v planning_lock = Some 2;

  locs = (L = goal_loc # map (\<lambda> x. off_loc) actions); 
  prop_state = (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)));
  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)

in 
  bounded
\<and> acts_active
\<and> planning_state
\<and> locs
\<and> prop_state 
\<and> lock_state"


text \<open>Each happening\<close>

definition "happening_pre i Lvc \<equiv>
let
  t = planning_sem.time_index i;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ i p));
  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before t p)));

  active = (v acts_active = Some (int (planning_sem.active_before t)));

  active_locs = (\<forall>i < length actions. planning_sem.open_active_count t (actions ! i) = 0 \<longrightarrow> L ! Suc i = (off_loc));
  inactive_locs = (\<forall>i < length actions. planning_sem.open_active_count t (actions ! i) = 1  \<longrightarrow> L ! Suc i = (running_loc));

  start_time = (\<forall>i < length actions. act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  end_time = (\<forall>i < length actions. act_clock_pre_happ c act_to_end_clock (actions ! i) t)
in prop_state \<and> lock_state 
  \<and> active
  \<and> active_locs \<and> inactive_locs
  \<and> start_time \<and> end_time"

(* These should delay c and not t *)
definition "happening_pre_pre_delay i Lvc \<equiv>
let 
  (L, v, c) = Lvc;
  \<delta> = get_delay i
in happening_pre i (L, v, c \<oplus> \<delta>)"

definition "happening_pre_post_delay i Lvc \<equiv> happening_pre i Lvc"

definition "happening_post i Lvc \<equiv>
let 
  t = planning_sem.time_index i;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ i p));
  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after t p)));

  active = (v acts_active = Some (int (planning_sem.active_after t)));

  active_locs = (\<forall>i < length actions. planning_sem.closed_active_count t (actions ! i) = 0 \<longrightarrow> L ! Suc i = (off_loc));
  inactive_locs = (\<forall>i < length actions. planning_sem.closed_active_count t (actions ! i) = 1  \<longrightarrow> L ! Suc i = (running_loc));

  start_time = (\<forall>i < length actions. act_clock_post_happ c act_to_start_clock (actions ! i) t);
  end_time = (\<forall>i < length actions. act_clock_post_happ c act_to_end_clock (actions ! i) t)
in prop_state \<and> lock_state 
  \<and> active
  \<and> active_locs \<and> inactive_locs
  \<and> start_time \<and> end_time"


definition "happening_invs n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v :: String.literal \<Rightarrow> int option, c) = Lvc;

  ending_start_time = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  starting_end_time = (\<forall>i < length actions. is_starting_index t i \<longrightarrow>  act_clock_pre_happ c act_to_end_clock (actions ! i) t);

  other_start_time = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  other_end_time = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t);

  other_inactive_loc = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> planning_sem.closed_active_count t (actions ! i) = 0 \<longrightarrow> L ! Suc i = (off_loc));
  other_active_loc = (\<forall>i < length actions. is_not_happening_index t i \<longrightarrow> planning_sem.closed_active_count t (actions ! i) = 1  \<longrightarrow> L ! Suc i = (running_loc))
in ending_start_time
  \<and> starting_end_time
  \<and> other_start_time \<and> other_end_time
  \<and> other_inactive_loc \<and> other_active_loc"

text \<open>The beginning of the end of an action\<close>

definition "end_start_invs n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p));
  active = (v acts_active = Some (int (planning_sem.active_before t)));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);


  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (off_loc));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))

in happening_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> starting_start_time
  \<and> instant_start_time \<and> instant_end_time
  \<and> starting_loc
  \<and> instant_loc"

definition "happening_pre_end_starts n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before t p)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (running_loc));

  ending_end_time =  (\<forall>i < length actions. is_ending_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t)

in end_start_invs n Lvc
  \<and> locked 
  \<and> ending_loc
  \<and> ending_end_time"

definition "happening_post_end_starts n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during t p)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = ending_loc);

  ending_end_time =  (\<forall>i < length actions. is_ending_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)

in end_start_invs n Lvc
  \<and> locked 
  \<and> ending_loc
  \<and> ending_end_time"

definition "end_start_cond n i Lvc \<equiv> 
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (partially_updated_locked_before t p i));

  updated_locs = (\<forall>j. j < i \<and> is_ending_index t j \<longrightarrow> L ! Suc j = ending_loc);
  not_updated_locs = (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index t j \<longrightarrow> L ! Suc j = running_loc);

  updated_clocks =  (\<forall>j. j < i \<and> is_ending_index t j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0);
  not_updated_clocks =  (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index t j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n))

in end_start_invs n Lvc
  \<and> locked 
  \<and> updated_locs
  \<and> not_updated_locs
  \<and> updated_clocks
  \<and> not_updated_clocks"

definition "end_start_pre n \<equiv> end_start_cond n"

definition "end_start_post n \<equiv> end_start_cond n o Suc"

text \<open>Actions which are executed in their entirety\<close>

definition "instant_action_invs n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (planning_sem.locked_during t  p));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (off_loc));
  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = ending_loc)

in happening_invs n Lvc
  \<and> lock_state
  \<and> starting_start_time
  \<and> ending_end_time
  \<and> starting_loc
  \<and> ending_loc"


definition "happening_pre_instants n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p));

  active = (v acts_active = Some (int (planning_sem.active_before t)));

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t);
  
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))
in instant_action_invs n Lvc
  \<and> prop_state
  \<and> active
  \<and> instant_start_time \<and> instant_end_time
  \<and> instant_loc"

definition "happening_post_instants n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_happ n p));

  active = (v acts_active = Some (int (planning_sem.active_before t)));

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);
  
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))
in instant_action_invs n Lvc
  \<and> prop_state
  \<and> active 
  \<and> instant_start_time \<and> instant_end_time
  \<and> instant_loc"
                          
definition "instant_cond n j Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_part_updated_prop_state n j p));

  active = (v acts_active = Some (int (planning_sem.active_before t)));

  updated_start_time = (\<forall>i. i < j \<and> is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  updated_end_time = (\<forall>i. i < j \<and> is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  not_updated_start_time = (\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  not_updated_end_time =  (\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t);
  
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))
in instant_action_invs n Lvc
  \<and> prop_state 
  \<and> active
  \<and> updated_start_time \<and> updated_end_time
  \<and> not_updated_start_time \<and> not_updated_end_time
  \<and> instant_loc"

definition "instant_pre n \<equiv> instant_cond n"

definition "instant_post n \<equiv> instant_cond n o Suc"

find_theorems name: "locked_during*and"

definition "instant_starting_cond n j Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_intermediate_prop_state n j p));

  active = (v acts_active = Some (int (planning_sem.active_before t + 1)));

  updated_start_time = (\<forall>i. i \<le> j \<and> is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  updated_end_time = (\<forall>i. i < j \<and> is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  not_updated_start_time = (\<forall>i. j < i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  not_updated_end_time =  (\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t);
  
  loc = (L ! Suc j = starting_loc);
  other_instant_loc = (\<forall>i < length actions. i \<noteq> j \<and> is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))
in instant_action_invs n Lvc
  \<and> prop_state 
  \<and> active
  \<and> updated_start_time \<and> updated_end_time
  \<and> not_updated_start_time \<and> not_updated_end_time
  \<and> loc
  \<and> other_instant_loc"

definition "instant_ending_cond n j Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_intermediate_prop_state n j p));

  active = (v acts_active = Some (int (planning_sem.active_before t + 1)));

  updated_start_time = (\<forall>i. i \<le> j \<and> is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  updated_end_time = (\<forall>i. i \<le> j \<and> is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  not_updated_start_time = (\<forall>i. j < i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  not_updated_end_time =  (\<forall>i. j < i \<and> i < length actions \<and> is_instant_index t i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) t);
  
  loc = (L ! Suc j = ending_loc);
  other_instant_loc = (\<forall>i < length actions. i \<noteq> j \<and> is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))
in instant_action_invs n Lvc
  \<and> prop_state 
  \<and> active
  \<and> updated_start_time \<and> updated_end_time
  \<and> not_updated_start_time \<and> not_updated_end_time
  \<and> loc
  \<and> other_instant_loc"

definition "start_start_invs n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during t p)));

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = ending_loc);
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))

in happening_invs n Lvc
  \<and> locked
  \<and> ending_end_time
  \<and> instant_start_time
  \<and> instant_end_time
  \<and> ending_loc
  \<and> instant_loc"

definition "happening_pre_start_starts n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_happ n p));

  active = (v acts_active = Some (int (planning_sem.active_before t)));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (off_loc))
in start_start_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> starting_start_time
  \<and> starting_loc"

definition "start_start_cond n j Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (starting_part_updated_prop_state n j p));

  active = (v acts_active = Some (int (updated_active_before n j)));

  updated_start_time = (\<forall>i. i < j \<and> is_starting_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  not_updated_start_time = (\<forall>i. j \<le> i \<longrightarrow> i  < length actions \<longrightarrow> is_starting_index t i  \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) t);
  
  not_updated_start_loc =  (\<forall>i. i < j \<and> is_starting_index t i \<longrightarrow> L ! Suc i = (starting_loc));
  updated_start_loc = (\<forall>i. j \<le> i \<longrightarrow> i < length actions \<longrightarrow> is_starting_index t i  \<longrightarrow> L ! Suc i = (off_loc))
in start_start_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> not_updated_start_time \<and> updated_start_time
  \<and> not_updated_start_loc \<and> updated_start_loc"

definition "start_start_pre \<equiv> start_start_cond"

definition "start_start_post n j \<equiv> start_start_cond n (Suc j)"

definition "happening_post_start_starts n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_start_happ n p));

  active = (v acts_active = Some (int (planning_sem.active_during t)));

  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (starting_loc))
in start_start_invs n Lvc
  \<and> prop_state \<and> active 
  \<and> starting_start_time
  \<and> starting_loc"

definition "end_end_invs n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during t p)));

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);
  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (starting_loc));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))

in happening_invs n Lvc
  \<and> locked
  \<and> starting_start_time
  \<and> ending_end_time
  \<and> instant_start_time \<and> instant_end_time
  \<and> starting_loc
  \<and> instant_loc"


definition "happening_pre_end_ends n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_start_happ n p));

  active = (v acts_active = Some (int (planning_sem.active_during t)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = ending_loc)

in end_end_invs n Lvc
  \<and> prop_state \<and> active
  \<and> ending_loc"

definition "end_end_cond n j Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;
                                                                                      
  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (ending_part_updated_prop_state n j p));

  active = (v acts_active = Some (int (updated_active_during n j)));

  not_upd_loc = (\<forall>i. j \<le> i \<longrightarrow> i < length actions \<longrightarrow> is_ending_index t i \<longrightarrow> L ! Suc i = ending_loc);
  upd_loc = (\<forall>i. i < j \<longrightarrow> is_ending_index t i \<longrightarrow> L ! Suc i = (off_loc))

in end_end_invs n Lvc
  \<and> prop_state \<and> active
  \<and> not_upd_loc \<and> upd_loc"

definition "end_end_pre \<equiv> end_end_cond"
definition "end_end_post n j \<equiv> end_end_cond n (Suc j)"


definition "happening_post_end_ends n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ n p));

  active = (v acts_active = Some (int (planning_sem.active_during_minus_ended t)));

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (off_loc))
in end_end_invs n Lvc
  \<and> prop_state \<and> active
  \<and> ending_loc"

definition "start_end_invs n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  active = (v acts_active = Some (int (planning_sem.active_after t)));

  prop_state = (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ n p));

  ending_end_time = (\<forall>i < length actions. is_ending_index t i  \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);
  starting_start_time = (\<forall>i < length actions. is_starting_index t i  \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);

  instant_start_time = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0);
  instant_end_time =  (\<forall>i < length actions. is_instant_index t i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0);

  ending_loc = (\<forall>i < length actions. is_ending_index t i \<longrightarrow> L ! Suc i = (off_loc));
  instant_loc = (\<forall>i < length actions. is_instant_index t i \<longrightarrow> L ! Suc i = (off_loc))

in happening_invs n Lvc
  \<and> active
  \<and> prop_state
  \<and> starting_start_time
  \<and> ending_end_time
  \<and> instant_start_time \<and> instant_end_time
  \<and> ending_loc
  \<and> instant_loc"

definition "happening_pre_start_ends n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during t p)));

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (starting_loc))
in start_end_invs n Lvc
  \<and> locked
  \<and> starting_loc"

definition "start_end_cond n j Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (updated_locked_during n j p)));

  not_upd_loc = (\<forall>i. j \<le> i \<longrightarrow> i < length actions \<longrightarrow> is_starting_index t i \<longrightarrow> L ! Suc i = (starting_loc));
  upd_loc = (\<forall>i. i < j \<longrightarrow> is_starting_index t i \<longrightarrow> L ! Suc i = (running_loc))
in start_end_invs n Lvc
  \<and> locked
  \<and> not_upd_loc
  \<and> upd_loc"

definition "start_end_pre \<equiv> start_end_cond"
definition "start_end_post n j \<equiv> start_end_cond n (Suc j)"

definition "happening_post_start_ends n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after t p)));

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (running_loc))
in start_end_invs n Lvc
  \<and> locked
  \<and> starting_loc"


definition "happening_post_inv_check n Lvc \<equiv>
let 
  t = planning_sem.time_index n;
  (L, v, c) = Lvc;

  locked = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after t p)));

  starting_loc = (\<forall>i < length actions. is_starting_index t i \<longrightarrow> L ! Suc i = (running_loc))
in start_end_invs n Lvc
  \<and> locked
  \<and> starting_loc"

text \<open>Rules\<close>



lemma init_state_propsE: 
  assumes "init_state_props x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> bounded (map_of net_bounds) v \<Longrightarrow> L = init_loc # map (\<lambda> x. off_loc) actions \<Longrightarrow> \<forall>x\<in>set (map fst net_bounds). v x = Some 0 \<Longrightarrow> \<forall>x. x \<notin> set (map fst net_bounds) \<longrightarrow> v x = None \<Longrightarrow> c = (\<lambda>_. 0) \<Longrightarrow> thesis"
      shows thesis 
  using assms unfolding init_state_props_def by auto

lemma init_state_props_dests: 
  assumes "init_state_props Lvc"
      and "Lvc = (L, v, c)"
    shows "bounded (map_of net_bounds) v"
      "L = init_loc # map (\<lambda> x. off_loc) actions"
      "x \<in>set (map fst net_bounds) \<Longrightarrow> v x = Some 0"
      "x \<notin> set (map fst net_bounds) \<Longrightarrow> v x = None"
      "c = (\<lambda>_. 0)"
  using assms unfolding init_state_props_def by auto

lemma init_state_propsI:
  assumes "x = (L, v, c)"
    and "bounded (map_of net_bounds) v"
    and "L = init_loc # map (\<lambda> x. off_loc) actions"
    and "\<And>x. x \<in> set (map fst net_bounds) \<Longrightarrow> v x = Some 0"
    and "\<And>x. x \<notin> set (map fst net_bounds) \<Longrightarrow> v x = None" 
    and "c = (\<lambda>_. 0)" 
  shows "init_state_props x"
  unfolding init_state_props_def using assms by simp

lemma init_planning_state_propsE:
  assumes "init_planning_state_props x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> v acts_active = Some 0
      \<Longrightarrow> L = planning_loc # map (\<lambda> x. off_loc) actions \<Longrightarrow> (\<forall>p\<in>set init. v (prop_to_var p) = Some 1) 
      \<Longrightarrow> (\<forall>x\<in>set (map fst net_bounds) - ({planning_lock, acts_active} \<union> prop_to_var ` set init). v x = Some 0) 
      \<Longrightarrow> (\<forall>x. x \<notin> set (map fst net_bounds) \<longrightarrow> v x = None) \<Longrightarrow> c = (\<lambda>_. 0) \<Longrightarrow> thesis"
    shows thesis 
  using assms unfolding init_planning_state_props_def Let_def prod.case by blast

lemma init_planning_state_props_dests:
  assumes "init_planning_state_props x"
      and "x = (L, v, c)" 
    shows "v acts_active = Some 0" 
    "L = planning_loc # map (\<lambda> x. off_loc) actions"
    "\<And>p. p\<in>set init \<Longrightarrow> v (prop_to_var p) = Some 1" 
    "\<And>x. x \<in> set (map fst net_bounds) \<Longrightarrow> x \<notin> {planning_lock, acts_active} \<Longrightarrow> x \<notin> prop_to_var ` set init \<Longrightarrow> v x = Some 0" 
    "\<And>x. x \<notin> set (map fst net_bounds) \<Longrightarrow> v x = None" "c = (\<lambda>_. 0)" 
  using assms unfolding init_planning_state_props_def Let_def prod.case by auto

lemma init_planning_state_propsI:
  assumes "x = (L, v, c)" 
    "v acts_active = Some 0" 
    "L = planning_loc # map (\<lambda> x. off_loc) actions"
    "\<And>p. p \<in> set init \<Longrightarrow> v (prop_to_var p) = Some 1" 
    "\<And>x. x \<in> set (map fst net_bounds) \<Longrightarrow> x \<notin> {planning_lock, acts_active} \<Longrightarrow> x \<notin> prop_to_var ` set init \<Longrightarrow> v x = Some 0" 
    "\<And>x. x \<notin> set (map fst net_bounds) \<Longrightarrow> v x = None" 
    "c = (\<lambda>_. 0)"
  shows "init_planning_state_props x"  
  using assms unfolding init_planning_state_props_def by auto


lemma init_planning_state_props'E:
  assumes "init_planning_state_props' x"
      and "\<And>L v c. x = (L, v, c) 
      \<Longrightarrow> v acts_active = Some 0
      \<Longrightarrow> L = planning_loc # map (\<lambda> x. off_loc) actions 
      \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p)) 
      \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0) 
      \<Longrightarrow> (\<forall>i<length actions. c (act_to_start_clock (actions ! i)) = 0) 
      \<Longrightarrow> (\<forall>i<length actions. c (act_to_end_clock (actions ! i)) = 0) \<Longrightarrow> thesis"
    shows thesis 
  using assms unfolding init_planning_state_props'_def by auto

lemma init_planning_state_props'I:
  assumes "x = (L, v, c)" 
    "v acts_active = Some 0 " 
    "L = planning_loc # map (\<lambda> x. off_loc) actions " 
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p))" 
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)" 
    "(\<forall>i<length actions. c (act_to_start_clock (actions ! i)) = 0)" 
    "(\<forall>i<length actions. c (act_to_end_clock (actions ! i)) = 0)"
  shows "init_planning_state_props' x"  
  apply (subst assms(1)) 
  unfolding init_planning_state_props'_def Let_def prod.case using assms by blast

lemma goal_trans_preE:
  assumes "goal_trans_pre x"
      and "\<And>L v c. x = (L, v, c) \<Longrightarrow> v acts_active = Some 0 \<Longrightarrow> L = planning_loc # map (\<lambda> x. off_loc) actions 
      \<Longrightarrow> \<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)) 
    \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0) \<Longrightarrow> thesis"
    shows thesis 
  using assms by (auto simp: goal_trans_pre_def)

lemma goal_trans_preI:
  assumes "x = (L, v, c)"  
    "v acts_active = Some 0" 
    "L = planning_loc # map (\<lambda> x. off_loc) actions" 
    "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p))" 
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)"
  shows "goal_trans_pre x"
  using assms by (auto simp: goal_trans_pre_def)

lemma goal_state_condsE:
  assumes "goal_state_conds x"
      and "\<And>L v c. x = (L, v, c)
        \<Longrightarrow> Simple_Network_Language.bounded (map_of net_bounds) v
        \<Longrightarrow> v acts_active = Some 0
        \<Longrightarrow> v planning_lock = Some 2
        \<Longrightarrow> L = goal_loc # map (\<lambda> x. off_loc) actions
        \<Longrightarrow> (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)))
        \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)
        \<Longrightarrow> thesis"
    shows thesis
  apply (cases x)
  using assms unfolding goal_state_conds_def by simp

lemma goal_state_condsI:
  assumes "x = (L, v, c)"
    "Simple_Network_Language.bounded (map_of net_bounds) v"
    "v acts_active = Some 0" 
    "v planning_lock = Some 2" 
    "L = goal_loc # map (\<lambda> x. off_loc) actions" 
    "(\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)))" 
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)"
  shows "goal_state_conds x"
  using assms by (auto simp: goal_state_conds_def)
  
lemma Lv_condsE:
  assumes "Lv_conds L v"
    and "length L = Suc (length actions) \<Longrightarrow> L ! 0 = planning_loc 
    \<Longrightarrow> Simple_Network_Language.bounded (map_of net_bounds) v 
    \<Longrightarrow> v planning_lock = Some 1 \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding Lv_conds_def by blast


lemma Lv_condsD:
  assumes "Lv_conds L v"
  shows "length L = Suc (length actions) \<and> L ! 0 = planning_loc \<and> Simple_Network_Language.bounded (map_of net_bounds) v \<and> v planning_lock = Some 1"
  using assms unfolding Lv_conds_def by auto

lemma Lv_conds_dests:
  assumes "Lv_conds L v"
  shows "length L = Suc (length actions)" 
    "L ! 0 = planning_loc" 
    "Simple_Network_Language.bounded (map_of net_bounds) v" 
    "v planning_lock = Some 1"
  using assms unfolding Lv_conds_def by auto


lemma Lv_condsI:
  assumes "length L = Suc (length actions)" 
    "L ! 0 = planning_loc" 
    "Simple_Network_Language.bounded (map_of net_bounds) v" 
    "v planning_lock = Some 1"
  shows "Lv_conds L v"
  using Lv_conds_def assms by blast

lemma happening_pre_pre_delayI:
  assumes "x = (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)" 
    "(\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay n) act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay n) act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  shows "happening_pre_pre_delay n x" 
  unfolding happening_pre_pre_delay_def Let_def happening_pre_def  assms prod.case
  using assms by blast

lemma happening_pre_pre_delayE: 
  assumes "happening_pre_pre_delay n x"
  and "\<And>L v c. x = (L, v, c) 
    \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))
    \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))
    \<Longrightarrow> v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))
    \<Longrightarrow> (\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)
    \<Longrightarrow> (\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)
    \<Longrightarrow> (\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay n) act_to_start_clock (actions ! i) (planning_sem.time_index n))
    \<Longrightarrow> (\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay n) act_to_end_clock (actions ! i) (planning_sem.time_index n))
    \<Longrightarrow> thesis"
shows thesis using assms(1)
  apply (cases x rule: prod_cases3)
  unfolding happening_pre_pre_delay_def Let_def happening_pre_def 
  subgoal
    apply (rule assms(2))
    by blast+
  done

lemma happening_pre_pre_delay_dests: 
  assumes "happening_pre_pre_delay n x"
          "x = (L, v, c)"
  shows  "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)"
    "(\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay n) act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay n) act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  using assms unfolding happening_pre_pre_delay_def happening_pre_def Let_def by auto

lemma happening_pre_post_delay_dests:
  assumes "happening_pre_post_delay n x"
      "x = (L, v, c)"
    shows "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)"
    "(\<forall>i<length actions. act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))" 
  using assms unfolding happening_pre_post_delay_def happening_pre_def Let_def by auto


lemma happening_pre_post_delayI:
  assumes "x = (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)"
    "(\<forall>i<length actions. act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))" 
  shows "happening_pre_post_delay n x"
  using assms unfolding happening_pre_post_delay_def happening_pre_def Let_def by auto

lemma happening_postI:
  assumes "x = (L, v, c)"
  and "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ t p)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index t) p))"
    "v acts_active = Some (int (planning_sem.active_after (planning_sem.time_index t)))"
    "\<And>i. i < length actions \<Longrightarrow> planning_sem.closed_active_count (planning_sem.time_index t) (actions ! i) = 0 \<Longrightarrow> L ! Suc i = off_loc"
    "\<And>i. i < length actions \<Longrightarrow> planning_sem.closed_active_count (planning_sem.time_index t) (actions ! i) = 1 \<Longrightarrow> L ! Suc i = running_loc"
    "\<And>i. i < length actions \<Longrightarrow> act_clock_post_happ c act_to_start_clock (actions ! i) (planning_sem.time_index t)"
    "\<And>i. i < length actions \<Longrightarrow> act_clock_post_happ c act_to_end_clock (actions ! i) (planning_sem.time_index t)"
  shows "happening_post t x"
  unfolding happening_post_def Let_def 
  using assms by blast


lemma happening_postE:
  assumes "happening_post n x"
    and "\<And>L v c. x = (L, v, c)
      \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ n p))
      \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index n) p)))
      \<Longrightarrow> v acts_active = Some (int (planning_sem.active_after (planning_sem.time_index n)))
      \<Longrightarrow> (\<forall>i<length actions. planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)
      \<Longrightarrow> (\<forall>i<length actions. planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)
      \<Longrightarrow> (\<forall>i<length actions. act_clock_post_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))
      \<Longrightarrow> (\<forall>i<length actions. act_clock_post_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow> thesis"
  shows "thesis"
  apply (cases x)
  subgoal 
    using assms(1)
    unfolding happening_post_def Let_def apply simp
    apply (elim conjE)
    apply (erule assms(2))
    by simp_all
  done


lemma happening_post_dests:
  assumes "happening_post n x"
    and "x = (L, v, c)"
  shows "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ n p))"
      "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index n) p)))"
      "v acts_active = Some (int (planning_sem.active_after (planning_sem.time_index n)))"
      "(\<forall>i<length actions. planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc)"
      "(\<forall>i<length actions. planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc)"
      "(\<forall>i<length actions. act_clock_post_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
      "(\<forall>i<length actions. act_clock_post_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  using assms unfolding happening_post_def Let_def by auto

lemma end_start_invsE:
  assumes "end_start_invs n x"
    and "\<And>L v c. happening_invs n (L, v, c) \<Longrightarrow>
    (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p)) \<Longrightarrow>
    v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n))) \<Longrightarrow>
    (\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
    (\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
    (\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
    (\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc) \<Longrightarrow>
    (\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc) \<Longrightarrow>
    thesis"
  shows thesis
  using assms by (auto simp: end_start_invs_def Let_def split: prod.splits)


lemma end_start_invsD:
  assumes "end_start_invs n (L, v, c)"
  shows "happening_invs n (L, v, c) \<and>
    (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p)) \<and>
    v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n))) \<and>
    (\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)) \<and>
    (\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)) \<and>
    (\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)) \<and>
    (\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc) \<and>
    (\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms by (auto simp: end_start_invs_def Let_def split: prod.splits)


lemma end_start_invs_dests:
  assumes "end_start_invs n (L, v, c)"
  shows "happening_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms by (auto dest!: end_start_invsD)

lemma end_start_invsI:
  assumes "x = (L, v, c)"
      "happening_invs n (L, v, c)" 
      "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
      "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
      "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
      "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
      "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
      "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
      "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  shows "end_start_invs n x"
  using assms by (auto simp: end_start_invs_def)

lemma happening_invsE:
  assumes "happening_invs n x"
    "\<And>L v c. x = (L, v, c) \<Longrightarrow>
     (\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
     (\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc) \<Longrightarrow>
     (\<forall>i<length actions. is_not_happening_index (planning_sem.time_index n) i \<longrightarrow> planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc) \<Longrightarrow>
       thesis"
  shows thesis
  using assms by (auto simp: happening_invs_def Let_def split: prod.splits)

lemma happening_invs_dests:
  assumes "happening_invs n (L, v, c)"
  shows "i < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)"
    "i < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)"
    "i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)"
    "i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)"
    "i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 0 \<Longrightarrow> L ! Suc i = off_loc"
    "i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 1 \<Longrightarrow> L ! Suc i = running_loc"
  using assms 
  by (auto simp: happening_invs_def Let_def split: prod.splits)

lemma happening_invsI:
  assumes "x = (L, v, c)"
    "\<And>i. i < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)"
    "\<And>i. i < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)"
    "\<And>i. i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n)"
    "\<And>i. i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n)"
    "\<And>i. i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 0 \<Longrightarrow> L ! Suc i = off_loc"
    "\<And>i. i < length actions \<Longrightarrow> is_not_happening_index (planning_sem.time_index n) i \<Longrightarrow> planning_sem.closed_active_count (planning_sem.time_index n) (actions ! i) = 1 \<Longrightarrow> L ! Suc i = running_loc"
  shows "happening_invs n x"
  using assms
  by (auto simp: happening_invs_def)

lemma end_start_preE:
  assumes "end_start_pre n i x"
    and "\<And>L v c. x = (L, v, c) \<Longrightarrow>
    end_start_invs n (L, v, c) \<Longrightarrow>
    (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p i))) \<Longrightarrow>
    (\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc) \<Longrightarrow>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc) \<Longrightarrow>
    (\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0) \<Longrightarrow>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n)) \<Longrightarrow>
    thesis"
  shows thesis
  apply (cases x)
  apply (rule assms(2), assumption)
  using assms(1) unfolding end_start_pre_def end_start_cond_def Let_def
  by blast+
  
  

lemma end_start_preD:
  assumes "end_start_pre n i (L, v, c)"
  shows "end_start_invs n (L, v, c) \<and>
    (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p i))) \<and>
    (\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc) \<and>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc) \<and>
    (\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0) \<and>
    (\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n))"
  using assms by (auto simp: end_start_pre_def end_start_cond_def Let_def split: prod.splits)

lemma end_start_pre_dests:
  assumes "end_start_pre n i (L, v, c)"
  shows "end_start_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p i)))"
    "(\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc)"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc)"
    "(\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0)"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n))"
  using assms by (auto dest!: end_start_preD)

lemma end_start_preI:
  assumes "x = (L, v, c)"
    "end_start_invs n x"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p i)))"
    "(\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc)"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc)"
    "(\<forall>j. j < i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0)"
    "(\<forall>j. i \<le> j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n))"
  shows "end_start_pre n i x"
  using assms by (auto simp: end_start_pre_def end_start_cond_def)

lemma end_start_postE:
  assumes "end_start_post n i x"
    and "x = (L, v, c)"
    and "end_start_invs n x \<Longrightarrow>   
    (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p (Suc i)))) \<Longrightarrow>
    (\<forall>j. j \<le> i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc) \<Longrightarrow>
    (\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc) \<Longrightarrow>
    (\<forall>j. j \<le> i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0) \<Longrightarrow> 
    (\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n)) \<Longrightarrow> 
    thesis"
  shows thesis
  using assms by (auto simp: end_start_post_def end_start_cond_def Let_def split: prod.splits)

lemma end_start_post_dests:
  assumes "end_start_post n i x"
    and "x = (L, v, c)"
  shows "end_start_invs n x"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p (Suc i))))"
    "(\<forall>j. j \<le> i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc)"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc)"
    "(\<forall>j. j \<le> i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0)"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n))"
  using assms by (auto simp: end_start_post_def end_start_cond_def Let_def split: prod.splits)

lemma end_start_postI:
  assumes "x = (L, v, c)"
    and "end_start_invs n x"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (partially_updated_locked_before (planning_sem.time_index n) p (Suc i))))"
    "(\<forall>j. j \<le> i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = ending_loc)"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> L ! Suc j = running_loc)"
    "(\<forall>j. j \<le> i \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> c (act_to_end_clock (actions ! j)) = 0)"
    "(\<forall>j. i < j \<and> j < length actions \<and> is_ending_index (planning_sem.time_index n) j \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! j) (planning_sem.time_index n))"
  shows "end_start_post n i x"
  using assms by (auto simp: end_start_post_def end_start_cond_def)

lemma happening_pre_end_starts_dests:
  assumes "happening_pre_end_starts n x"
      and "x = (L, v, c)"
  shows "end_start_invs n (L, v, c)"
        "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))"
        "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = running_loc)" 
        "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  using assms unfolding happening_pre_end_starts_def Let_def by (auto split: prod.splits)

lemma happening_pre_end_startsI:
  assumes "x = (L, v, c)"
    "end_start_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index n) p)))"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = running_loc)" 
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    shows "happening_pre_end_starts n x"
  using assms happening_pre_end_starts_def by auto

lemma happening_post_end_starts_dests:
  assumes "happening_post_end_starts n x"
    and "x = (L, v, c)"
  shows "end_start_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index n) p)))"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = ending_loc)"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  using assms unfolding happening_post_end_starts_def Let_def by (auto split: prod.splits)


lemma happening_post_end_startsI:
  assumes  "x = (L, v, c)"
  and "end_start_invs n (L, v, c)"
      "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index n) p)))"
      "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = ending_loc)"
      "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  shows "happening_post_end_starts n x"
  using assms unfolding happening_post_end_starts_def by auto

lemma happening_pre_instants_dests:
  assumes "happening_pre_instants n (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms unfolding happening_pre_instants_def Let_def prod.case
  by (auto split: prod.splits)

lemma happening_pre_instantsI:
  assumes "x = (L, v, c)"
    "instant_action_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ n p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  shows "happening_pre_instants n x" using assms unfolding happening_pre_instants_def Let_def prod.case by auto

lemma instant_action_invs_dests:
  assumes "instant_action_invs n (L, v, c)" 
  shows "happening_invs n (L, v, c)"
    "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index n) p))"
    "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = ending_loc)"
  using assms unfolding instant_action_invs_def Let_def by (auto split: prod.splits)
  
lemma instant_action_invsI:
  assumes "x = (L, v, c)"
    "happening_invs n (L, v, c)"
    "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index n) p))"
    "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i<length actions. is_starting_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
    "(\<forall>i<length actions. is_ending_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = ending_loc)"
  shows "instant_action_invs n x" 
  using assms unfolding instant_action_invs_def by auto

lemma instant_pre_dests:
  assumes "instant_pre n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_part_updated_prop_state n j p))"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
  "(\<forall>i. i < j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
  "(\<forall>i. i < j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
  "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms unfolding instant_pre_def instant_cond_def Let_def prod.case by blast+

lemma instant_preI:
  assumes "x = (L, v, c)"
    "instant_action_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_part_updated_prop_state n j p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i. i < j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
    "(\<forall>i. i < j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  shows "instant_pre n j x" 
  using assms unfolding instant_pre_def instant_cond_def Let_def prod.case by blast+

lemma instant_post_dests:
  assumes "instant_post n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_part_updated_prop_state n (Suc j) p))"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
  "(\<forall>i. i < Suc j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
  "(\<forall>i. i < Suc j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  "(\<forall>i. Suc j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
  "(\<forall>i. Suc j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))" 
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms unfolding instant_post_def comp_def instant_cond_def Let_def prod.case by blast+

lemma instant_postI:
  assumes "instant_action_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_part_updated_prop_state n (Suc j) p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))" 
    "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  shows "instant_post n j (L, v, c)"
  using assms unfolding instant_post_def comp_def instant_cond_def by auto

lemma instant_starting_cond_dests:
  assumes "instant_starting_cond n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_intermediate_prop_state n j p))"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n) + 1))"
  "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
  "(\<forall>i. i < j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
  "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
  "L ! Suc j = starting_loc"
  "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms unfolding instant_starting_cond_def Let_def prod.case by blast+

lemma instant_starting_condI:
  assumes "instant_action_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_intermediate_prop_state n j p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n) + 1))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
    "(\<forall>i. i < j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i. j \<le> i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    "L ! Suc j = starting_loc"
    "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  shows "instant_starting_cond n j (L, v, c)" 
  using assms unfolding instant_starting_cond_def by auto 

lemma instant_ending_cond_dests:
  assumes "instant_ending_cond n j (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_intermediate_prop_state n j p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n) + 1))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    "L ! Suc j = ending_loc"
    "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  using assms unfolding instant_ending_cond_def Let_def prod.case by blast+


lemma instant_ending_condI:
  assumes "instant_action_invs n (L, v, c)"
    "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (instant_intermediate_prop_state n j p))"
    "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n) + 1))"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
    "(\<forall>i. i \<le> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! i) (planning_sem.time_index n))"
    "(\<forall>i. j < i \<and> i < length actions \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> act_clock_pre_happ c act_to_end_clock (actions ! i) (planning_sem.time_index n))"
    "L ! Suc j = ending_loc"
    "(\<forall>i<length actions. i \<noteq> j \<and> is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)"
  shows "instant_ending_cond n j (L, v, c)"
  using assms unfolding instant_ending_cond_def by auto


lemma happening_post_instants_dests:
  assumes "happening_post_instants n (L, v, c)"
  shows "instant_action_invs n (L, v, c)"
  "(p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_happ n p))"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
  "(i<length actions \<Longrightarrow> is_instant_index (planning_sem.time_index n) i \<Longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
  "(i<length actions \<Longrightarrow> is_instant_index (planning_sem.time_index n) i \<Longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  "(i<length actions \<Longrightarrow> is_instant_index (planning_sem.time_index n) i \<Longrightarrow> L ! Suc i = off_loc)"  
  using assms unfolding happening_post_instants_def Let_def prod.case act_clock_pre_happ_def by blast+
  
lemma happening_post_instantsI:
  assumes "instant_action_invs n (L, v, c)"
  "(\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_happ n p))"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index n)))"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_start_clock (actions ! i)) = 0)"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> c (act_to_end_clock (actions ! i)) = 0)"
  "(\<forall>i<length actions. is_instant_index (planning_sem.time_index n) i \<longrightarrow> L ! Suc i = off_loc)" 
  shows "happening_post_instants n (L, v, c)" 
  using assms unfolding happening_post_instants_def Let_def prod.case act_clock_pre_happ_def by blast+

lemma happening_pre_start_starts_dests:
  assumes "happening_pre_start_starts i (L, v, c)"
  shows "start_start_invs i (L, v, c)"
  "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_happ i p)"
  "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index i)))"
  "j<length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) j \<Longrightarrow>  act_clock_pre_happ c act_to_start_clock (actions ! j) (planning_sem.time_index i)"
  "j<length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) j \<Longrightarrow>  L ! Suc j = off_loc"
  using assms unfolding happening_pre_start_starts_def Let_def prod.case by blast+

lemma happening_pre_start_startsI:
  assumes "start_start_invs i (L, v, c)"
      "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_happ i p)"
      "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index i)))"
      "\<And>ia. ia < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) ia \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! ia) (planning_sem.time_index i)"
      "\<And>ia. ia < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) ia \<Longrightarrow> L ! Suc ia = off_loc"
  shows "happening_pre_start_starts i (L, v, c)"
  unfolding happening_pre_start_starts_def using assms unfolding Let_def prod.case by blast+

lemma start_start_invsI:
  assumes "happening_invs i (L, v, c)"
      "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))"
      "\<And>ia. ia < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) ia \<Longrightarrow> c (act_to_end_clock (actions ! ia)) = 0"
      "\<And>ia. ia < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) ia \<Longrightarrow> c (act_to_start_clock (actions ! ia)) = 0"
      "\<And>ia. ia < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) ia \<Longrightarrow> c (act_to_end_clock (actions ! ia)) = 0"
      "\<And>ia. ia < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) ia \<Longrightarrow> L ! Suc ia = ending_loc"
      "\<And>ia. ia < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) ia \<Longrightarrow> L ! Suc ia = off_loc"
  shows "start_start_invs i (L, v, c)"
  unfolding start_start_invs_def using assms by auto

lemma start_start_invs_dests:
  assumes "start_start_invs i (L, v, c)"
  shows "happening_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding start_start_invs_def Let_def prod.case by blast+

lemma start_start_preI:
  assumes "start_start_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (starting_part_updated_prop_state i n p)"
    "v acts_active = Some (int (updated_active_before i n))"
    "\<And>k. k < n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! k) (planning_sem.time_index i)"
    "\<And>k. k < n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "\<And>k. n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "start_start_pre i n (L, v, c)"
  unfolding start_start_pre_def start_start_cond_def
  using assms by auto

lemma start_start_pre_dests:
  assumes "start_start_pre i n (L, v, c)"
  shows "start_start_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (starting_part_updated_prop_state i n p)"
    "v acts_active = Some (int (updated_active_before i n))"
    "k < n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! k) (planning_sem.time_index i)"
    "k < n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding start_start_pre_def start_start_cond_def Let_def prod.case by blast+

lemma start_start_postI:
  assumes "start_start_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (starting_part_updated_prop_state i (Suc n) p)"
    "v acts_active = Some (int (updated_active_before i (Suc n)))"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! k) (planning_sem.time_index i)"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "start_start_post i n (L, v, c)"
  unfolding start_start_post_def start_start_cond_def Let_def prod.case
  using assms by auto

lemma start_start_post_dests:
  assumes "start_start_post i n (L, v, c)"
  shows "start_start_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (starting_part_updated_prop_state i (Suc n) p)"
    "v acts_active = Some (int (updated_active_before i (Suc n)))"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> act_clock_pre_happ c act_to_start_clock (actions ! k) (planning_sem.time_index i)"
    "\<And>k. k < Suc n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding start_start_post_def start_start_cond_def Let_def prod.case by blast+

lemma happening_post_start_startsI:
  assumes "start_start_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_start_happ i p)"
    "v acts_active = Some (int (planning_sem.active_during (planning_sem.time_index i)))"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
  shows "happening_post_start_starts i (L, v, c)"
  unfolding happening_post_start_starts_def
  using assms by auto

lemma happening_post_start_starts_dests:
  assumes "happening_post_start_starts i (L, v, c)"
  shows "start_start_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_start_happ i p)"
    "v acts_active = Some (int (planning_sem.active_during (planning_sem.time_index i)))"
    "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
  using assms unfolding happening_post_start_starts_def Let_def prod.case by blast+

lemma happening_pre_end_endsI:
  assumes "end_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_start_happ i p)"
    "v acts_active = Some (int (planning_sem.active_during (planning_sem.time_index i)))"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
  shows "happening_pre_end_ends i (L, v, c)"
  using assms unfolding happening_pre_end_ends_def Let_def prod.case
  by auto

lemma happening_pre_end_ends_dests:
  assumes "happening_pre_end_ends i (L, v, c)"
  shows "end_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow>  prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_instant_start_happ i p)"
    "v acts_active = Some (int (planning_sem.active_during (planning_sem.time_index i)))"
    "k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
  using assms unfolding happening_pre_end_ends_def Let_def prod.case
  by auto

lemma end_end_invsI:
  assumes "happening_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "end_end_invs i (L, v, c)"
  using assms unfolding end_end_invs_def Let_def prod.case by auto

lemma end_end_invs_dests:
  assumes "end_end_invs i (L, v, c)"
  shows "happening_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow>prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))"
    "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding end_end_invs_def Let_def prod.case by blast+

lemma end_end_preI:
  assumes "end_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (ending_part_updated_prop_state i n p)"
     "v acts_active = Some (int (updated_active_during i n))"
    "\<And>k. n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
    "\<And>k. k < n \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "end_end_pre i n (L, v, c)"
  using assms unfolding end_end_pre_def end_end_cond_def Let_def prod.case by blast+

lemma end_end_pre_dests:
  assumes "end_end_pre i n (L, v, c)"
  shows "end_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (ending_part_updated_prop_state i n p)"
    "v acts_active = Some (int (updated_active_during i n))"
    "n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
    "k < n \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding end_end_pre_def end_end_cond_def Let_def prod.case by blast+
  
lemma end_end_postI:
  assumes "end_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (ending_part_updated_prop_state i (Suc n) p)"
    "v acts_active = Some (int (updated_active_during i (Suc n)))"
    "\<And>k. Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
    "\<And>k. k < Suc n \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "end_end_post i n (L, v, c)"
  using assms unfolding end_end_post_def end_end_cond_def Let_def prod.case by blast+

lemma end_end_post_dests:
  assumes "end_end_post i n (L, v, c)"
  shows "end_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (ending_part_updated_prop_state i (Suc n) p)"
    "v acts_active = Some (int (updated_active_during i (Suc n)))"
    "Suc n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = ending_loc"
    "k < Suc n \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding end_end_post_def end_end_cond_def Let_def prod.case by blast+

lemma happening_post_end_endsI:
  assumes "end_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ i p)"
    "v acts_active = Some (int (planning_sem.active_during_minus_ended (planning_sem.time_index i)))"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "happening_post_end_ends i (L, v, c)"
  using assms unfolding happening_post_end_ends_def Let_def prod.case by blast+

lemma happening_post_end_ends_dests:
  assumes "happening_post_end_ends i (L, v, c)"
  shows "end_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ i p)"
    "v acts_active = Some (int (planning_sem.active_during_minus_ended (planning_sem.time_index i)))"
    "k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding happening_post_end_ends_def Let_def prod.case by blast+

lemma happening_pre_start_endsI:
  assumes "start_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
  shows "happening_pre_start_ends i (L, v, c)"
  using assms unfolding happening_pre_start_ends_def Let_def prod.case by blast+

lemma happening_pre_start_ends_dests:
  assumes "happening_pre_start_ends i (L, v, c)"
  shows "start_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_during (planning_sem.time_index i) p))"
    "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
  using assms unfolding happening_pre_start_ends_def Let_def prod.case by blast+

lemma start_end_invsI:
  assumes "happening_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ i p)"
    "v acts_active = Some (int (planning_sem.active_after (planning_sem.time_index i)))"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "\<And>k. k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
    "\<And>k. k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  shows "start_end_invs i (L, v, c)"
  using assms unfolding start_end_invs_def Let_def prod.case by blast+

lemma start_end_invs_dests:
  assumes "start_end_invs i (L, v, c)"
  shows "happening_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_var p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_var p) = Some (prop_state_after_happ i p)"
    "v acts_active = Some (int (planning_sem.active_after (planning_sem.time_index i)))"
    "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_start_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> c (act_to_end_clock (actions ! k)) = 0"
    "k < length actions \<Longrightarrow> is_ending_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
    "k < length actions \<Longrightarrow> is_instant_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = off_loc"
  using assms unfolding start_end_invs_def Let_def prod.case by blast+

lemma start_end_preI:
  assumes "start_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (updated_locked_during i n p))"
    "\<And>k. n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "\<And>k. k < n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  shows "start_end_pre i n (L, v, c)"
  using assms unfolding start_end_pre_def start_end_cond_def by auto

lemma start_end_pre_dests:
  assumes "start_end_pre i n (L, v, c)"
  shows "start_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (updated_locked_during i n p))"
    "n \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "k < n \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  using assms unfolding start_end_pre_def start_end_cond_def Let_def prod.case by blast+

lemma start_end_postI:
  assumes "start_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (updated_locked_during i (Suc n) p))"
    "\<And>k. (Suc n) \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "\<And>k. k < (Suc n) \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  shows "start_end_post i n (L, v, c)"
  using assms unfolding start_end_post_def start_end_cond_def by auto

lemma start_end_post_dests:
  assumes "start_end_post i n (L, v, c)"
  shows "start_end_invs i (L, v, c)"
    "p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (updated_locked_during i (Suc n) p))"
    "(Suc n) \<le> k \<Longrightarrow> k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = starting_loc"
    "k < (Suc n) \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  using assms unfolding start_end_post_def start_end_cond_def Let_def by (auto split: prod.splits)

lemma happening_post_start_endsI:
  assumes "start_end_invs i (L, v, c)"
      "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index i) p))"
      "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  shows "happening_post_start_ends i (L, v, c)"
  using assms unfolding happening_post_start_ends_def Let_def prod.case by blast+

lemma happening_post_start_ends_dests:
  assumes "happening_post_start_ends i (L, v, c)"
  shows "start_end_invs i (L, v, c)"
      "p \<in> set props \<Longrightarrow>p \<in> set props \<Longrightarrow>prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index i) p))"
      "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  using assms unfolding happening_post_start_ends_def Let_def prod.case by blast+

lemma happening_post_inv_checkI:
  assumes "start_end_invs i (L, v, c)"
    "\<And>p. p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index i) p))"
    "\<And>k. k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  shows "happening_post_inv_check i (L, v, c)"
  using assms unfolding happening_post_inv_check_def by auto

lemma happening_post_inv_check_dests:
  assumes "happening_post_inv_check i (L, v, c)"
    shows "start_end_invs i (L, v, c)"
      "p \<in> set props \<Longrightarrow> prop_to_lock p \<in> dom (map_of net_bounds) \<Longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_after (planning_sem.time_index i) p))"
      "k < length actions \<Longrightarrow> is_starting_index (planning_sem.time_index i) k \<Longrightarrow> L ! Suc k = running_loc"
  using assms unfolding happening_post_inv_check_def Let_def prod.case by blast+


end
end

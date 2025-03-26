theory TP_NTA_Reduction_Spec
  imports Temporal_Planning_Base.Temporal_Plans
      TA_Code.Simple_Network_Language_Export_Code

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
  ActEnd 'action |
  Urge

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
  
  guard = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec start_snap);
  
  not_locked_check = map (is_prop_lock_ab 0) (dels start_snap);
  pre_check = map (is_prop_ab 1) (pre start_snap);
  var_check = bexp_and_all (not_locked_check @ pre_check);
  
  add_upds = map (set_prop_ab 1) (adds start_snap);
  del_upds = map (set_prop_ab 0) (dels start_snap);
  upds = add_upds @ del_upds;

  resets = [ActStart a]
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

definition edge_3_spec::"'action \<Rightarrow> _" where
"edge_3_spec a \<equiv>
let
  end_snap = at_end a;
  
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec end_snap);

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
  dels = map (set_prop_ab 0) (dels end_snap);
  
  resets = [ActEnd a]
in
  (end_instant, check, [], Sil (STR ''''), adds @ dels, resets, off)
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
  invs = []
in 
  (init_loc, locs, committed_locs, urgent_locs, edges, invs)"

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
  (init_loc, locs, committed_locs, urgent_locs, edges, invs)
"

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
  automata = zip (map to_nat [0..length automata - 1]) automata;

  clocks = map ActStart actions @ map ActEnd actions;

  prop_lock_var_defs = map (\<lambda>p. (PropLock p, 0::int, int (length actions))) props;
  prop_var_vars_defs = map (\<lambda>p . (PropVar p, 0::int, 1::int)) props;
  acts_active_var = (ActsActive, 0, from_nat (length actions)::int);
  planning_lock_var = (PlanningLock, 0, 2::int);
  vars = planning_lock_var # acts_active_var # prop_lock_var_defs @ prop_var_vars_defs;

  formula = formula.EX (loc 0 GoalLocation)
in (automata, clocks, vars, formula)"
(* The id of the main automaton is 0 *)
end

find_consts name: "renum"

definition mk_renum::"'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"mk_renum l \<equiv>
  let
    nums = [0..length l - 1]  |> map nat;
    act_nums = nums |> zip l;
    f = map_of act_nums
  in the o f"

definition mk_snd_ord_renum::"'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat" where
"mk_snd_ord_renum \<equiv> (!) o map mk_renum"

context tp_nta_reduction_spec
begin
definition "nta_vars \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in vars"

abbreviation "var_renum \<equiv> mk_renum (map fst nta_vars)"

definition "nta_clocks \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in clocks"

abbreviation "clock_renum \<equiv> mk_renum nta_clocks"

definition "ntas \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in automata"

(* Explicitly returned states *)
abbreviation "ta_states a \<equiv> case a of 
  (name, init, states, _) \<Rightarrow> states"

abbreviation "individual_ta_states \<equiv> map ta_states ntas"

definition "all_ta_states = fold (@) individual_ta_states []"

(* Actual states defined by transitions *)

abbreviation get_actual_auto where
"get_actual_auto gen_auto \<equiv> 
  let 
    (name, initial, states, committed, urgent, transitions) = gen_auto 
  in (committed, urgent, transitions)"

definition actual_autos where
"actual_autos = map get_actual_auto ntas"

abbreviation trans_locs where
"trans_locs tr \<equiv>
  let
    (s, g, c, a, u, r, t) = tr
  in
    {s, t}"

abbreviation auto_trans where
"auto_trans auto \<equiv> 
  let
    (committed, urgent, trans, invs) = auto
  in
    trans"

definition actual_locs where
"actual_locs \<equiv>
  let 
    trans = (fold (@) (map auto_trans actual_autos) [])
  in
    fold (\<union>) (map trans_locs trans) {}"

(* Renumbering states *)
abbreviation "state_renum' \<equiv> mk_snd_ord_renum individual_ta_states"

(* The injective renumbering from every single state *)
definition "inj_state_renum i \<equiv> 
  let renum' = state_renum' i;
      states = individual_ta_states ! i;
      other_states = list_of_set (set all_ta_states - set states);
      renum = extend_domain renum' other_states (length states - 1)
  in renum"

lemma extend_domain_not_in_set:
  assumes "x \<notin> set es"
  shows "extend_domain f es n x = f x"
  using assms
  unfolding extend_domain_def
  by (auto split: prod.splits)

find_theorems "?f ?x = (?y::nat list)"

lemma extend_domain_fold_lemma:
  assumes "set as \<subseteq> set as'"
  shows "fold (\<lambda>x (i, xs). if x \<in> set as' then (i + 1, (x, i + 1) # xs) else (i, xs)) as (n, bs)
  = (n + length as, rev (zip as [(n+1)..<(n + (length as) + 1)]) @ bs)" (is "fold ?f as (n, bs) = _")
  using assms
proof (induction as arbitrary: n bs)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  have "\<And>n bs. fold ?f else (i, xs)) as (n, bs) =
    (n + length as, rev (zip as [(n+1)..<(n + length as + 1)]) @ bs)"
    using Cons by auto
  hence IH': "\<And>n bs. fold ?f as (n, bs) =
    (n + length as, rev (zip as [n+1..(n + length as)]) @ bs)"
    by blast
  have "a \<in> set as'" using Cons by simp
  hence "fold ?f (a # as) (n, bs)
    = fold ?f as (n + 1, (a, n + 1) # bs)"
    apply (subst fold_Cons) 
    apply (subst o_apply)
    apply (subst prod.case)+
    by (auto simp: z3_rule(112))
  also have "... = 
    ((n + 1) + length as, rev (zip as [int ((n + 1) + 1)..int (n + 1) + int (length as)]) @ (a, n + 1) # bs)" 
    using IH' 
    by auto
  also have "... = (n + (length (a#as)), rev (zip as [int ((n + 1) + 1)..int (n + length (a#as))]) @ (a, n + 1) # bs)" 
    by (metis add_Suc add_Suc_right int_ops(5) length_nth_simps(2) semiring_norm(174))
  also have "... = (n + (length (a#as)), rev (zip as [int ((n + 1) + 1)..int (n + length (a#as))]) @ [(a, n + 1)] @ bs)" 
    by fastforce
  also have "... = (n + (length (a#as)), (rev ((a, n + 1)#(zip as [int ((n + 1) + 1)..int (n + length (a#as))]))) @ bs)" 
    by auto
  also have "... = (n + (length (a#as)), (rev (zip (a#as) [int (n + 1)..int (n + length (a#as))])) @ bs)"
    apply (subst prod.case)
    apply (subst zip_Cons_Cons[symmetric])
    apply (subst (2) int_plus)
    apply (subst int_ops(2))
    apply (subst upto_rec1[symmetric])
     apply simp
    by simp
  finally show ?case by blast
qed


lemma extend_domain_fold:
  "extend_domain f (e#es) n x = extend_domain (f(e := n + 1)) es (n + 1) x"
proof (induction es arbitrary: f e n)
  case Nil
  then show ?case unfolding extend_domain_def 
    by (auto split: prod.splits)
next
  case (Cons a es f e n)
  have "extend_domain f (e # a # es) n x = 
    ( let 
        (i, xs) = fold 
            (\<lambda>x (i, xs). if x \<in> set (e # a # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
            (e # a # es) 
            (n, []); 
        m' = map_of xs
      in 
        (\<lambda>x. if x \<in> set (e # a # es) then the (m' x) else f x)
    ) x" unfolding extend_domain_def ..
  hence "extend_domain f (e # a # es) n x = 
    (let 
      (i, xs) = fold 
          (\<lambda>x (i, xs). if x \<in> set (e # a # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
          (a # es)
          (n + 1, [(e, n + 1)]);
         m' = map_of xs
     in (\<lambda>x. if x \<in> set (e # a # es) then the (m' x) else f x)) x"
    using fold_Cons by simp
  have "extend_domain (f(e := n + 1)) (a # es) (n + 1) x = extend_domain (f(e := n + 1, a := n + 1 + 1)) es (n + 1 + 1) x" 
    apply (subst Cons.IH) 
    ..
  
  show ?case
  proof (cases "x \<in> set (a # es)"; cases "x = e")
    assume "x \<in> set (a # es)" "x = e"
    then show ?thesis sorry
  next
    assume "x \<in> set (a # es)" "x \<noteq> e"
    then show ?thesis sorry
  next
    assume "x \<notin> set (a # es)" "x = e"
    then show ?thesis sorry
  next
    assume "x \<notin> set (a # es)" "x \<noteq> e"
    then show ?thesis sorry
  qed
qed

lemma extend_domain_index:
  assumes "x \<in> set es"
  shows "extend_domain f es n x = n + last_index es x + 1"
  using assms
proof (induction es arbitrary: f  n)
  case Nil
  then show ?case by simp
next
  case (Cons e es f n)
  then show ?case 
  proof (cases "x \<in> set es")
    case False
    with Cons
    have xe: "x = e" by simp
    hence "n + last_index (e # es) x + 1 = n + 1" using False
      apply (subst last_index_Cons)
      by simp
    from xe 
    have "extend_domain f (e # es) n x = 
    (
      let 
        (i, xs) = fold 
            (\<lambda>x (i, xs). if x \<in> set (e # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
            (es) (n + 1, [(e, n + 1)]); 
        m' = map_of xs 
      in 
        (\<lambda>x. if x \<in> set (e # es) then the (m' x) else f x)) x" 
      unfolding extend_domain_def fold_Cons by (auto split: prod.splits)
    also have "... = 
      (let 
        (i, xs) = fold 
            (\<lambda>x (i, xs). if x \<in> set (e # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
            (es) (n + 1, [(e, n + 1)]); 
        m' = map_of xs
      in 
       the (m' x))" using xe by (auto split: prod.splits)
    also have "... = n + 1" using False xe 
      apply (subst Let_def)
      using  extend_domain_fold_lemma[where as' = "e#es" and as = es and n = "n + 1" and bs = "[(e, n + 1)]"]
      apply (simp add:)
    find_theorems name: "fold*filter"
    thus ?thesis 
  next
    case False
    then show ?thesis sorry
  qed
qed

lemma extend_domain_inj_new:
  "inj_on (extend_domain f e n) (set e)"
proof (induction e)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
   show ?case 
   proof (rule inj_onI)
     fix x y
     assume x: "x \<in> set (a # as)" 
        and y: "y \<in> set (a # as)" 
        and f: "extend_domain f (a # as) n x = extend_domain f (a # as) n y"
     consider "x \<noteq> a \<and> y \<noteq> a"
       | "x \<noteq> a \<and> y = a"
       | "x = a \<and> y \<noteq> a"
       | "x = a \<and> y = a" by blast
     thus "x = y"
     proof cases
       case 1
       then show ?thesis 
         using x y f unfolding extend_domain_def
         apply -
         apply (rule Cons.IH[THEN inj_onD])
         
     next
       case 2
       then show ?thesis sorry
     next
       case 3
       then show ?thesis sorry
     next
       case 4
       then show ?thesis sorry
     qed
   qed
qed
   apply simp
  subgoal for x xs


lemma extend_domain_inj:
  assumes "inj_on f (set d)"
      and "\<forall>x \<in> set d. f x \<le> n"
          "n = length d - 1"
  shows "inj_on (extend_domain f e n) (set d \<union> set e)"
proof -

qed

lemma state_renum'_inj: 
  assumes i_ran: "i < length individual_ta_states"
      and x: "x \<in> set all_ta_states"
      and y: "y \<in> set all_ta_states"
      and e: "inj_state_renum i x = inj_state_renum i y"
        shows "x = y"
proof -
  
qed

abbreviation "nta_init \<equiv> fst o snd"

abbreviation "ntas_inits \<equiv> map nta_init ntas"

definition "urge_clock \<equiv> Urge"

(* This needs to be lifted out of the locale *)
definition "broadcast \<equiv> []::String.literal list"

(* There is one action *)
definition "nta_actions \<equiv> [STR '''']::String.literal list"

find_consts name: "mk_renaming"

abbreviation "act_renum \<equiv> mk_renum (broadcast @ nta_actions)"

abbreviation "init_vars \<equiv> map (\<lambda>x. (fst x, 0::int)) nta_vars"

definition "autos \<equiv> map (snd o snd o snd) ntas"

definition "form \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in formula"

sublocale Simple_Network_Rename_Formula
    broadcast 
    nta_vars 
    act_renum 
    var_renum 
    clock_renum
    inj_state_renum
    urge_clock
    init_vars
    ntas_inits
    autos
    form
proof

qed
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
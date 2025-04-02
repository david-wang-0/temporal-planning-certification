theory TP_NTA_Reduction_Spec
  imports Temporal_Planning_Base.Temporal_Plans
      TA_Code.Simple_Network_Language_Export_Code

begin
(* To do: implement the compilation abstractly or directly using show? *)

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

(* Some hard-coding of sets as lists. To do: fix *)
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
  assumes fluent_domain: "fluent_domain (set props) at_start at_end
    (set o over_all) (set o pre) (set o adds) (set o dels) (set actions)"
        and init_props: "set init \<subseteq> set props"
        and goal_props: "set goal \<subseteq> set props"
begin

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
definition start_edge_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
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

definition edge_2_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
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

definition edge_3_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
"edge_3_spec a \<equiv>
let
  end_snap = at_end a;
  
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec end_snap);

  u_dur_const = u_dur_spec a;
  guard = l_dur_spec a @ u_dur_spec a @ int_clocks;

  unlock_invs = map (inc_prop_lock_ab (-1)) (over_all a);
  
  resets = [ActEnd a]
in 
  (Running a, bexp.true, guard, Sil (STR ''''), [], resets, EndInstant a)
"

definition end_edge_spec::"'action \<Rightarrow> 'action location \<times> ('proposition variable, int) Simple_Expressions.bexp \<times> ('action clock, int) acconstraint list \<times> String.literal act \<times> ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 'action clock list \<times> 'action location" where
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
  invs = []
in 
  (init_loc, locs, committed_locs, urgent_locs, edges, invs)"

(* To do: add the conditions on the planning state *)

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
  can_end = var_is 1 PlanningLock;
  goal_sat = map (is_prop_ab 1) goal;
  cond = bexp_and_all (can_end # goal_sat);
  
  lock_plan = set_var 2 PlanningLock
in
  (Planning, cond, [], Sil (STR ''''), [lock_plan], [], GoalLocation)
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
      'action location) list \<times>
      ('action location \<times> 
      ('action clock, int) acconstraint list
    ) list" where
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
  automata = zip [0..<length automata] automata;

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

subsubsection \<open>Some functions for renumbering\<close>


definition mk_renum::"'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"mk_renum l \<equiv>
  let
    nums = [0..<length l];
    act_nums = zip l nums;
    f = map_of act_nums
  in the o f"

definition mk_snd_ord_renum::"'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat" where
"mk_snd_ord_renum \<equiv> (!) o map mk_renum"

lemma map_of_zip_lemma:
  assumes "x \<in> set as"
  shows "the (map_of (zip as [n..<n + length as]) x) = n + List_Index.index as x"
  using assms
proof (induction as arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a as n)
  show ?case 
  proof (cases "x \<in> set as")
    case True
    show ?thesis
    proof (cases "x = a")
      case xa: True
      hence xa: "x = a" using Cons by simp
      hence "the (map_of (zip (a # as) [n..<n + length (a # as)]) x) = n" by (subst upt_conv_Cons) auto
      then show ?thesis using xa by simp
    next
      case False
      hence "the (map_of (zip (a # as) [n..<n + length (a # as)]) x) = the (map_of (zip as [Suc n..<n + length (a # as)]) x)"
        apply (subst upt_conv_Cons)
         apply simp
        apply (subst zip_Cons_Cons)
        apply (subst map_of_Cons_code(2)) 
        by (metis (full_types))
      also have "... = the (map_of (zip as [Suc n..<Suc n + length as]) x)"
        by simp
      also have "... = Suc n + List_Index.index as x" using Cons.IH[OF True] by blast
      finally show ?thesis using index_Cons False by auto
    qed
  next
    case False
    hence xa: "x = a" using Cons by simp
    hence "the (map_of (zip (a # as) [n..<n + length (a # as)]) x) = n"
      apply (subst upt_conv_Cons)
      by auto
    then show ?thesis 
      using xa by simp
  qed
qed
    

lemma mk_renum_index: 
  assumes "x \<in> set xs"
  shows "mk_renum xs x = List_Index.index xs x"
  unfolding mk_renum_def
  using map_of_zip_lemma[OF assms, of 0]
  by auto
  

lemma mk_renum_inj: "inj_on (mk_renum xs) (set xs)"
proof
  fix x y
  assume x: "x \<in> set xs"
     and y: "y \<in> set xs"
     and rn: "mk_renum xs x = mk_renum xs y"
  from x mk_renum_index
  have "mk_renum xs x = List_Index.index xs x" by metis
  moreover
  from y mk_renum_index
  have "mk_renum xs y = List_Index.index xs y" by metis
  ultimately
  have "List_Index.index xs x = List_Index.index xs y" using rn by simp
  thus "x = y" using inj_on_index unfolding inj_on_def using x y by simp
qed

context tp_nta_reduction_spec
begin

subsection \<open>Automata\<close>

definition "ntas \<equiv> 
let (automata, clocks, vars, formula) = timed_automaton_net_spec 
in automata"

text \<open>The returned automata also contain extra values\<close>
abbreviation "get_actual_auto \<equiv> snd o snd o snd"

subsubsection \<open>Parts of transitions\<close>
abbreviation "trans_resets \<equiv> fst o snd o snd o snd o snd o snd"

abbreviation "trans_guards \<equiv> fst o snd o snd"

subsubsection \<open>Actual transitions\<close>

(* definition get_actual_auto where
"get_actual_auto gen_auto \<equiv> 
  let 
    (name, initial, states, committed, urgent, transitions, invs) = gen_auto 
  in (committed, urgent, transitions, invs)" *)


definition actual_autos where
"actual_autos = map get_actual_auto ntas"

find_theorems name: "option*E"

lemma in_actual_autosE:
  assumes auto: "auto \<in> set actual_autos"
      and alt:  "\<And>act. auto = (snd o snd) (action_to_automaton_spec act) \<Longrightarrow> act \<in> set actions \<Longrightarrow> thesis"
                "auto = (snd o snd) main_auto_spec \<Longrightarrow> thesis"
   shows thesis
proof -
  from auto 
  have "auto \<in> (\<lambda>a. snd (snd a)) ` (set (map action_to_automaton_spec actions)) \<or> auto = snd (snd main_auto_spec)"
    unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case comp_apply
    set_map 
    apply -
    apply (subst (asm) image_image[symmetric, of _ snd])
    apply (subst (asm) zip_range_id)
    by auto
  then consider
    "\<exists>act \<in> set actions. auto = (snd o snd) (action_to_automaton_spec act)"
  | "auto = (snd o snd) main_auto_spec"
    by force
  thus ?thesis
    apply cases
    using alt by blast+
qed
  
(* definition auto_trans where
"auto_trans auto \<equiv> 
  let
    (committed, urgent, trans, invs) = auto
  in
    trans" *)

abbreviation "auto_trans \<equiv> (fst o snd o snd)"

abbreviation "auto_invs \<equiv> (snd o snd o snd)"

definition ta_trans where
"ta_trans = map auto_trans actual_autos"

definition ta_invs where
"ta_invs = map auto_invs actual_autos"
                                  
subsection \<open>Clocks\<close>

definition "nta_clocks \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in clocks"

definition "urge_clock \<equiv> Urge"

definition "clock_renum \<equiv> mk_renum (urge_clock # nta_clocks)"

subsubsection \<open>Actual clocks\<close>

find_theorems name: "clkp"

definition "trans_clocks t\<equiv>
let (l, b, c, a, u, r, l') = t
in set r \<union> (fst ` collect_clock_pairs c)"

definition "trans_to_clocks trs \<equiv> 
let 
  trans_clocks = map trans_clocks trs
in
  fold (\<union>) trans_clocks {}"

definition "inv_clocks i \<equiv> fst ` (collect_clock_pairs (snd i))"

definition "invs_to_clocks is \<equiv>
let 
  inv_clocks = map inv_clocks is
in
  fold (\<union>) inv_clocks {}"

definition "ta_clocks \<equiv> map trans_to_clocks ta_trans @ map invs_to_clocks ta_invs"

definition "all_ta_clocks \<equiv> fold (\<union>) ta_clocks {}"

lemma fold_union:
  "fold (\<union>) S T =  \<Union> (set S) \<union> T"
  by (induction S arbitrary: T) auto

lemma fold_union':
  "fold (\<union>) S {} =  \<Union> (set S)"
  apply (subst fold_union)
  apply (subst Un_empty_right)
  ..

lemma int_clocks_set: "set (int_clocks_spec d) \<subseteq> set (map ActStart actions) \<union> set (map ActEnd actions)"
  unfolding int_clocks_spec_def by auto

lemma nta_clocks_alt: "set nta_clocks = set (map ActStart actions) \<union> set (map ActEnd actions)"
  unfolding nta_clocks_def Let_def timed_automaton_net_spec_def prod.case by simp


lemma all_ta_clocks_alt: "all_ta_clocks = 
(\<Union>trs\<in>set ta_trans. \<Union> ((set o trans_resets) ` set trs)) \<union> 
(\<Union>trs\<in>set ta_trans. \<Union> (((`) fst o collect_clock_pairs o trans_guards) ` set trs)) \<union> 
(\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
proof -
  have 1: "all_ta_clocks = (\<Union>trs\<in>set ta_trans. \<Union>(l, b, c, a, u, r, l')\<in>set trs. set r \<union> fst ` collect_clock_pairs c) \<union> 
    (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
  unfolding all_ta_clocks_def ta_clocks_def
  apply (subst fold_union')
  unfolding trans_to_clocks_def trans_clocks_def Let_def
  apply (subst fold_union')
  apply (subst set_map)+
  unfolding invs_to_clocks_def ta_invs_def Let_def
  apply (subst fold_union')
  apply (subst map_map)+
  unfolding comp_apply
  by simp
  show ?thesis
  proof (subst 1; rule equalityI; rule subsetI)
    fix x
    assume "x \<in> (\<Union>trs\<in>set ta_trans. \<Union>(l, b, c, a, u, r, l')\<in>set trs. set r \<union> fst ` collect_clock_pairs c)
       \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
    thus "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> ((set \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) snd ` set trs)) 
      \<union> (\<Union>trs\<in>set ta_trans. \<Union> (((`) fst \<circ> collect_clock_pairs \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd) snd ` set trs))
      \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
      by fastforce
  next
    fix x
    assume "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> ((set \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) snd ` set trs)) 
      \<union> (\<Union>trs\<in>set ta_trans. \<Union> (((`) fst \<circ> collect_clock_pairs \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd) snd ` set trs))
      \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
    hence "x \<in> (\<Union>trs\<in>set ta_trans. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x))))))) 
      \<union> (\<Union>trs\<in>set ta_trans. \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))
      \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" unfolding comp_apply .
    hence
      "(\<exists>tr \<in> set ta_trans. x \<in> (\<Union>x\<in>set tr. set (fst (snd (snd (snd (snd (snd x)))))))) \<or>
       (\<exists>tr \<in> set ta_trans. x \<in> (\<Union>x\<in>set tr. fst ` collect_clock_pairs (fst (snd (snd x))))) \<or>
       x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" by auto
    then consider 
      tr where "tr \<in> set ta_trans" "x \<in> (\<Union>x\<in>set tr. set (fst (snd (snd (snd (snd (snd x)))))))"
    | tr where "tr \<in> set ta_trans" "x \<in> (\<Union>x\<in>set tr. fst ` collect_clock_pairs (fst (snd (snd x))))" 
    | "x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" 
      apply -
      apply (elim disjE)
        apply blast
      apply metis
      by blast
    then consider
      tr where "tr \<in> set ta_trans" "x \<in> (\<Union>(l, b, c, a, u, r, l')\<in>set tr. set r)"
    | tr where "tr \<in> set ta_trans" "x \<in> (\<Union>(l, b, c, a, u, r, l')\<in>set tr. fst ` collect_clock_pairs c)" 
    | "x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" 
      apply cases
      by fastforce+
    hence "x \<in> (\<Union>tr\<in>set ta_trans.(\<Union>(l, b, c, a, u, r, l')\<in>set tr. set r))
        \<or> x \<in> (\<Union>tr\<in>set ta_trans.(\<Union>(l, b, c, a, u, r, l')\<in>set tr. fst ` collect_clock_pairs c))
        \<or> x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" 
      apply cases
      apply fast
       apply blast
      by blast
    thus "x \<in> (\<Union>trs\<in>set ta_trans. \<Union>(l, b, c, a, u, r, l')\<in>set trs. set r \<union> fst ` collect_clock_pairs c) \<union> 
          (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
      by blast
  qed
qed

lemma all_ta_clocks_correct: "all_ta_clocks \<subseteq> set nta_clocks"
proof -
  have "set nta_clocks = ActStart ` (set actions) \<union> ActEnd ` (set actions)"
    unfolding nta_clocks_def Let_def prod.case timed_automaton_net_spec_def by simp
  moreover
  have "all_ta_clocks \<subseteq> ActStart ` (set actions) \<union> ActEnd ` (set actions)"
  proof
    fix x
    assume "x \<in> all_ta_clocks"
    then consider "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> ((set o trans_resets) ` set trs))"
      | "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> (((`) fst o collect_clock_pairs o trans_guards) ` set trs))"
      | "x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" unfolding all_ta_clocks_alt comp_apply by blast
    thus "x \<in> ActStart ` (set actions) \<union> ActEnd ` (set actions)" 
    proof cases
      case 1
      then obtain auto_ts trans where
        at: "auto_ts \<in> set ta_trans"
        and t:"trans \<in> set auto_ts"
        and x: "x \<in> set (trans_resets trans)" by auto
      from at obtain auto where
        auto: "auto \<in> set actual_autos" 
        and at': "auto_ts = auto_trans auto" unfolding ta_trans_def by auto
      consider (act) act where
        "act \<in> set actions"
        "auto = (snd o snd) (action_to_automaton_spec act)"
      | (main) "auto = (snd o snd) main_auto_spec"
        using in_actual_autosE[OF auto] unfolding comp_apply by metis
      then show ?thesis
      proof cases
        case act
        have "trans \<in> set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act]" 
          using t[simplified at' act(2)] unfolding comp_apply action_to_automaton_spec_def Let_def prod.case snd_conv fst_conv .
        with x consider
          "x \<in> set (trans_resets (start_edge_spec act))"|
          "x \<in> set (trans_resets (edge_2_spec act))"|
          "x \<in> set (trans_resets (edge_3_spec act))"|
          "x \<in> set (trans_resets (end_edge_spec act))" unfolding comp_apply by fastforce
        thus ?thesis 
          apply cases
          subgoal unfolding start_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
          subgoal unfolding edge_2_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          subgoal unfolding edge_3_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
          unfolding end_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
      next
        case main
        have "trans \<in> set [main_auto_init_edge_spec, main_auto_goal_edge_spec]" 
          using t[simplified at' main] unfolding comp_apply main_auto_spec_def Let_def prod.case snd_conv fst_conv .
        with x consider
          "x \<in> set (trans_resets main_auto_init_edge_spec)"|
          "x \<in> set (trans_resets main_auto_goal_edge_spec)" unfolding comp_apply by auto
        thus ?thesis 
          apply cases
          subgoal unfolding main_auto_init_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          unfolding main_auto_goal_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
      qed
    next
      case 2
      then obtain auto_ts trans g where
        at: "auto_ts \<in> set ta_trans"
        and t: "trans \<in> set auto_ts"
        and g: "g \<in> set (trans_guards trans)"
        and x: "x = fst (constraint_pair g)" unfolding comp_apply collect_clock_pairs_def by blast
      from at obtain auto where
        auto: "auto \<in> set actual_autos" 
        and at': "auto_ts = auto_trans auto" unfolding ta_trans_def by auto
      consider (act) act where
        "act \<in> set actions"
        "auto = (snd o snd) (action_to_automaton_spec act)"
      | (main) "auto = (snd o snd) main_auto_spec"
        using in_actual_autosE[OF auto] unfolding comp_apply by metis
      then show ?thesis 
      proof cases
        case act
        have "trans \<in> set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act]" 
          using t[simplified at' act(2)] unfolding comp_apply action_to_automaton_spec_def Let_def prod.case snd_conv fst_conv .
        with x g consider
          "x \<in> fst ` constraint_pair ` set (trans_guards (start_edge_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (edge_2_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (edge_3_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (end_edge_spec act))" unfolding comp_apply by fastforce
        hence "\<exists>act' \<in> set actions. x = ActStart act' \<or> x = ActEnd act'" 
          apply cases
          subgoal unfolding start_edge_spec_def Let_def prod.case comp_apply fst_conv snd_conv int_clocks_spec_def set_map set_append by auto
          subgoal unfolding edge_2_spec_def Let_def prod.case comp_apply fst_conv snd_conv by auto
          subgoal unfolding edge_3_spec_def Let_def prod.case comp_apply fst_conv snd_conv int_clocks_spec_def set_map u_dur_spec_def l_dur_spec_def set_append 
            using act(1) 
            apply (cases "lower act"; cases "upper act")
            subgoal by fastforce
            subgoal for a by (cases a) fastforce+
            subgoal for a by (cases a) fastforce+
            subgoal for a b by (cases a; cases b) fastforce+
            done
          subgoal unfolding end_edge_spec_def Let_def prod.case comp_apply fst_conv snd_conv by auto
          done
        then show ?thesis by blast
      next
        case main
        have "trans \<in> set [main_auto_init_edge_spec, main_auto_goal_edge_spec]" 
          using t[simplified at' main] unfolding comp_apply main_auto_spec_def Let_def prod.case snd_conv fst_conv .
        with x g consider
          "x \<in> fst ` constraint_pair ` set (trans_guards main_auto_init_edge_spec)"|
          "x \<in> fst ` constraint_pair ` set (trans_guards main_auto_goal_edge_spec)" unfolding comp_apply by auto
        then show ?thesis apply cases
          subgoal unfolding main_auto_init_edge_spec_def Let_def comp_apply fst_conv snd_conv by auto
          unfolding main_auto_goal_edge_spec_def Let_def comp_apply fst_conv snd_conv by auto
      qed
    next
      case 3
      then obtain auto invars where
        auto: "auto \<in> set actual_autos"
        and invars: "invars \<in> set (snd (snd (snd auto)))"
        and x: "x \<in> inv_clocks invars" by auto
      consider (act) act where
        "act \<in> set actions"
        "auto = (snd o snd) (action_to_automaton_spec act)"
      | (main) "auto = (snd o snd) main_auto_spec"
        using in_actual_autosE[OF auto] unfolding comp_apply by metis
      then show ?thesis
        apply cases
         unfolding action_to_automaton_spec_def main_auto_spec_def Let_def comp_apply snd_conv using invars x by simp+
    qed
  qed
  ultimately
  show ?thesis by simp
qed 
subsection \<open>Variables\<close>

definition "nta_vars \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in vars"

definition "var_renum \<equiv> mk_renum (map fst nta_vars)"

subsubsection \<open>Actual Variables\<close>


definition "vars_of_update u \<equiv>
let 
  (v, e) = u
in insert v (vars_of_exp e)"

definition "trans_vars t \<equiv> 
let
  (l, c, g, a, u, r, l') = t
in vars_of_bexp c \<union> fold (\<union>) (map vars_of_update u) {}"

definition "trans_to_vars ts \<equiv>
let 
  trans_vars = map trans_vars ts
in fold (\<union>) trans_vars {}"

definition "actual_variables \<equiv> 
let                                  
  ts_vars = map trans_to_vars ta_trans
in fold (\<union>) ts_vars {}"

lemma update_vars_simps: 
  "vars_of_update (set_prop_ab n p) = {PropVar p}"
  "vars_of_update (inc_prop_ab n p) = {PropVar p}"
  "vars_of_update (set_prop_lock_ab n p) = {PropLock p}"
  "vars_of_update (inc_prop_lock_ab n p) = {PropLock p}"
  unfolding vars_of_update_def set_prop_ab_def inc_prop_ab_def set_prop_lock_ab_def inc_prop_lock_ab_def Let_def prod.case by simp+

lemma condition_vars_simps: 
  "vars_of_bexp (is_prop_ab n p) = {PropVar p}"
  "vars_of_bexp (is_prop_lock_ab n p) = {PropLock p}"
  unfolding is_prop_ab_def is_prop_lock_ab_def by simp+

lemma vars_of_bexp_all:
  "vars_of_bexp (bexp_and_all bs) = (\<Union>b \<in> set bs. vars_of_bexp b)"
  by (induction bs; simp)



lemma actual_variables_correct: "actual_variables \<subseteq> set (map fst nta_vars)"
proof
  fix x
  assume "x \<in> actual_variables"
  then obtain tr aut where
    aut: "aut \<in> set actual_autos"
    and tr: "tr \<in> set (auto_trans aut)"
    and x: "x \<in> trans_vars tr"
      unfolding actual_variables_def trans_to_vars_def Let_def
      fold_union' comp_apply ta_trans_def by auto 
  from in_actual_autosE[OF aut]
  consider 
    (act) act where "act \<in> set actions"
    "aut = (snd o snd) (action_to_automaton_spec act)"
  | (main) "aut = (snd o snd) main_auto_spec" by metis

  hence "x = ActsActive \<or> x = PlanningLock \<or> x \<in> {PropVar p|p. p \<in> set props} \<or> x \<in> {PropLock p|p. p \<in> set props}"
  proof cases
    case act
    with tr
    have "tr \<in> {start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act}" unfolding action_to_automaton_spec_def Let_def comp_apply snd_conv by auto
    with x consider
      "x \<in> trans_vars (start_edge_spec act)" |
      "x \<in> trans_vars (edge_2_spec act)" |
      "x \<in> trans_vars (edge_3_spec act)" |
      "x \<in> trans_vars (end_edge_spec act)" by auto
    note act_cases = this
    from fluent_domain
    have as: "set (pre (at_start act)) \<subseteq> set props"
         "set (adds (at_start act)) \<subseteq> set props"
         "set (dels (at_start act)) \<subseteq> set props"
         and oa: 
         "set (over_all act) \<subseteq> set props"
         and ae: 
         "set (pre (at_end act)) \<subseteq> set props"
         "set (adds (at_end act)) \<subseteq> set props"
         "set (dels (at_end act)) \<subseteq> set props"
      unfolding fluent_domain_def act_ref_fluents_def using act(1) by auto
    show ?thesis 
      apply (cases rule: act_cases)
      subgoal unfolding start_edge_spec_def  Let_def trans_vars_def prod.case fold_union'
        apply (subst (asm) vars_of_bexp_all)
        unfolding set_map set_append using update_vars_simps condition_vars_simps using as
        by auto
      subgoal unfolding edge_2_spec_def Let_def trans_vars_def prod.case fold_union'
        apply (subst (asm) vars_of_bexp_all)
        unfolding set_map set_append using update_vars_simps condition_vars_simps oa
        by auto
      subgoal unfolding edge_3_spec_def Let_def trans_vars_def prod.case fold_union' 
        by auto
      subgoal unfolding end_edge_spec_def  Let_def trans_vars_def prod.case fold_union'
        apply (subst (asm) vars_of_bexp_all)
        unfolding set_map set_append using update_vars_simps condition_vars_simps  using ae
        by auto
      done
  next
    case main
    with tr
    have "tr \<in> {main_auto_init_edge_spec, main_auto_goal_edge_spec}" unfolding main_auto_spec_def Let_def comp_apply snd_conv by auto
    with x consider
      "x \<in> trans_vars (main_auto_init_edge_spec)" |
      "x \<in> trans_vars (main_auto_goal_edge_spec)" by blast
    then show ?thesis 
      apply cases
        subgoal
          unfolding main_auto_init_edge_spec_def main_auto_goal_edge_spec_def Let_def trans_vars_def prod.case fold_union'
         vars_of_bexp_all list.set(2) set_map image_insert Union_insert
          apply (elim UnE)
          subgoal by simp
          subgoal unfolding vars_of_update_def by simp
          subgoal unfolding vars_of_update_def by simp
          subgoal using update_vars_simps condition_vars_simps init_props by auto
              done
        subgoal 
          unfolding main_auto_goal_edge_spec_def main_auto_goal_edge_spec_def Let_def trans_vars_def prod.case fold_union'
       vars_of_bexp_all list.set(2) set_map image_insert Union_insert
        apply (elim UnE)
        subgoal by simp
        subgoal using update_vars_simps condition_vars_simps goal_props by auto
        subgoal unfolding vars_of_update_def by simp
        subgoal by simp
        done
      done
  qed
  thus "x \<in> set (map fst nta_vars)" unfolding nta_vars_def timed_automaton_net_spec_def Let_def prod.case set_map list.set(2) set_append by blast
qed

subsection \<open>States\<close>       
subsubsection \<open>Returned states for simplicity\<close>
(* Explicitly returned states *)
definition "ta_states a \<equiv> case a of 
  (name, init, states, _) \<Rightarrow> states"

definition "individual_ta_states \<equiv> map ta_states ntas"

definition "all_ta_states = fold (@) individual_ta_states []"

lemma set_fold_append: "set (fold (@) xs ys) = \<Union>(set ` (set xs)) \<union> set ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "set (fold (@) (x#xs) ys) = set (fold (@) xs (x @ ys))" by simp
  also have "... =  \<Union> (set ` set xs) \<union> set (x @ ys)" using Cons.IH by simp
  also have "... = \<Union> (set ` set xs) \<union> set x \<union> set ys" by auto
  also have "... =  \<Union> (set ` (insert x (set xs)))\<union> set ys" by auto
  also have "... = \<Union> (set ` set (x # xs)) \<union> set ys" by auto
  finally show ?case by auto
qed

lemma individual_ta_states_subset_of_all:
  assumes "i < length individual_ta_states"
  shows "set (individual_ta_states ! i) \<subseteq> set all_ta_states"
proof -
  have "individual_ta_states ! i \<in> set individual_ta_states" using assms[THEN nth_mem_mset]
    unfolding in_multiset_in_set by blast
  thus ?thesis unfolding all_ta_states_def set_fold_append
    by blast
qed

lemma individual_ta_states_subset_of_all':
  assumes "nta \<in> set ntas"
  shows "set (ta_states nta) \<subseteq> set all_ta_states"
  using assms
  apply (subst all_ta_states_def)
  apply (subst set_fold_append)
  apply (subst individual_ta_states_def)
  by auto

subsubsection \<open>Actual states\<close>

definition trans_locs where
"trans_locs tr \<equiv>
  let
    (s, g, c, a, u, r, t) = tr
  in
    {s, t}"

definition trans_to_locs where
"trans_to_locs trs \<equiv> 
  let
    locs = map trans_locs trs
  in 
    fold (\<union>) locs {}"

definition "ta_locs \<equiv> map trans_to_locs ta_trans"

definition all_locs where
"all_locs \<equiv> fold (\<union>) ta_locs {}"


lemma individual_locs_correct:
  assumes an: "auto \<in> set ntas"
  shows "trans_to_locs (auto_trans (get_actual_auto auto)) \<subseteq> set (ta_states auto)"
proof
  fix x
  assume x: "x \<in> trans_to_locs (auto_trans (get_actual_auto auto))"
  have "\<exists>n act. auto = (n, action_to_automaton_spec act) \<or> auto = (n, main_auto_spec)"
    using an unfolding ntas_def timed_automaton_net_spec_def
    apply simp
    apply (drule set_zip_cart)
    by auto
  then 
  consider act n where "auto = (n, action_to_automaton_spec act)" | n where "auto = (n, main_auto_spec)" by blast 
  thus "x \<in> set (ta_states auto)"
  proof cases
    case 1
    then obtain init states comm urg trans invs where
      tr: "auto = (n, init, states, comm, urg, trans, invs)" unfolding action_to_automaton_spec_def by simp
    
    {with 1
      have "(snd o snd o snd) auto = (comm, urg, trans, invs)" by fastforce
      hence "auto_trans (get_actual_auto auto) = trans" by simp
      with x
      have x_in_tr: "x \<in> trans_to_locs trans" by simp
      moreover
      have 2: "trans = [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act]"
        using 1 tr unfolding action_to_automaton_spec_def Let_def by blast
      moreover
      have "trans_to_locs trans = {Off act, StartInstant act, Running act, EndInstant act}"
        apply (rule equalityI)
        unfolding 2 trans_to_locs_def  Let_def fold_union start_edge_spec_def edge_2_spec_def edge_3_spec_def end_edge_spec_def Let_def trans_locs_def
          by simp+
      ultimately
      have "x \<in> {Off act, StartInstant act, Running act, EndInstant act}" 
      using x tr by blast
    }
    moreover
    {
      have st: "ta_states auto = states" using tr unfolding ta_states_def by auto
      hence "ta_states auto = [Off act, StartInstant act, Running act, EndInstant act]"
        using tr unfolding ta_states_def 1 action_to_automaton_spec_def Let_def by simp
    }
    ultimately show ?thesis by simp
  next
    case 2
    then obtain init states comm urg trans invs where
      tr: "auto = (n, init, states, comm, urg, trans, invs)" unfolding main_auto_spec_def by simp
    {with 2
      have "get_actual_auto auto = (comm, urg, trans, invs)" by fastforce
      hence "auto_trans (get_actual_auto auto) = trans" by simp
      with x
      have x_in_tr: "x \<in> trans_to_locs trans" by simp
      moreover
      have 3: "trans = [main_auto_init_edge_spec, main_auto_goal_edge_spec]"
        using 2 tr unfolding main_auto_spec_def Let_def by blast
      moreover
      have "trans_to_locs trans = {InitialLocation, Planning, GoalLocation}"
        apply (rule equalityI)
        unfolding 3 trans_to_locs_def  Let_def fold_union 
          main_auto_init_edge_spec_def main_auto_goal_edge_spec_def Let_def trans_locs_def
          by simp+
      ultimately
      have "x \<in> {InitialLocation, Planning, GoalLocation}" 
      using x tr by blast
    }
    moreover
    {
      have st: "ta_states auto = states" using tr unfolding ta_states_def by auto
      hence "ta_states auto = [InitialLocation, Planning, GoalLocation]"
        using tr unfolding ta_states_def 2 main_auto_spec_def Let_def by simp
    }
    ultimately show ?thesis by auto
  qed
qed

(* Renumbering states *)
abbreviation "state_renum' \<equiv> mk_snd_ord_renum individual_ta_states"

(* The injective renumbering from every single state *)
definition "inj_state_renum i \<equiv> 
  let renum' = state_renum' i;
      states = individual_ta_states ! i;
      other_states = list_remove_all all_ta_states states;
      renum = extend_domain renum' other_states (length states - 1)
  in renum"

lemma list_remove_all_set:
  "set (list_remove_all xs ys) \<union> set ys = set xs \<union> set ys"
proof (rule equalityI; intro subsetI)
  fix x
  assume "x \<in> set (list_remove_all xs ys) \<union> set ys"
  thus "x \<in> set xs \<union> set ys" 
    apply (rule UnE)
    apply (subst (asm) in_multiset_in_set[symmetric])
     apply (subst (asm) list_remove_all_mset)
     apply (rule UnI1)
    using in_diffD apply fastforce
    by (rule UnI2)
next
  fix x
  assume "x \<in> set xs \<union> set ys" 
  then
  consider "x \<in> set xs - set ys" | "x \<in> set ys" by blast
  thus "x \<in> set (list_remove_all xs ys) \<union> set ys"
    apply (cases)
     apply (rule UnI1)
    apply (subst in_multiset_in_set[symmetric])
     apply (subst list_remove_all_mset)
     apply (metis DiffE count_greater_zero_iff count_mset_0_iff in_diff_count set_mset_mset)
    by blast
qed

lemma extend_domain_not_in_set:
  assumes "x \<notin> set es"
  shows "extend_domain f es n x = f x"
  using assms
  unfolding extend_domain_def
  by (auto split: prod.splits)


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
  hence IH': "\<And>n bs. fold ?f as (n, bs) =
    (n + length as, rev (zip as [n+1..<(n + length as + 1)]) @ bs)"
    by (auto split: prod.split)
  have "a \<in> set as'" using Cons by simp
  hence "fold ?f (a # as) (n, bs)
    = fold ?f as (n + 1, (a, n + 1) # bs)"
    by (auto split: prod.split)
  also have "... = (n + (length (a#as)), rev (zip as [(n + 2)..<(n + length (a#as) + 1)]) @ (a, n + 1) # bs)" 
    by (simp add: IH')
  also have "... = (n + (length (a#as)), (rev ((a, n + 1)#(zip as [(n + 1) + 1..<((n + 1)+ length (a#as))]))) @ bs)" 
    by simp
  also have "... = (n + (length (a#as)), (rev (zip (a#as) [(n + 1)..<(n + length (a#as) + 1)])) @ bs)"
    apply (subst zip_Cons_Cons[symmetric])
    apply (subst Suc_eq_plus1[where n = "n + 1", symmetric])
    apply (subst upt_conv_Cons[symmetric])
    by auto
  finally show ?case by blast
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
    hence 1: "n + last_index (e # es) x + 1 = n + 1" using False
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
    also have "... = n + 1" using False  
      apply (subst Let_def)
      apply (subst extend_domain_fold_lemma[where as' = "e#es" and as = es and n = "n + 1" and bs = "[(e, n + 1)]"])
       apply auto[1]
      apply (subst prod.case)
      apply (subst Let_def)
      apply (subst xe, subst (asm) xe)
      apply (subst map_of_distinct_lookup)
        apply (subst zip_rev[symmetric])
         apply (subst length_upt)
         apply simp
        apply (subst map_fst_zip)
         apply (subst length_rev)+
         apply (subst length_upt)
      by simp+
    finally
    show ?thesis using 1 by simp
  next
    case True 
    {fix f n
      have "n + last_index es x + 1 = extend_domain f es n x" using Cons True by auto
      also have "... = the (map_of (rev (zip es [n + 1..<(n + (length es) + 1)])) x)" 
        apply (subst extend_domain_def) 
        apply (subst extend_domain_fold_lemma)
         apply simp
        apply (subst Let_def)
        apply (subst prod.case)
        apply (subst Let_def)
        using True by auto
      finally have "the (map_of (rev (zip es [n + 1..<n + length es + 1])) x) = n + last_index es x + 1" by simp
    } note IH' = this

    have 1: "x \<in> dom (map_of (rev (zip es [n + 1 + 1..<n + 1 + length es + 1])))" 
      using True
      apply (subst zip_rev[symmetric])
       apply (subst length_upt)
       apply simp
      apply (subst dom_map_of_zip)
       apply (subst length_rev)+
       apply (subst length_upt)
      by simp+
      
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
       the (m' x))" using True by (auto split: prod.splits)
    also have "... = n + 1 + last_index es x + 1" apply (subst Let_def)
      apply (subst extend_domain_fold_lemma[where as' = "e#es" and as = es and n = "n + 1" and bs = "[(e, n + 1)]"])
       apply auto[1]
      apply (subst prod.case)
        apply (subst Let_def)
        apply (subst map_of_append)
        apply (subst map_add_dom_app_simps(1))
         apply (rule 1)
        find_theorems "map_of (?xs @ ?ys)"
        apply (subst IH')
        ..
      finally show ?thesis using True 
        apply (subst last_index_Cons)
        by simp
  qed
qed

find_theorems name: "last_index"

lemma extend_domain_inj_new:
  "inj_on (extend_domain f es (n::nat)) (set es)"
  apply (rule inj_onI)
  subgoal for x y
    using extend_domain_index[of x] extend_domain_index[of y]
    by simp
  done


lemma extend_domain_inj:
  assumes inj_on_f: "inj_on f (set d)"
      and f_ran: "\<forall>x \<in> set d. f x \<le> n"
      and n: "n = length d - 1"
    shows "inj_on (extend_domain f e n) (set d \<union> set e)"
  find_theorems "inj_on ?f (?s \<union> ?t)"
proof (subst inj_on_Un; intro conjI)
  show "inj_on (extend_domain f e n) (set e)" using extend_domain_inj_new by blast
  show "inj_on (extend_domain f e n) (set d)"
  proof (rule inj_onI)
    fix x y 
    assume x: "x \<in> set d" 
       and y: "y \<in> set d" 
       and e: "extend_domain f e n x = extend_domain f e n y"
    show "x = y"
    proof (cases "x \<in> set e"; cases "y \<in> set e") 
      assume a: "x \<notin> set e" "y \<notin> set e"
      hence "f x = f y" using extend_domain_not_in_set[of _ e f n] e by auto
      with x y
      show "x = y" using inj_on_f[simplified inj_on_def] by blast
    next
      assume a: "x \<notin> set e" "y \<in> set e"
      hence "extend_domain f e n x = f x" using extend_domain_not_in_set[of x e f n] by blast
      hence "extend_domain f e n x \<le> n" using f_ran x by auto
      moreover
      have "extend_domain f e n y = n + last_index e y + 1" using a extend_domain_index by auto
      ultimately 
      have "False" using e by auto
      thus ?thesis by simp
    next
      assume a: "x \<in> set e" "y \<notin> set e"
      hence "extend_domain f e n y = f y" using extend_domain_not_in_set by metis
      hence "extend_domain f e n y \<le> n" using f_ran y by auto
      moreover
      have "extend_domain f e n x = n + last_index e x + 1" using a extend_domain_index by auto
      ultimately 
      have "False" using e by auto
      thus ?thesis by simp
    next
      assume a: "x \<in> set e" "y \<in> set e"
      have "extend_domain f e n x = n + last_index e x + 1" using extend_domain_index a by auto
      moreover
      have "extend_domain f e n y = n + last_index e y + 1" using extend_domain_index a by auto
      ultimately
      have "last_index e x = last_index e y" using e by auto
      with a
      show "x = y" by auto
    qed
  qed
  
  show "extend_domain f e n ` (set d - set e) \<inter> extend_domain f e n ` (set e - set d) = {}"
  proof -
    { fix x y
      assume x: "x \<in> (set d - set e)"
         and y: "y \<in> (set e - set d)"
      have "extend_domain f e n x \<le> n" using f_ran extend_domain_not_in_set[of x e f n] x by auto
      moreover
      have "extend_domain f e n y = n + last_index e y + 1" using extend_domain_index y by fast
      ultimately
      have "extend_domain f e n x \<noteq> extend_domain f e n y" by force
    }
    thus ?thesis by blast
  qed
qed

lemma map_of_zip_fst:
  assumes "x \<in> set as"
     and "length as = length bs"
   shows "map_of (zip as bs) x = Some (bs ! (List_Index.index as x))"
  using assms
proof (induction as arbitrary: bs)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then obtain c cs where
    bs[simp]: "bs =c#cs" by (cases bs, auto)
  show ?case 
  proof (cases "x = a")
    case [simp]: True
    hence "List_Index.index (a # as) x = 0" by auto
    hence "bs ! (List_Index.index (a # as) x) = c" using nth_Cons_0 by simp
    moreover
    have "map_of (zip (a # as) bs) x = Some c" by auto
    ultimately
    show ?thesis by simp
  next
    case False
    show ?thesis 
      apply (subst bs)+
      apply (subst zip_Cons_Cons)
      apply (subst map_of_Cons_code(2))
      using False Cons
      by simp
  qed
qed

(* lemma map_of_zip_ran_distinct_inj:
  assumes dist: "distinct bs"
      and l: "length as = length bs"
    shows "inj_on (map_of (zip as bs)) (set as)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> set as"
     and y: "y \<in> set as"
     and mz: "map_of (zip as bs) x = map_of (zip as bs) y"
  
qed *)

    

lemma individual_ta_states_inj:
  assumes i_ran: "i < length individual_ta_states"
  shows "inj_on (state_renum' i) (set (individual_ta_states ! i))"
  using assms
  apply (subst mk_snd_ord_renum_def)
  apply (subst comp_apply)
  using mk_renum_inj 
  apply (subst nth_map)
  by blast+

lemma state_renum'_ran:
  assumes i: "i < length individual_ta_states"
      and x: "x \<in> set (individual_ta_states ! i)" 
    shows "state_renum' i x \<le> (length (individual_ta_states ! i) - 1)"
  unfolding mk_snd_ord_renum_def comp_apply mk_renum_def Let_def
  apply (subst nth_map[OF i])
  apply (subst map_of_zip_fst[OF x])
   apply simp
  apply (subst option.sel)
  using x[simplified index_less_size_conv[symmetric]]
  by simp

lemma state_renum'_inj: 
  assumes i_ran: "i < length individual_ta_states"
      and x: "x \<in> set all_ta_states"
      and y: "y \<in> set all_ta_states"
      and e: "inj_state_renum i x = inj_state_renum i y"
    shows "x = y"
proof -
  have a: "inj_state_renum i = 
  extend_domain (state_renum' i) (list_remove_all all_ta_states (individual_ta_states ! i)) (length (individual_ta_states ! i) - 1)" 
    apply (subst inj_state_renum_def)
    apply (subst Let_def)+
    by blast
  
  have 1: "inj_on (state_renum' i) (set (individual_ta_states ! i))" using individual_ta_states_inj[OF i_ran] .
  have 2: " \<forall>x\<in>set (individual_ta_states ! i). state_renum' i x \<le> length (individual_ta_states ! i) - 1"
    using state_renum'_ran i_ran by blast
  
  have "inj_on (extend_domain (state_renum' i)  (list_remove_all all_ta_states (individual_ta_states ! i)) (length (individual_ta_states ! i) - Suc 0)) (set (individual_ta_states ! i) \<union> set (list_remove_all all_ta_states (individual_ta_states ! i)))" 
    using extend_domain_inj[OF 1 2, simplified]
    by blast
  hence "inj_on (extend_domain (state_renum' i) (list_remove_all all_ta_states (individual_ta_states ! i)) (length (individual_ta_states ! i) - Suc 0))
   (set all_ta_states)" 
    apply -
    apply (subst (asm) Un_commute)
    apply (subst (asm) list_remove_all_set)
    apply (subst (asm) Un_commute)
    apply (subst (asm) individual_ta_states_subset_of_all[OF i_ran, simplified subset_Un_eq])
    by assumption
  hence "inj_on (inj_state_renum i) (set all_ta_states)" using a by auto
  thus ?thesis using e x y unfolding inj_on_def by blast
qed

abbreviation "nta_init \<equiv> fst o snd"

abbreviation "ntas_inits \<equiv> map nta_init ntas"


(* This needs to be lifted out of the locale *)
definition "broadcast \<equiv> []::String.literal list"

(* There is one action *)
definition "nta_actions \<equiv> [STR '''']::String.literal list"

find_consts name: "mk_renaming"

abbreviation "act_renum \<equiv> mk_renum (broadcast @ nta_actions)"

abbreviation "init_vars \<equiv> map (\<lambda>x. (fst x, 0::int)) nta_vars"

definition "form \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in formula"

lemma nta_length[simp]: "length individual_ta_states = length ntas"
  unfolding individual_ta_states_def
  using length_map .

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
    actual_autos
    form
proof
  show "\<forall>i<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars).
       \<forall>x\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars).
          \<forall>y\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars). 
            inj_state_renum i x = inj_state_renum i y \<longrightarrow> x = y"
  proof -
    { fix i x y
      assume i: "i<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
         and x: "x\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
         and y: "y\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
         and rn: "inj_state_renum i x = inj_state_renum i y"
      have "Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars) = length ntas"
        unfolding Prod_TA_Defs.n_ps_def actual_autos_def by simp
      hence 2: "p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)
          \<Longrightarrow> p < length ntas" for p unfolding Prod_TA_Defs.n_ps_def actual_autos_def by auto

      have "x \<in> set (all_ta_states)" if x: "x \<in> Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" for x
      proof - (* showing that an arbitrary x must be in the local set of locations *)
        { fix p (* the local equivalent set of transitions *)
          assume p: "p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)" 
          hence p1: "p < length actual_autos" unfolding Prod_TA_Defs.n_ps_def by auto
          hence p2: "p < length ntas" unfolding actual_autos_def by auto

          let ?f = "fst o snd o snd"
          have 1: "?f (Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) = 
              set (?f (get_actual_auto (ntas ! p)))" unfolding Prod_TA_Defs.N_def apply simp
            unfolding automaton_of_def
            apply (subst nth_map, rule p1)
            unfolding actual_autos_def comp_apply
            apply (subst nth_map, rule p2)
            by (auto split: prod.split)
          have "Simple_Network_Language.trans (Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p)
            = set (auto_trans (get_actual_auto (ntas ! p)))" 
            unfolding Simple_Network_Language.trans_def
            apply (subst 1[simplified comp_apply])
            unfolding Let_def comp_apply
            apply (cases "snd (snd (snd (ntas ! p)))" rule: prod_cases4)
            by auto
        } note 1 = this
    
        have "x \<in> \<Union> {fst ` set (auto_trans (get_actual_auto (ntas ! p))) |p.
              p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<union>
           \<Union> {(snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` set (auto_trans (get_actual_auto (ntas ! p))) |p.
               p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}" 
          using x 1 
          unfolding Prod_TA_Defs.loc_set_def by blast
        hence "x \<in> \<Union> {fst ` set (auto_trans (get_actual_auto (ntas ! p))) |p.
              p < length ntas} \<union>
           \<Union> {(snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` set (auto_trans (get_actual_auto (ntas ! p))) |p.
               p < length ntas}"
          using 2  by blast
  
        hence "\<exists>nta \<in> set ntas.
            x \<in> \<Union> {fst ` set (auto_trans (get_actual_auto nta))} \<union>
            \<Union> {(snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` set (auto_trans (get_actual_auto nta))}"
          by auto
        hence "\<exists>nta \<in> set ntas.
            x \<in> set (map fst (auto_trans (get_actual_auto nta))) \<union>
            set (map (snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd) (auto_trans (get_actual_auto nta)))" by simp
        hence "\<exists>nta \<in> set ntas. x \<in> \<Union> (set (map trans_locs (auto_trans (get_actual_auto nta))))" 
          unfolding trans_locs_def Let_def comp_apply 
          apply -
          apply (erule bexE)
          subgoal for nta
            apply (rule bexI[of _ nta])
             apply (subst (asm) Un_iff)
             apply (erule disjE)
            by fastforce+
          done
        with trans_to_locs_def
        have "\<exists>nta \<in> set ntas. x \<in> (trans_to_locs (auto_trans (get_actual_auto nta)))" 
          unfolding trans_to_locs_def fold_union Let_def by blast
        then obtain nta where
          nta: "nta \<in> set ntas"
          "x \<in> (trans_to_locs (auto_trans (get_actual_auto nta)))" by blast
        with individual_locs_correct
        have "x \<in> set (ta_states nta)" by blast
        with nta
        show "x \<in> set (all_ta_states)" using individual_ta_states_subset_of_all' by blast
      qed

      with x y
      have x: "x \<in> set all_ta_states" 
       and y: "y \<in> set all_ta_states" by blast+
      with i 2
      have "i < length individual_ta_states" unfolding individual_ta_states_def by simp
      with state_renum'_inj x y rn
      have "x = y" by blast
    }
    thus ?thesis by blast
  qed
  show "inj_on clock_renum (insert urge_clock (Simple_Network_Impl.clk_set' actual_autos))"
  proof -
    have 1: "(\<Union>A\<in>set actual_autos. \<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r) 
      = (\<Union>trs\<in>set ta_trans. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))"
      unfolding ta_trans_def comp_apply set_map
    proof (rule equalityI; rule subsetI)
      fix x
      assume "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r)"
      then obtain A where
       A: "A \<in> set actual_autos"
        "x \<in> (\<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r)" by blast
      then obtain r where
        "\<exists>a b c d e f. (a, b, c, d, e, r, f) \<in> set (fst (snd (snd A)))" 
        "x \<in> set r" by blast
      hence "\<exists>tr. tr \<in> set (fst (snd (snd A))) \<and> x \<in> set (fst (snd (snd (snd (snd (snd tr))))))" by fastforce
      with A(1)
      show "x \<in> (\<Union>trs\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))" by blast
    next
      fix x
      assume "x \<in> (\<Union>trs\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))"
      then obtain trs where
        "trs \<in> (fst o snd o snd) ` set actual_autos"
        "x \<in> (\<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))" by auto
      then obtain A tr where
        Atr: "A \<in> set actual_autos"
        "trs = fst (snd (snd A))"
        "tr \<in> set trs"
        "x \<in> set (fst (snd (snd (snd (snd (snd tr))))))" by auto
      then obtain r where
        "\<exists>a b c d e f. (a, b, c, d, e, r, f) = tr" apply (cases tr) by auto
      with Atr
      show "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r)" by fastforce
    qed
    have 2: "B = C \<Longrightarrow> A \<union> B = A \<union> C" for A B C by blast

    have invr_clocks: "(\<Union>A\<in>set actual_autos. \<Union>g\<in>set (snd (snd (snd A))). fst ` (collect_clock_pairs (snd g))) = 
      (\<Union>auto\<in>set actual_autos. \<Union>i\<in>set (snd (snd (snd auto))). fst ` collect_clock_pairs (snd i))" by simp

    have guard_clocks: " (\<Union>A\<in>set actual_autos. \<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g)) 
        = (\<Union>trs\<in>set (map (\<lambda>x. fst (snd (snd x))) actual_autos). \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))"
    proof (rule equalityI; rule subsetI)
      fix x 
      assume "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g))"
      then obtain A where
        A: "A \<in> set actual_autos"
        "x \<in> (\<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g))" by blast
      then obtain trans where
        "trans \<in> set (fst (snd (snd A)))"
        "x \<in> fst ` collect_clock_pairs (fst (snd (snd trans)))"
        apply -
        apply (subst (asm) Union_iff)
        apply (erule bexE)
        subgoal for trs
          apply (erule imageE)
          subgoal for trs'
            apply (induction trs')
            subgoal for l b g
              apply (subst (asm) prod.case)+
              by simp
            done
          done
        done
      with A
      show "x \<in> (\<Union>trs\<in>set (map (\<lambda>x. fst (snd (snd x))) actual_autos). \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))" by auto
    next
      fix x
      assume "x \<in> (\<Union>trs\<in>set (map (\<lambda>x. fst (snd (snd x))) actual_autos). \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))" 
      then obtain A tr where
        A: "A \<in> set actual_autos"
        "tr \<in> set (fst (snd (snd A)))"
        "x \<in> fst ` collect_clock_pairs (fst (snd (snd tr)))" 
        apply -
        apply (subst (asm) Union_iff)
        apply (erule bexE)
        subgoal for tr
          apply (subst (asm) set_map)
          apply (erule imageE)
          subgoal for trs
            by blast
          done
        done
      then obtain l c g a b d e where
        g: "tr = (l, c, g, a, b, d, e)" apply (cases tr) by auto
      show "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g))" 
        using A unfolding g
        apply -
        apply (subst (asm) snd_conv | subst (asm) fst_conv)+
        by blast
    qed

    have clk_set'_alt: "insert urge_clock (Simple_Network_Impl.clk_set' actual_autos) = insert urge_clock all_ta_clocks"
      apply (rule arg_cong[where f = "insert urge_clock"])
      apply (subst Simple_Network_Impl.clk_set'_def)
      apply (subst all_ta_clocks_alt)
      apply (subst 1)
      unfolding comp_apply
      apply (subst Un_commute)
      apply (subst Un_assoc)
      apply (rule 2)
      unfolding Simple_Network_Impl.clkp_set'_def
      unfolding ta_trans_def comp_apply inv_clocks_def
      apply (subst (2) Un_commute) 
      apply (subst invr_clocks[symmetric])
      apply (subst guard_clocks[symmetric])
      by blast
      
        
    have ins: "insert urge_clock all_ta_clocks \<subseteq> set (urge_clock # nta_clocks)"
      using all_ta_clocks_correct by auto

    show "inj_on clock_renum (insert urge_clock (Simple_Network_Impl.clk_set' actual_autos))"
      apply (subst clk_set'_alt)
      apply (rule inj_on_subset[OF _ ins])
      unfolding clock_renum_def 
      using mk_renum_inj by blast
  qed
  show "inj_on var_renum (Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars))" 
  proof -                                                                                          
    have "Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars) = actual_variables"
    proof (rule equalityI; rule subsetI)
      fix x 
      assume "x \<in> Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
      hence "x \<in> (\<Union>S\<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
           \<Union> (vars_of_bexp ` S)) \<union>
       (\<Union>S\<in>{(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) `
             Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |
             p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
           \<Union>f\<in>S. \<Union>(x, e)\<in>set f. {x} \<union> vars_of_exp e)"  unfolding Prod_TA_Defs.var_set_def .
      then consider "x \<in> (\<Union>S\<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
           \<Union> (vars_of_bexp ` S))" |
       "x \<in> (\<Union>S\<in>{(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) `
             Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |
             p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
           \<Union>f\<in>S. \<Union>(x, e)\<in>set f. {x} \<union> vars_of_exp e)" by blast
      then have
        "(\<exists>auto trans cond. x \<in> vars_of_bexp cond 
        \<and> cond = fst (snd trans)
        \<and> trans \<in> Simple_Network_Language.trans auto
        \<and> auto \<in> set (map automaton_of actual_autos)) \<or> 
      (\<exists>auto trans v e. x \<in> insert v (vars_of_exp e) 
        \<and> (v, e) \<in> set ((fst o snd o snd o snd o snd) trans) 
        \<and> trans \<in> Simple_Network_Language.trans auto 
        \<and> auto \<in> set (map automaton_of actual_autos))" unfolding Prod_TA_Defs.n_ps_def Prod_TA_Defs.N_def
        apply cases
        unfolding comp_apply
         apply (rule disjI1)
        unfolding fst_conv snd_conv
         apply (subst (asm) Union_iff)
         apply (erule bexE)
        subgoal for cvs
          apply (erule imageE)
          subgoal for conds
            apply (erule CollectE)
            apply (erule exE)
            subgoal for n
              apply (erule conjE)
              apply (drule nth_mem)
              by blast
            done
          done
        apply (rule disjI2)
        apply (subst (asm) Union_iff)
        apply (erule bexE)
        subgoal for upd_vs
          apply (erule imageE)
          subgoal for upds
            apply (erule CollectE)
            apply (erule exE)
            subgoal for n
              apply (erule conjE)
              apply (drule nth_mem)
              by blast
            done
          done
        done
      then consider 
        (conds) auto trans cond where
        "x \<in> vars_of_bexp cond"
        "cond = fst (snd trans)"
        "trans \<in> Simple_Network_Language.trans auto"
        "auto \<in> set (map automaton_of actual_autos)" |
        (upds) auto trans v e where
        "x \<in> insert v (vars_of_exp e)"
        "(v, e) \<in> set ((fst o snd o snd o snd o snd) trans)"
        "trans \<in> Simple_Network_Language.trans auto"
        "auto \<in> set (map automaton_of actual_autos)"
        by blast
      thus "x \<in> actual_variables" 
      proof cases
        case conds
        hence "x \<in> (\<Union>ts\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>(l, c, g, a, u, r, l')\<in>set ts. vars_of_bexp c)"
          unfolding Simple_Network_Language.trans_def  Let_def fold_union' comp_apply set_map 
          automaton_of_def 
          apply -
          apply (erule imageE)
          subgoal for a'
            apply (induction a')
            subgoal for _ _ tr
              apply (subst (asm) prod.case)+
              apply simp
              apply (rule bexI)
               apply (rule bexI[of _ trans])
              by auto
            done
          done
        then show ?thesis unfolding actual_variables_def ta_trans_def trans_vars_def trans_to_vars_def Let_def comp_apply fold_union' set_map by blast
      next
        case upds
        hence "x \<in> (\<Union>ts\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>(l, c, g, a, u, r, l')\<in>set ts. \<Union> (vars_of_update ` set u))"
          unfolding Simple_Network_Language.trans_def comp_apply vars_of_update_def Let_def set_map
          apply -
          apply (erule imageE)
          subgoal for a'
            apply (induction a')
            subgoal for a b tr d
              apply simp
              unfolding automaton_of_def prod.case
              snd_conv fst_conv
              apply (rule bexI[of _ "(a, b, tr, d)"])
               apply (rule bexI[of _ trans])
                apply (induction trans)
              subgoal unfolding prod.case
                by auto
               apply simp
              by simp
            done
          done
          then show ?thesis unfolding actual_variables_def ta_trans_def trans_vars_def trans_to_vars_def Let_def comp_apply fold_union' set_map by blast
      qed
    next
      fix x
      assume "x \<in> actual_variables"
      then obtain tran aut l c g a u r l' where
        trans: "aut \<in> set actual_autos"
            "tran \<in> (fst o snd o snd) aut"        
            "tran = (l, c, g, a, u, r, l')"
        and "x \<in> vars_of_bexp c \<or> x \<in> \<Union> (vars_of_update ` set u)"
        unfolding actual_variables_def Let_def fold_union' set_map trans_to_vars_def trans_vars_def ta_trans_def comp_apply by blast
      then consider "x \<in> vars_of_bexp c" | "x \<in> \<Union> (vars_of_update ` set u)" by blast
      thus "x \<in> Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" 
      proof cases
        case 1
        have s: "{(Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} = 
            automaton_of ` (set actual_autos)"
          unfolding Simple_Network_Language.Prod_TA_Defs.N_def Simple_Network_Language.Prod_TA_Defs.n_ps_def
          apply (subst set_map[symmetric])
          apply (subst (3) set_conv_nth)
          unfolding fst_conv snd_conv by blast
        from trans(1,2)
        have "\<exists>com urg invr. aut = (com, urg, trans, invr)" apply (auto split: prod.split) try
        obtain com urg invr where
        "aut = (com, urg, trans, invr)" apply (auto split: prod.split simp: trans(1, 2)) 
        from trans
        have "Simple_Network_Language.trans (automaton_of aut) = set trans" unfolding Simple_Network_Language.trans_def automaton_of_def apply (cases aut) 
          subgoal 
        have "\<exists>c tr trs aut. c = fst (snd tr) \<and> tr \<in> trs \<and> trs = Simple_Network_Language.trans aut \<and> aut \<in> automaton_of ` set actual_autos \<and> x \<in> vars_of_bexp c"
          using trans 1 
        hence "\<exists>c tr trs aut. (c = fst (snd tr)) \<and> tr \<in> trs \<and> trs = Simple_Network_Language.trans aut \<and> aut \<in> {Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p |p.
              p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> vars_of_bexp c" unfolding s by blast
        hence "\<exists>c tr trs. (c = fst (snd tr)) \<and> tr \<in> trs \<and> trs \<in> {Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
              p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> vars_of_bexp c" by blast
        hence "\<exists>c trans. (c \<in> (fst o snd) ` trans) \<and> trans \<in> {Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
              p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> vars_of_bexp c" unfolding comp_apply by fastforce
        hence "\<exists>c. c \<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
              p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> \<Union>(vars_of_bexp ` c)" by auto
        hence "x \<in> (\<Union>S\<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
              p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
             \<Union> (vars_of_bexp ` S))" by blast
        then show ?thesis unfolding Prod_TA_Defs.var_set_def by blast
      next
        case 2
        then show ?thesis sorry
      qed
    qed
    moreover
    have "inj_on var_renum (set (map fst nta_vars))" unfolding var_renum_def using mk_renum_inj by blast
    ultimately
    show ?thesis using inj_on_subset actual_variables_correct by blast
  qed
  show "inj_on (mk_renum (broadcast @ nta_actions)) (Prod_TA_Defs.act_set (set broadcast, map automaton_of actual_autos, map_of nta_vars))" sorry
  show "infinite UNIV" sorry
  show "infinite UNIV" sorry
  show "infinite UNIV" sorry
  show "infinite UNIV" sorry
  show "fst ` set nta_vars = Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" sorry
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
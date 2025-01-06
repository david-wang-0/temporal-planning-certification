theory ExecutableCompilation
  imports Compilation
begin
datatype RefinedLocation =
  Init 
  | Goal
  | Main
  | PropDecoding nat 
  | ExecDecoding nat
  | DecAtStart nat 
  | DecAtEnd nat
  | ExecAtStart nat
  | ExecAtEnd nat

datatype RefinedClock =
  Delta
  | Stop
  | PropClock nat
  | Running nat
  | StartDur nat
  | EndDur   nat
  | SchedStartSnap nat
  | SchedEndSnap   nat

text \<open>Treat a list as an array and find the indexes.\<close>
fun double_filter::"(nat \<Rightarrow> 'x \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'x list \<Rightarrow> (nat \<times> 'x) list \<Rightarrow> (nat \<times> 'x) list" where
"double_filter P n [] ns = ns" |
"double_filter P n (pr#ps) ns = (if P n pr then double_filter P (Suc n) ps ((n,pr)#ns) else double_filter P (Suc n) ps ns)"

abbreviation numbers_gather::"('x \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'x list \<Rightarrow> nat list" where
"numbers_gather P n pr \<equiv> map fst (double_filter (\<lambda>x y. P y) n pr [])"

fun numbers_find::"('x \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'x list \<Rightarrow> nat" where
"numbers_find P n [] = 0" |
"numbers_find P n (pr#ps) = (if P pr then n else numbers_find P (Suc n) ps)"

fun refined_AND_ALL::"(RefinedClock, 'time::time) dconstraint list \<Rightarrow> (RefinedClock, 'time) dconstraint" where
"refined_AND_ALL [] = GE Stop 0" |
"refined_AND_ALL (c#cs) = AND c (refined_AND_ALL cs)"

context ta_temp_planning
begin 
text \<open>Refined numbering for propositions\<close>
definition "action_list' \<equiv> sorted_list_of_set actions"
definition "prop_list' \<equiv> sorted_list_of_set props"

definition "M' \<equiv> length action_list'"
definition "N' \<equiv> length prop_list'"

text \<open>Gets the numbers of every numbered propositional clock\<close>
definition "refined_prop_numbers S = numbers_gather (\<lambda>p. p \<in> S) 0 prop_list'"
definition "refined_act_numbers S = numbers_gather (\<lambda>a. a \<in> S) 0 action_list'"

text \<open>Indexing\<close>
definition "refined_act n = (!) action_list' n"

text \<open>Preventing time from passing in any location other than the main location.\<close>
fun refined_invs::"(RefinedClock, 'time, RefinedLocation) invassn" where
  "refined_invs Main  = GE Stop 0"
| "refined_invs _     = EQ Stop 0"

text \<open>The transition from the initial location \<open>l\<^sub>I\<close> to the main location \<open>l\<^sub>\<epsilon>\<close>\<close>

definition refined_init_asmt::"(RefinedClock, 'time) clkassn list" where
"refined_init_asmt \<equiv> map (\<lambda>x. (PropClock x, 1)) (refined_prop_numbers init)"

definition refined_initial_transition::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_initial_transition \<equiv> (Init, GE Stop 0, Unit, refined_init_asmt, Main)"

text \<open>The transition from the main location \<open>l\<^sub>\<epsilon>\<close> to the \<open>0\<^sup>t\<^sup>h\<close> location of the location decoding path \<open>s\<^sub>0\<close>.\<close>
definition refined_main_to_decoding::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_main_to_decoding \<equiv> (Main, GE Stop 0, Unit, [(Stop, 0)], PropDecoding 0)"

subsubsection \<open>State decoding\<close>

fun collect_nats::"nat \<Rightarrow> nat set \<Rightarrow> nat set" where
"collect_nats 0 S = S" |
"collect_nats (Suc n) S = insert n (collect_nats n S)"

definition "refined_all_props = collect_nats N' {}"
definition "refined_all_acts = collect_nats M' {}"

text \<open>The transitions between the decoding locations for the propositional clocks \<open>cp\<^sub>i\<close>\<close>
definition refined_prop_decoding::"(alpha, RefinedClock, 'time, RefinedLocation) transition set" where
"refined_prop_decoding \<equiv> ((\<lambda>n. (PropDecoding n, DEQ (PropClock n) Delta 1, Unit, [(PropClock n, 1)], PropDecoding (Suc n))) ` refined_all_props)
  \<union> ((\<lambda>n. (PropDecoding n, DEQ (PropClock n) Delta 0, Unit, [(PropClock n, 0)], PropDecoding (Suc n))) ` refined_all_props)"

text \<open>A transition from the decoding locations for propositional clocks to the decoding locations for
the execution clocks\<close>
definition refined_prop_decoding_to_exec_decoding::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_prop_decoding_to_exec_decoding \<equiv> (PropDecoding N', GE Stop 0, Unit, [], ExecDecoding 0)"

text \<open>The transitions between the decoding locations for the execution clocks \<open>cr\<^sub>a\<close>\<close>
definition refined_exec_decoding::"(alpha, RefinedClock, 'time, RefinedLocation) transition set" where
"refined_exec_decoding \<equiv> ((\<lambda>m. (ExecDecoding m, DEQ (Running m) Delta 1, Unit, [(Running m, 1)], ExecDecoding (Suc m))) ` refined_all_acts)
  \<union> ((\<lambda>m. (ExecDecoding m, DEQ (Running m) Delta 0, Unit, [(Running m, 0)], ExecDecoding (Suc m))) ` refined_all_acts)"

text \<open>The transition from the execution decoding locations to the decision-making locations\<close>
definition refined_exec_decoding_to_decision_making::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_exec_decoding_to_decision_making \<equiv> (ExecDecoding M', GE Stop 0, Unit, [], DecAtStart 0)"

subsubsection \<open>Decision-making\<close>


text \<open>Interfering snap-actions\<close>

definition "start_snap_list \<equiv> map at_start action_list'"
definition "end_snap_list \<equiv> map at_end action_list'"

text \<open>Every start snap action that interferes with the given start snap-action and has been
treated in the current execution cycle\<close>
definition "s_snap_s_int sn \<equiv> (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 start_snap_list;
    P = (\<lambda>n' sn'. n' < n \<and> msa sn sn')
  in
    double_filter P 0 start_snap_list []
)"

text \<open>start and end\<close>
definition "s_snap_e_int sn \<equiv> (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 start_snap_list;
    P = (\<lambda>n' sn'. n' \<le> n \<and> msa sn sn')
  in
    double_filter P 0 end_snap_list []
)"

text \<open>end and start\<close>
definition "e_snap_s_int sn \<equiv> (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 end_snap_list;
    P = (\<lambda>n' sn'. n' \<le> n \<and> msa sn sn')
  in
    double_filter P 0 start_snap_list []
)"

text \<open>end and end\<close>
definition "e_snap_e_int sn \<equiv> (
  let 
    n = numbers_find (\<lambda>x. x = sn) 0 end_snap_list;
    P = (\<lambda>n' sn'. n' < n \<and> msa sn sn')
  in
    double_filter P 0 end_snap_list []
)"

text \<open>Constraints\<close>

definition refined_start_start_consts::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_start_start_consts a = map (\<lambda>b. GE (StartDur (fst  b)) \<epsilon>) (s_snap_s_int a)"

definition refined_start_end_consts::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_start_end_consts a = map (\<lambda>b. GE (EndDur (fst  b)) \<epsilon>) (s_snap_e_int a)"

definition refined_end_start_consts::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_end_start_consts a = map (\<lambda>b. GE (StartDur (fst  b)) \<epsilon>) (e_snap_s_int a)"

definition refined_end_end_consts::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_end_end_consts a = map (\<lambda>b. GE (EndDur (fst  b)) \<epsilon>) (e_snap_e_int a)"
text \<open>The constraints are incorrectly implemented, but they should be okay.\<close>


definition refined_start_constraints::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_start_constraints a = (refined_start_start_consts a @ refined_start_end_consts a)"

definition refined_end_constraints::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_end_constraints a =  (refined_end_start_consts a @ refined_end_end_consts a)"

text \<open>The clock constraints for the precondition\<close>
definition refined_pre_clocks::"'snap_action \<Rightarrow> RefinedClock list" where
"refined_pre_clocks a \<equiv> map PropClock (refined_prop_numbers (pre a))"

definition refined_pre_constraints::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_pre_constraints a \<equiv>  (map (\<lambda>c. EQ c 1) (refined_pre_clocks a))"

text \<open>The guard constraints\<close>
definition refined_start_guard::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_start_guard a \<equiv> (refined_start_constraints a) @ (refined_pre_constraints a)"

definition refined_end_guard::"'snap_action \<Rightarrow> (RefinedClock, 'time) dconstraint list" where
"refined_end_guard a \<equiv> (refined_end_constraints a) @ (refined_pre_constraints a)"

text \<open>Another layer of guard constraints\<close>
definition refined_guard_at_start::"nat \<Rightarrow> (RefinedClock, 'time::time) dconstraint" where
"refined_guard_at_start n \<equiv> refined_AND_ALL ((EQ (Running n) 0)#(refined_start_guard (at_start (refined_act n))))"

definition refined_clock_duration_bounds::"nat \<Rightarrow> (RefinedClock, 'time::time) dconstraint" where
"refined_clock_duration_bounds n \<equiv> 
  let a = refined_act n;
    l = case (lower a) of 
    Some (lower_bound.GT t) \<Rightarrow> GT (StartDur n) t
  | Some (lower_bound.GE t) \<Rightarrow> GE (StartDur n) t
  | None \<Rightarrow> GE Stop 0;
  u = case (upper a) of 
    Some (upper_bound.LT t) \<Rightarrow> LT (StartDur n) t
  | Some (upper_bound.LE t) \<Rightarrow> LE (StartDur n) t
  | None \<Rightarrow> GE Stop 0
  in (AND l u)"

definition refined_guard_at_end::"nat \<Rightarrow> (RefinedClock, 'time::time) dconstraint" where
"refined_guard_at_end n \<equiv> refined_AND_ALL ((EQ (Running n) 1)#refined_clock_duration_bounds n#(refined_end_guard (at_end (refined_act n))))"

definition refined_decision_making::"(alpha, RefinedClock, 'time, RefinedLocation) transition set" where
"refined_decision_making \<equiv> 
  ((\<lambda>m. (DecAtStart m, refined_guard_at_start m, Unit, [(SchedStartSnap m, 1)], DecAtEnd m)) ` refined_all_acts)
  \<union> ((\<lambda>m. (DecAtStart m, GE Stop 0, Unit, [(SchedStartSnap m, 0)], DecAtEnd m)) ` refined_all_acts)
  \<union> ((\<lambda>m. (DecAtEnd m, refined_guard_at_end m, Unit, [(SchedEndSnap m, 1)], DecAtStart (Suc m))) ` refined_all_acts)
  \<union> ((\<lambda>m. (DecAtEnd m, GE Stop 0, Unit, [(SchedEndSnap m, 0)], DecAtStart (Suc m))) ` refined_all_acts)"

definition refined_dm_to_exec::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_dm_to_exec \<equiv> (DecAtStart M', GE Stop 0, Unit, [], ExecAtStart 0)"

subsubsection \<open>Execution\<close>

definition refined_add_effects::"'snap_action \<Rightarrow> (RefinedClock, 'time) clkassn list" where
"refined_add_effects s \<equiv> map (\<lambda>p. (PropClock p, 1)) (refined_prop_numbers (adds s))"

definition refined_del_effects::"'snap_action  \<Rightarrow> (RefinedClock, 'time) clkassn list" where
"refined_del_effects s \<equiv> 
  let P = (\<lambda>p. p \<in> dels s \<and> p \<notin> adds s)
  in map (\<lambda>p. (PropClock p, 0)) (numbers_gather P 0 prop_list')"

definition refined_effects::"'snap_action \<Rightarrow> (RefinedClock, 'time) clkassn list" where
"refined_effects s \<equiv> refined_del_effects s @ refined_add_effects s"

definition refined_at_start_effects::"nat \<Rightarrow> (RefinedClock, 'time) clkassn list" where
"refined_at_start_effects n \<equiv> (Running n, 1) # (StartDur n, 0) # refined_effects (at_start (act n))"

definition refined_at_end_effects::"nat \<Rightarrow> (RefinedClock, 'time) clkassn list" where
"refined_at_end_effects n \<equiv> (Running n, 0) # (EndDur n, 0) # refined_effects (at_end (act n))"

definition refined_execution::"(alpha, RefinedClock, 'time, RefinedLocation) transition set" where
"refined_execution \<equiv> 
  ((\<lambda>m. (ExecAtStart m, EQ (SchedStartSnap m) 1, Unit, refined_at_start_effects m, ExecAtEnd m)) ` refined_all_acts)
  \<union> ((\<lambda>m. (ExecAtStart m, EQ (SchedStartSnap m) 0, Unit, [], ExecAtEnd m)) ` refined_all_acts)
  \<union> ((\<lambda>m. (ExecAtEnd m, EQ (SchedEndSnap m) 1, Unit, refined_at_end_effects m, ExecAtStart (Suc m))) ` refined_all_acts)
  \<union> ((\<lambda>m. (ExecAtEnd m, EQ (SchedEndSnap m) 0, Unit, [], ExecAtStart (Suc m))) ` refined_all_acts)"

subsubsection \<open>Over-all conditions\<close>
definition "refined_action_number_list \<equiv> numbers_gather (\<lambda>x. True) 0 action_list'"

definition refined_over_all_clocks::"'action \<Rightarrow> RefinedClock list" where
"refined_over_all_clocks a \<equiv> map PropClock (refined_prop_numbers (over_all a))"

definition refined_action_over_all::"nat \<Rightarrow> (RefinedClock, 'time) dconstraint" where
"refined_action_over_all n \<equiv> refined_AND_ALL (map (\<lambda>c. DLE (Running n) c 0) (refined_over_all_clocks (refined_act n)))"

definition refined_over_all_conds::"(RefinedClock, 'time) dconstraint" where
"refined_over_all_conds \<equiv> refined_AND_ALL (map refined_action_over_all refined_action_number_list)"

definition refined_exec_to_main::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_exec_to_main \<equiv> (ExecAtStart M', refined_over_all_conds, Unit, [(Delta, 0)], Main)"

subsubsection \<open>The goal\<close>
definition refined_none_running::"(RefinedClock, 'time) dconstraint" where
"refined_none_running \<equiv> refined_AND_ALL (map (\<lambda>a. EQ (Running a) 0) refined_action_number_list)"

definition "refined_goal_props \<equiv> refined_prop_numbers goal"

definition refined_goal_satisfied::"(RefinedClock, 'time) dconstraint" where
"refined_goal_satisfied \<equiv> refined_AND_ALL (map (\<lambda>p. EQ (PropClock p) 1) refined_goal_props)"

definition refined_goal_constraint::"(RefinedClock, 'time) dconstraint" where
"refined_goal_constraint \<equiv> AND refined_none_running refined_goal_satisfied"

definition refined_goal_trans::"(alpha, RefinedClock, 'time, RefinedLocation) transition" where
"refined_goal_trans \<equiv> (ExecDecoding M', refined_goal_constraint, Unit, [], Goal)"

subsubsection \<open>The automaton\<close>
definition refined_prob_automaton::"(alpha, RefinedClock, 'time, RefinedLocation) ta" ("\<T>") where
"refined_prob_automaton \<equiv> ({refined_initial_transition} \<union> {refined_main_to_decoding} \<union> refined_prop_decoding 
  \<union> {refined_prop_decoding_to_exec_decoding} \<union> refined_exec_decoding \<union> {refined_exec_decoding_to_decision_making}
  \<union> refined_decision_making \<union> {refined_dm_to_exec} \<union> refined_execution \<union> {refined_exec_to_main} 
  \<union> {refined_goal_trans}, refined_invs)"



lemma set_map: "set (map f refined_action_number_list) = f ` refined_all_acts"
  unfolding refined_action_number_list_def refined_all_acts_def M'_def 
proof -
  { fix x
    have "(i \<in> collect_nats n {}) = (i < n)" for i n by  (induction n) auto
    hence "x \<in> refined_all_acts \<longleftrightarrow> x < M'"  unfolding M'_def refined_all_acts_def by sipm
  }
  { fix x
    have "i \<in> set (numbers_gather (\<lambda>y. True) 0 xs) \<longleftrightarrow> i < length xs" for i xs
      apply (induction xs)
      apply simp sorry
    have "x \<in> set (numbers_gather (\<lambda>y. True) 0 action_list') \<longleftrightarrow> x < M'"
    
    }
    show ?thesis sorry
qed

end

end
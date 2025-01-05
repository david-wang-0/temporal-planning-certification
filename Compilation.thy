theory Compilation
  imports Temporal_Plans Diagonal_Timed_Automata
begin

text \<open>This formalisation follows the pen-and-paper compilation defined by Gigante, et al.\<close>

datatype ('proposition, 'action, 'snap_action) location =
  Init 
  | Goal
  | Main
  | PropDecoding 'proposition 
  | ExecDecoding 'action
  | Decision 'snap_action
  | Execution 'snap_action

datatype ('proposition, 'action) clock =
  Delta
  | Stop
  | PropClock 'proposition
  | Running 'action
  | StartDur 'action
  | EndDur   'action
  | SchedStartSnap 'action
  | SchedEndSnap   'action

datatype alpha = Unit

context ta_temp_planning
begin

abbreviation "N \<equiv> card props"

abbreviation "M \<equiv> card actions"

definition "true_const \<equiv> GE Stop 0"

text \<open>Preventing time from passing in any location other than the main location.\<close>
fun invs::"(('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) invassn" where
  "invs Main  = GE Stop 0"
| "invs _     = EQ Stop 0"

abbreviation "prop_numbers S \<equiv> {n| n pr. n < N \<and> pr \<in> S \<and> (p n) = pr}"

definition "prop_list S \<equiv> map p (sorted_list_of_set (prop_numbers S))"

abbreviation "msa \<equiv> mutex_snap_action pre adds dels"

lemma set_prop_list: 
  assumes "P \<subseteq> props"
  shows "set (prop_list P) = P"
proof -
  have "finite (prop_numbers P)" by simp
  have "\<forall>pr \<in> P. \<exists>n < N. p n = pr" using p_img_props assms by force
  hence "p ` (prop_numbers P) = P" by auto
  thus ?thesis unfolding prop_list_def by simp
qed

text \<open>The transition from the initial location \<open>l\<^sub>I\<close> to the main location \<open>l\<^sub>\<epsilon>\<close>\<close>
definition init_pos::"'proposition list" where
"init_pos \<equiv> prop_list init"

definition init_asmt::"(('proposition, 'action) clock, 'time) clkassn list" where
"init_asmt \<equiv> map (\<lambda>x. (PropClock x, 1)) init_pos"

definition initial_transition::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"initial_transition \<equiv> (Init, true_const, Unit, init_asmt, Main)"

text \<open>The transition from the main location \<open>l\<^sub>\<epsilon>\<close> to the \<open>0\<^sup>t\<^sup>h\<close> location of the location decoding path \<open>s\<^sub>0\<close>.\<close>
definition main_to_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"main_to_decoding \<equiv> (Main, true_const, Unit, [(Stop, 0)], PropDecoding (p 0))"

subsubsection \<open>State decoding\<close>

text \<open>The transitions between the decoding locations for the propositional clocks \<open>cp\<^sub>i\<close>\<close>
definition prop_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"prop_decoding \<equiv> {(PropDecoding (p n), DEQ (PropClock (p n)) Delta 1, Unit, [(PropClock (p n), 1)], PropDecoding (p (n + 1))) | n. n < N}
  \<union> {(PropDecoding (p n), DEQ (PropClock (p n)) Delta 0, Unit, [(PropClock (p n), 0)], PropDecoding (p (n + 1))) | n. n < N}"

text \<open>A transition from the decoding locations for propositional clocks to the decoding locations for
the execution clocks\<close>
definition prop_decoding_to_exec_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"prop_decoding_to_exec_decoding \<equiv> (PropDecoding (p N), true_const, Unit, [], ExecDecoding (act 0))"

text \<open>The transitions between the decoding locations for the execution clocks \<open>cr\<^sub>a\<close>\<close>
definition exec_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"exec_decoding \<equiv> {(ExecDecoding (act m), DEQ (Running (act m)) Delta 1, Unit, [(Running (act m), 1)], ExecDecoding (act (m + 1))) | m. m < M}
  \<union> {(ExecDecoding (act m), DEQ (Running (act m)) Delta 0, Unit, [(Running (act m), 0)], ExecDecoding (act (m + 1))) | m. m < M}"
(* To do: We index into (act M) here. Executable when actions are numbered from 0 to M - 1?
Change the locations to use number parameters? Add assumptions p and act
  are injective on {0..N} (instead of {0..<N}) and {0..M} respectively?
 *)

text \<open>The transition from the execution decoding locations to the decision-making locations\<close>
definition exec_decoding_to_decision_making::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"exec_decoding_to_decision_making \<equiv> (ExecDecoding (act M), true_const, Unit, [], Decision (at_start (act 0)))"

subsubsection \<open>Decision-making\<close>

text \<open>Interfering snap-actions\<close>

text \<open>In order to capture \<open>0\<close>-separation, we need to check that that all snap actions numbered
lower than \<open>n\<close>, do not interfere. For at-end snap-actions we also need to include the at-start 
snap action with the same numbering.\<close> (* TODO *)

definition interfering_at_start::"'snap_action \<Rightarrow> nat list" where
"interfering_at_start a = sorted_list_of_set {n. n < M \<and> (msa a (at_start (act n)) \<or> a = at_start (act n))}"
(* 
definition n_int_at_start::"nat \<Rightarrow> nat list" where
"n_int_at_start a = sorted_list_of_set {n. n < M \<and> (msa a (at_start (act n)) \<or> a = at_start (act n))}"

 *)
definition start_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"start_constraints a = map (\<lambda>b. GE (StartDur (act b)) \<epsilon>) (interfering_at_start a)"
(* 
definition n_start_constraints::"nat \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"n_start_constraints a = map (\<lambda>b. GE (StartDur (act b)) \<epsilon>) (interfering_at_start a)"
 *)
definition interfering_at_end::"'snap_action \<Rightarrow> nat list" where
"interfering_at_end a = sorted_list_of_set {n. n < M \<and> (msa a (at_end (act n)) \<or> a = at_end (act n))}"

definition end_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"end_constraints a = map (\<lambda>b. GE (EndDur (act b)) \<epsilon>) (interfering_at_end a)"
(* 
definition n_end_constraints::"nat \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"n_end_constraints a = map (\<lambda>b. AND (GE (StartDur (act b)) \<epsilon>) (GT (SchedStartSnap (act b)) 0)) (interfering_at_start a)"
                 *)
definition instant_start_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"instant_start_constraints a = map (\<lambda>b. DGE (SchedStartSnap (act b)) Delta \<epsilon>) (interfering_at_start a)"

definition sep::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"sep a \<equiv> AND_ALL (start_constraints a @ end_constraints a)"
(* 
definition n_sep_s::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"n_sep_s \<equiv> AND_ALL (start_constraints n @ end_constraints a)"
 *)
text \<open>The clock constraints for the precondition\<close>
definition pre_clocks::"'snap_action \<Rightarrow> ('proposition, 'action) clock list" where
"pre_clocks a \<equiv> map PropClock (prop_list (pre a))"

definition pre_constraint::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"pre_constraint a \<equiv> AND_ALL (map (\<lambda>c. EQ c 1) (pre_clocks a))"

text \<open>The guard constraints\<close>
definition guard::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"guard a \<equiv> AND (sep a) (pre_constraint a)"

(* 
definition n_guard_s::"nat \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"n_guard_s n \<equiv> AND (sep n) (pre_constraint a)"

definition n_guard_e::"nat \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"n_guard_e n \<equiv> AND (sep n) (pre_constraint a)" *)

definition guard_at_start::"'action \<Rightarrow> (('proposition, 'action) clock, 'time::time) dconstraint" where
"guard_at_start a \<equiv> AND (guard (at_start a)) (EQ (Running a) 0)"
(* 
definition guard_at_start_snap::"nat \<Rightarrow> (('proposition, 'action) clock, 'time::time) dconstraint" where
"guard_at_start a \<equiv> AND (guard (at_start a)) (EQ (Running a) 0)" *)

definition clock_duration_bounds::"'action \<Rightarrow> (('proposition, 'action) clock, 'time::time) dconstraint" where
"clock_duration_bounds a \<equiv> 
  let l = case (lower a) of 
    Some (lower_bound.GT t) \<Rightarrow> GT (StartDur a) t
  | Some (lower_bound.GE t) \<Rightarrow> GE (StartDur a) t
  | None \<Rightarrow> true_const;
  u = case (upper a) of 
    Some (upper_bound.LT t) \<Rightarrow> LT (StartDur a) t
  | Some (upper_bound.LE t) \<Rightarrow> LE (StartDur a) t
  | None \<Rightarrow> true_const
  in (AND l u)"

definition guard_at_end::"'action \<Rightarrow> (('proposition, 'action) clock, 'time::time) dconstraint" where
"guard_at_end a \<equiv> AND (AND (guard (at_end a)) (EQ (Running a) 1)) (clock_duration_bounds a)"

definition decision_making::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"decision_making \<equiv> 
  {(Decision (at_start (act m)), guard_at_start (act m), Unit, [(SchedStartSnap (act m), 1)], Decision (at_end (act m))) | m. m < M}
  \<union> {(Decision (at_start (act m)), true_const, Unit, [(SchedStartSnap (act m), 0)], Decision (at_end (act m))) | m. m < M}
  \<union> {(Decision (at_end (act m)), guard_at_end (act m), Unit, [(SchedEndSnap (act m), 1)], Decision (at_start (act (Suc m)))) | m. m < M}
  \<union> {(Decision (at_end (act m)), true_const, Unit, [(SchedEndSnap (act m), 0)], Decision (at_start (act (Suc m)))) | m. m < M}"

definition dm_to_exec::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"dm_to_exec \<equiv> (Decision (at_start (act M)), true_const, Unit, [], Execution (at_start (act 0)))"

subsubsection \<open>Execution\<close>

definition add_effects::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"add_effects s \<equiv> map (\<lambda>p. (PropClock p, 1)) (prop_list (adds s))"

definition del_effects::"'snap_action  \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"del_effects s \<equiv> map (\<lambda>p. (PropClock p, 0)) (prop_list ((dels s) - (adds s)))"

definition effects::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"effects s \<equiv> del_effects s @ add_effects s"

definition at_start_effects::"'action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"at_start_effects a \<equiv> (Running a, 1) # (StartDur a, 0) # effects (at_start a)"

definition at_end_effects::"'action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"at_end_effects a \<equiv> (Running a, 0) # (EndDur a, 0) # effects (at_end a)"

definition execution::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"execution \<equiv> 
  {(Execution (at_start (act m)), EQ (SchedStartSnap (act m)) 1, Unit, at_start_effects (act m), Execution (at_end (act m))) | m. m < M}
  \<union> {(Execution (at_start (act m)), EQ (SchedStartSnap (act m)) 0, Unit, [], Execution (at_end (act m))) | m. m < M}
  \<union> {(Execution (at_end (act m)), EQ (SchedEndSnap (act m)) 1, Unit, at_end_effects (act m), Execution (at_start (act (Suc m)))) | m. m < M}
  \<union> {(Execution (at_end (act m)), EQ (SchedEndSnap (act m)) 0, Unit, [], Execution (at_start (act (Suc m)))) | m. m < M}"
(* To do: again, a non-existent action is being accessed
The benefit here is that there is no need to change the indexing to {0..2M} *)

subsubsection \<open>Over-all conditions\<close>
abbreviation "action_list \<equiv> map act (sorted_list_of_set {m. m < M})"

lemma set_act_list: 
  shows "set action_list = actions"
  using act_img_actions by auto

definition over_all_clocks::"'action \<Rightarrow> ('proposition, 'action) clock list" where
"over_all_clocks a \<equiv> map PropClock (prop_list (over_all a))"

definition action_over_all::"'action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"action_over_all a \<equiv> AND_ALL (map (\<lambda>c. DLE (Running a) c 0) (over_all_clocks a))"

definition over_all_conds::"(('proposition, 'action) clock, 'time) dconstraint" where
"over_all_conds \<equiv> AND_ALL (map action_over_all action_list)"

definition exec_to_main::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"exec_to_main \<equiv> (Execution (at_start (act M)), over_all_conds, Unit, [(Delta, 0)], Main)"

subsubsection \<open>The goal\<close>
definition none_running::"(('proposition, 'action) clock, 'time) dconstraint" where
"none_running \<equiv> AND_ALL (map (\<lambda>a. EQ (Running a) 0) action_list)"

definition goal_satisfied::"(('proposition, 'action) clock, 'time) dconstraint" where
"goal_satisfied \<equiv> AND_ALL (map (\<lambda>p. EQ (PropClock p) 1) (prop_list goal))"

definition goal_constraint::"(('proposition, 'action) clock, 'time) dconstraint" where
"goal_constraint \<equiv> AND none_running goal_satisfied"

definition goal_trans::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"goal_trans \<equiv> (ExecDecoding (act M), goal_constraint, Unit, [], Goal)"

subsubsection \<open>The automaton\<close>
definition prob_automaton::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) ta" ("\<T>") where
"prob_automaton \<equiv> ({initial_transition} \<union> {main_to_decoding} \<union> prop_decoding 
  \<union> {prop_decoding_to_exec_decoding} \<union> exec_decoding \<union> {exec_decoding_to_decision_making}
  \<union> decision_making \<union> {dm_to_exec} \<union> execution \<union> {exec_to_main} \<union> {goal_trans}, invs)"
end

end

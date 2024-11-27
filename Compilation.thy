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
  | SchedEndSnap    'action

datatype alpha = Unit

context temp_planning_problem
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
"interfering_at_start a = sorted_list_of_set {n. n < M \<and> (mutex_snap_action a (at_start (act n)) \<or> a = at_start (act n))}"
(* 
definition n_int_at_start::"nat \<Rightarrow> nat list" where
"n_int_at_start a = sorted_list_of_set {n. n < M \<and> (mutex_snap_action a (at_start (act n)) \<or> a = at_start (act n))}"

 *)
definition start_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"start_constraints a = map (\<lambda>b. GE (StartDur (act b)) \<epsilon>) (interfering_at_start a)"
(* 
definition n_start_constraints::"nat \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"n_start_constraints a = map (\<lambda>b. GE (StartDur (act b)) \<epsilon>) (interfering_at_start a)"
 *)
definition interfering_at_end::"'snap_action \<Rightarrow> nat list" where
"interfering_at_end a = sorted_list_of_set {n. n < M \<and> (mutex_snap_action a (at_end (act n)) \<or> a = at_end (act n))}"

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
    (lower_bound.GT t) \<Rightarrow> GT (StartDur a) t
  | (lower_bound.GE t) \<Rightarrow> GE (StartDur a) t;
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

context temp_planning_problem
begin
context 
  fixes \<pi>::"('i, 'action, 'time) temp_plan"
begin

abbreviation "happ_seq \<equiv> plan_happ_seq _ \<pi>"

abbreviation "finite_\<pi> \<equiv> finite_plan _ \<pi>"

abbreviation "B" where "B \<equiv> happ_at happ_seq"

abbreviation "timepoint_list \<equiv> htpl _ \<pi>"

abbreviation "timepoint_set \<equiv> htps _ \<pi>"

abbreviation "ti \<equiv> time_index _ \<pi>"

abbreviation "pap_\<pi> \<equiv> plan_actions_in_problem _ \<pi>"

abbreviation "dp_\<pi> \<equiv> durations_positive _ \<pi>"

abbreviation "fp_\<pi> \<equiv> finite_plan _ \<pi>"

abbreviation "nso_\<pi> \<equiv> no_self_overlap _ \<pi>"

abbreviation "dv_\<pi> \<equiv> durations_valid _ \<pi>"

abbreviation "vss \<equiv> valid_state_sequence _ \<pi>"

abbreviation "\<pi>_inv_seq \<equiv> plan_inv_seq _ \<pi>"

abbreviation "Inv \<equiv> invs_at \<pi>_inv_seq"

abbreviation "vp_\<pi> \<equiv> valid_plan _ \<pi>"


subsection \<open>Definitions that connect the plan to the automaton\<close>
subsubsection \<open>Proposition and execution state\<close>
abbreviation prop_corr::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'proposition state \<Rightarrow> 'proposition \<Rightarrow> bool" where
"prop_corr W Q prop \<equiv> (W (PropClock prop) = 1 \<longleftrightarrow> prop \<in> Q) \<and> (W (PropClock prop) = 0 \<longleftrightarrow> prop \<notin> Q)"

definition prop_model::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'proposition state \<Rightarrow> bool" where
"prop_model W Q \<equiv> \<forall>p \<in> props. prop_corr W Q p"

abbreviation delta_prop_corr::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'proposition state \<Rightarrow> 'proposition \<Rightarrow> bool" where
"delta_prop_corr W Q prop \<equiv> (W (PropClock prop) - W Delta = 1 \<longleftrightarrow> prop \<in> Q) \<and> (W (PropClock prop) - W Delta = 0 \<longleftrightarrow> prop \<notin> Q)"

definition delta_prop_model::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'proposition state \<Rightarrow> bool" where
"delta_prop_model W Q \<equiv> \<forall>p \<in> props. delta_prop_corr W Q p"

abbreviation exec_corr::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'action state \<Rightarrow> 'action \<Rightarrow> bool" where
"exec_corr W E a \<equiv> (W (Running a) = 1 \<longleftrightarrow> a \<in> E) \<and> (W (Running a) = 0 \<longleftrightarrow> a \<notin> E)"

definition exec_model::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'action state \<Rightarrow> bool" where
"exec_model W E \<equiv> \<forall>a \<in> actions. exec_corr W E a"

abbreviation delta_exec_corr::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'action state \<Rightarrow> 'action \<Rightarrow> bool" where
"delta_exec_corr W E a \<equiv> ((W (Running a)) - (W Delta) = 1 \<longleftrightarrow> a \<in> E) \<and> ((W (Running a)) - (W Delta) = 0 \<longleftrightarrow> a \<notin> E)"

definition delta_exec_model::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'action state \<Rightarrow> bool" where
"delta_exec_model W E \<equiv> \<forall>a \<in> actions. delta_exec_corr W E a"

definition exec_state_sequence::"('time \<times> 'action) set" where
"exec_state_sequence \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s < t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)}"

definition exec_state_sequence'::"('time \<times> 'action) set" where
"exec_state_sequence' \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)}"

abbreviation "ES t \<equiv> {a. (t, a) \<in> exec_state_sequence}"

abbreviation "IES t \<equiv> {a. (t, a) \<in> exec_state_sequence'}"

abbreviation "PES t \<equiv> {a. (t, at_start a) \<in> happ_seq \<and> (t, at_end a) \<in> happ_seq}" 

lemma in_ES_iff: "a \<in> ES t \<longleftrightarrow> (\<exists>s. a \<in> actions \<and>  at_start a \<in> B s \<and> s < t 
                  \<and> \<not>(\<exists>s'. at_end a \<in> B s' \<and> s \<le> s' \<and> s' < t))"
  unfolding exec_state_sequence_def happ_at_def by blast


lemma in_IES_iff: "a \<in> IES t \<longleftrightarrow> (\<exists>s. a \<in> actions \<and>  at_start a \<in> B s \<and> s \<le> t 
                  \<and> \<not>(\<exists>s'. at_end a \<in> B s' \<and> s \<le> s' \<and> s' \<le> t))"
  unfolding exec_state_sequence'_def happ_at_def by blast

lemma inc_es_is_next_es:
  assumes "finite_\<pi>"
      and "Suc l < length timepoint_list"
  shows "IES (ti l) = ES (ti(Suc l))"
proof (rule equalityI; rule subsetI)
  fix a
  assume "a \<in> IES (ti l)"
  then obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> ti l"
    "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> ti l)"
    unfolding exec_state_sequence'_def by blast
  from this(2) time_index_strict_sorted_list[rotated, OF assms(2)] no_actions_between_indexed_timepoints[OF assms]
  have "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < ti (Suc l))"
    unfolding happ_at_def by fastforce
  with time_index_strict_sorted_list[rotated, OF \<open>Suc l < length timepoint_list\<close>] s(1)
  show "a \<in> ES (ti(Suc l))" using exec_state_sequence_def by force
next
  fix a
  assume "a \<in> ES (ti (Suc l))"
  then obtain s where
    s: "a \<in> actions"
    "(s, at_start a) \<in> happ_seq"  
    "s < ti (Suc l)"
    "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < ti (Suc l))"
    unfolding exec_state_sequence_def by blast
  from this(2, 3) no_actions_between_indexed_timepoints[OF assms]
  have "s \<le> ti l" using happ_at_def by fastforce
  moreover
  have "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> ti l)" 
  proof (rule notI)
    assume "\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> ti l"
    with time_index_strict_sorted_list assms(2)
    have "\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < ti(Suc l)" by fastforce
    with s(4)
    show "False" by blast
  qed
  ultimately
  show "a \<in> IES (ti l)" using s(1,2) exec_state_sequence'_def by blast
qed

lemma last_ies_empty:
  assumes pap: "pap_\<pi>"
      and dnz: "dp_\<pi>"
      and fpl:  "fp_\<pi>"
  shows "IES (ti(length timepoint_list - 1)) = {}" (is "IES ?te = {}")
proof -   
  have "a \<notin> IES ?te" for a
  proof (rule notI)
    assume a: "a \<in> IES ?te"
    then obtain s where
      s: "a \<in> actions"
      "(s, at_start a) \<in> happ_seq" 
      "s \<le> ?te"
      "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> ?te)"
      using exec_state_sequence'_def by blast
    from this(2)[simplified plan_happ_seq_def]
    consider "(s, at_start a) \<in> {(t, at_start a)|a t d. (a, t, d) \<in> ran \<pi>}" 
      | "(s, at_start a) \<in>  {(t + d, at_end a) |a t d. (a, t, d) \<in> ran \<pi>}"
      by blast
    then
    have "\<exists>d. (a, s, d) \<in> ran \<pi>"
    proof cases
      case 1
      hence "\<exists>a' t d. (s, at_start a) = (t, at_start a') \<and> (a', t, d) \<in> ran \<pi>" by simp
      with assms(1)[simplified plan_actions_in_problem_def]
      show ?thesis by (metis Pair_inject at_start_inj_on inj_on_contraD s(1))
    next
      case 2
      hence "\<exists>a' t d. (s, at_start a) = (t + d, at_end a') \<and> (a', t, d) \<in> ran \<pi>" by auto
      with s(1) assms(1)[simplified plan_actions_in_problem_def] snaps_disj
      have False by blast
      thus ?thesis ..
    qed
    then obtain d where
      d: "(a, s, d) \<in> ran \<pi>"
      "(s + d, at_end a) \<in> happ_seq" using plan_happ_seq_def by blast
    with s(4) assms(2)[simplified durations_positive_def]
    have "s + d > ?te" by fastforce
    
    have "t \<le> ?te" if "t \<in> set timepoint_list" for t
    proof -
      from that[simplified time_index_bij_betw_list[simplified bij_betw_def, THEN conjunct2, symmetric]]
      obtain n where
        n: "n < length timepoint_list" "t = ti n" by blast
      show "t \<le> ?te"
      proof (cases "n < length timepoint_list - 1")
        case True
        show ?thesis
          apply (subst n(2))
          apply (rule time_index_sorted_list)
          using True by simp+
      next
        case False
        hence "n = length timepoint_list - 1" using n by linarith
        thus ?thesis using n by blast
      qed
    qed
    moreover
    
    from d(1) set_htpl_eq_htps[OF fpl] 
    have "s + d \<in> set timepoint_list" unfolding htps_def by blast
    ultimately
    show False using \<open>s + d > ?te\<close> by fastforce
  qed
  thus "IES ?te = {}" by blast
qed

lemma first_es_empty:
assumes pap: "pap_\<pi>"
      and dnz: "dp_\<pi>"
      and fpl:  "fp_\<pi>"
    shows "ES (ti 0) = {}"
proof (rule ccontr)
  assume "ES (ti 0) \<noteq> {}"
  then obtain a where
    a: "a \<in> ES (ti 0)" by blast

  then obtain t where
    t: "t < ti 0"
    "at_start a \<in> B t" using in_ES_iff by blast

  show False
  proof (cases "card timepoint_set")
    case 0
    with time_index_img_set fpl
    have "timepoint_set = {}" by fastforce
    with t(2) a_in_B_iff_t_in_htps
    show ?thesis by blast
  next
    case (Suc nat)
    hence "0 < card timepoint_set" by auto
    from t(2)
    have "t \<in> timepoint_set" using a_in_B_iff_t_in_htps by blast
    then obtain i where
      i: "t = ti i" 
      "i < card timepoint_set" using time_index_img_set fpl by blast
    have "0 \<le> i" by simp
    with i(2)
    have "ti 0 \<le> ti i" using time_index_sorted_set by blast
    with i(1) t
    show ?thesis by simp
  qed
qed

lemma not_executing_when_starting:
  assumes snap_in_B: "(at_start a) \<in> B t"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap: "nso_\<pi>"
      and durations_positive: "dp_\<pi>"
      and plan_actions_in_problem: "pap_\<pi>"
  shows "a \<notin> ES t"
proof (rule notI)
  assume "a \<in> ES t"
  then obtain s where
    started: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s < t"
    and not_ended: "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)"
    unfolding exec_state_sequence_def by blast
  
  from started
  obtain d where
    as_in_plan: "(a, s, d) \<in> ran \<pi>"
    using at_start_in_happ_seqE assms by blast+
  hence "(s + d, at_end a) \<in> happ_seq" unfolding plan_happ_seq_def by blast
  with durations_positive[simplified durations_positive_def] as_in_plan not_ended 
  have t_sd: "t \<le> s + d" by fastforce
  
  from snap_in_B
  obtain d' where
    at_in_plan: "(a, t, d') \<in> ran \<pi>" 
    using at_start_in_happ_seqE assms unfolding happ_at_def by blast

  from started as_in_plan t_sd at_in_plan
  show False using no_self_overlap[THEN no_self_overlap_spec] by fastforce
qed

lemma executing_when_ending:
  assumes snap_in_B: "(at_end a) \<in> B t"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap: nso_\<pi>
      and durations_positive: dp_\<pi>
      and plan_actions_in_problem: pap_\<pi>
    shows "a \<in> ES t"
proof -
  from snap_in_B
  obtain s d where
    s: "(a, s, d) \<in> ran \<pi>"   
    "t = s + d"
    using at_end_in_happ_seqE assms unfolding happ_at_def by blast
  with durations_positive[simplified durations_positive_def] 
  have "(s, at_start a) \<in> happ_seq \<and> s < t" unfolding plan_happ_seq_def by auto
  moreover
  have "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)"
  proof (rule notI)
    assume "\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t"
    then obtain s' where
      s': "(s', at_end a) \<in> happ_seq" 
      "s \<le> s' \<and> s' < t" by auto
  
    then obtain \<tau> \<epsilon> where
      \<tau>: "(a, \<tau>, \<epsilon>) \<in> ran \<pi>"
      "s' = \<tau> + \<epsilon>"
      using at_end_in_happ_seqE assms by blast

    hence "(\<tau>, at_start a) \<in> happ_seq" unfolding plan_happ_seq_def by blast

    consider "\<tau> \<le> s" | "s \<le> \<tau>" by fastforce
    thus False
    proof cases
      case 1
      with s'(2) s(2) \<tau>(2)
      have "\<tau> = s \<longrightarrow> \<epsilon> \<noteq> d" by blast
      with no_self_overlap[THEN no_self_overlap_spec, OF \<tau>(1) s(1)] 1 s'(2) \<tau>(2) 
      show ?thesis by blast
    next
      case 2
      from \<open>s \<le> s' \<and> s' < t\<close>[simplified \<open>t = s + d\<close> \<open>s' = \<tau> + \<epsilon>\<close>] 
        durations_positive[simplified durations_positive_def] \<open>(a, \<tau>, \<epsilon>) \<in> ran \<pi>\<close>
      have "\<tau> \<le> s + d" by (meson less_add_same_cancel1 order_le_less_trans order_less_imp_le)
      moreover
      from 2 s'(2) s(2) \<tau>(2)
      have "\<tau> = s \<longrightarrow> \<epsilon> \<noteq> d" by blast
      ultimately 
      show ?thesis using 2 no_self_overlap[THEN no_self_overlap_spec, OF s(1) \<tau>(1)] by blast
    qed
  qed
  ultimately
  show ?thesis unfolding exec_state_sequence_def using a_in_actions by blast
qed

lemma execution_state_unchanging:
  assumes not_starting: "at_start a \<notin> B t"
      and not_ending:   "at_end a \<notin> B t"
    shows "a \<in> ES t \<longleftrightarrow> a \<in> IES t"
proof (rule iffI)
  assume "a \<in> ES t"
  with exec_state_sequence_def
  obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s < t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)" by blast
  have "s \<le> t" using s by auto
  moreover
  have "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)" using s' not_ending unfolding happ_at_def by auto
  ultimately
  show "a \<in> IES t" using s unfolding exec_state_sequence'_def by blast
next
  assume "a \<in> IES t"
  with exec_state_sequence'_def
  obtain s where  
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)" by blast
  have "s < t" using not_starting s unfolding happ_at_def by force
  moreover 
  have "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)" using s' by auto
  ultimately
  show "a \<in> ES t" using s unfolding exec_state_sequence_def by blast
qed

subsubsection \<open>Execution time\<close>

definition pt::"'snap_action \<Rightarrow> ('time \<Rightarrow> 'time \<Rightarrow> bool) \<Rightarrow> 'time \<Rightarrow> 'time" where
"pt a c t \<equiv> if (\<exists>t'. c t' t \<and> a \<in> B t') 
  then (Greatest (\<lambda>t'. c t' t \<and> a \<in> B t')) 
  else (Least (\<lambda>t'. B t' \<noteq> {}) - (\<epsilon> + 1))"

abbreviation last_snap_exec::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"last_snap_exec a t \<equiv> pt a (<) t"

definition exec_time::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"exec_time a t = (let t' = last_snap_exec a t in t - t')"

abbreviation last_snap_exec'::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"last_snap_exec' a t \<equiv> pt a (\<le>) t"

definition exec_time'::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"exec_time' a t = (let t' = last_snap_exec' a t in t - t')"

lemma a_not_in_b_last_unchanged: "a \<notin> B t \<Longrightarrow> last_snap_exec' a t = last_snap_exec a t"
proof -
  assume "a \<notin> B t"
  have 1: "(GREATEST t'. t' < t \<and> a \<in> B t') = (GREATEST t'. t' \<le> t \<and> a \<in> B t')"
    if defined: "\<exists>x\<le>t. a \<in> B x"
  proof (rule classical)
    assume "(GREATEST t'. t' < t \<and> a \<in> B t') \<noteq> (GREATEST t'. t' \<le> t \<and> a \<in> B t')"
    then have "\<exists>t'. t' \<le> t \<and> \<not>(t' < t) \<and> a \<in> B t'"
      using defined
      by (meson nless_le)
    then have "a \<in> B t" by auto
    with \<open>a \<notin> B t\<close>
    have "False" by simp
    thus "(GREATEST t'. t' < t \<and> a \<in> B t') = (GREATEST t'. t' \<le> t \<and> a \<in> B t')"
      by blast
  qed
  from \<open>a \<notin> B t\<close>
  have "(\<exists>x<t. a \<in> B x) = (\<exists>x\<le>t. a \<in> B x)"
    using nless_le by auto
  with \<open>a \<notin> B t\<close> 1
  show "last_snap_exec' a t = last_snap_exec a t"
    using pt_def by auto
qed

lemma a_not_in_b_exec_time_unchanged: "a \<notin> B t \<Longrightarrow> exec_time a t = exec_time' a t"
  using a_not_in_b_last_unchanged unfolding exec_time_def exec_time'_def by simp

lemma a_in_b_last_now: "a \<in> B t \<Longrightarrow> last_snap_exec' a t = t"
  using pt_def
  by (auto intro: Greatest_equality)

lemma a_in_b_exec_time'_0: "a \<in> B t \<Longrightarrow> exec_time' a t = 0"
  using a_in_b_last_now unfolding exec_time'_def by simp

lemma subseq_last_snap_exec:
  assumes fp: fp_\<pi>
      and llen: "(Suc l) < length timepoint_list" 
shows "last_snap_exec a (ti(Suc l)) = last_snap_exec' a (ti l)"
proof -

  define t where 
    "t = last_snap_exec a (ti (Suc l))"    

  define s where
    "s = last_snap_exec' a (ti l)" 
  
  have cl: "length timepoint_list = card timepoint_set" unfolding htpl_def by simp
  
  have tl_ord: "ti l < ti (Suc l)" 
    using time_index_strict_sorted_list llen by blast
  
  from t_def consider "\<exists>t'. t' < (ti (Suc l)) \<and> a \<in> B t'" 
    | "\<not>(\<exists>t'. t' < (ti (Suc l)) \<and> a \<in> B t')" by auto
  hence "t = s"
  proof cases
    case 1 
    hence exsl: "Ex (\<lambda>t'. t' < ti(Suc l) \<and> a \<in> B t')" (is "Ex ?psl") by blast
    have "\<forall>t'. t' < ti(Suc l) \<and> a \<in> B t' \<longrightarrow> t' \<le> ti l"
      using time_index_strict_sorted_list[OF _ llen] time_index_sorted_list[OF _ llen] 
        no_actions_between_indexed_timepoints[OF assms] by fastforce
    moreover
    have "\<forall>t'. t' \<le> ti l \<and> a \<in> B t' \<longrightarrow> t' < ti(Suc l)" 
      using time_index_strict_sorted_list[OF _ llen] time_index_sorted_list[OF _ llen] 
        no_actions_between_indexed_timepoints[OF assms] by fastforce
    ultimately 
    have fa: "\<forall>t'. t' < ti(Suc l) \<and> a \<in> B t' \<longleftrightarrow> t' \<le> ti l \<and> a \<in> B t'" by blast
    with 1
    have exl: "Ex (\<lambda>t'. t' \<le> ti l \<and> a \<in> B t')" (is "Ex ?pl") by blast
    from fa
    have "Greatest ?psl = Greatest ?pl" by auto
    thus "t = s" unfolding t_def s_def pt_def using exl exsl by auto
  next
    case 2
    hence "\<not> (\<exists>t' \<le> ti l. a \<in> B t')" using tl_ord by force
    with 2 t_def[simplified pt_def] s_def[simplified pt_def]
    show ?thesis by auto
  qed
  thus "last_snap_exec a (ti(Suc l)) = last_snap_exec' a (ti l)" 
    using s_def t_def by auto
  qed

lemma updated_exec_time_and_next: 
  assumes fp_\<pi>
      and "Suc l < length timepoint_list"
  shows "exec_time a (ti (Suc l)) = (exec_time' a (ti l)) + (ti (Suc l) - ti l)"
  using subseq_last_snap_exec[OF assms] exec_time_def exec_time'_def 
  by simp


lemma exec_time_and_epsilon:
  assumes nm: "nm_happ_seq happ_seq"
      and s_at_t: "s \<in> B t"
      and mutex: "mutex_snap_action s b \<or> s = b"
      and fp: "fp_\<pi>"
    shows "exec_time b t \<ge> \<epsilon>"
proof (cases "\<exists>u < t. b \<in> B u")
  case True

  from s_at_t
  have "t \<in> timepoint_set" using a_in_B_iff_t_in_htps by blast
  then obtain tx where
    tx: "t = ti tx"
    "tx < card timepoint_set" using time_index_img_set[OF fp] by force
  
  have P_iff: "(\<lambda>t'. t' < t \<and> b \<in> B t') = (\<lambda>t'. \<exists>i < card timepoint_set. ti i = t' \<and> i < tx \<and> b \<in> B (ti i))" (is "?P = ?P'")
  proof -
    have "(\<lambda>t'. t' < t \<and> b \<in> B t') = (\<lambda>t'. t' \<in> timepoint_set \<and> t' < t \<and> b \<in> B t')" using a_in_B_iff_t_in_htps by blast
    also have "... = (\<lambda>t'. \<exists>i < card timepoint_set. ti i = t' \<and> t' < t \<and> b \<in> B (ti i))" using time_index_img_set[OF fp] by force
    also have "... = (\<lambda>t'. \<exists>i < card timepoint_set. ti i = t' \<and> i < tx \<and> b \<in> B (ti i))"
      unfolding tx(1) 
      using time_index_strict_sorted_set'[where j = tx] 
      using time_index_strict_sorted_set[OF _ tx(2)] 
      by blast
    finally show ?thesis .
  qed
  
  obtain u where
    u: "u < t"
    "b \<in> B u"
    using True by blast
  hence "u \<in> timepoint_set" using a_in_B_iff_t_in_htps by blast
  hence "\<exists>i < card timepoint_set. i < tx \<and> b \<in> B (ti i)" (is "Ex ?P2") using P_iff u by meson
  moreover
  have P2_int: "\<And>x. ?P2 x \<Longrightarrow> x \<le> tx" using time_index_sorted_set' by auto
  ultimately
  have P2: "?P2 (Greatest ?P2)" using GreatestI_ex_nat[where P = ?P2] by blast
  
  have P_1: "?P (ti(Greatest ?P2))" 
  proof -
    from P2 time_index_strict_sorted_set[OF _ tx(2)] 
    show ?thesis unfolding tx(1) by blast
  qed
  
  have P_max: "x \<le> ti (Greatest ?P2)" if assm: "?P x" for x 
  proof -
    from assm P_iff
    obtain i where
      i: "?P2 i"
      "x = ti i" by metis
    moreover
    have "i \<le> Greatest ?P2" using Greatest_le_nat[where P = ?P2] i(1) P2_int by blast
    moreover
    have "Greatest ?P2 < card timepoint_set" using P2 ..
    ultimately
    show "x \<le> ti(Greatest ?P2)" using time_index_sorted_set by blast
  qed

  have "?P (Greatest ?P)" 
    apply (rule GreatestI_time)
     apply (rule P_1)
    using P_max by blast
  moreover
  have 1: "last_snap_exec b t = (GREATEST t'. t' < t \<and> b \<in> B t')" using True unfolding pt_def by auto
  ultimately
  have b_at_t': "(\<lambda>u. u < t \<and> b \<in> B u) (last_snap_exec b t)" (is "?t < t \<and> b \<in> B ?t") by auto
  

  have nm_cond: "t - ?t < \<epsilon> \<and> ?t - t < \<epsilon> \<and> s \<in> (B t) \<and> b \<in> (B ?t) 
    \<longrightarrow> ((s \<noteq> b \<longrightarrow> \<not>mutex_snap_action s b) \<and> (s = b \<longrightarrow> t = ?t))" using nm nm_happ_seq_def by blast
  hence "\<not>(s \<noteq> b \<longrightarrow> \<not>mutex_snap_action s b) \<or> \<not>(s = b \<longrightarrow> t = ?t)
    \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> s \<notin> (B t) \<or> b \<notin> (B ?t)" by auto
  hence "\<not>(s \<noteq> b \<longrightarrow> \<not>mutex_snap_action s b) \<or> \<not>(s = b \<longrightarrow> t = ?t)
    \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  using s_at_t b_at_t' by blast
  hence "(s \<noteq> b \<and> mutex_snap_action s b) \<or> (s = b \<and> t \<noteq> ?t)
    \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  by blast
  moreover
  have "s \<noteq> b \<longrightarrow> mutex_snap_action s b" using mutex by blast
  moreover
  have "t \<noteq> ?t" using b_at_t' by auto
  ultimately
  consider "t - ?t \<ge> \<epsilon>" | "?t - t \<ge> \<epsilon>" by auto
  note c = this
  
  have "t > ?t" using b_at_t' by blast
  moreover
  have "\<epsilon> \<ge> 0" using eps_range less_le_not_le by fastforce
  ultimately 
  have "t - ?t \<ge> \<epsilon>"  apply (cases rule: c) apply blast using order.trans by fastforce
  thus ?thesis using exec_time_def by auto
next
  case False
  have 1: "ti 0 \<le> u" if "B u \<noteq> {}" for u
  proof -
    have "u \<in> set timepoint_list" using that a_in_B_iff_t_in_htps set_htpl_eq_htps[OF fp] by auto
    hence "\<exists>i. ti i = u \<and> i < length timepoint_list" using time_index_img_list by force
    thus "ti 0 \<le> u" using time_index_sorted_list by blast
  qed
  with s_at_t
  have 2: "ti 0 \<le> t" by auto
  
  have 3: "Least (\<lambda>t. B t \<noteq> {}) = (ti 0)" 
  proof (rule Least_equality[OF _ 1])
    have "card timepoint_set > 0" using a_in_B_iff_t_in_htps s_at_t card_gt_0_iff finite_htps fp by blast
    hence "ti 0 \<in> timepoint_set" using time_index_img_set[OF fp] by blast
    thus "B (ti 0) \<noteq> {}" using a_in_B_iff_t_in_htps by auto
  qed

  have "last_snap_exec b t = (LEAST t'. B t' \<noteq> {}) - (\<epsilon> + 1)" using False unfolding pt_def by argo
  from this[simplified 3]
  have "last_snap_exec b t = ti 0 - (\<epsilon> + 1)" .
  hence 4: "t - last_snap_exec b t = \<epsilon> + 1 + t - ti 0" by auto
  with 2
  have "0 < 1 + t - ti 0" by (simp add: add_strict_increasing)
  with 4
  have "\<epsilon> < t - last_snap_exec b t" unfolding 4
    by auto
  thus ?thesis unfolding exec_time_def by simp
qed

lemma exec_time_and_duration:
  assumes "at_end a \<in> B t"
      and a_in_actions: "a \<in> actions"
      and nso: "nso_\<pi>"
      and dp: "dp_\<pi>"
      and pap: "pap_\<pi>"
  shows "\<exists>t' d. (a, t', d) \<in> ran \<pi> \<and> exec_time (at_start a) t = d"
proof -
  have "\<exists>!(s,d). (a, s, d) \<in> ran \<pi> \<and> t = s + d" using at_end_in_happ_seqE[OF _ assms(2) nso dp pap] assms(1)[simplified happ_at_def] by simp
  then obtain s d where
    sd: "(a, s, d) \<in> ran \<pi>" 
    "t = s + d" by auto
  with dp
  have wit: "s < t \<and> at_start a \<in> B s" unfolding happ_at_def plan_happ_seq_def durations_positive_def by force
  moreover
  have "t' \<le> s" if "t' < t" "at_start a \<in> B t'" for t'
  proof (rule ccontr)
    assume "\<not> t' \<le> s"
    hence st': "s < t'" by simp
    from that(2)[simplified happ_at_def]
    obtain d' where
       t'd': "(a, t', d') \<in> ran \<pi>" 
      using at_start_in_happ_seqE[OF _ assms(2,3,4,5)]  by blast
    thus False using that st' sd nso[THEN no_self_overlap_spec] by force
  qed
  ultimately
  have "(GREATEST s. s < t \<and> at_start a \<in> B s) = s" unfolding Greatest_def by fastforce
  hence "exec_time (at_start a) t = d" using sd(2) wit unfolding exec_time_def pt_def by auto
  thus ?thesis using sd(1) by blast
qed

lemma exec_time_sat_dur_const:
  assumes "at_end a \<in> B t"
      and a_in_actions: "a \<in> actions"
      and "nso_\<pi>"
      and "dp_\<pi>"
      and "pap_\<pi>"
      and "dv_\<pi>"
    shows "satisfies_duration_bounds a (exec_time (at_start a) t)"
  using exec_time_and_duration[OF assms(1,2,3,4,5)] \<open>dv_\<pi>\<close>[simplified durations_valid_def]
  by blast

lemma exec_time_at_init:
  assumes fp: "fp_\<pi>"
    and some_happs: "0 < card timepoint_set"
  shows "exec_time b (ti 0) = \<epsilon> + 1"
proof -
  have "\<forall>i < card timepoint_set. ti 0 \<le> ti i" using time_index_sorted_set by blast
  hence "\<forall>t \<in> timepoint_set. ti 0 \<le> t" using time_index_img_set[OF fp] by force
  hence "\<not>(\<exists>s \<in> timepoint_set. s < ti 0)" by auto
  hence 1: "\<not>(\<exists>s < ti 0. B s \<noteq> {})" unfolding happ_at_def plan_happ_seq_def htps_def by blast
  
  have "ti 0 \<in> timepoint_set" using time_index_img_set[OF fp]  using some_happs by blast
  hence "B (ti 0) \<noteq> {}" unfolding happ_at_def plan_happ_seq_def unfolding htps_def by blast
  with 1
  have "Least (\<lambda>t'. B t' \<noteq> {}) = ti 0" by (meson Least_equality not_le_imp_less)
  with 1
  show ?thesis unfolding exec_time_def pt_def by (auto simp: Let_def)
qed 

subsubsection \<open>Restricting snap action sets by an upper limit on the index\<close>

definition limited_snap_action_set::"'snap_action set \<Rightarrow> nat \<Rightarrow> 'snap_action set" where
"limited_snap_action_set S m = 
  {at_start (act n) | n. n < m \<and> at_start (act n) \<in> S} 
  \<union> {at_end (act n) | n. n < m \<and> at_end (act n) \<in> S}"

lemma limited_snap_action_set_mono: "i < j \<Longrightarrow> limited_snap_action_set S i \<subseteq> limited_snap_action_set S j"
  unfolding limited_snap_action_set_def by auto

lemma limited_snap_action_subset: "limited_snap_action_set S i \<subseteq> S"
  unfolding limited_snap_action_set_def by blast

lemma limit_M_eq_orig: "S \<subseteq> snap_actions \<Longrightarrow> limited_snap_action_set S M = S"
proof (rule equalityI; rule subsetI)
  fix x
  assume S: "S \<subseteq> snap_actions" 
     and x: "x \<in> limited_snap_action_set S M"
  from x obtain n where
    "x = at_start (act n) \<and> at_start (act n) \<in> S 
    \<or> x = at_end (act n) \<and> at_end (act n) \<in> S"
    unfolding limited_snap_action_set_def by blast         
  then show "x \<in> S" by blast
next 
  fix x
  assume S: "S \<subseteq> snap_actions" 
     and x: "x \<in> S"
  hence "x \<in> at_start ` actions \<or> x \<in> at_end ` actions" 
    unfolding snap_actions_def by blast
  hence "\<exists>m. m < M \<and> (x = at_start (act m) \<or> x = at_end (act m))" 
    using act_img_actions by force
  with x
  show "x \<in> limited_snap_action_set S M" unfolding  limited_snap_action_set_def
    by blast
qed

abbreviation B_lim::"'time \<Rightarrow> nat \<Rightarrow> 'snap_action set" where
"B_lim t m \<equiv> limited_snap_action_set (B t) m"

lemma B_lim_M_eq_B:
  assumes "pap_\<pi>"
  shows "B_lim t M = B t" 
proof (rule limit_M_eq_orig)
  show "B t \<subseteq> snap_actions"
  proof (rule subsetI)
    fix x
    assume "x \<in> B t"
    then have "\<exists>a. (x = at_start a \<or> x = at_end a) \<and> a \<in> actions" 
      unfolding happ_at_def plan_happ_seq_def using assms(1)[simplified plan_actions_in_problem_def]
      by blast
    then show "x \<in> snap_actions" unfolding snap_actions_def by blast
  qed
qed

subsection \<open>Simulated execution of a single snap-action\<close>

lemma main_loc_delta_prop_model: 
  assumes initial: "prop_model W Q"
      and delta: "W Delta = 0"
      and transition: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>Main, W'\<rangle>"
    shows "delta_prop_model W' Q"
proof -
  have "delta_prop_corr W' Q p" (is "?goal") if "p \<in> props" for p
  proof -
    have W: "prop_corr W Q p" using assms(1) that prop_model_def by auto
    have W': "W' = W \<oplus> d" by (cases rule: step_t.cases[OF transition]) simp
    
    have "W' (PropClock p) = 1 + d \<longleftrightarrow> p \<in> Q"
         "W' (PropClock p) = d \<longleftrightarrow> p \<notin> Q"
         "W' Delta = d"
      using W delta W'[simplified cval_add_def] by simp+
    thus ?goal by force
  qed
  thus "delta_prop_model W' Q" using delta_prop_model_def by simp
qed 

lemma main_loc_delta_exec_model: 
  assumes initial: "exec_model W Q"
      and delta: "W Delta = 0"
      and transition: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>Main, W'\<rangle>"
    shows "delta_exec_model W' Q"
proof -
  have "delta_exec_corr W' Q a" (is "?goal") if "a \<in> actions" for a
  proof -
    have W: "exec_corr W Q a" using assms(1) that exec_model_def by auto
    have W': "W' = W \<oplus> d" by (cases rule: step_t.cases[OF transition]) simp
    
    have "W' (Running a) = 1 + d \<longleftrightarrow> a \<in> Q"
         "W' (Running a) = d \<longleftrightarrow> a \<notin> Q"
         "W' Delta = d"
      using W delta W'[simplified cval_add_def] by simp+
    thus ?goal by force
  qed
  thus "delta_exec_model W' Q" using delta_exec_model_def by simp
qed 

lemma main_to_prop_decoding:
  assumes pc: "prop_model W Q"
      and ac: "exec_model W E"
      and delta: "W Delta = 0"
      and stop: "W Stop \<ge> 0"
    shows "\<exists>W'. \<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>PropDecoding (p 0), W'\<rangle> 
    \<and> delta_prop_model W' Q \<and> delta_exec_model W' E \<and> W' Stop = 0"
proof -
  have "\<And>W' d. prop_model W Q \<and> exec_model W E \<and> W Delta = 0 \<and> \<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>Main, W'\<rangle> \<Longrightarrow> delta_prop_model W' Q \<and> delta_exec_model W' E"
    using main_loc_delta_exec_model main_loc_delta_prop_model
    by blast
  obtain d W' where 
    W': "W' = W \<oplus> d"
        "d \<ge> 0" by auto
  
  have W_inv: "W \<turnstile> inv_of \<T> Main" unfolding inv_of_def prob_automaton_def
    using stop by auto
  
  have W'_inv: "W' \<turnstile> inv_of \<T> Main" unfolding inv_of_def prob_automaton_def cval_add_def W'(1)
    using stop W'(2) by auto
  
  from W_inv W'_inv W'
  have "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>Main, W'\<rangle>"
    using step_t.intros by blast
  with pc ac delta
  have W'1: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle> \<and> delta_prop_model W' Q \<and> delta_exec_model W' E" 
    using main_loc_delta_exec_model main_loc_delta_prop_model by blast
  
  have W'_stop: "W' Stop \<ge> 0" unfolding W' cval_add_def using stop W' by simp
  have "\<T> \<turnstile> \<langle>Main, W'\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>PropDecoding (p 0), W'(Stop := 0)\<rangle>"
    apply (rule step_a.intros)
       apply (subst trans_of_def)
    apply (subst prob_automaton_def)
       apply (subst main_to_decoding_def)
       apply auto[1]
      apply (simp add: true_const_def)
      apply (auto simp: W'_stop)[1]
    subgoal
    unfolding prob_automaton_def cval_add_def W'(1) inv_of_def
    using stop W'(2) by auto
  by auto
  
  from step_a[OF this, THEN step, OF refl]
  have W'2: "\<T> \<turnstile> \<langle>Main, W'\<rangle> \<rightarrow>* \<langle>PropDecoding (p 0), W'(Stop := 0)\<rangle>"  .
  
  from W'1
  have "delta_prop_model (W'(Stop := 0)) Q \<and> delta_exec_model (W'(Stop := 0)) E"
    unfolding delta_exec_model_def delta_prop_model_def by simp
  moreover
  from W'1[THEN conjunct1] W'2
  have " \<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>PropDecoding (p 0), W'(Stop := 0)\<rangle>" using steps_trans by fast
  ultimately
  show ?thesis by auto
qed

abbreviation prop_dec_automaton ("\<T> pd") where 
"prop_dec_automaton \<equiv> (prop_decoding \<union> {prop_decoding_to_exec_decoding}, invs)"

abbreviation es_dec_automaton ("\<T> ed") where 
"es_dec_automaton \<equiv> (exec_decoding, invs)"

fun is_boolean_clock::"('proposition, 'action) clock \<Rightarrow> bool" where
"is_boolean_clock (PropClock _) = True"
| "is_boolean_clock (Running _) = True"
| "is_boolean_clock _ = False"

fun is_propositional_clock::"('proposition, 'action) clock \<Rightarrow> bool" where
"is_propositional_clock (PropClock _) = True"
| "is_propositional_clock _ = False"

fun is_exec_clock::"('proposition, 'action) clock \<Rightarrow> bool" where
"is_exec_clock (Running _) = True"
| "is_exec_clock _ = False"


lemma boolean_state_decoding:
  assumes prop_clocks: "delta_prop_model W Q"
      and exec_clocks: "delta_exec_model W E"
      and stop: "W Stop = 0"
  shows "\<exists>W'. \<T> \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W'\<rangle> 
    \<and> prop_model W' Q 
    \<and> exec_model W' E 
    \<and> (\<forall>c. \<not>(is_boolean_clock c) \<longrightarrow> W c = W' c)"
proof -
  have propositional_decoding_step:
      "\<exists>W'. \<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle> 
            \<and> (\<forall>i < Suc n. prop_corr W' Q (p i))
            \<and> (\<forall>i \<ge> Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i))
            \<and> (\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)
            \<and> W' Stop = 0"
      if  done_props: "\<forall>i < n. prop_corr W Q (p i)"
      and to_do_props: "\<forall>i \<ge> n. i < N \<longrightarrow> delta_prop_corr W Q (p i)"
      and n_lt_N: "n < N"
      and stop_inv: "W Stop = 0"
    for W n
  proof -
    have dpcn: "delta_prop_corr W Q (p n)" using to_do_props n_lt_N by blast

    from stop_inv
    have W'_stop: "(W(PropClock (p n) := x)) Stop = 0" for x by simp

    { assume a: "p n \<notin> Q"
      define W' where [simp]: "W' = (W(PropClock (p n) := 0))"
      have "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>PropDecoding (p (Suc n)), W'\<rangle>"
        apply (rule step_a.intros)
           apply (subst trans_of_def)
           apply (subst prop_decoding_def)
        using dpcn \<open>n < N\<close> apply auto[1]
        using a dpcn apply auto[1]
        unfolding inv_of_def using W'_stop
        by auto
      hence "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle>"
        using steps.step[OF step_a refl] by auto
      moreover
      have "\<forall>i < Suc n. prop_corr W' Q (p i)" using a dpcn done_props less_Suc_eq by auto
      moreover
      have "\<forall>i \<ge> Suc n. i < N \<longrightarrow>  delta_prop_corr W' Q (p i)" 
      proof - 
        from p_inj_on[simplified inj_on_def] 
        have 1: "\<forall>x y. x < N \<and> y < N \<longrightarrow> p x = p y \<longrightarrow> x = y" by blast
        have "\<And>i. Suc n \<le> i \<Longrightarrow> i < N \<Longrightarrow> p i \<noteq> p n"
          subgoal for i
            apply (subst (asm) Suc_le_eq)
            apply (rule notI)
            apply (frule less_trans, assumption)
            using 1 by blast
          done
        with to_do_props
        show "\<forall>i \<ge> Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i)" by simp
      qed
      moreover
      have "(\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)" by auto
      moreover
      have "W' Stop = 0" using stop_inv by auto
      ultimately
      have "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle> 
            \<and> (\<forall>i < Suc n. prop_corr W' Q (p i))
            \<and> (\<forall>i \<ge> Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i))
            \<and> (\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)
            \<and> W' Stop = 0" by blast
    }
    moreover
    { assume a:"p n \<in> Q"
      define W' where [simp]: "W' = (W(PropClock (p n) := 1))"
      have 1: "W (PropClock (p n)) - W Delta = 1 \<Longrightarrow> W \<turnstile> DEQ (PropClock (p n)) Delta 1"
        by (metis add.commute clock_val.intros(9) diff_add_cancel)
      
      have "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>PropDecoding (p (Suc n)), W'\<rangle>"
        apply (rule step_a.intros[where g = "DEQ (PropClock (p n)) Delta 1"])
        apply (subst trans_of_def)
           apply (subst prop_decoding_def)
        using dpcn \<open>n < N\<close> apply auto[1]
        using a conjunct1[OF dpcn] apply (intro 1) apply auto[1]
        unfolding inv_of_def using W'_stop by auto
      hence "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle>"
        using steps.step[OF step_a refl] by auto
      moreover
      have "\<forall>i < Suc n. prop_corr W' Q (p i)" using a dpcn  done_props less_Suc_eq by auto
      moreover
      have "\<forall>i \<ge> Suc n. i < N \<longrightarrow>  delta_prop_corr W' Q (p i)" 
      proof - 
        from p_inj_on[simplified inj_on_def] 
        have 1: "\<forall>x y. x < N \<and> y < N \<longrightarrow> p x = p y \<longrightarrow> x = y" by blast
        have "\<And>i. Suc n \<le> i \<Longrightarrow> i < N \<Longrightarrow> p i \<noteq> p n"
          subgoal for i
            apply (subst (asm) Suc_le_eq)
            apply (rule notI)
            apply (frule less_trans, assumption)
            using 1 by blast
          done
        with to_do_props
        show "\<forall>i \<ge> Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i)" by simp
      qed
      moreover
      have "(\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)" by auto
      moreover
      have "W' Stop = 0" using stop_inv by auto
      ultimately
      have "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle> 
            \<and> (\<forall>i < Suc n. prop_corr W' Q (p i))
            \<and> (\<forall>i \<ge> Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i))
            \<and> (\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)
            \<and> W' Stop = 0" by blast
    }
    ultimately
    show ?thesis by blast
  qed


  have propositional_decoding_strong: 
    "\<exists>W'. \<T> pd \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle> 
    \<and> (\<forall>i < Suc n. prop_corr W' Q (p i)) 
    \<and> (\<forall>i \<ge> Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i)) 
    \<and> (\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0" 
    if "n < N" for n
    using that
  proof (induction n)
    case 0
    have "\<forall>i < 0. prop_corr W Q (p i)" by simp
    moreover
    have "\<forall>i \<ge> 0. i < N \<longrightarrow> delta_prop_corr W Q (p i)" 
      using p_in_props_iff delta_prop_model_def prop_clocks by blast
    moreover
    have "delta_exec_model W E" using exec_clocks .
    moreover
    have "0 < N" using some_props .
    moreover
    have "W Stop = 0" using stop .
    ultimately
    show ?case using propositional_decoding_step by presburger
  next
    case (Suc n)
    then obtain W' where
      steps: "\<T> pd \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc n)), W'\<rangle>"
      and done_props: "\<forall>i<Suc n. prop_corr W' Q (p i)"
      and to_do_props: "\<forall>i\<ge>Suc n. i < N \<longrightarrow> delta_prop_corr W' Q (p i)"
      and other_inv: "(\<forall>c. \<not> is_propositional_clock c \<longrightarrow> W c = W' c)"
      and stop_inv: "W' Stop = 0" by auto
    from propositional_decoding_step[OF done_props to_do_props \<open>Suc n < N\<close> stop_inv]
    obtain W'' where
        steps': "\<T> pd \<turnstile> \<langle>PropDecoding (p (Suc n)), W'\<rangle> \<rightarrow>* \<langle>PropDecoding (p (Suc (Suc n))), W''\<rangle>"
        and other: "\<forall>i<Suc (Suc n). prop_corr W'' Q (p i)"
         "\<forall>i\<ge>Suc (Suc n). i < N \<longrightarrow> delta_prop_corr W'' Q (p i)"
        "(\<forall>c. \<not> is_propositional_clock c \<longrightarrow> W' c = W'' c)" 
        "W'' Stop = 0" by blast
    from steps_trans[OF steps steps'] other_inv other
    show ?case by auto
  qed
  
  
  have propositional_decoding: "\<exists>W'. \<T> pd \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p N), W'\<rangle> 
    \<and> prop_model W' Q
    \<and> (\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0" 
    using propositional_decoding_strong[of "N - 1"] Suc_diff_1[OF some_props] some_props
    prop_model_def[simplified props_pred] by auto

  have prop_dec_to_exec_dec: "\<T> pd \<turnstile> \<langle>PropDecoding (p N), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act 0), W\<rangle>" if "W Stop = 0" for W
    apply (rule steps.step)
     defer
     apply (rule steps.refl, rule step_a, rule step_a.intros)
       apply (subst trans_of_def, subst prop_decoding_to_exec_decoding_def)
       apply auto[1]
    unfolding true_const_def apply (auto simp: that)[1]
    unfolding inv_of_def apply (auto simp: that)[1]
    by simp
  
  have to_exec_decoding_start: "\<exists>W'. \<T> pd \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act 0), W'\<rangle> 
    \<and> prop_model W' Q
    \<and> delta_exec_model W' E 
    \<and> (\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0"
  proof -
    from propositional_decoding exec_clocks[simplified delta_exec_model_def] delta_exec_model_def
    obtain W' where 
    W': "\<T> pd \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>PropDecoding (p N), W'\<rangle>"
      "prop_model W' Q"
      "delta_exec_model W' E"
      "(\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)"
      "W' Stop = 0" by auto
    show ?thesis using steps_trans[OF W'(1) prop_dec_to_exec_dec[of W', OF W'(5)]] W' by blast                         
  qed


  have execution_decoding_step: 
    "\<exists>W'. \<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle> 
    \<and> (\<forall>i < Suc m. exec_corr W' E (act i)) 
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i)) 
    \<and> (\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0"
      if  done_acts: "\<forall>i < m. exec_corr W E (act i)"
      and to_do_acts: "\<forall>i \<ge> m. i < M \<longrightarrow> delta_exec_corr W E (act i)"
      and m_lim: "m < M"
      and stop_inv: "W Stop = 0" for m W
  proof -
    have decm: "delta_exec_corr W E (act m)" using to_do_acts m_lim by blast

    from stop_inv
    have W'_stop: "(W(Running (act m) := x)) Stop = 0" for x by simp

    { assume a: "act m \<notin> E"
      define W' where [simp]: "W' = (W(Running (act m) := 0))"
      have "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>ExecDecoding (act (Suc m)), W'\<rangle>"
        apply (rule step_a.intros)
           apply (subst trans_of_def)
           apply (subst exec_decoding_def)
        using decm \<open>m < M\<close> apply auto[1]
        using a decm apply auto[1]
        unfolding inv_of_def using W'_stop
        by auto
      hence "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle>"
        using steps.step[OF step_a refl] by auto
      moreover
      have "\<forall>i < Suc m. exec_corr W' E (act i)" using a decm done_acts less_Suc_eq by auto
      moreover
      have "\<forall>i \<ge> Suc m. i < M \<longrightarrow>  delta_exec_corr W' E (act i)" 
      proof - 
        from act_inj_on[simplified inj_on_def] 
        have 1: "\<forall>x y. x < M \<and> y < M \<longrightarrow> act x = act y \<longrightarrow> x = y" by blast
        have "\<And>i. Suc m \<le> i \<Longrightarrow> i < M \<Longrightarrow> act i \<noteq> act m"
          subgoal for i
            apply (subst (asm) Suc_le_eq)
            apply (rule notI)
            apply (frule less_trans, assumption)
            using 1 by blast
          done
        with to_do_acts
        show "\<forall>i \<ge> Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i)" by simp
      qed
      moreover
      have "(\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)" by auto
      moreover
      have "W' Stop = 0" using stop_inv by auto
      ultimately
      have "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle> 
      \<and> (\<forall>i < Suc m. exec_corr W' E (act i))
      \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i))
      \<and> (\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)
      \<and> W' Stop = 0" by blast
    }
    moreover
    { assume a: "act m \<in> E"
      define W' where [simp]: "W' = (W(Running (act m) := 1))"
      have 1: "W (Running (act m)) - W Delta = 1 \<Longrightarrow> W \<turnstile> DEQ (Running (act m)) Delta 1"
        by (metis add.commute clock_val.intros(9) diff_add_cancel)
      
      have "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>ExecDecoding (act (Suc m)), W'\<rangle>"
        apply (rule step_a.intros[where g = "DEQ (Running (act m)) Delta 1"])
           apply (subst trans_of_def)
           apply (subst exec_decoding_def)
        using decm \<open>m < M\<close> apply auto[1]
        apply (rule 1) using a decm apply blast
        unfolding inv_of_def using W'_stop
        by auto
      hence "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle>"
        using steps.step[OF step_a refl] by auto
      moreover
      have "\<forall>i < Suc m. exec_corr W' E (act i)" using a decm done_acts less_Suc_eq by auto
      moreover
      have "\<forall>i \<ge> Suc m. i < M \<longrightarrow>  delta_exec_corr W' E (act i)" 
      proof - 
        from act_inj_on[simplified inj_on_def] 
        have 1: "\<forall>x y. x < M \<and> y < M \<longrightarrow> act x = act y \<longrightarrow> x = y" by blast
        have "\<And>i. Suc m \<le> i \<Longrightarrow> i < M \<Longrightarrow> act i \<noteq> act m"
          subgoal for i
            apply (subst (asm) Suc_le_eq)
            apply (rule notI)
            apply (frule less_trans, assumption)
            using 1 by blast
          done
        with to_do_acts
        show "\<forall>i \<ge> Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i)" by simp
      qed
      moreover
      have "(\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)" by auto
      moreover
      have "W' Stop = 0" using stop_inv by auto
      ultimately
      have "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle> 
            \<and> (\<forall>i < Suc m. exec_corr W' E (act i))
            \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i))
            \<and> (\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)
            \<and> W' Stop = 0" by blast
    }
    ultimately
    show ?thesis by blast
  qed

  have execution_decoding_strong: "\<exists>W'. \<T> ed \<turnstile> \<langle>ExecDecoding (act 0), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle> 
    \<and> (\<forall>i < Suc m. exec_corr W' E (act i)) 
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i)) 
    \<and> (\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0"
    if to_do_acts: "delta_exec_model W E"
    and m_lim: "m < M"
    and stop_inv: "W Stop = 0"for m W
    using that
  proof (induction m)
    case 0
    have "\<forall>i < 0. exec_corr W E (act i)" using to_do_acts by simp
    moreover
    have "\<forall>i \<ge> 0. i < M \<longrightarrow> delta_exec_corr W E (act i)" using to_do_acts delta_exec_model_def act_pred by simp
    ultimately
    show ?case using execution_decoding_step stop_inv some_actions by presburger
  next
    case (Suc m)
    then obtain W' where
      step: "\<T> ed \<turnstile> \<langle>ExecDecoding (act 0), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc m)), W'\<rangle>"
      and "\<forall>i<Suc m. exec_corr W' E (act i)"
      "\<forall>i\<ge>Suc m. i < M \<longrightarrow> delta_exec_corr W' E (act i)"
      and other_inv:"(\<forall>c. \<not> is_exec_clock c \<longrightarrow> W c = W' c)"
      and "W' Stop = 0" by auto
    from execution_decoding_step[OF this(2,3) \<open>Suc m < M\<close>] this
    obtain W'' where
      W'': "\<T> ed \<turnstile> \<langle>ExecDecoding (act (Suc m)), W'\<rangle> \<rightarrow>* \<langle>ExecDecoding (act (Suc (Suc m))), W''\<rangle>"
        "\<forall>i<Suc (Suc m). exec_corr W'' E (act i)"
        "\<forall>i\<ge>Suc (Suc m). i < M \<longrightarrow> delta_exec_corr W'' E (act i)"
        "\<forall>c. \<not> is_exec_clock c \<longrightarrow> W' c = W'' c"
        "W'' Stop = 0" by auto
    from steps_trans[OF step(1) W''(1)] W'' other_inv
    show ?case by auto
  qed

  have exec_decoding: "\<exists>W'. \<T> ed \<turnstile> \<langle>ExecDecoding (act 0), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W'\<rangle> 
    \<and> exec_model W' E 
    \<and> (\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0"
    if dem: "delta_exec_model W E"
    and stop_inv: "W Stop = 0"for W
    using execution_decoding_strong[OF dem, of "M - 1", OF _ stop_inv] 
      Suc_diff_1[OF some_actions] some_actions exec_model_def[simplified act_pred] by simp


  have "le_ta (\<T> pd) \<T>" unfolding prob_automaton_def le_ta_def trans_of_def inv_of_def by simp
  from ta_superset[OF _ this] to_exec_decoding_start
  obtain W' where 
  W': "\<T> \<turnstile> \<langle>PropDecoding (p 0), W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act 0), W'\<rangle>"
    "prop_model W' Q"
    "delta_exec_model W' E"
    "(\<forall>c. \<not>(is_propositional_clock c) \<longrightarrow> W c = W' c)"
    "W' Stop = 0" by blast
  
  have "le_ta (\<T> ed) \<T>" unfolding prob_automaton_def le_ta_def trans_of_def inv_of_def by simp
  from ta_superset[OF _ this] exec_decoding W'
  obtain W'' where
    W'': "\<T> \<turnstile> \<langle>ExecDecoding (act 0), W'\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W''\<rangle>" 
    "exec_model W'' E" 
    "\<forall>c. \<not>(is_exec_clock c) \<longrightarrow> W' c = W'' c"
    "W'' Stop = 0" by metis
  with W'
  have pmW'': "prop_model W'' Q" unfolding prop_model_def by auto
  
  have invW'': "(\<forall>c. \<not>(is_boolean_clock c) \<longrightarrow> W c = W'' c)" 
  proof -
    have "\<not>(is_boolean_clock c) \<longrightarrow> \<not>(is_propositional_clock c)" for c by (cases c) simp+
    moreover
    have "\<not>(is_boolean_clock c) \<longrightarrow> \<not>(is_exec_clock c)" for c by (cases c) simp+
    ultimately
    show ?thesis using W'(4) W''(3) by auto
  qed
  
  show ?thesis using steps_trans[OF W'(1) W''(1)] W'' pmW'' invW'' by blast
qed

lemma main_to_dec_end: 
  assumes pc: "prop_model W Q"
      and ac: "exec_model W E"
      and delta: "W Delta = 0"
      and stop: "W Stop \<ge> 0"
    shows "\<exists>W'. \<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W'\<rangle> 
    \<and> prop_model W' Q \<and> exec_model W' E \<and> W' Stop = 0"
proof -
  from main_to_prop_decoding[OF pc ac delta stop]
  obtain W' where
    W': "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>PropDecoding (p 0), W'\<rangle>" 
    "delta_prop_model W' Q" 
    "delta_exec_model W' E" 
    "W' Stop = 0"
    by blast
  with boolean_state_decoding
  obtain W'' where
    W'': "\<T> \<turnstile> \<langle>PropDecoding (p 0), W'\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W''\<rangle>"
    "prop_model W'' Q" 
    "exec_model W'' E"
    "\<forall>c. \<not>(is_boolean_clock c) \<longrightarrow> W' c = W'' c"
    by blast
  from this(4) W'(4)
  have "W'' Stop = 0" by auto
  with steps_trans[OF W'(1) W''(1)] W''(2,3)
  show ?thesis by blast
qed

definition start_snap_sched_corr::"(('proposition, 'action) clock, 'time) cval 
  \<Rightarrow> 'snap_action state 
  \<Rightarrow> 'action 
  \<Rightarrow> bool" where
"start_snap_sched_corr W Q a \<equiv> (W (SchedStartSnap a) = 1 \<longleftrightarrow> (at_start a) \<in> Q) 
  \<and> (W (SchedStartSnap a) = 0 \<longleftrightarrow> (at_start a) \<notin> Q)"

definition end_snap_sched_corr::"(('proposition, 'action) clock, 'time) cval 
  \<Rightarrow> 'snap_action state 
  \<Rightarrow> 'action 
  \<Rightarrow> bool" where
"end_snap_sched_corr W Q a \<equiv> (W (SchedEndSnap a) = 1 \<longleftrightarrow> (at_end a) \<in> Q) 
  \<and> (W (SchedEndSnap a) = 0 \<longleftrightarrow> (at_end a) \<notin> Q)"

definition snap_exec_sched_corr::"(('proposition, 'action) clock, 'time) cval 
  \<Rightarrow> 'snap_action state
  \<Rightarrow> bool" where
"snap_exec_sched_corr W Q \<equiv> \<forall>a \<in> actions. start_snap_sched_corr W Q a \<and> end_snap_sched_corr W Q a"


fun is_snap_dec_clock::"('proposition, 'action) clock \<Rightarrow> bool" where
  "is_snap_dec_clock (SchedStartSnap _) = True"
| "is_snap_dec_clock (SchedEndSnap _) = True"
| "is_snap_dec_clock _ = False"

lemma duration_bound_lemma:
  assumes "W \<turnstile> true_const"
  assumes "satisfies_duration_bounds a (W (StartDur a))"
  shows "W \<turnstile> clock_duration_bounds a"
proof (cases "upper a")
  case None
  then show ?thesis 
    using assms satisfies_duration_bounds_def clock_duration_bounds_def assms(1)
    by (cases "lower a"; auto)
next
  case (Some lim)
  then show ?thesis 
    using assms satisfies_duration_bounds_def clock_duration_bounds_def 
    apply (cases "lower a"; cases lim)
    by auto
qed

definition decision_making_automaton ("\<T> dm") where
"decision_making_automaton = (decision_making, invs)"

lemma decision_making:
  assumes l_len: "l < length timepoint_list" 
      and MS_valid: "vss MS"
      and prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (ti l))"
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
      and stop: "W Stop = 0"
      and nm: "nm_happ_seq happ_seq"
      and fpl: "fp_\<pi>"
      and nso: "nso_\<pi>"
      and dp: "dp_\<pi>"
      and dv: "dv_\<pi>"
      and pap: "pap_\<pi>"
  shows "\<exists>W'. \<T> \<turnstile> \<langle>Decision (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act M)), W'\<rangle> 
    \<and> snap_exec_sched_corr W' (B (ti l))
    \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)"
proof -
  have W_sat_guard: "W \<turnstile> guard snap" 
       if snap_in_B: "snap \<in> B (ti l)"
      and prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (ti l))" 
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
      and stop: "W Stop = 0" for snap W
  proof -
    have "W \<turnstile> sep snap"
    proof -
      { fix b
        assume b: "b \<in> set (interfering_at_start snap)"
        hence b_in_act: "act b \<in> actions" unfolding interfering_at_start_def using act_img_actions by auto
        have "b \<in> {n. n < M \<and> (mutex_snap_action snap (at_start (act n)) \<or> snap = at_start (act n))}" 
          using b unfolding interfering_at_start_def by auto
        hence "\<epsilon> \<le> exec_time (at_start (act b)) (ti l)" using exec_time_and_epsilon[OF nm snap_in_B _ fpl] by blast
        hence "W \<turnstile> dconstraint.GE (StartDur (act b)) \<epsilon>" using start_durs[THEN bspec, OF b_in_act] by auto
      }
      hence "list_all (clock_val W) (start_constraints snap)" 
        unfolding start_constraints_def
        by (subst list_all_iff) auto
      hence "W \<turnstile> AND_ALL (start_constraints snap)" using AND_ALL_iff by blast
      moreover
      { fix b
        assume b: "b \<in> set (interfering_at_end snap)"
        hence b_in_act: "act b \<in> actions" unfolding interfering_at_end_def using act_img_actions by auto
        have "b \<in> {n. n < M \<and> (mutex_snap_action snap (at_end (act n)) \<or> snap = at_end (act n))}" 
          using b unfolding interfering_at_end_def by auto
        hence "\<epsilon> \<le> exec_time (at_end (act b)) (ti l)" using exec_time_and_epsilon[OF nm snap_in_B _ fpl] by blast
        hence "W \<turnstile> dconstraint.GE (EndDur (act b)) \<epsilon>" using end_durs b_in_act by auto
      }
      hence "list_all (clock_val W) (end_constraints snap)" 
        unfolding end_constraints_def
        by (subst list_all_iff) auto
      hence "W \<turnstile> AND_ALL (end_constraints snap)" using AND_ALL_iff by blast
      ultimately
      show ?thesis unfolding sep_def using AND_ALL_iff list_all_append by blast
    qed
    moreover
    have "W \<turnstile> (pre_constraint snap)"
    proof -
      { fix c
        assume "c \<in> set (pre_clocks snap)"
        then obtain pr where
          pr: "pr \<in> set (prop_list (pre snap))"
          and cpr: "c = PropClock pr" using pre_clocks_def by auto
        moreover
        have "finite (prop_numbers (pre snap))" by simp
        ultimately
        have pr_in_pre: "pr \<in> pre snap" using set_sorted_list_of_set unfolding prop_list_def by auto
        hence "pr \<in> MS l" using MS_valid[simplified valid_state_sequence_def] l_len snap_in_B by (auto simp: Let_def)
        moreover
        have "\<exists>a \<in> actions. snap = at_start a \<or> snap = at_end a" using snap_in_B[simplified happ_at_def]  in_happ_seqE
          pap[simplified plan_actions_in_problem_def] by blast
        hence "pr \<in> props" using wf_acts pr_in_pre act_img_actions by auto
        ultimately
        have "W c = 1" using prop_clocks cpr unfolding prop_model_def by blast
      }
      hence "W \<turnstile> AND_ALL (map (\<lambda>c. EQ c 1) (pre_clocks snap))" 
        unfolding AND_ALL_iff list_all_iff by auto
      thus ?thesis using pre_constraint_def by simp
    qed
    ultimately
    show "W \<turnstile> guard snap" unfolding guard_def by blast
  qed

  have at_start_step: "\<exists>W'. \<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_end (act m)), W'\<rangle>
        \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (ti l)) (act n))
        \<and> (\<forall>n < m. end_snap_sched_corr W' (B (ti l)) (act n))
        \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)" 
    if prop_clocks: "prop_model W (MS l)"
    and exec_clocks: "exec_model W (ES (ti l))"
    and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
    and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
    and stop: "W Stop = 0"
    and m: "m < M"
    and s_snap_corr: "\<forall>n < m. start_snap_sched_corr W (B (ti l)) (act n)"
    and e_snap_corr: "\<forall>n < m. end_snap_sched_corr W (B (ti l)) (act n)"
  for W m
  proof (cases "at_start (act m) \<in> B (ti l)")
    case True
    have trans: "(Decision (at_start (act m)), guard_at_start (act m), Unit, [(SchedStartSnap (act m), 1)], Decision (at_end (act m))) \<in> trans_of \<T> dm"
      unfolding decision_making_automaton_def decision_making_def trans_of_def using m by auto
    
    have guard_sat: "W \<turnstile> guard_at_start (act m)" 
    proof -
      have "W \<turnstile> guard (at_start (act m))" using W_sat_guard[OF True prop_clocks exec_clocks start_durs end_durs stop] .
      moreover 
      have "act m \<in> actions" using act_img_actions m by blast
      hence "W (Running (act m)) = 0" using exec_clocks[simplified exec_model_def] 
        not_executing_when_starting[OF True] nso dp pap
        by blast
      ultimately
      show ?thesis using guard_at_start_def by auto
    qed
    
    define W' where "W' = clock_set [(SchedStartSnap (act m), 1)] W" 
    have "\<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_end (act m)), W'\<rangle>"
      apply (rule step_a)
      apply (rule step_a.intros[OF trans])
        apply (rule guard_sat)
       apply (subst inv_of_def)
       apply (subst decision_making_automaton_def)
      by (auto simp: stop W'_def)
    moreover
    {
      have "start_snap_sched_corr W' (B (ti l)) (act m)" using True unfolding W'_def start_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. start_snap_sched_corr W' (B (ti l)) (act n))" using s_snap_corr unfolding start_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. start_snap_sched_corr W' (B (ti l)) (act n))" using less_antisym by blast
    }
    moreover
    { 
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (ti l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
    }
    moreover
    have "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c)" unfolding W'_def by simp
    ultimately
    show ?thesis by meson
  next
    case False
    have trans: "(Decision (at_start (act m)), true_const, Unit, [(SchedStartSnap (act m), 0)], Decision (at_end (act m))) \<in> trans_of \<T> dm"
      unfolding decision_making_automaton_def decision_making_def trans_of_def using m by auto
    define W' where "W' = W((SchedStartSnap (act m)) := 0)"
    have "\<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_end (act m)), W'\<rangle>"
      apply (rule step_a)
      apply (rule step_a.intros[OF trans])
      by (auto simp: true_const_def inv_of_def decision_making_automaton_def stop W'_def)
    moreover
    {
      have "start_snap_sched_corr W' (B (ti l)) (act m)" using False unfolding W'_def start_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. start_snap_sched_corr W' (B (ti l)) (act n))" using s_snap_corr unfolding start_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. start_snap_sched_corr W' (B (ti l)) (act n))" using less_antisym by blast
    }
    moreover
    { 
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (ti l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
    }
    moreover
    have "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c)" unfolding W'_def by simp
    ultimately
    show ?thesis by meson
  qed

  have at_end_step: "\<exists>W'. \<T> dm \<turnstile> \<langle>Decision (at_end (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_start (act (Suc m))), W'\<rangle>
        \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (ti l)) (act n))
        \<and> (\<forall>n < (Suc m). end_snap_sched_corr W' (B (ti l)) (act n))
        \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)" 
    if prop_clocks: "prop_model W (MS l)"
    and exec_clocks: "exec_model W (ES (ti l))"
    and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
    and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
    and stop: "W Stop = 0"
    and m: "m < M"
    and s_snap_corr: "\<forall>n < Suc m. start_snap_sched_corr W (B (ti l)) (act n)"
    and e_snap_corr: "\<forall>n < m. end_snap_sched_corr W (B (ti l)) (act n)"
  for W m
  proof (cases "at_end (act m) \<in> B (ti l)")
    case True
    
    have act_m_in_actions: "act m \<in> actions" using m act_img_actions by blast
  
    have trans: "(Decision (at_end (act m)), guard_at_end (act m), Unit, [(SchedEndSnap (act m), 1)], Decision (at_start (act (Suc m)))) \<in> trans_of \<T> dm"
      unfolding decision_making_automaton_def decision_making_def trans_of_def using m by auto

    have W_tc: "W \<turnstile> true_const" unfolding true_const_def using stop by auto
    
    have guard_sat: "W \<turnstile> guard_at_end (act m)"
    proof -
      have "W \<turnstile> guard (at_end (act m))" using W_sat_guard[OF True prop_clocks exec_clocks start_durs end_durs stop] .
      moreover
      have "satisfies_duration_bounds (act m) (exec_time (at_start (act m)) (ti l))" using exec_time_sat_dur_const[OF True act_m_in_actions nso dp pap dv] .
      hence "satisfies_duration_bounds (act m) (W (StartDur (act m)))" using start_durs act_m_in_actions by simp
      hence "W \<turnstile> clock_duration_bounds (act m)" using duration_bound_lemma W_tc by auto
      moreover
      have "W \<turnstile> EQ (Running (act m)) 1" using executing_when_ending[OF True _ nso dp pap] exec_clocks
        unfolding exec_model_def using act_m_in_actions by blast
      ultimately
      show "W \<turnstile> guard_at_end (act m)" unfolding guard_at_end_def by fast
    qed
    
    define W' where "W' = clock_set [(SchedEndSnap (act m), 1)] W" 
    have "\<T> dm \<turnstile> \<langle>Decision (at_end (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_start (act (Suc m))), W'\<rangle>"
      apply (rule step_a)
      apply (rule step_a.intros[OF trans])
        apply (rule guard_sat)
       apply (subst inv_of_def)
       apply (subst decision_making_automaton_def)
      by (auto simp: stop W'_def)
    moreover
    {
      have "\<forall>n < Suc m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "\<forall>n < Suc m. start_snap_sched_corr W' (B (ti l)) (act n)"  using s_snap_corr unfolding start_snap_sched_corr_def by auto
    }
    moreover
    {
      have "end_snap_sched_corr W' (B (ti l)) (act m)" using True unfolding W'_def end_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (ti l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. end_snap_sched_corr W' (B (ti l)) (act n))" using less_antisym by blast
    }
    moreover
    have "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c)" unfolding W'_def by simp
    ultimately
    show ?thesis by meson
  next
    case False
    have trans: "(Decision (at_end (act m)), true_const, Unit, [(SchedEndSnap (act m), 0)], Decision (at_start (act (Suc m)))) \<in> trans_of \<T> dm"
      unfolding decision_making_automaton_def decision_making_def trans_of_def using m by auto
    define W' where "W' = W((SchedEndSnap (act m)) := 0)"
    have "\<T> dm \<turnstile> \<langle>Decision (at_end (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_start (act (Suc m))), W'\<rangle>"
      apply (rule step_a)
      apply (rule step_a.intros[OF trans])
      by (auto simp: true_const_def inv_of_def decision_making_automaton_def stop W'_def)
    moreover
    {
      have "\<forall>n < Suc m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "\<forall>n < Suc m. start_snap_sched_corr W' (B (ti l)) (act n)"  using s_snap_corr unfolding start_snap_sched_corr_def by auto
    }
    moreover
    {
      have "end_snap_sched_corr W' (B (ti l)) (act m)" using False unfolding W'_def end_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (ti l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. end_snap_sched_corr W' (B (ti l)) (act n))" using less_antisym by blast
    }
    moreover
    have "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c)" unfolding W'_def by simp
    ultimately
    show ?thesis by meson
  qed
  
  have decision_steps: "\<exists>W'. \<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act (Suc m))), W'\<rangle>
          \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (ti l)) (act n))
          \<and> (\<forall>n < (Suc m). end_snap_sched_corr W' (B (ti l)) (act n))
          \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)" 
      if prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (ti l))"
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
      and stop: "W Stop = 0"
      and m: "m < M"
      and s_snap_corr: "\<forall>n < m. start_snap_sched_corr W (B (ti l)) (act n)"
      and e_snap_corr: "\<forall>n < m. end_snap_sched_corr W (B (ti l)) (act n)"
    for m W
  proof -
  
    from at_start_step[OF that]
    obtain W' where
      W': "\<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_end (act m)),W'\<rangle>"
      and s_snap_corr': "\<forall>n<Suc m. start_snap_sched_corr W' (B (ti l)) (act n)"
      and e_snap_corr': "\<forall>n<m. end_snap_sched_corr W' (B (ti l)) (act n)"
      and dec: "\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c" by force
    moreover
    from prop_clocks exec_clocks start_durs end_durs stop and dec
    have prop_clocks': "prop_model W' (MS l)" 
      and exec_clocks': "exec_model W' (ES (ti l))"
      and start_durs': "\<forall>a \<in> actions. W' (StartDur a) = exec_time (at_start a) (ti l)"
      and end_durs': "\<forall>a \<in> actions. W' (EndDur a) = exec_time (at_end a) (ti l)"
      and stop': "W' Stop = 0"
      unfolding prop_model_def exec_model_def by auto
    ultimately 
    obtain W'' where 
      W'': "\<T> dm \<turnstile> \<langle>Decision (at_end (act m)), W'\<rangle> \<rightarrow> \<langle>Decision (at_start (act (Suc m))), W''\<rangle>
          \<and> (\<forall>n < (Suc m). start_snap_sched_corr W'' (B (ti l)) (act n))
          \<and> (\<forall>n < (Suc m). end_snap_sched_corr W'' (B (ti l)) (act n))
          \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W' c = W'' c)" 
      using m at_end_step by presburger
    moreover
    have "\<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act (Suc m))), W''\<rangle>"
      apply (rule steps.step[OF _ steps.step[OF _ steps.refl]])
      using W' W'' by blast+
    moreover
    have "\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W'' c" using dec W'' by simp
    ultimately
    show ?thesis by blast
  qed

  have decision_steps': "\<exists>W'. \<T> dm \<turnstile> \<langle>Decision (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act (Suc m))), W'\<rangle>
          \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)
          \<and> prop_model W' (MS l)
          \<and> exec_model W' (ES (ti l))
          \<and> (\<forall>a \<in> actions. W' (StartDur a) = exec_time (at_start a) (ti l))
          \<and> (\<forall>a \<in> actions. W' (EndDur a) = exec_time (at_end a) (ti l))
          \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (ti l)) (act n))
          \<and> (\<forall>n < (Suc m). end_snap_sched_corr W' (B (ti l)) (act n))
          \<and> W' Stop = 0"
      if prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (ti l))"
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
      and stop: "W Stop = 0"
      and m: "m < M"
      and s_snap_corr: "\<forall>n < m. start_snap_sched_corr W (B (ti l)) (act n)"
      and e_snap_corr: "\<forall>n < m. end_snap_sched_corr W (B (ti l)) (act n)"
    for m W
    apply (insert decision_steps[OF that])
    apply (erule exE)
    subgoal for W'
      apply (rule exI[where x = W'])
      using that by (auto simp: prop_model_def exec_model_def)
    done

  have decision_making_strong: "\<exists>W'. \<T> dm \<turnstile> \<langle>Decision (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act (Suc m))), W'\<rangle>
    \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)
    \<and> prop_model W' (MS l)
    \<and> exec_model W' (ES (ti l))
    \<and> (\<forall>a \<in> actions. W' (StartDur a) = exec_time (at_start a) (ti l))
    \<and> (\<forall>a \<in> actions. W' (EndDur a) = exec_time (at_end a) (ti l))
    \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (ti l)) (act n))
    \<and> (\<forall>n < (Suc m). end_snap_sched_corr W' (B (ti l)) (act n))
    \<and> W' Stop = 0" if "m < M" for m
    using that
    proof (induction m)
      case 0
      from decision_steps'[OF prop_clocks exec_clocks start_durs end_durs stop 0]
      show ?case by auto
    next
      case (Suc m)
      then obtain W' where
        W': "\<T> dm \<turnstile> \<langle>Decision (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act (Suc m))), W'\<rangle>"
         "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c) \<and>
         prop_model W' (MS l) \<and>
         exec_model W' (ES (ti l)) \<and>
         (\<forall>a\<in>actions. W' (StartDur a) = exec_time (at_start a) (ti l)) \<and>
         (\<forall>a\<in>actions. W' (EndDur a) = exec_time (at_end a) (ti l)) \<and>
         (\<forall>n<Suc m. start_snap_sched_corr W' (B (ti l)) (act n)) \<and>
         (\<forall>n<Suc m. end_snap_sched_corr W' (B (ti l)) (act n)) \<and> 
         W' Stop = 0" by auto
      with decision_steps' \<open>Suc m < M\<close>
      obtain W'' where
        W'': "\<T> dm \<turnstile> \<langle>Decision (at_start (act (Suc m))), W'\<rangle> \<rightarrow>* \<langle>Decision (at_start (act (Suc (Suc m)))), W''\<rangle> \<and>
         (\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W'' c) \<and>
         prop_model W'' (MS l) \<and>
         exec_model W'' (ES (ti l)) \<and>
         (\<forall>a\<in>actions. W'' (StartDur a) = exec_time (at_start a) (ti l)) \<and>
         (\<forall>a\<in>actions. W'' (EndDur a) = exec_time (at_end a) (ti l)) \<and>
         (\<forall>n<Suc (Suc m). start_snap_sched_corr W'' (B (ti l)) (act n)) \<and>
         (\<forall>n<Suc (Suc m). end_snap_sched_corr W'' (B (ti l)) (act n)) \<and> 
         W'' Stop = 0" by presburger
      from this[THEN conjunct2] steps_trans[OF W'(1) this[THEN conjunct1]] 
      show ?case by auto
    qed
    
    obtain W' where
      W': "\<T> dm \<turnstile> \<langle>Decision (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act M)), W'\<rangle> \<and>
       (\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c) \<and>
       (\<forall>n< M. start_snap_sched_corr W' (B (ti l)) (act n)) \<and>
       (\<forall>n< M. end_snap_sched_corr W' (B (ti l)) (act n))"
      using some_actions decision_making_strong[of "M - 1"] by auto
    moreover
    have lt: "le_ta \<T> dm \<T>" unfolding prob_automaton_def decision_making_automaton_def le_ta_def trans_of_def inv_of_def by auto
    moreover
    have "\<forall>a \<in> actions. start_snap_sched_corr W' (B (ti l)) a" using W' act_pred by simp
    moreover
    have "\<forall>a \<in> actions. end_snap_sched_corr W' (B (ti l)) a" using W' act_pred by simp
    ultimately
    show ?thesis unfolding snap_exec_sched_corr_def using ta_superset[OF _ lt] by meson
  qed


definition execution_automaton ("\<T> e") where
"execution_automaton = (execution, invs)"

definition conditionally_apply_snap where 
"conditionally_apply_snap S s Q \<equiv> if (s \<in> S) then (Q - dels s) \<union> adds s else Q"

definition conditionally_apply_action where
"conditionally_apply_action S a \<equiv> conditionally_apply_snap S (at_end a) o conditionally_apply_snap S (at_start a)"

fun is_execution_invariant_clock::"('proposition, 'action) clock \<Rightarrow> bool" where
  "is_execution_invariant_clock (SchedStartSnap _) = True"
| "is_execution_invariant_clock (SchedEndSnap _) = True"
| "is_execution_invariant_clock Stop = True"
| "is_execution_invariant_clock Delta = True"
| "is_execution_invariant_clock _ = False"


lemma sim_snap_exec:
  assumes prop_model: "prop_model W Q"
  and snap_in_problem: "snap \<in> snap_actions"
shows "prop_model (clock_set (effects snap) W) ((Q - dels snap) \<union> adds snap)" (is "prop_model ?W' ?Q'")
proof -
  have "prop_corr ?W' ?Q' pr" if pr_in_props: "pr \<in> props" for pr
  proof (cases "pr \<in> ?Q'")
    case True
    have ds_in_props: "(dels snap) - (adds snap) \<subseteq> props" 
     and as_in_props: "adds snap \<subseteq> props" using wf_acts snap_in_problem snap_actions_def by auto
    from True
    consider "pr \<in> Q \<and> pr \<notin> dels snap" | "pr \<in> adds snap" by auto
    then show ?thesis 
    proof cases
      case 1
      with set_prop_list ds_in_props
      have "pr \<notin> set (prop_list ((dels snap) - (adds snap)))" by blast
      hence "\<forall>n \<noteq> 1. (PropClock pr, n) \<notin> set (effects snap)" unfolding effects_def add_effects_def del_effects_def by auto
      hence "\<forall>n. (PropClock pr, n) \<in> set (effects snap) \<longrightarrow> n = 1" unfolding at_start_effects_def by auto
      moreover
      have "W (PropClock pr) = 1" using prop_model 1 pr_in_props unfolding prop_model_def by blast
      ultimately
      have "?W' (PropClock pr) = 1" using clock_set_all_cases by metis
      with 1
      show ?thesis by simp
    next
      case 2
      with set_prop_list ds_in_props
      have "pr \<notin> set (prop_list ((dels snap) - (adds snap)))" by simp
      hence all: "\<forall>n. (PropClock pr, n) \<in> set (effects snap) \<longrightarrow> n = 1" 
        unfolding at_start_effects_def effects_def add_effects_def del_effects_def by auto
      moreover
      from set_prop_list as_in_props 2
      have "pr \<in> set (prop_list (adds snap))" by blast
      hence ex: "(PropClock pr, 1) \<in> set (effects snap)" 
        unfolding at_start_effects_def effects_def add_effects_def del_effects_def by auto
      ultimately
      show ?thesis 
        using 2 clock_set_certain[of "PropClock pr" "effects snap" "1"] by simp
    qed
  next
    case False
    hence not_in_adds: "pr \<notin> adds snap" by blast
    moreover
    have "adds snap \<subseteq> props" using wf_acts snap_in_problem snap_actions_def by auto
    ultimately
    have "pr \<notin> set (prop_list (adds snap))" using set_prop_list by simp
    hence all_0: "\<forall>n. (PropClock pr, n) \<in> set (effects snap) \<longrightarrow> n = 0" 
      unfolding at_start_effects_def effects_def add_effects_def del_effects_def by fastforce
    
    consider "pr \<notin> Q" | "pr \<in> dels snap" using False  by blast
    thus ?thesis 
    proof cases
      case 1
      with prop_model pr_in_props
      have "W (PropClock pr) = 0" unfolding prop_model_def by blast
      with all_0 False
      show ?thesis using clock_set_all_cases[of "PropClock pr" "effects snap" 0 W] by auto
    next
      case 2
      have "(dels snap) - (adds snap) \<subseteq> props" using wf_acts snap_in_problem snap_actions_def by auto
      with 2 not_in_adds
      have "pr \<in> set (prop_list (dels snap - (adds snap)))" 
        using set_prop_list by auto
      hence "(PropClock pr, 0) \<in> set (effects snap)" unfolding at_start_effects_def effects_def del_effects_def by auto
      with all_0 False
      show ?thesis using clock_set_certain[of "PropClock pr" "effects snap" 0]  by auto
    qed
  qed 
  thus ?thesis unfolding prop_model_def by blast
qed

lemma conditional_application_is_application:
  assumes "\<forall>a b. a \<in> S \<and> b \<in> S \<and> a \<noteq> b \<longrightarrow> \<not>(mutex_snap_action a b)"
      and "S \<subseteq> snap_actions"
      and "m \<le> M"
      and "\<forall>a \<in> actions. \<not>(at_start a \<in> S \<and> at_end a \<in> S)"
  shows "foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<m] = apply_effects Q (limited_snap_action_set S m)"
  using assms
proof (induction m)
  case 0
  have "[0..<0] = Nil" by simp
  moreover
  have "limited_snap_action_set S 0 = {}" unfolding limited_snap_action_set_def by auto
  ultimately
  show ?case unfolding apply_effects_def by simp
next
  case (Suc m)
  have inter: "\<Union> (adds ` (limited_snap_action_set S m)) \<inter> dels s = {}" if 
    s_in_S: "s \<in> S" and 
    diff: "s \<notin> (limited_snap_action_set S m)" for s
  proof -
    have "adds b \<inter> dels s = {}" if "b \<in> limited_snap_action_set S m" for b
      proof -
        from Suc
        have "\<forall>a b. a \<in> S \<and> b \<in> S \<and> a \<noteq> b \<longrightarrow> \<not> mutex_snap_action a b " by blast
        moreover
        have "b \<in> S" using limited_snap_action_subset that by blast
        moreover
        have "s \<noteq> b" using diff that by blast
        ultimately
        have "\<not> mutex_snap_action s b" using diff s_in_S by auto
        thus ?thesis unfolding mutex_snap_action_def by auto
      qed
      thus ?thesis by blast
    qed

  
    have snaps_disj: "snaps (act i) \<inter> snaps (act j) = {}" if 
      "i \<noteq> j"
      "i < M"
      "j < M" for i j
    proof -
      from act_inj_on_spec that
      have 1: "act i \<noteq> act j" by force
      have 2: "act i \<in> actions" using that act_img_actions by auto
      have 3: "act j \<in> actions" using that act_img_actions by auto
      
      have "at_start (act i) \<noteq> at_end (act j)" using snaps_disj 2 3 by blast
      moreover
      have "at_end (act i) \<noteq> at_start (act j)" using snaps_disj 2 3 by blast
      moreover
      have "at_start (act i) \<noteq> at_start (act j)" using 1 2 3 at_start_inj_on unfolding inj_on_def by auto
      moreover
      have "at_end (act i) \<noteq> at_end (act j)" using 1 2 3 at_end_inj_on unfolding inj_on_def by auto
      ultimately
      show ?thesis by simp
    qed

  have m_in_actions: "act m \<in> actions" using Suc(4) act_img_actions by auto
  show ?case 
  proof (cases "at_start (act m) \<in> S"; cases "at_end (act m) \<in> S")
    assume "at_start (act m) \<in> S" "at_end (act m) \<in> S"
    hence False using m_in_actions Suc(5) by blast
    thus ?thesis ..
  next
    assume a: "at_start (act m) \<in> S" "at_end (act m) \<notin> S"
    have diff: "at_start (act m) \<notin> limited_snap_action_set S m"
    proof -
      have "b \<noteq> at_start (act m)" if b: "b \<in> limited_snap_action_set S m" for b
      proof -
        from that
        obtain i where
          b: "b = at_start (act i) \<or> b = at_end (act i)"
          "i < m" unfolding limited_snap_action_set_def by blast
        thus ?thesis using snaps_disj \<open>Suc m \<le> M\<close> by auto
      qed
      thus ?thesis by auto
    qed
  
    have lim_inc: "(limited_snap_action_set S m) \<union> {at_start (act m)} = limited_snap_action_set S (Suc m)" 
    proof (rule equalityI; rule subsetI)
      fix x 
      assume "x \<in> limited_snap_action_set S m \<union> {at_start (act m)}"
      then
      consider "x \<in> limited_snap_action_set S m" | "x = at_start (act m)" by blast
      thus "x \<in> limited_snap_action_set S (Suc m)" 
        apply cases
        using limited_snap_action_set_mono apply auto[1]
        unfolding limited_snap_action_set_def using a(1) by blast
    next
      fix x
      assume x: "x \<in> limited_snap_action_set S (Suc m)" 
      from this[simplified limited_snap_action_set_def]
      obtain i where
        i: "i < Suc m \<and> (at_start (act i) = x \<or> at_end (act i) = x)"
        unfolding limited_snap_action_set_def by blast
      moreover
      from x 
      have x_in_S: "x \<in> S" using limited_snap_action_subset by blast
      ultimately
      have "at_end (act i) = x \<longrightarrow> i < m" using a(2) using less_SucE by blast
      with i
      consider "i < m \<and> at_start (act i) = x" | "at_start (act m) = x" | "i < m \<and> at_end (act i) = x" using not_less_less_Suc_eq by blast
      thus "x \<in> limited_snap_action_set S m \<union> {at_start (act m)}" 
        apply cases unfolding limited_snap_action_set_def using x_in_S by auto
    qed

    
    have "foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<Suc m] 
      = conditionally_apply_snap S (at_start (act m)) (foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<m])"
      using a conditionally_apply_snap_def conditionally_apply_action_def by auto
    also have "...  = conditionally_apply_snap S (at_start (act m)) (apply_effects Q (limited_snap_action_set S m))" using Suc by simp
    also have  "... = ((apply_effects Q (limited_snap_action_set S m)) - dels (at_start (act m))) \<union> adds (at_start (act m))"
      unfolding conditionally_apply_snap_def using a by simp
    also have "... = (Q - \<Union> (dels ` (limited_snap_action_set S m))) \<union> \<Union> (adds ` (limited_snap_action_set S m)) - dels (at_start (act m)) \<union> adds (at_start (act m))" unfolding apply_effects_def by blast
    also have "... = (Q - \<Union> (dels ` (limited_snap_action_set S m)) - dels (at_start (act m))) \<union> \<Union> (adds ` (limited_snap_action_set S m)) \<union> adds (at_start (act m))" using inter[OF a(1) diff] by blast
    also have "... = (Q - \<Union> (dels ` (limited_snap_action_set S (Suc m)))) \<union> \<Union> (adds ` (limited_snap_action_set S (Suc m)))" using lim_inc by blast
    finally show ?thesis unfolding apply_effects_def by blast
  next
    assume a: "at_start (act m) \<notin> S" "at_end (act m) \<in> S"
    have diff: "at_end (act m) \<notin> limited_snap_action_set S m"
    proof -
      have "b \<noteq> at_end (act m)" if b: "b \<in> limited_snap_action_set S m" for b
      proof -
        from that
        obtain i where
          b: "b = at_start (act i) \<or> b = at_end (act i)"
          "i < m" unfolding limited_snap_action_set_def by blast
        thus ?thesis using snaps_disj \<open>Suc m \<le> M\<close> by auto
      qed
      thus ?thesis by auto
    qed

  
    have lim_inc: "(limited_snap_action_set S m) \<union> {at_end (act m)} = limited_snap_action_set S (Suc m)" 
    proof (rule equalityI; rule subsetI)
      fix x 
      assume "x \<in> limited_snap_action_set S m \<union> {at_end (act m)}"
      then
      consider "x \<in> limited_snap_action_set S m" | "x = at_end (act m)" by blast
      thus "x \<in> limited_snap_action_set S (Suc m)" 
        apply cases
        using limited_snap_action_set_mono apply auto[1]
        unfolding limited_snap_action_set_def using a(2) by blast
    next
      fix x
      assume x: "x \<in> limited_snap_action_set S (Suc m)" 
      from this[simplified limited_snap_action_set_def]
      obtain i where
        i: "i < Suc m \<and> (at_start (act i) = x \<or> at_end (act i) = x)"
        unfolding limited_snap_action_set_def by blast
      moreover
      from x 
      have x_in_S: "x \<in> S" using limited_snap_action_subset by blast
      ultimately
      have "at_start (act i) = x \<longrightarrow> i < m" using a(1) using less_SucE by blast
      with i
      consider "i < m \<and> at_start (act i) = x" | "at_end (act m) = x" | "i < m \<and> at_end (act i) = x" using not_less_less_Suc_eq by blast
      thus "x \<in> limited_snap_action_set S m \<union> {at_end (act m)}" 
        apply cases unfolding limited_snap_action_set_def using x_in_S by auto
    qed

    
    have "foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<Suc m] 
      = conditionally_apply_snap S (at_end (act m)) (foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<m])"
      using a conditionally_apply_snap_def conditionally_apply_action_def by auto
    also have "...  = conditionally_apply_snap S (at_end (act m)) (apply_effects Q (limited_snap_action_set S m))" using Suc by simp
    also have  "... = ((apply_effects Q (limited_snap_action_set S m)) - dels (at_end (act m))) \<union> adds (at_end (act m))"
      unfolding conditionally_apply_snap_def using a by simp
    also have "... = (Q - \<Union> (dels ` (limited_snap_action_set S m))) \<union> \<Union> (adds ` (limited_snap_action_set S m)) - dels (at_end (act m)) \<union> adds (at_end (act m))" unfolding apply_effects_def by blast
    also have "... = (Q - \<Union> (dels ` (limited_snap_action_set S m)) - dels (at_end (act m))) \<union> \<Union> (adds ` (limited_snap_action_set S m)) \<union> adds (at_end (act m))" using inter[OF a(2) diff] by blast
    also have "... = (Q - \<Union> (dels ` (limited_snap_action_set S (Suc m)))) \<union> \<Union> (adds ` (limited_snap_action_set S (Suc m)))" using lim_inc by blast
    finally show ?thesis unfolding apply_effects_def by blast
  next 
    assume a: "at_start (act m) \<notin> S" "at_end (act m) \<notin> S"
    have 1: "foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<Suc m] = conditionally_apply_action S (act m) (foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<m])"
      by simp
    have l: "foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<Suc m]  = foldl (\<lambda>p i. conditionally_apply_action S (act i) p) Q [0..<m]"
      using a apply (subst 1, subst conditionally_apply_action_def)
      unfolding conditionally_apply_snap_def by auto
    moreover
    have "limited_snap_action_set S (Suc m) \<subseteq> limited_snap_action_set S m" 
    proof (rule subsetI)
      fix x 
      assume a': "x \<in> limited_snap_action_set S (Suc m)"
      then obtain i where
        i: "i < Suc m \<and> (at_start (act i) \<in> S \<and> at_start (act i) = x \<or> at_end (act i) \<in> S \<and> at_end(act i) = x)" unfolding limited_snap_action_set_def by blast
      with a
      have "i \<noteq> m" by blast
      with \<open>Suc m \<le> M\<close> act_inj_on_spec i
      have "i < m" by auto
      thus "x \<in> limited_snap_action_set S m" using i unfolding limited_snap_action_set_def by blast
    qed
    hence r: "limited_snap_action_set S (Suc m) = limited_snap_action_set S m" using limited_snap_action_set_mono by blast
    ultimately
    show ?thesis using Suc by simp
  qed
qed

lemma execution:
  assumes l_len: "l < length timepoint_list" 
      and MS_valid: "vss MS"
      and prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (ti l))"
      and snap_exec_sched: "snap_exec_sched_corr W (B (ti l))"
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (ti l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (ti l)"
      and stop: "W Stop = 0"
      and nm: "nm_happ_seq happ_seq"
      and fpl: "fp_\<pi>"
      and nso: "nso_\<pi>"
      and dp: "dp_\<pi>"
      and dv: "dv_\<pi>"
      and pap: "pap_\<pi>"
  shows "\<exists>W'. \<T> \<turnstile> \<langle>Execution (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act M)), W'\<rangle> 
    \<and> prop_model W' (MS (Suc l))
    \<and> exec_model W' (IES (ti l))
    \<and> (\<forall>a \<in> actions. W' (StartDur a) = exec_time' (at_start a) (ti l))
    \<and> (\<forall>a \<in> actions. W' (EndDur a) = exec_time' (at_end a) (ti l))
    \<and> (\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)
    \<and> W' Stop = 0"
proof -

  have execution_step: "\<exists>W'. \<T> e\<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle>
    \<and> prop_model W' (conditionally_apply_action (B (ti l)) (act m) Q)
    \<and> (\<forall>i < Suc m. exec_corr W' (IES (ti l)) (act i))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i))
    \<and> (\<forall>i < Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l))
    \<and> (\<forall>i < Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))
    \<and> (\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)"
    if prop_model:      "prop_model W Q"
      and exec_corr':   "\<forall>i < m. exec_corr W (IES (ti l)) (act i)"
      and exec_corr:    "\<forall>i \<ge> m. i < M \<longrightarrow> exec_corr W (ES (ti l)) (act i)"
      and start_durs':  "\<forall>i < m. W (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)"
      and end_durs':    "\<forall>i < m. W (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)"
      and start_durs:   "\<forall>i \<ge> m. i < M \<longrightarrow> W (StartDur (act i)) = exec_time (at_start (act i)) (ti l)"
      and end_durs:     "\<forall>i \<ge> m. i < M \<longrightarrow> W (EndDur (act i)) = exec_time (at_end (act i)) (ti l)"
      and s_snap_sched_corr: "\<forall>a\<in>actions. start_snap_sched_corr W (B (ti l)) a"
      and e_snap_sched_corr: "\<forall>a\<in>actions. end_snap_sched_corr W (B (ti l)) a"
      and stop:         "W Stop = 0"
      and m:            "m < M"
    for W m Q
  proof (cases "at_start (act m) \<in> B (ti l)"; cases "at_end (act m) \<in> B (ti l)")
    assume "at_start (act m) \<in> B (ti l)" "at_end (act m) \<in> B (ti l)"
    moreover
    have "act m \<in> actions" using m act_img_actions by auto
    ultimately
    have False using not_executing_when_starting executing_when_ending nso dp pap by blast
    thus ?thesis by simp
  next
    assume a: "at_start (act m) \<in> B (ti l)" "at_end (act m) \<notin> B (ti l)"
    define W' where "W' = clock_set (at_start_effects (act m)) W"

    have m_in_acts: "act m \<in> actions" using act_img_actions m by blast

    have "prop_model W' (conditionally_apply_action (B (ti l)) (act m) Q)"
    proof -
      have caa_def: "conditionally_apply_action (B (ti l)) (act m) Q = (Q - dels (at_start (act m))) \<union> (adds (at_start (act m)))"
        using a unfolding conditionally_apply_action_def conditionally_apply_snap_def by force 
      have "(at_start (act m)) \<in> snap_actions" unfolding snap_actions_def using m_in_acts by blast
      hence "prop_model ([effects (at_start (act m))]W) (conditionally_apply_action (B (ti l)) (act m) Q)" using caa_def prop_model sim_snap_exec by auto
      moreover 
      have "([effects (at_start (act m))]W) (PropClock pr) = W' (PropClock pr)" for pr
        unfolding W'_def using clock_set_append_other unfolding at_start_effects_def by simp
      ultimately
      show ?thesis unfolding W'_def prop_model_def by auto
    qed
    moreover
    have "\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i)" 
     and "\<forall>i<Suc m. exec_corr W' (IES (ti l)) (act i)" 
    proof -
      have r_invs: "W' (Running (act i)) = W (Running (act i))" if "i < m \<or> ((Suc m) \<le> i \<and> i < M)" for i
      proof -
        have "act m \<noteq> act i" using act_inj_on_spec[of m i] that m by auto
        thus ?thesis unfolding W'_def at_start_effects_def effects_def add_effects_def del_effects_def
          by (auto intro: clock_set_none)
      qed
      thus "\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i)" using exec_corr by simp
      have "W' (Running (act m)) = 1" unfolding W'_def at_start_effects_def effects_def add_effects_def del_effects_def by simp
      moreover 
      have "act m \<in> IES (ti l)" using a m_in_acts unfolding happ_at_def exec_state_sequence'_def by auto
      ultimately
      have m_c: "exec_corr W' (IES (ti l)) (act m)" by simp
      have "exec_corr W' (IES (ti l)) (act i)" if "i < Suc m" for i 
      proof -
        from that
        consider "i = m" | "i < m" by linarith
        thus ?thesis using r_invs exec_corr' m_c
          by cases auto
      qed
      thus "\<forall>i<Suc m. exec_corr W' (IES (ti l)) (act i)" by blast
    qed
    moreover
    have "\<forall>i<Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)"
     and "\<forall>i<Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)"
    proof -
      have "W' (StartDur (act i)) = W (StartDur (act i))" if "i < m" for i
      proof -
        have "act m \<noteq> act i" using act_inj_on_spec that m by fastforce
        thus ?thesis unfolding W'_def at_start_effects_def effects_def add_effects_def del_effects_def
          by (auto intro: clock_set_none)
      qed
      moreover
      have "W' (StartDur (act m)) = exec_time' (at_start (act m)) (ti l)"
      proof -
        have "W' (StartDur (act m)) = 0" unfolding W'_def at_start_effects_def effects_def del_effects_def add_effects_def
          using clock_set_certain by auto
        thus ?thesis by (simp add: a(1) a_in_b_last_now exec_time'_def)
      qed
      ultimately
      show "\<forall>i<Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)" using start_durs'
        using less_Suc_eq by presburger
      have "\<forall>i < Suc m. W' (EndDur (act i)) = W (EndDur (act i))"
        using that unfolding W'_def at_start_effects_def effects_def add_effects_def del_effects_def 
        by (auto intro: clock_set_none)
      moreover 
      have "W (EndDur (act m)) = exec_time' (at_end (act m)) (ti l)" using a(1) end_durs 
        by (simp add: a(2) a_not_in_b_last_unchanged exec_time'_def exec_time_def m)
      ultimately
      show "\<forall>i<Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)" using end_durs'
        using less_Suc_eq by presburger
    qed
    moreover
    have "(\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l))
      \<and> (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))"
    proof -
      have "W' (StartDur (act i)) = W (StartDur (act i)) \<and> W' (EndDur (act i)) = W (EndDur (act i))" if "i \<ge> Suc m \<and> i < M" for i
      proof -
        have "act i \<noteq> act m" using that m act_inj_on_spec by fastforce
        thus ?thesis unfolding W'_def at_start_effects_def effects_def add_effects_def del_effects_def 
        by (auto intro: clock_set_none)
      qed
      thus ?thesis using start_durs end_durs by simp
    qed
    moreover
    have W'_invs: "\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c"
      apply (rule allI)
      subgoal for c
        unfolding W'_def
        apply (cases c rule: is_snap_dec_clock.cases)
        subgoal for s 
          using clock_set_none[of "SchedStartSnap s" "at_start_effects (act m)"]
          unfolding at_start_effects_def effects_def add_effects_def del_effects_def 
          by fastforce
        subgoal for s
          using clock_set_none[of "SchedEndSnap s" "at_start_effects (act m)"]
          unfolding at_start_effects_def effects_def add_effects_def del_effects_def 
          by fastforce
        subgoal 
          using clock_set_none[of "Delta" "at_start_effects (act m)"]
          unfolding at_start_effects_def effects_def add_effects_def del_effects_def 
          by fastforce
        subgoal
          using clock_set_none[of "Stop" "at_start_effects (act m)"]
          unfolding at_start_effects_def effects_def add_effects_def del_effects_def 
          by fastforce
        by auto
      done
    moreover
    have "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle>"
    proof (rule steps.step[OF _ steps.step[OF _ steps.refl]])
      show "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Execution (at_end (act m)), W'\<rangle>"
      proof (rule step_a[where a = Unit], rule step_a.intros[where s = "at_start_effects (act m)"])
        show "\<T> e \<turnstile> Execution (at_start (act m)) \<longrightarrow>\<^bsup>EQ (SchedStartSnap (act m)) 1,Unit,at_start_effects (act m)\<^esup> Execution (at_end (act m))" 
          unfolding execution_automaton_def trans_of_def execution_def using m by auto
        have "act m \<in> actions" using m act_img_actions by blast
        show "W \<turnstile> EQ (SchedStartSnap (act m)) 1" 
          using s_snap_sched_corr \<open>act m \<in> actions\<close> a(1) unfolding start_snap_sched_corr_def a by blast
        have "W' Stop = 0" using W'_invs stop by auto
        thus "W' \<turnstile> inv_of \<T> e (Execution (at_end (act m)))" unfolding inv_of_def execution_automaton_def by auto
        thus "W' = [at_start_effects (act m)]W" using W'_def by simp
      qed
      show "\<T> e \<turnstile> \<langle>Execution (at_end (act m)), W'\<rangle> \<rightarrow> \<langle>Execution (at_start (act (Suc m))),W'\<rangle>"
      proof (rule step_a[where a = Unit], rule step_a.intros[where g = "EQ (SchedEndSnap (act m)) 0" and s = "[]"])
        show "\<T> e \<turnstile> Execution (at_end (act m)) \<longrightarrow>\<^bsup>EQ (SchedEndSnap (act m)) 0,Unit,[]\<^esup> Execution (at_start (act (Suc m)))"
          unfolding execution_automaton_def trans_of_def execution_def using m by auto
        have "W' (SchedEndSnap (act m)) = 0" using e_snap_sched_corr \<open>act m \<in> actions\<close> a(2) W'_invs unfolding end_snap_sched_corr_def by simp
        thus "W' \<turnstile> EQ (SchedEndSnap (act m)) 0" by blast
        have "W' Stop = 0" using W'_invs stop by auto
        thus "W' \<turnstile> inv_of \<T> e (Execution (at_start (act (Suc m))))" unfolding inv_of_def execution_automaton_def by auto
        thus "W' = [[]]W'" by simp
      qed
    qed
    ultimately
    show ?thesis by blast
  next 
    assume a: "at_start (act m) \<notin> B (ti l)" "at_end (act m) \<in> B (ti l)"
    define W' where "W' = clock_set (at_end_effects (act m)) W"

    have W'_stop: "W' Stop = 0" 
      apply (subst stop[symmetric])
      unfolding W'_def
      apply (rule clock_set_none)
      unfolding at_end_effects_def effects_def add_effects_def del_effects_def by auto

    have m_in_acts: "act m \<in> actions" using act_img_actions m by blast
    
    have m_neq: "act i \<noteq> act m" if "i < m \<or> (i \<ge> Suc m \<and> i < M)" for i using m that act_inj_on_spec by fastforce

    have "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle>"
    proof (rule steps.step[OF _ steps.step[OF _ steps.refl]])
      show "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Execution (at_end (act m)), W\<rangle>"
        apply (rule step_a)
        apply (rule step_a.intros[where s = Nil])
        unfolding trans_of_def execution_automaton_def inv_of_def execution_def using m
        apply auto[1]
        subgoal using a(1) s_snap_sched_corr unfolding start_snap_sched_corr_def using m act_img_actions by auto
        subgoal using stop by auto
        by auto
      show "\<T> e \<turnstile> \<langle>Execution (at_end (act m)), W\<rangle> \<rightarrow> \<langle>Execution (at_start (act (Suc m))),W'\<rangle>"
        apply (rule step_a)
        apply (rule step_a.intros[OF _ _ _ W'_def])
        unfolding trans_of_def execution_automaton_def inv_of_def execution_def using m
          apply auto[1]
        subgoal using a(2) e_snap_sched_corr unfolding end_snap_sched_corr_def using m_in_acts by auto
        using W'_stop by auto
    qed
    moreover
    have "prop_model W' (conditionally_apply_action (B (ti l)) (act m) Q)"
    proof -
      have caa_def: "conditionally_apply_action (B (ti l)) (act m) Q = (Q - dels (at_end (act m))) \<union> (adds (at_end (act m)))"
        using a unfolding conditionally_apply_action_def conditionally_apply_snap_def by force 
      have "(at_end (act m)) \<in> snap_actions" unfolding snap_actions_def using m_in_acts by blast
      hence "prop_model ([effects (at_end (act m))]W) (conditionally_apply_action (B (ti l)) (act m) Q)" using caa_def prop_model sim_snap_exec by auto
      moreover 
      have "([effects (at_end (act m))]W) (PropClock pr) = W' (PropClock pr)" for pr
        unfolding W'_def using clock_set_append_other unfolding at_end_effects_def by simp
      ultimately
      show ?thesis unfolding W'_def prop_model_def by auto
    qed
    moreover
    have "(\<forall>i<Suc m. exec_corr W' (IES (ti l)) (act i)) \<and>
         (\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i))"
    proof (rule conjI)
      have W'_inv: "W' (Running (act i)) = W (Running (act i))" if "i < m \<or> (i \<ge> Suc m \<and> i < M)" for i
      proof -
        have "\<nexists>v. ((Running (act i)), v) \<in> set (at_end_effects (act m))" using m_neq that 
          unfolding at_end_effects_def effects_def del_effects_def add_effects_def by auto
        thus ?thesis unfolding W'_def using clock_set_none by meson
      qed
      thus "\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i)"
        using exec_corr by simp
      have "\<forall>i< m. exec_corr W' (IES (ti l)) (act i)" using W'_inv exec_corr' by simp
      moreover 
      have "act m \<notin> IES (ti l)" using a(2) unfolding happ_at_def exec_state_sequence'_def by blast
      hence "exec_corr W' (IES (ti l)) (act m)" unfolding W'_def at_end_effects_def by simp
      ultimately
      show "\<forall>i<Suc m. exec_corr W' (IES (ti l)) (act i)" using less_antisym by blast
    qed
    moreover
    have "(\<forall>i<Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)) \<and>
         (\<forall>i<Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)) \<and>
         (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l)) \<and>
         (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))"
    proof (intro conjI)
      have W'_inv: "W' (StartDur (act i)) = W (StartDur (act i)) \<and> W' (EndDur (act i)) = W (EndDur (act i))"
          if "i < m \<or> (i \<ge> Suc m \<and> i < M)" for i
      proof -
        have "\<nexists>v. ((StartDur (act i)), v) \<in> set (at_end_effects (act m))" using m_neq that 
          unfolding at_end_effects_def effects_def del_effects_def add_effects_def by auto
        moreover
        have "\<nexists>v. ((EndDur (act i)), v) \<in> set (at_end_effects (act m))" using m_neq that 
          unfolding at_end_effects_def effects_def del_effects_def add_effects_def by auto
        ultimately 
        show ?thesis unfolding W'_def using clock_set_none by meson
      qed
      with start_durs end_durs
      show "\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l)"
           "\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l)" by auto
      
      have "W' (StartDur (act m)) = W (StartDur (act m))" 
        unfolding W'_def at_end_effects_def effects_def add_effects_def del_effects_def 
        apply (rule clock_set_none) by auto
      moreover
      have "exec_time (at_start (act m)) (ti l) = exec_time' (at_start (act m)) (ti l)"
        using a_not_in_b_exec_time_unchanged a(1) by simp
      ultimately
      have "W' (StartDur (act m)) = exec_time' (at_start (act m)) (ti l)" using start_durs m by simp
      with W'_inv start_durs'
      show "\<forall>i<Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)" using less_Suc_eq by presburger
  
      have "W' (EndDur (act m)) = exec_time' (at_end (act m)) (ti l)" apply (subst a_in_b_exec_time'_0[OF a(2)])
        unfolding W'_def at_end_effects_def by simp
      with W'_inv end_durs'
      show "\<forall>i<Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)" using less_Suc_eq by presburger
    qed
    moreover
    have "(\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)"
      apply (rule allI, rule impI)
      subgoal for c
        using clock_set_none[of c "at_end_effects (act m)"]
        apply (cases c; simp)
        unfolding W'_def at_end_effects_def effects_def del_effects_def add_effects_def 
        by fastforce+
      done
    ultimately
    show ?thesis by auto
  next 
    assume a: "at_start (act m) \<notin> B (ti l)" "at_end (act m) \<notin> B (ti l)"

    have m_in_acts: "act m \<in> actions" using act_img_actions m by blast

    have "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W\<rangle>"
    proof (rule steps.step[OF _ steps.step[OF _ steps.refl]])
      show "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow> \<langle>Execution (at_end (act m)), W\<rangle>"
        apply (rule step_a)
        apply (rule step_a.intros[where s = Nil])
        unfolding execution_automaton_def trans_of_def execution_def
        using m apply auto[1]
        subgoal using a s_snap_sched_corr m_in_acts unfolding start_snap_sched_corr_def by blast
        subgoal using stop unfolding inv_of_def by auto
        by auto
      show "\<T> e \<turnstile> \<langle>Execution (at_end (act m)), W\<rangle> \<rightarrow> \<langle>Execution (at_start (act (Suc m))),W\<rangle>"
        apply (rule step_a)
        apply (rule step_a.intros[where s = Nil])
        unfolding execution_automaton_def trans_of_def execution_def
        using m apply auto[1]
        subgoal using a e_snap_sched_corr m_in_acts unfolding end_snap_sched_corr_def by blast
        subgoal using stop unfolding inv_of_def by auto
        by auto
    qed
    moreover
    have "prop_model W (conditionally_apply_action (B (ti l)) (act m) Q)"
      using a unfolding conditionally_apply_action_def conditionally_apply_snap_def using prop_model by simp
    moreover 
    have "(\<forall>i<Suc m. exec_corr W (IES (ti l)) (act i)) \<and>
         (\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W (ES (ti l)) (act i))"
    proof (rule conjI)
      show "\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W (ES (ti l)) (act i)" using exec_corr m less_Suc_eq by simp
      have "act m \<in> IES (ti l) \<longleftrightarrow> act m \<in> ES (ti l)" using execution_state_unchanging[OF a] by simp
      hence "exec_corr W (IES (ti l)) (act m)" using exec_corr m by blast
      with exec_corr'
      show "\<forall>i<Suc m. exec_corr W (IES (ti l)) (act i)" using less_Suc_eq by simp
    qed
    moreover
    have "(\<forall>i<Suc m. W (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)) \<and>
         (\<forall>i<Suc m. W (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)) \<and>
         (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W (StartDur (act i)) = exec_time (at_start (act i)) (ti l)) \<and>
         (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W (EndDur (act i)) = exec_time (at_end (act i)) (ti l))"
    proof (intro conjI)
      show "\<forall>i\<ge>Suc m. i < M \<longrightarrow> W (StartDur (act i)) = exec_time (at_start (act i)) (ti l)" using Suc_leD start_durs by blast
      show "\<forall>i\<ge>Suc m. i < M \<longrightarrow> W (EndDur (act i)) = exec_time (at_end (act i)) (ti l)" using Suc_leD end_durs by blast

      have "exec_time (at_start (act m)) (ti l) = exec_time' (at_start (act m)) (ti l)"
        using a_not_in_b_exec_time_unchanged a by blast
      with start_durs
      have "W (StartDur (act m)) = exec_time' (at_start (act m)) (ti l)" using m by simp
      with start_durs'
      show "\<forall>i<Suc m. W (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)" using less_antisym by blast

      have "exec_time (at_end (act m)) (ti l) = exec_time' (at_end (act m)) (ti l)"
        using a_not_in_b_exec_time_unchanged a by blast
      with end_durs
      have "W (EndDur (act m)) = exec_time' (at_end (act m)) (ti l)" using m by simp
      with end_durs'
      show "\<forall>i<Suc m. W (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)" using less_antisym by blast
    qed
    ultimately
    show ?thesis by auto
  qed

  have execution_step': "\<exists>W'. \<T> e\<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle>
    \<and> prop_model W' (conditionally_apply_action (B (ti l)) (act m) Q)
    \<and> (\<forall>i < Suc m. exec_corr W' (IES (ti l)) (act i))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i))
    \<and> (\<forall>i < Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l))
    \<and> (\<forall>i < Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))
    \<and> (\<forall>a\<in>actions. start_snap_sched_corr W' (B (ti l)) a)
    \<and> (\<forall>a\<in>actions. end_snap_sched_corr W' (B (ti l)) a)
    \<and> W' Stop = 0
    \<and> (\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)"
    if prop_model:      "prop_model W Q"
      and exec_corr':   "\<forall>i < m. exec_corr W (IES (ti l)) (act i)"
      and exec_corr:    "\<forall>i \<ge> m. i < M \<longrightarrow> exec_corr W (ES (ti l)) (act i)"
      and start_durs':  "\<forall>i < m. W (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)"
      and end_durs':    "\<forall>i < m. W (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)"
      and start_durs:   "\<forall>i \<ge> m. i < M \<longrightarrow> W (StartDur (act i)) = exec_time (at_start (act i)) (ti l)"
      and end_durs:     "\<forall>i \<ge> m. i < M \<longrightarrow> W (EndDur (act i)) = exec_time (at_end (act i)) (ti l)"
      and s_snap_sched_corr: "\<forall>a\<in>actions. start_snap_sched_corr W (B (ti l)) a"
      and e_snap_sched_corr: "\<forall>a\<in>actions. end_snap_sched_corr W (B (ti l)) a"
      and stop:         "W Stop = 0"
      and m:            "m < M"
    for W m Q
  proof -
    from execution_step[OF that]
    obtain W' where
      W': "\<T> e \<turnstile> \<langle>Execution (at_start (act m)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle> \<and>
       prop_model W' (conditionally_apply_action (B (ti l)) (act m) Q) \<and>
       (\<forall>i<Suc m. (W' (Running (act i)) = 1) = (act i \<in> IES (ti l)) \<and> (W' (Running (act i)) = 0) = (act i \<notin> IES (ti l))) \<and>
       (\<forall>i\<ge>Suc m. i < M \<longrightarrow> (W' (Running (act i)) = 1) = (act i \<in> ES (ti l)) \<and> (W' (Running (act i)) = 0) = (act i \<notin> ES (ti l))) \<and>
       (\<forall>i<Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)) \<and>
       (\<forall>i<Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)) \<and>
       (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l)) \<and>
       (\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))" 
      and invs: "(\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)" by auto
    have "\<forall>a\<in>actions. start_snap_sched_corr W' (B (ti l)) a"
    proof (rule ballI)
      fix a
      assume a: "a \<in> actions"
      have "W (SchedStartSnap a) = W' (SchedStartSnap a)" using invs by simp
      thus "start_snap_sched_corr W' (B (ti l)) a" using s_snap_sched_corr a unfolding start_snap_sched_corr_def by fastforce
    qed
    moreover
    have "\<forall>a\<in>actions. end_snap_sched_corr W' (B (ti l)) a"
    proof (rule ballI)
      fix a
      assume a: "a \<in> actions"
      have "W (SchedEndSnap a) = W' (SchedEndSnap a)" using invs by simp
      thus "end_snap_sched_corr W' (B (ti l)) a" using e_snap_sched_corr a unfolding end_snap_sched_corr_def by fastforce
    qed
    moreover
    have "W' Stop = 0" using stop invs by auto
    ultimately
    show ?thesis using W' invs by auto
  qed

  
  have execution_strong: "\<exists>W'. \<T> e \<turnstile> \<langle>Execution (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle>
    \<and> prop_model W' (foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..<(Suc m)])
    \<and> (\<forall>i < Suc m. exec_corr W' (IES (ti l)) (act i))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i))
    \<and> (\<forall>i < Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l))
    \<and> (\<forall>i < Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l))
    \<and> (\<forall>i \<ge> Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))
    \<and> (\<forall>a\<in>actions. start_snap_sched_corr W' (B (ti l)) a)
    \<and> (\<forall>a\<in>actions. end_snap_sched_corr W' (B (ti l)) a)
    \<and> W' Stop = 0
    \<and> (\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)" if "m < M" for m
    using that
  proof (induction m)
    case 0
    
    have 1: "\<forall>i\<ge>0. i < M \<longrightarrow> (W (Running (act i)) = 1) = (act i \<in> ES (ti l)) \<and> (W (Running (act i)) = 0) = (act i \<notin> ES (ti l))"
      using exec_clocks unfolding exec_model_def using act_img_actions by blast
    
    have 2: "\<forall>i\<ge>0. i < M \<longrightarrow> W (StartDur (act i)) = exec_time (at_start (act i)) (ti l)" using start_durs act_img_actions by blast
    
    have 3: "\<forall>i\<ge>0. i < M \<longrightarrow> W (EndDur (act i)) = exec_time (at_end (act i)) (ti l)" using end_durs act_img_actions by blast
    
    have 4: "\<forall>a\<in>actions. start_snap_sched_corr W (B (ti l)) a"  "\<forall>a\<in>actions. end_snap_sched_corr W (B (ti l)) a" 
      using snap_exec_sched unfolding snap_exec_sched_corr_def by blast+
    
    have 5: "foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..<Suc 0]  = 
        conditionally_apply_action (B (ti l)) (act 0) (MS l)" by simp
    
    show ?case using execution_step'[OF prop_clocks _ 1  _ _ 2 3 4 stop \<open>0 < M\<close>, simplified 5[symmetric]] by auto
  next
    case (Suc m)
    then obtain W' where
       W':"\<T> e \<turnstile> \<langle>Execution (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc m))), W'\<rangle>"
       "prop_model W' (foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..<Suc m])"
       "(\<forall>i<Suc m. exec_corr W' (IES (ti l)) (act i))"
       "(\<forall>i\<ge>Suc m. i < M \<longrightarrow> exec_corr W' (ES (ti l)) (act i))"
       "(\<forall>i<Suc m. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l))"
       "(\<forall>i<Suc m. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l))"
       "(\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (StartDur (act i)) = exec_time (at_start (act i)) (ti l))"
       "(\<forall>i\<ge>Suc m. i < M \<longrightarrow> W' (EndDur (act i)) = exec_time (at_end (act i)) (ti l))"
       "(\<forall>a\<in>actions. start_snap_sched_corr W' (B (ti l)) a)"
       "(\<forall>a\<in>actions. end_snap_sched_corr W' (B (ti l)) a)"
       "W' Stop = 0"
       and W'_invs: "(\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c)" by auto
    from execution_step'[OF W'(2,3,4,5,6,7,8,9,10,11) Suc(2)] 
      obtain W'' where
        W'':"\<T> e \<turnstile> \<langle>Execution (at_start (act (Suc m))), W'\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc (Suc m)))), W''\<rangle>"
        and W''2: "prop_model W''
         (conditionally_apply_action (B (ti l)) (act (Suc m))
           (foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..<Suc m]))"
        and W''3:"(\<forall>i<Suc (Suc m). (W'' (Running (act i)) = 1) = (act i \<in> IES (ti l)) \<and> (W'' (Running (act i)) = 0) = (act i \<notin> IES (ti l))) \<and>
        (\<forall>i\<ge>Suc (Suc m). i < M \<longrightarrow> (W'' (Running (act i)) = 1) = (act i \<in> ES (ti l)) \<and> (W'' (Running (act i)) = 0) = (act i \<notin> ES (ti l))) \<and>
        (\<forall>i<Suc (Suc m). W'' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)) \<and>
        (\<forall>i<Suc (Suc m). W'' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)) \<and>
        (\<forall>i\<ge>Suc (Suc m). i < M \<longrightarrow> W'' (StartDur (act i)) = exec_time (at_start (act i)) (ti l)) \<and>
        (\<forall>i\<ge>Suc (Suc m). i < M \<longrightarrow> W'' (EndDur (act i)) = exec_time (at_end (act i)) (ti l)) \<and>
        (\<forall>a\<in>actions. start_snap_sched_corr W'' (B (ti l)) a) \<and>
        (\<forall>a\<in>actions. end_snap_sched_corr W'' (B (ti l)) a) \<and> W'' Stop = 0" 
        and W''_invs: "(\<forall>c. is_execution_invariant_clock c \<longrightarrow> W' c = W'' c)" by auto
      
      have 2: "(conditionally_apply_action (B (ti l)) (act (Suc m)) (foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..< Suc m])) 
            = foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..< Suc (Suc m)]"
        using foldl_append by auto
      
      have "\<T> e \<turnstile> \<langle>Execution (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act (Suc (Suc m)))), W''\<rangle>"
        using steps_trans[OF W'(1) W''(1)] .
      moreover
      from W'_invs W''_invs
      have "\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W'' c" by simp
      ultimately
      show ?case using W''2[simplified 2] W''3 by auto
    qed
    
    obtain W' where
      W': "\<T> e \<turnstile> \<langle>Execution (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act M)), W'\<rangle>"
      "prop_model W' (foldl (\<lambda>p i. conditionally_apply_action (B (ti l)) (act i) p) (MS l) [0..<M])"
      "\<forall>i < M. exec_corr W' (IES (ti l)) (act i)"
      "\<forall>i < M. W' (StartDur (act i)) = exec_time' (at_start (act i)) (ti l)"
      "\<forall>i < M. W' (EndDur (act i)) = exec_time' (at_end (act i)) (ti l)"
      "\<forall>c. is_execution_invariant_clock c \<longrightarrow> W c = W' c"
      "W' Stop = 0"
      using some_actions execution_strong[of "M - 1"] by auto

    have "(B (ti l)) \<subseteq> snap_actions" unfolding happ_at_def plan_happ_seq_def snap_actions_def using pap unfolding plan_actions_in_problem_def by auto
    moreover
    have "\<forall>a b. a \<in> B (ti l) \<and> b \<in> B (ti l) \<and> a \<noteq> b \<longrightarrow> \<not> mutex_snap_action a b"
      apply (intro allI)
      subgoal for a b
        apply (rule impI)
        apply (elim conjE)
        using nm[simplified nm_happ_seq_def] unfolding happ_at_def 
        using eps_range by force
      done
    moreover
    have "\<forall>a\<in>actions. \<not> (at_start a \<in> B (ti l) \<and> at_end a \<in> B (ti l))" using executing_when_ending not_executing_when_starting assms by blast
    ultimately
    have "prop_model W' (apply_effects (MS l) (B_lim (ti l) M))"
      using conditional_application_is_application[where m = M] W'(2) by simp
    hence "prop_model W' (apply_effects (MS l) (B(ti l)))" using B_lim_M_eq_B pap by auto
    hence pm: "prop_model W' (MS (Suc l))" using MS_valid unfolding valid_state_sequence_def using l_len by (auto simp: Let_def)
    
    have "le_ta \<T> e \<T>" unfolding le_ta_def prob_automaton_def execution_automaton_def trans_of_def inv_of_def by simp
    with W'(1)
    have path: "\<T> \<turnstile> \<langle>Execution (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Execution (at_start (act M)), W'\<rangle>" using ta_superset by fast
    
    show ?thesis using W' pm path
      apply -
      apply (subst (asm) act_pred[symmetric])+
      unfolding exec_model_def by blast
  qed

lemma invs_of_active_actions: 
  assumes pap: "pap_\<pi>"
      and nso: "nso_\<pi>"
      and dp: "dp_\<pi>" 
  shows
  "Inv t = \<Union>(over_all ` (ES t))"
proof (rule equalityI; rule subsetI)
  fix x
  assume "x \<in> Inv t"
  then obtain a t' d where
    x: "x \<in> over_all a"
    "(a, t', d) \<in> ran \<pi>" 
    "t' < t \<and> t \<le> t' + d" unfolding invs_at_def plan_inv_seq_def by blast
  hence t': "(t', at_start a) \<in> happ_seq \<and> t' < t" unfolding plan_happ_seq_def by auto 
  moreover
  from x
  have a_in_acts: "a \<in> actions" using pap unfolding plan_actions_in_problem_def by blast
  have "\<not> (\<exists>s. (s, at_end a) \<in> happ_seq \<and> t' \<le> s \<and> s < t)"
  proof (rule notI)
    assume "\<exists>s. (s, at_end a) \<in> happ_seq \<and> t' \<le> s \<and> s < t"
    then obtain s where
      s: "(s, at_end a) \<in> happ_seq"
      "t' \<le> s" "s < t" by blast
    then obtain s' d' where
      s': "s = s' + d'"
      "(a, s', d') \<in> ran \<pi>" using at_end_in_happ_seqE a_in_acts pap nso dp by blast
    hence "(s', at_start a) \<in> happ_seq" unfolding plan_happ_seq_def by blast
    show False
    proof (cases "s' < t'")
      case True
      with s(2)[simplified s'(1)]
      show ?thesis using nso[THEN no_self_overlap_spec, OF s'(2) x(2)] by fastforce
    next
      case False
      from s s'
      have "s' + d' < t" by simp
      moreover
      from x
      have "t \<le> t' + d" by simp
      ultimately
      have "s' + d' < t' + d" by simp
      moreover
      from dp[simplified durations_positive_def] s'(2)
      have "0 < d'" by simp
      ultimately
      have "s' < t' + d" by (meson less_add_same_cancel1 order_less_trans)
      moreover
      from False
      have "t' = s' \<longrightarrow> d' \<noteq> d" using s x t' s' by auto
      ultimately
      show ?thesis using nso[THEN no_self_overlap_spec, OF x(2) s'(2)] False by fastforce
    qed
  qed
  ultimately
  have "a \<in> ES t" unfolding exec_state_sequence_def using a_in_acts by blast
  with x
  show "x \<in> \<Union> (over_all ` ES t)" by blast
next 
  fix x
  assume "x \<in> \<Union> (over_all ` ES t)"
  then obtain t' a where
    x: "x \<in> over_all a"
    "a \<in> actions"
    "(t', at_start a) \<in> happ_seq"
    "t' < t"
    "\<not>(\<exists>s. (s, at_end a) \<in> happ_seq \<and> t' \<le> s \<and> s < t)"
    unfolding exec_state_sequence_def by force
  then obtain d where
    a: "(a, t', d) \<in> ran \<pi>" using at_start_in_happ_seqE nso dp pap by blast
  have "t' + d \<ge> t" 
  proof (rule ccontr)
    assume "\<not> t \<le> t' + d"
    hence "t' + d < t" by simp
    moreover
    have "(t' + d, at_end a) \<in> happ_seq" using a unfolding plan_happ_seq_def by blast
    moreover
    have "t' < t' + d" using dp[simplified durations_positive_def] a by auto
    ultimately
    show False using x(5) by simp
  qed
  with a x
  show "x \<in> Inv t" unfolding invs_at_def plan_inv_seq_def by auto
qed

lemma return_to_main:
  assumes prop_model:   "prop_model W (MS (Suc l))"
  and exec_model:       "exec_model W (IES (ti l))"
  and start_times_corr: "\<forall>a \<in> actions. W (StartDur a) = exec_time' (at_start a) (ti l)"
  and end_times_corr:   "\<forall>a \<in> actions. W (EndDur a) = exec_time' (at_end a) (ti l)"
  and stop:             "W Stop = 0"
  and l:                "l < length timepoint_list"
  and vss: "vss MS"
  and pap: "pap_\<pi>"
  and nso: "nso_\<pi>"
  and dp: "dp_\<pi>" 
  and fp: "fp_\<pi>"
    shows "\<T> \<turnstile> \<langle>Execution (at_start (act M)), W\<rangle> \<rightarrow>* \<langle>Main, W(Delta:=0)\<rangle>"
proof -
  have over_all: "W \<turnstile> action_over_all a" if a_in_actions: "a \<in> actions" for a 
  proof (cases "a \<in> IES (ti l)")
    case True
    with exec_model that
    have running: "W (Running a) = 1" unfolding exec_model_def by blast
    
    
    have "W p = 1" if "p \<in> set (map PropClock (prop_list (over_all a)))" for p
    proof -
      from that obtain pr where
        pr: "pr \<in> set (prop_list (over_all a))"
         "p = PropClock pr" by auto
      
      have oap: "over_all a \<subseteq> props" using wf_acts \<open>a \<in> actions\<close> by auto
      hence "set (prop_list (over_all a)) = over_all a" using set_prop_list by auto
      with pr
      have pr_in_a_invs: "pr \<in> over_all a" by simp
      moreover
      from True last_ies_empty pap dp fp
      have sl: "Suc l < length timepoint_list" by (metis Suc_lessI diff_Suc_1 empty_iff l)
      with inc_es_is_next_es fp True
      have "a \<in> ES (ti(Suc l))" by blast
      ultimately 
      have "pr \<in> Inv (ti(Suc l))" using invs_of_active_actions pap nso dp by blast
      moreover
      from vss
      have "Inv (ti(Suc l)) \<subseteq> MS (Suc l)" unfolding valid_state_sequence_def using sl by (auto simp: Let_def)
      ultimately
      have "pr \<in> MS (Suc l)" by blast 
      moreover
      from pr_in_a_invs a_in_actions
      have "pr \<in> props" using wf_acts by auto
      ultimately
      have "W (PropClock pr) = 1" using prop_model unfolding prop_model_def by simp
      thus ?thesis using pr by simp
    qed
    with running
    have "list_all (\<lambda>p. W \<turnstile> DLE (Running a) p 0) (over_all_clocks a)"
      unfolding over_all_clocks_def
      using list_all_iff by force
    then show ?thesis unfolding action_over_all_def AND_ALL_iff list_all_iff by simp
  next
    case False
    with exec_model that
    have not_running: "W (Running a) = 0" unfolding exec_model_def by blast
    moreover
    from prop_model
    have prop_cases: "\<forall>p \<in> props. W (PropClock p) = 0 \<or> W (PropClock p) = 1" unfolding prop_model_def by blast
    have oap: "over_all a \<subseteq> props" using wf_acts that by auto
    hence "set (prop_list (over_all a)) = over_all a" using set_prop_list by auto
    with oap prop_cases
    have "\<forall>p \<in> set (prop_list (over_all a)). W (PropClock p) = 0 \<or> W (PropClock p) = 1" by blast
    hence "\<forall>p \<in> set (map PropClock (prop_list (over_all a))). W p = 0 \<or> W p = 1" by simp
    with not_running
    have "list_all (\<lambda>p. W \<turnstile> DLE (Running a) p 0) (over_all_clocks a)"
      unfolding over_all_clocks_def list_all_iff
      apply -
      apply (rule ballI)
      subgoal for p
        apply (drule bspec[where x = p])
         apply assumption
        apply (erule disjE) by auto
        
      done
    thus ?thesis unfolding action_over_all_def AND_ALL_iff list_all_iff
      by simp
  qed

  have sat_conds: "W \<turnstile> over_all_conds"
  proof -
    have "W \<turnstile> action_over_all a" if "a \<in> set action_list" for a
    proof -
      from that act_img_actions
      have "a \<in> actions" by simp
      thus ?thesis using over_all by simp
    qed
    thus ?thesis unfolding over_all_conds_def AND_ALL_iff list_all_iff by simp
  qed
  show ?thesis
    apply (rule steps.step[OF _ steps.refl])
    apply (rule step_a)
    apply (rule step_a.intros[where g = over_all_conds])
    unfolding trans_of_def inv_of_def prob_automaton_def exec_to_main_def 
    using sat_conds stop by auto
qed

term valid_plan

lemma instant_execution_cycle:
  assumes l_len: "l < length timepoint_list" 
      and prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (ti l))"
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) + d = exec_time (at_start a) (ti l) "
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) + d = exec_time (at_end a) (ti l)"
      and time_d: "0 \<le> d"
      and stop: "W Stop = 0"
      and delta_clock: "W Delta = 0"
      and vss: "vss MS"
      and nso: "nso_\<pi>"
      and pap: "pap_\<pi>"
      and dp: "dp_\<pi>"
      and dv: "dv_\<pi>"
      and nm: "nm_happ_seq happ_seq"
      and fpl: "fp_\<pi>"
  shows "\<exists>W'. \<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle> 
    \<and> prop_model W' (MS (Suc l))
    \<and> exec_model W' (IES (ti l))
    \<and> (\<forall>a \<in> actions. W' (StartDur a) = exec_time' (at_start a) (ti l))
    \<and> (\<forall>a \<in> actions. W' (EndDur a) = exec_time' (at_end a) (ti l))
    \<and> W' Stop = 0
    \<and> W' Delta = 0"
proof -                            
  define W_delta where "W_delta = W \<oplus> d"


  have W_delta_trans: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>Main,W_delta\<rangle>"
    unfolding W_delta_def
    apply (rule step_t.intros)
    unfolding inv_of_def prob_automaton_def cval_add_def 
    using time_d stop by auto

  have W_delta_steps: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main,W_delta\<rangle>"
    using W_delta_trans[THEN step_t, THEN steps_step] .
  
  from main_loc_delta_prop_model main_loc_delta_exec_model W_delta_trans delta_clock prop_clocks exec_clocks
  have W_delta_prop: "delta_prop_model W_delta (MS l)"
   and W_delta_exec: "delta_exec_model W_delta (ES (ti l))"
    by blast+

  have W_delta_other: "\<forall>c. W_delta c = W c + d" 
    unfolding W_delta_def cval_add_def by simp

  define W_delta_0 where "W_delta_0 = W_delta(Stop:=0)"
  have main_to_bool: "\<T> \<turnstile> \<langle>Main, W_delta\<rangle> \<rightarrow>* \<langle>PropDecoding (p 0),W_delta_0\<rangle>"
    unfolding W_delta_0_def
    apply (rule steps_step)
    apply (rule step_a)
    apply (rule step_a.intros)
    unfolding prob_automaton_def main_to_decoding_def trans_of_def
       apply auto[1]
    using W_delta_other stop unfolding true_const_def using time_d apply auto[1]
    unfolding inv_of_def by auto

  from W_delta_other
  have W_delta_0_other: "\<forall>c. c \<noteq> Stop \<longrightarrow> W_delta_0 c = W c + d" unfolding W_delta_0_def by simp

  from W_delta_0_def
  have W_delta_0_stop: "W_delta_0 Stop = 0" by simp

  from W_delta_0_def W_delta_prop W_delta_exec 
  have W_delta_0_prop: "delta_prop_model W_delta_0 (MS l)"
   and W_delta_0_exec: "delta_exec_model W_delta_0 (ES (ti l))" unfolding delta_prop_model_def delta_exec_model_def 
    by auto

  from W_delta_0_prop W_delta_0_exec W_delta_0_stop 
  obtain W_decoded where
    W_decoded_trans: "\<T> \<turnstile> \<langle>PropDecoding (p 0), W_delta_0\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W_decoded\<rangle>"
    and W_decoded_prop: "prop_model W_decoded (MS l)"
    and W_decoded_exec: "exec_model W_decoded (ES (ti l))"
    and W_decoded_other: "\<forall>c. \<not>(is_boolean_clock c) \<longrightarrow> W_delta_0 c = W_decoded c"
    using boolean_state_decoding by blast

  from W_decoded_other W_delta_0_stop
  have W_decoded_stop: "W_decoded Stop = 0" by simp

  from W_decoded_other W_delta_0_other
  have W_decoded_other: "\<forall>c. c \<noteq> Stop \<and> \<not>(is_boolean_clock c) \<longrightarrow> W_decoded c = W c + d" by fastforce

  from W_decoded_other start_durs end_durs
  have W_decoded_start_durs:"\<forall>a \<in> actions. W_decoded (StartDur a) = exec_time (at_start a) (ti l)"
   and W_decoded_end_durs: "\<forall>a \<in> actions. W_decoded (EndDur a) = exec_time (at_end a) (ti l)" 
    by auto

  have bool_to_dec: "\<T> \<turnstile> \<langle>ExecDecoding (act M), W_decoded\<rangle> \<rightarrow>* \<langle>Decision (at_start (act 0)), W_decoded\<rangle>"
    apply (rule steps_step)
    apply (rule step_a)
    apply (rule step_a.intros)
    unfolding trans_of_def
    unfolding prob_automaton_def 
    unfolding exec_decoding_to_decision_making_def
       apply auto[1]
    unfolding true_const_def inv_of_def using W_decoded_stop by auto

  from decision_making[OF l_len vss W_decoded_prop W_decoded_exec 
      _ _ 
      W_decoded_stop nm fpl nso dp dv pap] W_decoded_start_durs W_decoded_end_durs
  obtain W_decided where
    W_decided_trans: "\<T> \<turnstile> \<langle>Decision (at_start (act 0)), W_decoded\<rangle> \<rightarrow>* \<langle>Decision (at_start (act M)), W_decided\<rangle>" 
    and W_decided_sched: "snap_exec_sched_corr W_decided (B (ti l))"
    and W_decided_other: "\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W_decoded c = W_decided c"
    by blast

  from W_decided_other W_decoded_stop
  have W_decided_stop: "W_decided Stop = 0" by simp

  from W_decided_other W_decoded_start_durs W_decoded_end_durs
  have W_decided_start_durs: "\<forall>a \<in> actions. W_decided (StartDur a) = exec_time (at_start a) (ti l)"
   and W_decided_end_durs: "\<forall>a \<in> actions. W_decided (EndDur a) = exec_time (at_end a) (ti l)"
    by auto

  from W_decided_other W_decoded_prop W_decoded_exec
  have W_decided_prop: "prop_model W_decided (MS l)"
   and W_decided_exec: "exec_model W_decided (ES (ti l))" 
    unfolding prop_model_def exec_model_def by simp+

  have dec_to_exec: "\<T> \<turnstile> \<langle>Decision (at_start (act M)), W_decided\<rangle> \<rightarrow>* \<langle>Execution (at_start (act 0)), W_decided\<rangle>"
    apply (rule steps_step)
    apply (rule step_a)
    apply (rule step_a.intros)
    unfolding trans_of_def prob_automaton_def dm_to_exec_def apply auto[1]
    unfolding true_const_def using W_decided_stop unfolding inv_of_def by auto

  from execution l_len vss W_decided_prop W_decided_exec W_decided_sched W_decided_start_durs W_decided_end_durs W_decided_stop
    nm fpl nso dp dv pap
  obtain W_e where
    W_e_trans: "\<T> \<turnstile> \<langle>Execution (at_start (act 0)), W_decided\<rangle> \<rightarrow>* \<langle>Execution (at_start (act M)), W_e\<rangle>"
    and W_e_prop: "prop_model W_e (MS (Suc l))"
    and W_e_exec: "exec_model W_e (IES (ti l))"
    and W_e_start: "\<forall>a \<in> actions. W_e (StartDur a) = exec_time' (at_start a) (ti l)"
    and W_e_end: "\<forall>a \<in> actions. W_e (EndDur a) = exec_time' (at_end a) (ti l)"
    and W_e_other: "\<forall>c. is_execution_invariant_clock c \<longrightarrow> W_decided c = W_e c"
    and W_e_stop: "W_e Stop = 0"
    by blast

  define W' where "W' = W_e(Delta:=0)"
  from return_to_main W_e_prop W_e_exec W_e_start W_e_end W_e_stop l_len vss pap nso dp fpl
  have ret: "\<T> \<turnstile> \<langle>Execution (at_start (act M)), W_e\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle>" unfolding W'_def by blast

  from W_e_prop W_e_exec W_e_start W_e_end W_e_stop
  have W'_prop: "prop_model W' (MS (Suc l))"
  and W'_exec: "exec_model W' (IES (ti l))"
  and W'_start: "\<forall>a \<in> actions. W' (StartDur a) = exec_time' (at_start a) (ti l)"
  and W'_end: "\<forall>a \<in> actions. W' (EndDur a) = exec_time' (at_end a) (ti l)"
  and W'_stop: "W' Stop = 0"
  and W'_delta: "W' Delta = 0" unfolding W'_def 
    unfolding prop_model_def exec_model_def by auto
  
  from W_delta_steps main_to_bool W_decoded_trans bool_to_dec W_decided_trans dec_to_exec W_e_trans ret
  have W'_trans: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle>"
    apply -
    apply (elim steps_trans)
    by (rule steps.refl)

  from W'_prop W'_exec W'_start W'_end W'_stop W'_delta W'_trans
  show ?thesis by blast
qed

fun deltas::"nat \<Rightarrow> 'time" where
"deltas 0 = \<epsilon> + 1" |
"deltas (Suc n) = ti (Suc n) - ti n"

find_theorems name: "exec_time*nex"

lemma multiple_execution_cycles:
  assumes l_len: "l < length timepoint_list" 
      and prop_clocks: "prop_model W (MS 0)"
      and exec_clocks: "exec_model W (ES (ti 0))"
      and stop: "W Stop = 0"
      and delta_clock: "W Delta = 0"
      and other_clocks: "\<forall>c. \<not>(is_boolean_clock c) \<longrightarrow> W c = 0"
      and vss: "vss MS"
      and nso: "nso_\<pi>"
      and pap: "pap_\<pi>"
      and dp: "dp_\<pi>"
      and dv: "dv_\<pi>"
      and nm: "nm_happ_seq happ_seq"
      and fpl: "fp_\<pi>"
  shows "\<exists>W'. \<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle> 
    \<and> prop_model W' (MS (Suc l))
    \<and> exec_model W' (IES (ti l))
    \<and> (\<forall>a \<in> actions. W' (StartDur a) = exec_time' (at_start a) (ti l))
    \<and> (\<forall>a \<in> actions. W' (EndDur a) = exec_time' (at_end a) (ti l))
    \<and> W' Stop = 0
    \<and> W' Delta = 0"
  using l_len
proof (induction l)
  case 0
  let ?d = "deltas 0"
  have sd: "W (StartDur a) + ?d = exec_time (at_start a) (ti 0)" if "a \<in> actions" for a
  proof -
    have "W (StartDur a) = 0" using other_clocks by auto
    moreover
    have "0 < card timepoint_set" unfolding card_htps_len_htpl using 0 .
    hence "exec_time (at_start a) (ti 0) = \<epsilon> + 1" using exec_time_at_init fpl by blast
    ultimately
    show ?thesis by auto
  qed

  
   
  have ed: "W (EndDur a) + ?d = exec_time (at_end a) (ti 0)" if "a \<in> actions" for a
  proof -
    have "W (EndDur a) = 0" using other_clocks by auto
    moreover
    have "0 < card timepoint_set" unfolding card_htps_len_htpl using 0 by simp
    hence "exec_time (at_end a) (ti 0) = \<epsilon> + 1" using exec_time_at_init fpl by blast
    ultimately
    show ?thesis by auto
  qed
  
  have td: "0 \<le> ?d" using eps_range by simp

  show ?case 
    apply (rule instant_execution_cycle)
    using assms sd ed td by auto
next
  case (Suc l)
  then obtain W' where
    t1: "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle>"
    and pm: "prop_model W' (MS (Suc l))"
    and em: "exec_model W' (IES (ti l))"
    and sd: "\<forall>a\<in>actions. W' (StartDur a) = exec_time' (at_start a) (ti l)"
    and ed: "\<forall>a\<in>actions. W' (EndDur a) = exec_time' (at_end a) (ti l)" 
    and stop: "W' Stop = 0"
    and delta: "W' Delta = 0" by auto

  from Suc.prems em
  have em': "exec_model W' (ES (ti(Suc l)))" using inc_es_is_next_es[OF fpl] by auto

  from Suc.prems sd ed
  have sd': "\<forall>a\<in>actions. W' (StartDur a) + deltas (Suc l) = exec_time (at_start a) (ti(Suc l))"
     and ed': "\<forall>a \<in> actions. W' (EndDur a) + deltas (Suc l) = exec_time (at_end a) (ti(Suc l))"
    using updated_exec_time_and_next[OF fpl] by simp+

  have deltas: "0 \<le> deltas (Suc l)" using time_index_sorted_list[OF _ Suc.prems] by simp
    
  from instant_execution_cycle[where W = W' and MS = MS and l = "Suc l" and d = "deltas (Suc l)"]
    pm em' sd' ed' deltas stop delta vss nso pap dp dv nm fpl Suc.prems
  obtain W'' where
    t2: "\<T> \<turnstile> \<langle>Main, W'\<rangle> \<rightarrow>* \<langle>Main, W''\<rangle>"
    and pm: "prop_model W'' (MS (Suc (Suc l)))"
    and em: "exec_model W'' (IES (ti(Suc l)))"
    and sd: "\<forall>a\<in>actions. W'' (StartDur a) = exec_time' (at_start a) (ti(Suc l))"
    and ed: "\<forall>a\<in>actions. W'' (EndDur a) = exec_time' (at_end a) (ti(Suc l))" 
    and stop: "W'' Stop = 0"
    and delta: "W'' Delta = 0" by blast
  moreover
  have "\<T> \<turnstile> \<langle>Main, W\<rangle> \<rightarrow>* \<langle>Main, W''\<rangle>" using steps_trans[OF t1 t2] .
  ultimately
  show ?case by auto
qed

 
definition "W\<^sub>0 \<equiv> \<lambda>c. 0"

lemma automaton_complete:
  assumes vp: "vp_\<pi>"
      and fpl: "fp_\<pi>"
  shows "\<exists>W'. \<T> \<turnstile> \<langle>Init, W\<^sub>0\<rangle> \<rightarrow>* \<langle>Goal, W'\<rangle>"
proof - 
  from vp obtain MS where
      vss: "vss MS" 
  and MS: "MS 0 = init" "goal \<subseteq> MS (length timepoint_list)"
  and nso: "nso_\<pi>"
  and pap: "pap_\<pi>"
  and dp: "dp_\<pi>"
  and dv: "dv_\<pi>"
  and nm: "nm_happ_seq happ_seq"
    unfolding valid_plan_def valid_state_sequence_def by (auto simp: Let_def)
    

  define W\<^sub>I where "W\<^sub>I = [init_asmt] W\<^sub>0"

  have init_0: "\<forall>c. \<not>is_propositional_clock c \<longrightarrow> W\<^sub>I c = 0"
  proof - 
    have 1: "\<not>(\<exists>v. (c, v) \<in> set init_asmt)" if "\<not>is_propositional_clock c" for c
      using that apply (cases c)
      unfolding init_asmt_def by auto

    have "W\<^sub>I c = W\<^sub>0 c" if "\<not>is_propositional_clock c" for c
      using 1[OF that, THEN clock_set_none, where W = W\<^sub>0]
      unfolding W\<^sub>0_def W\<^sub>I_def by simp
    thus ?thesis unfolding W\<^sub>0_def by blast
  qed

  have init_trans: "\<T> \<turnstile> \<langle>Init, W\<^sub>0\<rangle> \<rightarrow>* \<langle>Main, W\<^sub>I\<rangle>"
  proof (rule steps_step, rule step_a, rule step_a.intros)
    show "\<T> \<turnstile> Init \<longrightarrow>\<^bsup>true_const,Unit,init_asmt\<^esup> Main" 
      unfolding trans_of_def prob_automaton_def initial_transition_def by auto

    show "W\<^sub>0 \<turnstile> true_const" unfolding true_const_def unfolding W\<^sub>0_def by blast

    thus "W\<^sub>I \<turnstile> inv_of \<T> Main" unfolding inv_of_def prob_automaton_def using init_0 by auto
    show "W\<^sub>I = [init_asmt]W\<^sub>0" using W\<^sub>I_def by blast
  qed
  
  have prop_model: "prop_model W\<^sub>I init"
  proof -
    have "prop_corr W\<^sub>I init pr" if "pr \<in> props" for pr
    proof (cases "pr \<in> init")
      case True
      have "pr \<in> set (prop_list init)" using set_prop_list[OF wf_init] True by blast
      hence 1: "(PropClock pr, 1) \<in> set init_asmt" unfolding init_asmt_def init_pos_def by simp
      
      have 2: "\<forall>v. (PropClock pr, v) \<in> set init_asmt \<longrightarrow> 1 = v" unfolding init_asmt_def by auto
      from clock_set_certain[OF 2 1]
      have "W\<^sub>I (PropClock pr) = 1" unfolding W\<^sub>I_def by blast
      with True
      show ?thesis by simp
    next
      case False
      have "pr \<notin>set (prop_list init)" using set_prop_list[OF wf_init] False by blast
      hence "\<not> (\<exists>v. (PropClock pr, v) \<in> set init_asmt)" unfolding init_asmt_def init_pos_def by auto
      from clock_set_none[OF this] 
      have "W\<^sub>I (PropClock pr) = 0" unfolding W\<^sub>I_def W\<^sub>0_def by simp
      with False
      show ?thesis by simp
    qed
    thus ?thesis unfolding prop_model_def by blast
  qed


  have exec_model: "exec_model W\<^sub>I {}" using init_0 unfolding exec_model_def by auto
  
  have "\<exists>W' Q. \<T> \<turnstile> \<langle>Main, W\<^sub>I\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle> 
  \<and> prop_model W' Q 
  \<and> goal \<subseteq> Q
  \<and> exec_model W' {}
  \<and> W' Stop = 0
  \<and> W' Delta = 0"
  proof (cases "length timepoint_list")
    case 0
    have "\<T> \<turnstile> \<langle>Main, W\<^sub>I\<rangle> \<rightarrow>* \<langle>Main, W\<^sub>I\<rangle>" using steps.refl by blast
    moreover
    have "goal \<subseteq> init" using MS 0 by simp
    moreover
    have "W\<^sub>I Stop = 0" "W\<^sub>I Delta = 0" using init_0 by auto
    ultimately
    show ?thesis using prop_model exec_model by blast
  next
    case (Suc nat)
    with prop_model
    have prop_model': "prop_model W\<^sub>I (MS 0)" using MS by blast

    from exec_model first_es_empty pap dp fpl 
    have exec_model: "exec_model W\<^sub>I (ES (ti 0))" by simp

    have stop: "W\<^sub>I Stop = 0" using init_0 by simp
    have delta: "W\<^sub>I Delta = 0" using init_0 by simp
    have other_clocks: "\<forall>c. \<not>(is_boolean_clock c) \<longrightarrow> W\<^sub>I c = 0"  
      apply (rule allI) 
      subgoal for c 
        apply (cases c) 
        by (auto simp: init_0)
      done

    have "length timepoint_list - 1 < length timepoint_list" "Suc (length timepoint_list - 1) = length timepoint_list" using Suc by simp+
    with prop_model' exec_model stop delta other_clocks vss nso pap dp dv nm fpl
    obtain W' where
      W': "\<T> \<turnstile> \<langle>Main, W\<^sub>I\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle>"
      "prop_model W' (MS (length timepoint_list))"
      "exec_model W' (IES (ti(length timepoint_list - 1)))" 
      "W' Stop = 0"
      "W' Delta = 0"
      using multiple_execution_cycles[where l = "length timepoint_list - 1", where W = "W\<^sub>I" and MS = MS] by auto
    from W'(3) 
    have em': "exec_model W' {}" using last_ies_empty pap dp fpl by auto
    with W'(1,2,4,5) MS(2)
    show ?thesis by blast
  qed
 
  then obtain W' Q where
    cycles: "\<T> \<turnstile> \<langle>Main, W\<^sub>I\<rangle> \<rightarrow>* \<langle>Main, W'\<rangle>" 
    and "prop_model W' Q" 
        "exec_model W' {}"
    and gQ: "goal \<subseteq> Q"
    and "W' Stop = 0" 
        "W' Delta = 0" by blast
  
  then obtain W'' where
    last_dec_trans: "\<T> \<turnstile> \<langle>Main, W'\<rangle> \<rightarrow>* \<langle>ExecDecoding (act M), W''\<rangle>"
    and pm_last: "prop_model W'' Q" 
    and em_last: "exec_model W'' {}" 
    and stop: "W'' Stop = 0"
    using main_to_dec_end by force

  have final_trans: "\<T> \<turnstile> \<langle>ExecDecoding (act M), W''\<rangle> \<rightarrow>* \<langle>Goal, W''\<rangle>"
  proof (rule steps_step, rule step_a, rule step_a.intros)
    show "\<T> \<turnstile> ExecDecoding (act M) \<longrightarrow>\<^bsup>goal_constraint,Unit,[]\<^esup> Goal"
      unfolding trans_of_def prob_automaton_def goal_trans_def by auto
    show "W'' \<turnstile> goal_constraint"
    proof -
      have "W'' \<turnstile> none_running"
      proof -
        have "W'' (Running a) = 0" if "a \<in> set action_list" for a
        proof -
          from that 
          have "a \<in> actions" using set_act_list by blast
          thus ?thesis using em_last unfolding exec_model_def by simp
        qed
        thus ?thesis unfolding none_running_def AND_ALL_iff list_all_iff by auto
      qed
      moreover
      have "W'' \<turnstile> goal_satisfied" 
      proof -
        have "W'' (PropClock pr) = 1" if "pr \<in> set (prop_list goal)" for pr
        proof -
          from that
          have "pr \<in> goal" "pr \<in> props" using set_prop_list wf_goal by auto
          with gQ
          have "pr \<in> Q" by blast+
          with pm_last \<open>pr \<in> props\<close>
          show "W'' (PropClock pr) = 1" unfolding prop_model_def by auto
        qed
        thus ?thesis unfolding goal_satisfied_def AND_ALL_iff list_all_iff by auto
      qed
      ultimately
      show ?thesis unfolding goal_constraint_def by auto
    qed
    show "W'' \<turnstile> inv_of \<T> Goal" using stop unfolding inv_of_def prob_automaton_def by auto
    show "W'' = [Nil]W''" by auto
  qed

  from init_trans cycles last_dec_trans final_trans
  have "\<T> \<turnstile> \<langle>Init, W\<^sub>0\<rangle> \<rightarrow>* \<langle>Goal, W''\<rangle>" 
    apply (elim steps_trans)
    by (rule steps.refl)
  thus ?thesis by blast
qed
end
end

end
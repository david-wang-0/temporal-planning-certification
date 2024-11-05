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

definition A ("A\<^sub>_" 65) where "A \<equiv> act"

abbreviation "M \<equiv> card actions"

definition "true_const \<equiv> GE Stop 0"

text \<open>Preventing time from passing in any location other than the main location.\<close>
fun invs::"(('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) invassn" where
  "invs Main  = GE Stop 0"
| "invs _     = EQ Stop 0"

abbreviation "prop_numbers S \<equiv> {n| n pr. n < N \<and> pr \<in> S \<and> (p n) = pr}"

definition "prop_list S \<equiv> map p (sorted_list_of_set (prop_numbers S))"

text \<open>The transition from the initial location \<open>l\<^sub>I\<close> to the main location \<open>l\<^sub>\<delta>\<close>\<close>
definition init_pos::"'proposition list" where
"init_pos \<equiv> prop_list init"

definition init_asmt::"(('proposition, 'action) clock, 'time) clkassn list" where
"init_asmt \<equiv> map (\<lambda>x. (PropClock x, 1)) init_pos"

definition initial_transition::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"initial_transition \<equiv> (Init, true_const, Unit, init_asmt, Main)"

text \<open>The transition from the main location \<open>l\<^sub>\<delta>\<close> to the \<open>0\<^sup>t\<^sup>h\<close> location of the location decoding path \<open>s\<^sub>0\<close>.\<close>
definition main_to_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"main_to_decoding \<equiv> (Main, true_const, Unit, [(Stop, 0)], PropDecoding (p 0))"

subsubsection \<open>State decoding\<close>

text \<open>The transitions between the decoding locations for the propositional clocks \<open>cp\<^sub>i\<close>\<close>
definition prop_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"prop_decoding \<equiv> {(PropDecoding (p n), CEQ (PropClock (p n)) Delta 1, Unit, [(PropClock (p n), 1)], PropDecoding (p (n + 1))) | n. n < N}
  \<union> {(PropDecoding (p n), CEQ (PropClock (p n)) Delta 0, Unit, [(PropClock (p n), 0)], PropDecoding (p (n + 1))) | n. n < N}"

text \<open>A transition from the decoding locations for propositional clocks to the decoding locations for
the execution clocks\<close>
definition prop_decoding_to_exec_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"prop_decoding_to_exec_decoding \<equiv> (PropDecoding (p N), true_const, Unit, [], ExecDecoding (act 0))"

text \<open>The transitions between the decoding locations for the execution clocks \<open>cr\<^sub>a\<close>\<close>
definition exec_decoding::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"exec_decoding \<equiv> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 1, Unit, [(Running (act m), 1)], ExecDecoding (act (m + 1))) | m. m < M}
  \<union> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 0, Unit, [(Running (act m), 0)], ExecDecoding (act (m + 1))) | m. m < M}"
(* To do: We index into (act M) here. Executable when actions are numbered from 0 to M - 1?
Change the locations to use number parameters?
 *)

text \<open>The transition from the execution decoding locations to the decision-making locations\<close>
definition exec_decoding_to_decision_making::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"exec_decoding_to_decision_making \<equiv> (ExecDecoding (act M), true_const, Unit, [], Decision (at_start (act 0)))"

subsubsection \<open>Decision-making\<close>

text \<open>Interfering snap-actions\<close>

definition interfering_at_start::"'snap_action \<Rightarrow> nat list" where
"interfering_at_start a = sorted_list_of_set {n. n < M \<and> (mutex_snap_action a (at_start (act n)) \<or> a = at_start (act n))}"

definition start_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"start_constraints a = map (\<lambda>b. GE (StartDur (act b)) \<delta>) (interfering_at_start a)"

definition interfering_at_end::"'snap_action \<Rightarrow> nat list" where
"interfering_at_end a = sorted_list_of_set {n. n < M \<and> (mutex_snap_action a (at_end (act n)) \<or> a = at_end (act n))}"

definition end_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint list" where
"end_constraints a = map (\<lambda>b. GE (EndDur (act b)) \<delta>) (interfering_at_end a)"

definition sep::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"sep a \<equiv> AND_ALL (start_constraints a @ end_constraints a)"

text \<open>The clock constraints for the precondition\<close>
definition pre_clocks::"'snap_action \<Rightarrow> ('proposition, 'action) clock list" where
"pre_clocks a \<equiv> map PropClock (prop_list (pre a))"

definition pre_constraint::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"pre_constraint a \<equiv> AND_ALL (map (\<lambda>c. EQ c 1) (pre_clocks a))"

text \<open>The guard constraints\<close>
definition guard::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"guard a \<equiv> AND (sep a) (pre_constraint a)"

definition guard_at_start::"'action \<Rightarrow> (('proposition, 'action) clock, 'time::time) dconstraint" where
"guard_at_start a \<equiv> AND (guard (at_start a)) (EQ (Running a) 0)"

definition guard_at_end::"'action \<Rightarrow> (('proposition, 'action) clock, 'time::time) dconstraint" where
"guard_at_end a \<equiv> 
  let l = case (lower a) of 
    (lower_bound.GT t) \<Rightarrow> GT (StartDur a) t
  | (lower_bound.GE t) \<Rightarrow> GE (StartDur a) t;
  u = case (upper a) of 
    (upper_bound.LT t) \<Rightarrow> LT (StartDur a) t
  | (upper_bound.LE t) \<Rightarrow> LE (StartDur a) t
  in
AND (AND (guard (at_end a)) (EQ (Running a) 1)) (AND l u)"

definition decision_making::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"decision_making \<equiv> 
  {(Decision (at_start (act m)), guard_at_start (act m), Unit, [(SchedStartSnap (act m), 1)], Decision (at_end (act m))) | m. m < M}
  \<union> {(Decision (at_start (act m)), true_const, Unit, [(SchedStartSnap (act m), 0)], Decision (at_end (act m))) | m. m < M}
  \<union> {(Decision (at_end (act m)), guard_at_end (act m), Unit, [(SchedEndSnap (act m), 1)], Decision (at_start (act (Suc m)))) | m. m < M}
  \<union> {(Decision (at_end (act m)), true_const, Unit, [(SchedEndSnap (act m), 0)], Decision (at_start (act (Suc m)))) | m. m < M}"

definition dm_to_exec::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"dm_to_exec \<equiv> (Decision (at_end (act M)), true_const, Unit, [], Execution (at_start (act 0)))"

subsubsection \<open>Execution\<close>

definition add_effects::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"add_effects s \<equiv> map (\<lambda>p. (PropClock p, 1)) (prop_list (adds s))"

definition del_effects::"'snap_action  \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"del_effects s \<equiv> map (\<lambda>p. (PropClock p, 1)) (prop_list ((dels s) - (adds s)))"

definition effects::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"effects s \<equiv> del_effects s @ add_effects s"

definition at_start_effects::"'action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"at_start_effects a \<equiv> (Running a, 1) # (StartDur a, 0) # effects (at_start a)"

definition at_end_effects::"'action \<Rightarrow> (('proposition, 'action) clock, 'time) clkassn list" where
"at_end_effects a \<equiv> (Running a, 0) # (EndDur a, 0) # effects (at_start a)"

definition execution::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition set" where
"execution \<equiv> 
  {(Execution (at_start (act m)), EQ (SchedStartSnap (act m)) 1, Unit, at_start_effects (act m), Execution (at_end (act m))) | m. m < M}
  \<union> {(Execution (at_start (act m)), true_const, Unit, [], Execution (at_end (act m))) | m. m < M}
  \<union> {(Execution (at_end (act m)), EQ (SchedEndSnap (act m)) 1, Unit, at_end_effects (act m), Execution (at_end (act (Suc m)))) | m. m < M}
  \<union> {(Execution (at_end (act m)), true_const, Unit, [], Decision (at_start (act (Suc m)))) | m. m < M}"
(* To do: again, a non-existent action is being accessed
The benefit here is that there is no need to change the indexing to {0..<2M} *)

subsubsection \<open>Over-all conditions\<close>
abbreviation "action_list \<equiv> map act (sorted_list_of_set {m. m < M})"

definition over_all_clocks::"'action \<Rightarrow> ('proposition, 'action) clock list" where
"over_all_clocks a \<equiv> map PropClock (prop_list (over_all a))"

definition action_over_all::"'action \<Rightarrow> (('proposition, 'action) clock, 'time) dconstraint" where
"action_over_all a \<equiv> AND_ALL (map (\<lambda>c. CLE (Running a) c 0) (over_all_clocks a))"

definition over_all_conds::"(('proposition, 'action) clock, 'time) dconstraint" where
"over_all_conds \<equiv> AND_ALL (map action_over_all action_list)"

definition exec_to_main::"(alpha, ('proposition, 'action) clock, 'time, ('proposition, 'action, 'snap_action) location) transition" where
"exec_to_main \<equiv> (Execution (at_end (act M)), over_all_conds, Unit, [(Delta, 0)], Main)"

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

context temporal_plan
begin             

abbreviation "B" where "B \<equiv> happ_at plan_happ_seq"

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

definition partial_exec_model::"(('proposition, 'action) clock, 'time) cval \<Rightarrow> 'action state \<Rightarrow> bool" where
"partial_exec_model W E \<equiv> \<forall>m < M. (W (Running (act m)) = 1 \<longleftrightarrow> (act m) \<in> E) \<and> (W (Running (act m)) = 0 \<longleftrightarrow> (act m) \<notin> E)"

definition exec_state_sequence::"('time \<times> 'action) set" where
"exec_state_sequence \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s < t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)}"

definition exec_state_sequence'::"('time \<times> 'action) set" where
"exec_state_sequence' \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s \<le> t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> t)}"

abbreviation "ES t \<equiv> {a. (t, a) \<in> exec_state_sequence}"

abbreviation "IES t \<equiv> {a. (t, a) \<in> exec_state_sequence'}"

lemma inc_es_is_next_es:
  assumes "finite_plan"
      and "Suc l < length htpl"
  shows "IES (time_index l) = ES (time_index (Suc l))"
proof (rule equalityI; rule subsetI)
  fix a
  assume "a \<in> IES (time_index l)"
  then obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s \<le> time_index l"
    "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> time_index l)"
    unfolding exec_state_sequence'_def by blast
  from this(2) time_index_strict_sorted_list[rotated, OF assms(2)] no_actions_between_indexed_timepoints[OF assms]
  have "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < time_index (Suc l))"
    using happ_at_def by fastforce
  with time_index_strict_sorted_list[rotated, OF \<open>Suc l < length htpl\<close>] s(1)
  show "a \<in> ES (time_index (Suc l))" using exec_state_sequence_def by force
next
  fix a
  assume "a \<in> ES (time_index (Suc l))"
  then obtain s where
    s: "a \<in> actions"
    "(s, at_start a) \<in> plan_happ_seq"  
    "s < time_index (Suc l)"
    "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < time_index (Suc l))"
    unfolding exec_state_sequence_def by blast
  from this(2, 3) no_actions_between_indexed_timepoints[OF assms]
  have "s \<le> time_index l" using happ_at_def by fastforce
  moreover
  have "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> time_index l)" 
  proof (rule notI)
    assume "\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> time_index l"
    with time_index_strict_sorted_list assms(2)
    have "\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < time_index (Suc l)" by fastforce
    with s(4)
    show "False" by blast
  qed
  ultimately
  show "a \<in> IES (time_index l)" using s(1,2) exec_state_sequence'_def by blast
qed

lemma last_ies_empty:
  assumes pap: "plan_actions_in_problem"
      and dnz: "durations_positive"
      and fpl:  "finite_plan"
  shows "IES (time_index (length htpl - 1)) = {}" (is "IES ?te = {}")
proof -
  have "a \<notin> IES ?te" for a
  proof (rule notI)
    assume a: "a \<in> IES ?te"
    then obtain s where
      s: "a \<in> actions"
      "(s, at_start a) \<in> plan_happ_seq" 
      "s \<le> ?te"
      "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> ?te)"
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
      "(s + d, at_end a) \<in> plan_happ_seq" using plan_happ_seq_def by blast
    with s(4) assms(2)[simplified durations_positive_def]
    have "s + d > ?te" by fastforce
    
    have "t \<le> ?te" if "t \<in> set htpl" for t
    proof -
      from that[simplified time_index_bij_betw_list[simplified bij_betw_def, THEN conjunct2, symmetric]]
      obtain n where
        n: "n < length htpl \<and> time_index n = t" by blast
      show "t \<le> ?te"
      proof (cases "n < length htpl - 1")
        case True
        with n
        show ?thesis using time_index_strict_sorted_list by fastforce
      next
        case False
        hence "n = length htpl - 1" using n by linarith
        thus ?thesis using n by blast
      qed
    qed
    moreover
    
    from d(1) set_htpl_eq_htps[OF fpl] htps_def
    have "s + d \<in> set htpl" by blast
    ultimately
    show False using \<open>s + d > ?te\<close> by fastforce
  qed
  thus "IES ?te = {}" by blast
qed


lemma not_executing_when_starting:
  assumes snap_in_B: "(at_start a) \<in> B t"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap: no_self_overlap
      and durations_positive: durations_positive
      and plan_actions_in_problem: plan_actions_in_problem
  shows "a \<notin> ES t"
proof (rule notI)
  assume "a \<in> ES t"
  then obtain s where
    started: "a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s < t"
    and not_ended: "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)"
    unfolding exec_state_sequence_def by blast
  
  from started
  obtain d where
    as_in_plan: "(a, s, d) \<in> ran \<pi>"
    using at_start_in_happ_seqE assms by blast+
  hence "(s + d, at_end a) \<in> plan_happ_seq" unfolding plan_happ_seq_def by blast
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
      and no_self_overlap: no_self_overlap
      and durations_positive: durations_positive
      and plan_actions_in_problem: plan_actions_in_problem
    shows "a \<in> ES t"
proof -
  from snap_in_B
  obtain s d where
    s: "(a, s, d) \<in> ran \<pi>"   
    "t = s + d"
    using at_end_in_happ_seqE assms unfolding happ_at_def by blast
  with durations_positive[simplified durations_positive_def] 
  have "(s, at_start a) \<in> plan_happ_seq \<and> s < t" unfolding plan_happ_seq_def by auto
  moreover
  have "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)"
  proof (rule notI)
    assume "\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t"
    then obtain s' where
      s': "(s', at_end a) \<in> plan_happ_seq" 
      "s \<le> s' \<and> s' < t" by auto
  
    then obtain \<tau> \<delta> where
      \<tau>: "(a, \<tau>, \<delta>) \<in> ran \<pi>"
      "s' = \<tau> + \<delta>"
      using at_end_in_happ_seqE assms by blast

    hence "(\<tau>, at_start a) \<in> plan_happ_seq" unfolding plan_happ_seq_def by blast

    consider "\<tau> \<le> s" | "s \<le> \<tau>" by fastforce
    thus False
    proof cases
      case 1
      with s'(2) s(2) \<tau>(2)
      have "\<tau> = s \<longrightarrow> \<delta> \<noteq> d" by blast
      with no_self_overlap[THEN no_self_overlap_spec, OF \<tau>(1) s(1)] 1 s'(2) \<tau>(2) 
      show ?thesis by blast
    next
      case 2
      from \<open>s \<le> s' \<and> s' < t\<close>[simplified \<open>t = s + d\<close> \<open>s' = \<tau> + \<delta>\<close>] 
        durations_positive[simplified durations_positive_def] \<open>(a, \<tau>, \<delta>) \<in> ran \<pi>\<close>
      have "\<tau> \<le> s + d" by (meson less_add_same_cancel1 order_le_less_trans order_less_imp_le)
      moreover
      from 2 s'(2) s(2) \<tau>(2)
      have "\<tau> = s \<longrightarrow> \<delta> \<noteq> d" by blast
      ultimately 
      show ?thesis using 2 no_self_overlap[THEN no_self_overlap_spec, OF s(1) \<tau>(1)] by blast
    qed
  qed
  ultimately
  show ?thesis unfolding exec_state_sequence_def using a_in_actions by blast
qed

subsubsection \<open>Execution time\<close>

definition pt::"'snap_action \<Rightarrow> ('time \<Rightarrow> 'time \<Rightarrow> bool) \<Rightarrow> 'time \<Rightarrow> 'time" where
"pt a c t \<equiv> if (\<exists>t'. c t' t \<and> a \<in> B t') then (Greatest (\<lambda>t'. c t' t \<and> a \<in> B t')) else (Least (\<lambda>t'. B t' \<noteq> {}) - \<delta>)"

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
find_theorems name: "Greatest*I"
lemma a_in_b_last_now: "a \<in> B t \<Longrightarrow> last_snap_exec' a t = t"
  using pt_def
  by (auto intro: Greatest_equality)

lemma subseq_last_snap_exec:
  assumes fpl: finite_plan
      and llen: "(Suc l) < length htpl" 
shows "last_snap_exec a (time_index (Suc l)) = last_snap_exec' a (time_index l)"
proof -

  define t where 
    "t = last_snap_exec a (time_index (Suc l))"    

  define s where
    "s = last_snap_exec' a (time_index l)" 
  
  have cl: "length htpl = card htps" using htpl_def by fastforce
  
  have tl_ord: "time_index l < time_index (Suc l)" 
    using time_index_strict_sorted_list llen
    by blast
  
  from t_def consider "\<exists>t'. t' < (time_index (Suc l)) \<and> a \<in> B t'" 
    | "\<not>(\<exists>t'. t' < (time_index (Suc l)) \<and> a \<in> B t')" by auto
  hence "t = s"
  proof cases
    case 1 
    hence exsl: "Ex (\<lambda>t'. t' < time_index (Suc l) \<and> a \<in> B t')" (is "Ex ?psl") by blast
    have "\<forall>t'. t' < time_index (Suc l) \<and> a \<in> B t' \<longrightarrow> t' \<le> time_index l"
      using time_index_strict_sorted_list[OF _ llen] time_index_sorted_list[OF _ llen] 
        no_actions_between_indexed_timepoints[OF assms] by fastforce
    moreover
    have "\<forall>t'. t' \<le> time_index l \<and> a \<in> B t' \<longrightarrow> t' < time_index (Suc l)" 
      using time_index_strict_sorted_list[OF _ llen] time_index_sorted_list[OF _ llen] 
        no_actions_between_indexed_timepoints[OF assms] by fastforce
    ultimately 
    have fa: "\<forall>t'. t' < time_index (Suc l) \<and> a \<in> B t' \<longleftrightarrow> t' \<le> time_index l \<and> a \<in> B t'" by blast
    with 1
    have exl: "Ex (\<lambda>t'. t' \<le> time_index l \<and> a \<in> B t')" (is "Ex ?pl") by blast
    from fa
    have "Greatest ?psl = Greatest ?pl" by auto
    thus "t = s" unfolding t_def s_def pt_def using exl exsl by auto
  next
    case 2
    hence "\<not> (\<exists>t' \<le> time_index l. a \<in> B t')" using tl_ord by force
    with 2 t_def[simplified pt_def] s_def[simplified pt_def]
    show ?thesis by auto
  qed
  thus "last_snap_exec a (time_index (Suc l)) = last_snap_exec' a (time_index l)" 
    using s_def t_def by auto
  qed

lemma updated_exec_time_and_next: 
  assumes finite_plan
      and "Suc l < length htpl"
  shows "exec_time a (time_index (Suc l)) = (exec_time' a (time_index l)) + (time_index (Suc l) - time_index l)"
  using subseq_last_snap_exec[OF assms] exec_time_def exec_time'_def 
  by simp

lemma exec_time_and_epsilon:
  assumes nm: "nm_happ_seq plan_happ_seq"
      and s_at_t: "s \<in> B t"
      and mutex: "mutex_snap_action s b \<or> s = b"
      and finite_plan: finite_plan
    shows "exec_time b t \<ge> \<delta>"
proof (cases "\<exists>u < t. b \<in> B u")
  case True
  have b_at_t': "(\<lambda>u. u < t \<and> b \<in> B u) (last_snap_exec b t)" (is "?t < t \<and> b \<in> B ?t")
    unfolding pt_def using GreatestI_ex_time[OF True] by auto
  have nm_cond: "t - ?t < \<delta> \<and> ?t - t < \<delta> \<and> s \<in> (B t) \<and> b \<in> (B ?t) 
    \<longrightarrow> ((s \<noteq> b \<longrightarrow> \<not>mutex_snap_action s b) \<and> (s = b \<longrightarrow> t = ?t))" using nm nm_happ_seq_def by blast
  hence "\<not>(s \<noteq> b \<longrightarrow> \<not>mutex_snap_action s b) \<or> \<not>(s = b \<longrightarrow> t = ?t)
    \<longrightarrow> t - ?t \<ge> \<delta> \<or> ?t - t \<ge> \<delta> \<or> s \<notin> (B t) \<or> b \<notin> (B ?t)" by auto
  hence "\<not>(s \<noteq> b \<longrightarrow> \<not>mutex_snap_action s b) \<or> \<not>(s = b \<longrightarrow> t = ?t)
    \<longrightarrow> t - ?t \<ge> \<delta> \<or> ?t - t \<ge> \<delta>"  using s_at_t b_at_t' by blast
  hence "(s \<noteq> b \<and> mutex_snap_action s b) \<or> (s = b \<and> t \<noteq> ?t)
    \<longrightarrow> t - ?t \<ge> \<delta> \<or> ?t - t \<ge> \<delta>"  by blast
  moreover
  have "s \<noteq> b \<longrightarrow> mutex_snap_action s b" using mutex by blast
  moreover
  have "t \<noteq> ?t" using b_at_t' by auto
  ultimately
  consider "t - ?t \<ge> \<delta>" | "?t - t \<ge> \<delta>" by auto
  note c = this
  
  have "t > ?t" using b_at_t' by blast
  moreover
  have "\<delta> \<ge> 0" using \<delta>_def eps_range least_time_gt_0 less_le_not_le by fastforce
  ultimately 
  have "t - ?t \<ge> \<delta>"  apply (cases rule: c) apply blast using order.trans by fastforce
  thus ?thesis using exec_time_def by auto
next
  case False
  have 1: "time_index 0 \<le> u" if "B u \<noteq> {}" for u
  proof -
    have "u \<in> set htpl" using that a_in_B_iff_t_in_htps set_htpl_eq_htps[OF finite_plan] by auto
    hence "\<exists>i. time_index i = u \<and> i < length htpl" using time_index_img_list by force
    thus "time_index 0 \<le> u" using time_index_sorted_list by blast
  qed
  moreover
  have "Least (\<lambda>t. B t \<noteq> {}) = (time_index 0)" 
  proof (rule Least_equality[OF _ 1])
    have "card htps > 0" using a_in_B_iff_t_in_htps s_at_t card_gt_0_iff finite_htps finite_plan by blast
    hence "time_index 0 \<in> htps" using time_index_img_set[OF finite_plan] by blast
    thus "B (time_index 0) \<noteq> {}" using a_in_B_iff_t_in_htps by auto
  qed
  ultimately
  have "t - last_snap_exec b t \<ge> \<delta>" using s_at_t False unfolding pt_def by auto
  thus ?thesis unfolding exec_time_def by simp
qed

lemma exec_time_and_duration:
  assumes "at_end a \<in> B t"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap
      and durations_positive
      and plan_actions_in_problem
  shows "\<exists>t' d. (a, t', d) \<in> ran \<pi> \<and> exec_time (at_start a) t = d"
proof -
  have "\<exists>!(s,d). (a, s, d) \<in> ran \<pi> \<and> t = s + d" using at_end_in_happ_seqE[OF _ assms(2,3,4,5)] assms(1)[simplified happ_at_def] by simp
  then obtain s d where
    sd: "(a, s, d) \<in> ran \<pi>" 
    "t = s + d" by auto
  with \<open>durations_positive\<close>
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
    thus False using that st' sd \<open>no_self_overlap\<close>[THEN no_self_overlap_spec] by force
  qed
  ultimately
  have "(GREATEST s. s < t \<and> at_start a \<in> B s) = s" unfolding Greatest_def by fastforce
  hence "exec_time (at_start a) t = d" using sd(2) wit unfolding exec_time_def pt_def by auto
  thus ?thesis using sd(1) by blast
qed

lemma exec_time_sat_dur_const:
  assumes "at_end a \<in> B t"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap
      and durations_positive
      and plan_actions_in_problem
      and durations_valid
    shows "satisfies_duration_bounds a (exec_time (at_start a) t)"
  using exec_time_and_duration[OF assms(1,2,3,4,5)] \<open>durations_valid\<close>[simplified durations_valid_def]
  by blast

subsubsection \<open>Restricting snap action sets by an upper limit on the index\<close>

definition limited_snap_action_set::"'snap_action set \<Rightarrow> nat \<Rightarrow> 'snap_action set" where
"limited_snap_action_set S m = 
  {at_start (act n) | n. n < m \<and> at_start (act n) \<in> S} 
  \<union> {at_end (act n) | n. n < m \<and> at_end (act n) \<in> S}"

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

definition partial_exec_time_update::"'snap_action \<Rightarrow> 'time \<Rightarrow> nat \<Rightarrow> 'time" where
"partial_exec_time_update a t m \<equiv> if (a \<in> B_lim t m) then 0 else exec_time a t"

lemma B_lim_M_eq_B:
  assumes "plan_actions_in_problem"
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

lemma exec_time_full_upd_eq_exec_time': 
  assumes "plan_actions_in_problem"
  shows "partial_exec_time_update a t M = exec_time' a t"
  using partial_exec_time_update_def exec_time_def exec_time'_def 
    a_not_in_b_last_unchanged a_in_b_last_now B_lim_M_eq_B[OF assms(1)]
  by simp 

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
      have 1: "W (PropClock (p n)) - W Delta = 1 \<Longrightarrow> W \<turnstile> CEQ (PropClock (p n)) Delta 1"
        by (metis add.commute clock_val.intros(9) diff_add_cancel)
      
      have "\<T> pd \<turnstile> \<langle>PropDecoding (p n), W\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>PropDecoding (p (Suc n)), W'\<rangle>"
        apply (rule step_a.intros[where g = "CEQ (PropClock (p n)) Delta 1"])
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
    using propositional_decoding_strong[where n = "N - 1"] Suc_diff_1[OF some_props] some_props
    prop_model_def[simplified props_pred]
    by auto

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
    show ?thesis using steps_trans[OF W'(1) prop_dec_to_exec_dec[where W = W', OF W'(5)]] W' by blast                         
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
      have 1: "W (Running (act m)) - W Delta = 1 \<Longrightarrow> W \<turnstile> CEQ (Running (act m)) Delta 1"
        by (metis add.commute clock_val.intros(9) diff_add_cancel)
      
      have "\<T> ed \<turnstile> \<langle>ExecDecoding (act m), W\<rangle> \<rightarrow>\<^bsub>Unit\<^esub> \<langle>ExecDecoding (act (Suc m)), W'\<rangle>"
        apply (rule step_a.intros[where g = "CEQ (Running (act m)) Delta 1"])
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
    using execution_decoding_strong[OF dem, where m = "M - 1", OF _ stop_inv] 
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

definition decision_making_automaton ("\<T> dm") where
"decision_making_automaton = (decision_making \<union> {dm_to_exec}, invs)"

lemma decision_making:
  assumes l_len: "l < length htpl" 
      and MS_valid: "valid_state_sequence MS"
      and prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (time_index l))"
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (time_index l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (time_index l)"
      and stop: "W Stop = 0"
      and nm: "nm_happ_seq plan_happ_seq"
      and fpl: finite_plan
      and no_self_overlap: no_self_overlap
      and durations_positive: durations_positive
      and plan_actions_in_problem: plan_actions_in_problem
  shows "\<exists>W'. \<T> \<turnstile> \<langle>Decision (at_start (act 0)), W\<rangle> \<rightarrow>* \<langle>Decision (at_start (act M)), W'\<rangle> 
    \<and> snap_exec_sched_corr W (B (time_index l))
    \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)"
proof -
  have W_sat_guard: "W \<turnstile> guard snap" 
       if snap_in_B: "snap \<in> B (time_index l)"
      and prop_clocks: "prop_model W (MS l)"
      and exec_clocks: "exec_model W (ES (time_index l))" 
      and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (time_index l)"
      and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (time_index l)"
      and stop: "W Stop = 0" for snap W
  proof -
    have "W \<turnstile> sep snap"
    proof -
      { fix b
        assume b: "b \<in> set (interfering_at_start snap)"
        hence b_in_act: "act b \<in> actions" unfolding interfering_at_start_def using act_img_actions by auto
        have "b \<in> {n. n < M \<and> (mutex_snap_action snap (at_start (act n)) \<or> snap = at_start (act n))}" 
          using b unfolding interfering_at_start_def by auto
        hence "\<delta> \<le> exec_time (at_start (act b)) (time_index l)" using exec_time_and_epsilon[OF nm snap_in_B _ fpl] by blast
        hence "W \<turnstile> dconstraint.GE (StartDur (act b)) \<delta>" using start_durs[THEN bspec, OF b_in_act] by auto
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
        hence "\<delta> \<le> exec_time (at_end (act b)) (time_index l)" using exec_time_and_epsilon[OF nm snap_in_B _ fpl] by blast
        hence "W \<turnstile> dconstraint.GE (EndDur (act b)) \<delta>" using end_durs b_in_act by auto
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
          plan_actions_in_problem[simplified plan_actions_in_problem_def] by blast
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
        \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (time_index l)) (act n))
        \<and> (\<forall>n < m. end_snap_sched_corr W' (B (time_index l)) (act n))
        \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)" 
    if prop_clocks: "prop_model W (MS l)"
    and exec_clocks: "exec_model W (ES (time_index l))"
    and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (time_index l)"
    and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (time_index l)"
    and stop: "W Stop = 0"
    and m: "m < M"
    and s_snap_corr: "\<forall>n < m. start_snap_sched_corr W (B (time_index l)) (act n)"
    and e_snap_corr: "\<forall>n < m. end_snap_sched_corr W (B (time_index l)) (act n)"
  for W m
  proof (cases "at_start (act m) \<in> B (time_index l)")
    case True
    have trans: "(Decision (at_start (act m)), guard_at_start (act m), Unit, [(SchedStartSnap (act m), 1)], Decision (at_end (act m))) \<in> trans_of \<T> dm"
      unfolding decision_making_automaton_def decision_making_def trans_of_def using m by auto
    
    have guard_sat: "W \<turnstile> guard_at_start (act m)" 
    proof -
      have "W \<turnstile> guard (at_start (act m))" using W_sat_guard[OF True prop_clocks exec_clocks start_durs end_durs stop] .
      moreover 
      have "act m \<in> actions" using act_img_actions m by blast
      hence "W (Running (act m)) = 0" using exec_clocks[simplified exec_model_def] 
        not_executing_when_starting[OF True _ no_self_overlap durations_positive plan_actions_in_problem]
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
      have "start_snap_sched_corr W' (B (time_index l)) (act m)" using True unfolding W'_def start_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. start_snap_sched_corr W' (B (time_index l)) (act n))" using s_snap_corr unfolding start_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. start_snap_sched_corr W' (B (time_index l)) (act n))" using less_antisym by blast
    }
    moreover
    { 
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (time_index l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
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
      have "start_snap_sched_corr W' (B (time_index l)) (act m)" using False unfolding W'_def start_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. start_snap_sched_corr W' (B (time_index l)) (act n))" using s_snap_corr unfolding start_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. start_snap_sched_corr W' (B (time_index l)) (act n))" using less_antisym by blast
    }
    moreover
    { 
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (time_index l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
    }
    moreover
    have "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c)" unfolding W'_def by simp
    ultimately
    show ?thesis by meson
  qed

  have at_end_step: "\<exists>W'. \<T> dm \<turnstile> \<langle>Decision (at_end (act m)), W\<rangle> \<rightarrow> \<langle>Decision (at_start (act (Suc m))), W'\<rangle>
        \<and> (\<forall>n < (Suc m). start_snap_sched_corr W' (B (time_index l)) (act n))
        \<and> (\<forall>n < (Suc m). end_snap_sched_corr W' (B (time_index l)) (act n))
        \<and> (\<forall>c. \<not>(is_snap_dec_clock c) \<longrightarrow> W c = W' c)" 
    if prop_clocks: "prop_model W (MS l)"
    and exec_clocks: "exec_model W (ES (time_index l))"
    and start_durs: "\<forall>a \<in> actions. W (StartDur a) = exec_time (at_start a) (time_index l)"
    and end_durs: "\<forall>a \<in> actions. W (EndDur a) = exec_time (at_end a) (time_index l)"
    and stop: "W Stop = 0"
    and m: "m < M"
    and s_snap_corr: "\<forall>n < Suc m. start_snap_sched_corr W (B (time_index l)) (act n)"
    and e_snap_corr: "\<forall>n < m. end_snap_sched_corr W (B (time_index l)) (act n)"
  for W m
  proof (cases "at_start (act m) \<in> B (time_index l)")
    case True
    have trans: "(Decision (at_end (act m)), guard_at_end (act m), Unit, [(SchedEndSnap (act m), 1)], Decision (at_start (act (Suc m)))) \<in> trans_of \<T> dm"
      unfolding decision_making_automaton_def decision_making_def trans_of_def using m by auto
    
    have guard_sat: "W \<turnstile> guard_at_end (act m)"
    proof -
      have m_in_acts: "act m \<in> actions" using m act_img_actions by blast
      have "W \<turnstile> (EQ (Running (act m)) 0)" 
      proof -
        have "act m \<notin> ES (time_index l)" 
          using not_executing_when_starting[OF True _ no_self_overlap durations_positive plan_actions_in_problem] m_in_acts
          by blast
        hence "W (Running (act m)) = 0" using exec_clocks exec_model_def m_in_acts by force
        thus ?thesis by blast
      qed
      moreover
      have "W \<turnstile> (guard (at_start (act m)))"
      proof -
        have "W \<turnstile> sep (at_start (act m))"
        proof -
          { fix b
            assume b: "b \<in> set (interfering_at_start (at_start (act m)))"
            hence b_in_act: "act b \<in> actions" unfolding interfering_at_start_def using act_img_actions by auto
            have "b \<in> {n. n < M \<and> (mutex_snap_action (at_start (act m)) (at_start (act n)) \<or> at_start (act m) = at_start (act n))}" 
              using b unfolding interfering_at_start_def by auto
            hence "\<delta> \<le> exec_time (at_start (act b)) (time_index l)" using exec_time_and_epsilon[OF nm True _ fpl] by blast
            hence "W \<turnstile> dconstraint.GE (StartDur (act b)) \<delta>" using start_durs b_in_act by auto
          }
          hence "list_all (clock_val W) (start_constraints (at_start (act m)))" 
            unfolding start_constraints_def
            by (subst list_all_iff) auto
          hence "W \<turnstile> AND_ALL (start_constraints (at_start (act m)))" using AND_ALL_iff by blast
          moreover
          { fix b
            assume b: "b \<in> set (interfering_at_end (at_start (act m)))"
            hence b_in_act: "act b \<in> actions" unfolding interfering_at_end_def using act_img_actions by auto
            have "b \<in> {n. n < M \<and> (mutex_snap_action (at_start (act m)) (at_end (act n)) \<or> at_start (act m) = at_end (act n))}" 
              using b unfolding interfering_at_end_def by auto
            hence "\<delta> \<le> exec_time (at_end (act b)) (time_index l)" using exec_time_and_epsilon[OF nm True _ fpl] by blast
            hence "W \<turnstile> dconstraint.GE (EndDur (act b)) \<delta>" using end_durs b_in_act by auto
          }
          hence "list_all (clock_val W) (end_constraints (at_start (act m)))" 
            unfolding end_constraints_def
            by (subst list_all_iff) auto
          hence "W \<turnstile> AND_ALL (end_constraints (at_start (act m)))" using AND_ALL_iff by blast
          ultimately
          show ?thesis unfolding sep_def using AND_ALL_iff list_all_append by blast
        qed
        moreover
        have "W \<turnstile> (pre_constraint (at_start (act m)))"
        proof -
          { fix c
            assume "c \<in> set (pre_clocks (at_start (act m)))"
            then obtain pr where
              pr: "pr \<in> set (prop_list (pre (at_start (act m))))"
              and cpr: "c = PropClock pr" using pre_clocks_def by auto
            moreover
            have "finite (prop_numbers (pre (at_start (act m))))" by simp
            ultimately
            have pr_in_pre: "pr \<in> pre (at_start (act m))" using set_sorted_list_of_set unfolding prop_list_def by auto
            hence "pr \<in> MS l" using MS_valid[simplified valid_state_sequence_def] l_len True by (auto simp: Let_def)
            moreover
            have "pr \<in> props" using wf_acts pr_in_pre m act_img_actions by fastforce
            ultimately
            have "W c = 1" using prop_clocks cpr unfolding prop_model_def by blast
          }
          hence "W \<turnstile> AND_ALL (map (\<lambda>c. EQ c 1) (pre_clocks (at_start (act m))))" 
            unfolding AND_ALL_iff list_all_iff by auto
          thus ?thesis using pre_constraint_def by simp
        qed
        ultimately
        show "W \<turnstile> guard (at_start (act m))" unfolding guard_def by blast
      qed
      ultimately
      show "W \<turnstile> guard_at_start (act m)" using guard_at_start_def by auto
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
      have "start_snap_sched_corr W' (B (time_index l)) (act m)" using True unfolding W'_def start_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. start_snap_sched_corr W' (B (time_index l)) (act n))" using s_snap_corr unfolding start_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. start_snap_sched_corr W' (B (time_index l)) (act n))" using less_antisym by blast
    }
    moreover
    { 
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (time_index l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
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
      have "start_snap_sched_corr W' (B (time_index l)) (act m)" using False unfolding W'_def start_snap_sched_corr_def by simp
      moreover
      have "\<forall>n < m. W' (SchedStartSnap (act n)) = W (SchedStartSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. start_snap_sched_corr W' (B (time_index l)) (act n))" using s_snap_corr unfolding start_snap_sched_corr_def by auto
      ultimately
      have "(\<forall>n < Suc m. start_snap_sched_corr W' (B (time_index l)) (act n))" using less_antisym by blast
    }
    moreover
    { 
      have "\<forall>n < m. W' (SchedEndSnap (act n)) = W (SchedEndSnap (act n))" using act_inj_on[simplified inj_on_def] m unfolding W'_def by fastforce
      hence "(\<forall>n < m. end_snap_sched_corr W' (B (time_index l)) (act n))" using e_snap_corr unfolding end_snap_sched_corr_def by auto
    }
    moreover
    have "(\<forall>c. \<not> is_snap_dec_clock c \<longrightarrow> W c = W' c)" unfolding W'_def by simp
    ultimately
    show ?thesis by meson
  qed


qed

definition "W\<^sub>0 \<equiv> \<lambda>c. 0"

lemma automaton_complete: "\<exists>W'. \<T> \<turnstile> \<langle>Init, W\<^sub>0\<rangle> \<rightarrow>* \<langle>Goal, W'\<rangle>"
  sorry
end

end
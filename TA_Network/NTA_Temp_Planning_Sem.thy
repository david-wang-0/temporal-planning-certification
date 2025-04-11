theory NTA_Temp_Planning_Sem
  imports Temporal_Planning_Base.Temporal_Plans
begin

locale nta_temp_planning = 
  finite_props_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions  +
  unique_snaps_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions 
    for init::    "'proposition set"
    and goal::    "'proposition set"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and \<epsilon>::       "'time"
    and props::   "'proposition set"
    and actions:: "'action set" 
+  
fixes \<pi>::"('i, 'action, 'time) temp_plan"
  and c::'time
assumes vp: "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon>"
    and pap: "plan_actions_in_problem \<pi> actions"
    and nso: "no_self_overlap \<pi>"
    and c: "0 < c" (* \<epsilon> + c is an initial delta transition. Necessary to not violate clock constraints
                      for mutual exclusivity. *)
begin

lemma at_start_inj_on_plan:
  "inj_on at_start {a| a t d. (a, t, d) \<in> ran \<pi>}"
  using pap at_start_inj_on unfolding inj_on_def plan_actions_in_problem_def by blast

lemma at_end_inj_on_plan:
  "inj_on at_end {a| a t d. (a, t, d) \<in> ran \<pi>}"
  using pap at_end_inj_on unfolding inj_on_def plan_actions_in_problem_def by blast

lemma snaps_disj_on_plan:
  "at_start ` {a| a t d. (a, t, d) \<in> ran \<pi>} \<inter> at_end ` {a| a t d. (a, t, d) \<in> ran \<pi>} = {}"
  using pap snaps_disj unfolding plan_actions_in_problem_def by fast

lemma at_start_in_happ_seqE':
  assumes a_in_acts: "a \<in> actions"
      and sn: "(s, at_start a) \<in> plan_happ_seq \<pi> at_start at_end"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  using at_start_in_happ_seqE[OF _ at_start_inj_on at_end_inj_on snaps_disj sn a_in_acts nso]
  using pap unfolding plan_actions_in_problem_def 
  using vp unfolding valid_plan_def by auto

lemma at_end_in_happ_seqE':
  assumes a_in_acts: "a \<in> actions"
      and sn: "(s, at_end a) \<in> plan_happ_seq \<pi> at_start at_end"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"
  using at_end_in_happ_seqE[OF _ at_start_inj_on at_end_inj_on snaps_disj sn a_in_acts nso]
  using pap unfolding plan_actions_in_problem_def 
  using vp unfolding valid_plan_def by auto
  
lemma eps_cases: 
  assumes "\<epsilon> = 0 \<Longrightarrow> thesis"
      and "0 \<le> \<epsilon> \<Longrightarrow> thesis"
    shows "thesis"
  using assms eps_range by blast

abbreviation snaps::"'action \<Rightarrow> 'snap_action set" where
"snaps a \<equiv> {at_start a, at_end a}"

definition snap_actions::"'snap_action set" where
"snap_actions \<equiv> (at_start ` actions) \<union> (at_end ` actions)"


definition "happ_seq \<equiv> plan_happ_seq \<pi> at_start at_end"

definition "pap \<equiv> plan_actions_in_problem \<pi> actions"

definition "dur_valid \<equiv> durations_valid \<pi> lower upper"

definition "valid_state_seq \<equiv> valid_state_sequence \<pi> at_start at_end over_all pre adds dels"

definition "invariant_sequence = plan_inv_seq \<pi> over_all"

definition "mutex_snap \<equiv> mutex_snap_action pre adds dels"

definition "mutex_valid_happ_seq = nm_happ_seq pre adds dels \<epsilon> happ_seq"

definition "dur_bounds_sat = satisfies_duration_bounds lower upper"

definition "app_effs \<equiv> apply_effects adds dels"

definition "plan_state_seq \<equiv> SOME MS. valid_state_seq MS"

lemma plan_state_seq_valid: "valid_state_seq plan_state_seq"
  using vp unfolding valid_plan_def Let_def  valid_state_seq_def 
    plan_state_seq_def 
  unfolding valid_state_seq_def[symmetric]
  apply -
  apply (rule  Hilbert_Choice.someI_ex[where P = valid_state_seq])
  by blast

subsubsection \<open>Execution state\<close>

text \<open>Binary, but could be changed to count the active instances.\<close>

definition exec_state_sequence::"('time \<times> 'action) set" where
"exec_state_sequence \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s < t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)}"

definition exec_state_sequence'::"('time \<times> 'action) set" where
"exec_state_sequence' \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)}"

abbreviation "ES t \<equiv> {a. (t, a) \<in> exec_state_sequence}"

abbreviation "IES t \<equiv> {a. (t, a) \<in> exec_state_sequence'}"

abbreviation "PES t \<equiv> {a. (t, at_start a) \<in> happ_seq \<and> (t, at_end a) \<in> happ_seq}" 


lemma inc_es_is_next_es:
  assumes "Suc l < length (htpl \<pi>)"
  shows "IES (time_index \<pi> l) = ES (time_index \<pi> (Suc l))"
proof (rule equalityI; rule subsetI)
  fix a
  assume "a \<in> IES (time_index \<pi> l)"
  then obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> time_index \<pi> l"
    "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> time_index \<pi> l)"
    unfolding exec_state_sequence'_def by blast
  from this(2) 
  have "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < time_index \<pi> (Suc l))"
    using time_index_strict_sorted_list[rotated, OF assms] no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite] assms]
    unfolding happ_seq_def by fastforce
  with time_index_strict_sorted_list[rotated, OF \<open>Suc l < length (htpl \<pi>)\<close>] s(1)
  show "a \<in> ES (time_index \<pi> (Suc l))" using exec_state_sequence_def by force
next
  fix a
  assume "a \<in> ES (time_index \<pi> (Suc l))"
  then obtain s where
    s: "a \<in> actions"
    "(s, at_start a) \<in> happ_seq"  
    "s < time_index \<pi> (Suc l)"
    "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < time_index \<pi> (Suc l))"
    unfolding exec_state_sequence_def by blast
  from this(2, 3) no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite] assms] 
  have "s \<le> time_index \<pi> l" unfolding happ_seq_def by fastforce
  moreover
  have "\<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> time_index \<pi> l)" 
  proof (rule notI)
    assume "\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> time_index \<pi> l"
    with time_index_strict_sorted_list assms
    have "\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < time_index \<pi> (Suc l)" by fastforce
    with s(4)
    show "False" by blast
  qed
  ultimately
  show "a \<in> IES (time_index \<pi> l)" using s(1,2) exec_state_sequence'_def by blast
qed

lemma last_ies_empty:
  shows "IES (time_index \<pi> (length (htpl \<pi>) - 1)) = {}" (is "IES ?te = {}")
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
      using at_start_in_happ_seqE'[OF s(1)] unfolding happ_seq_def by fast
    then
    have "\<exists>d. (a, s, d) \<in> ran \<pi>"
    proof cases
      case 1
      hence "\<exists>a' t d. (s, at_start a) = (t, at_start a') \<and> (a', t, d) \<in> ran \<pi>" by blast
      thus ?thesis using at_start_inj_on[simplified inj_on_def] \<open>a \<in> actions\<close> pap[simplified plan_actions_in_problem_def] by blast
    next
      case 2
      hence "\<exists>a' t d. (s, at_start a) = (t + d, at_end a') \<and> (a', t, d) \<in> ran \<pi>" by auto
      with s(1) snaps_disj
      have False using pap unfolding plan_actions_in_problem_def by blast 
      thus ?thesis ..
    qed
    then obtain d where
      d: "(a, s, d) \<in> ran \<pi>"
      "(s + d, at_end a) \<in> happ_seq" using plan_happ_seq_def happ_seq_def by fast
    with s(4) vp[THEN valid_plan_durs(1)]
    have "s + d \<ge> ?te" unfolding durations_ge_0_def by fastforce
    
    have "t \<le> ?te" if "t \<in> set (htpl \<pi>)" for t
    proof -
      from that[simplified time_index_bij_betw_list[simplified bij_betw_def, THEN conjunct2, symmetric]]
      obtain n where
        n: "n < length (htpl \<pi>)" "t = time_index \<pi> n" by blast
      show "t \<le> ?te"
      proof (cases "n < length (htpl \<pi>) - 1")
        case True
        show ?thesis
          apply (subst n(2))
          apply (rule time_index_sorted_list)
          using True by simp+
      next
        case False
        hence "n = length (htpl \<pi>) - 1" using n by linarith
        thus ?thesis using n by blast
      qed
    qed
    moreover
    from d(1) set_htpl_eq_htps vp[THEN valid_plan_finite]
    have "s + d \<in> set (htpl \<pi>)" unfolding htps_def by blast
    ultimately
    show False unfolding exec_state_sequence'_def 
      using \<open>time_index \<pi> (length (htpl \<pi>) - 1) \<le> s + d\<close> a d 
      using dual_order.trans s(3,4) by blast
  qed
  thus "IES ?te = {}" by blast
qed

lemma first_es_empty:
    shows "ES (time_index \<pi> 0) = {}"
proof (rule ccontr)
  assume "ES (time_index \<pi> 0) \<noteq> {}"
  then obtain a where
    a: "a \<in> ES (time_index \<pi> 0)" by blast

  then obtain t where
    t: "t < time_index \<pi> 0"
    "(t, at_start a) \<in> happ_seq" unfolding happ_seq_def exec_state_sequence_def by auto

  show False
  proof (cases "card (htps \<pi>)")
    case 0
    with time_index_img_set vp
    have "htps \<pi> = {}" unfolding valid_plan_def by fastforce
    with t(2) a_in_B_iff_t_in_htps
    show ?thesis unfolding happ_seq_def by fast
  next
    case (Suc nat)
    hence "0 < card (htps \<pi>)" by auto
    from t(2)
    have "t \<in> htps \<pi>" using a_in_B_iff_t_in_htps unfolding happ_seq_def  by fast
    then obtain i where
      i: "t = time_index \<pi> i" 
      "i < card (htps \<pi>)" using time_index_img_set vp[THEN valid_plan_finite] by blast
    have "0 \<le> i" by simp
    with i(2)
    have "time_index \<pi> 0 \<le> time_index \<pi> i" using time_index_sorted_set by blast
    with i(1) t
    show ?thesis by simp
  qed
qed

lemma not_executing_when_starting:
  assumes snap_in_B: "(t, at_start a) \<in> happ_seq"
      and a_in_actions: "a \<in> actions"
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
    using at_start_in_happ_seqE' assms unfolding happ_seq_def by blast
  hence "(s + d, at_end a) \<in> happ_seq" unfolding plan_happ_seq_def happ_seq_def by blast
  hence t_sd: "t \<le> s + d" using vp[THEN valid_plan_durs(1)] as_in_plan not_ended unfolding durations_ge_0_def by fastforce
  
  from snap_in_B
  obtain d' where
    at_in_plan: "(a, t, d') \<in> ran \<pi>" 
    using at_start_in_happ_seqE' assms unfolding happ_seq_def by blast

  from started as_in_plan t_sd at_in_plan
  show False using nso[THEN no_self_overlap_spec] by fastforce
qed

(* Not correct, because the action could have a duration of 0 *)
(* lemma executing_when_ending:
  assumes snap_in_B: "(t, at_end a) \<in> happ_seq"
      and a_in_actions: "a \<in> actions"
    shows "a \<in> ES t"
proof -
  from snap_in_B
  obtain s d where
    s: "(a, s, d) \<in> ran \<pi>"   
    "t = s + d"
    using at_end_in_happ_seqE' snap_in_B a_in_actions unfolding happ_seq_def by blast
  hence "(s, at_start a) \<in> happ_seq \<and> s \<le> t" using vp[THEN valid_plan_durs(1)] 
    unfolding durations_ge_0_def plan_happ_seq_def happ_seq_def by auto
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
      using at_end_in_happ_seqE' assms unfolding happ_seq_def by blast

    hence "(\<tau>, at_start a) \<in> happ_seq" unfolding plan_happ_seq_def happ_seq_def by blast

    consider "\<tau> \<le> s" | "s \<le> \<tau>" by fastforce
    thus False
    proof cases
      case 1
      with s'(2) s(2) \<tau>(2)
      have "\<tau> = s \<longrightarrow> \<epsilon> \<noteq> d" by blast
      with nso[THEN no_self_overlap_spec, OF \<tau>(1) s(1)] 1 s'(2) \<tau>(2) 
      show ?thesis by blast
    next
      case 2
      from \<open>s \<le> s' \<and> s' < t\<close>[simplified \<open>t = s + d\<close> \<open>s' = \<tau> + \<epsilon>\<close>] 
        vp[THEN valid_plan_durs(1), simplified durations_ge_0_def] \<open>(a, \<tau>, \<epsilon>) \<in> ran \<pi>\<close>
      have "\<tau> \<le> s + d" by (meson dual_order.strict_trans2 le_add_same_cancel1 order.strict_iff_not)
      moreover
      from 2 s'(2) s(2) \<tau>(2)
      have "\<tau> = s \<longrightarrow> \<epsilon> \<noteq> d" by blast
      ultimately 
      show ?thesis using 2 nso[THEN no_self_overlap_spec, OF s(1) \<tau>(1)] by blast
    qed
  qed
  ultimately
  show ?thesis unfolding exec_state_sequence_def happ_seq_def using a_in_actions
    apply simp unfolding happ_seq_def[symmetric]

    apply (rule exI)
    apply (rule conjI)
     apply blast


qed *)

lemma execution_state_unchanging:
  assumes not_starting: "(t, at_start a) \<notin> happ_seq"
      and not_ending:   "(t, at_end a) \<notin> happ_seq"
    shows "a \<in> ES t \<longleftrightarrow> a \<in> IES t"
proof (rule iffI)
  assume "a \<in> ES t"
  with exec_state_sequence_def
  obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s < t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)" by blast
  have "s \<le> t" using s by auto
  moreover
  have "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)" using s' not_ending by auto
  ultimately
  show "a \<in> IES t" using s unfolding exec_state_sequence'_def by blast
next
  assume "a \<in> IES t"
  with exec_state_sequence'_def
  obtain s where  
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)" by blast
  have "s < t" using not_starting s unfolding happ_seq_def
    using order_le_imp_less_or_eq by blast
  moreover 
  have "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)" using s' by auto
  ultimately
  show "a \<in> ES t" using s unfolding exec_state_sequence_def by blast
qed

subsubsection \<open>Invariant states\<close>

definition active_count where
"active_count t a \<equiv> card {s. s < t \<and> (s, at_start a) \<in> happ_seq} - card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"

(* Currently the number of active instances is either 0 or 1. I.e. this is equivalent to the sequence of
  execution states *)

definition "invariant_state t p \<equiv> \<Sum>{active_count t a | a. p \<in> over_all a}"

subsubsection \<open>Execution times\<close>

definition pt::"'snap_action \<Rightarrow> ('time \<Rightarrow> 'time \<Rightarrow> bool) \<Rightarrow> 'time \<Rightarrow> 'time" where
"pt a co t \<equiv> if (\<exists>t'. co t' t \<and> (t', a) \<in> happ_seq) 
  then (Greatest (\<lambda>t'. co t' t \<and> (t', a) \<in> happ_seq)) 
  else (Least (\<lambda>t'. \<exists>a. (t', a) \<in> happ_seq) - (\<epsilon> + c))"

abbreviation last_snap_exec::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"last_snap_exec a t \<equiv> pt a (<) t"

definition exec_time::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"exec_time a t \<equiv> (let t' = last_snap_exec a t in t - t')"

abbreviation last_snap_exec'::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"last_snap_exec' a t \<equiv> pt a (\<le>) t"

definition exec_time'::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"exec_time' a t \<equiv> (let t' = last_snap_exec' a t in t - t')"




 
lemma a_not_in_b_last_unchanged: "(t, a) \<notin> happ_seq \<Longrightarrow> last_snap_exec' a t = last_snap_exec a t"
proof -
  assume "(t, a) \<notin> happ_seq"
  have 1: "(GREATEST t'. t' < t \<and> (t', a) \<in> happ_seq) = (GREATEST t'. t' \<le> t \<and> (t', a) \<in> happ_seq)"
    if defined: "\<exists>t'\<le>t. (t', a) \<notin> happ_seq"
  proof (rule classical)
    assume "(GREATEST t'. t' < t \<and> (t', a) \<in> happ_seq) \<noteq> (GREATEST t'. t' \<le> t \<and> (t', a) \<in> happ_seq)"
    then have "\<exists>t'. t' \<le> t \<and> \<not>(t' < t) \<and> (t', a) \<in> happ_seq"
      using defined
      by (meson nless_le)
    then have "(t, a) \<in> happ_seq" by auto
    with \<open>(t, a) \<notin> happ_seq\<close>
    have "False" by simp
    thus "(GREATEST t'. t' < t \<and> (t', a) \<in> happ_seq) = (GREATEST t'. t' \<le> t \<and> (t', a) \<in> happ_seq)"
      by blast
  qed
  from \<open>(t, a) \<notin> happ_seq\<close>
  have "(\<exists>t'<t. (t', a) \<in> happ_seq) = (\<exists>t'\<le>t. (t', a) \<in> happ_seq)"
    using nless_le by auto
  with \<open>(t, a) \<notin> happ_seq\<close> 1
  show "last_snap_exec' a t = last_snap_exec a t"
    using pt_def by force
qed

lemma a_not_in_b_exec_time_unchanged: "(t, a) \<notin> happ_seq \<Longrightarrow> exec_time a t = exec_time' a t"
  using a_not_in_b_last_unchanged unfolding exec_time_def exec_time'_def by simp

lemma a_in_b_last_now: "(t, a) \<in> happ_seq \<Longrightarrow> last_snap_exec' a t = t"
  using pt_def
  by (auto intro: Greatest_equality)

lemma a_in_b_exec_time'_0: "(t, a) \<in> happ_seq \<Longrightarrow> exec_time' a t = 0"
  using a_in_b_last_now unfolding exec_time'_def by simp

lemma subseq_last_snap_exec:
  assumes llen: "(Suc l) < length (htpl \<pi>)" 
shows "last_snap_exec a (time_index \<pi> (Suc l)) = last_snap_exec' a (time_index \<pi> l)"
proof -

  define t where 
    "t = last_snap_exec a (time_index \<pi> (Suc l))"    

  define s where
    "s = last_snap_exec' a (time_index \<pi> l)" 
  
  have cl: "length (htpl \<pi>) = card (htps \<pi>)" unfolding htpl_def by simp
  
  have tl_ord: "time_index \<pi> l < time_index \<pi> (Suc l)" 
    using time_index_strict_sorted_list llen by blast
  
  from t_def consider "\<exists>t'. t' < (time_index \<pi> (Suc l)) \<and> (t', a) \<in> happ_seq" 
    | "\<not>(\<exists>t'. t' < (time_index \<pi> (Suc l)) \<and> (t', a) \<in> happ_seq)" by auto
  hence "t = s"
  proof cases
    case 1 
    hence exsl: "Ex (\<lambda>t'. t' < time_index \<pi> (Suc l) \<and> (t', a) \<in> happ_seq)" (is "Ex ?psl") by blast
    have "\<forall>t'. t' < time_index \<pi> (Suc l) \<and> (t', a) \<in> happ_seq \<longrightarrow> t' \<le> time_index \<pi> l"
      using time_index_strict_sorted_list[OF _ llen] time_index_sorted_list[OF _ llen] 
        no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite]] 
      by (metis happ_seq_def leI llen mem_Collect_eq)
    moreover
    have "\<forall>t'. t' \<le> time_index \<pi> l \<and> (t', a) \<in> happ_seq \<longrightarrow> t' < time_index \<pi> (Suc l)" 
      using time_index_strict_sorted_list[OF _ llen] time_index_sorted_list[OF _ llen] 
        no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite]] by fastforce
    ultimately 
    have fa: "\<forall>t'. t' < time_index \<pi> (Suc l) \<and> (t', a) \<in> happ_seq \<longleftrightarrow> t' \<le> time_index \<pi> l \<and> (t', a) \<in> happ_seq" by blast
    with 1
    have exl: "Ex (\<lambda>t'. t' \<le> time_index \<pi> l \<and> (t', a) \<in> happ_seq)" (is "Ex ?pl") by blast
    from fa
    have "Greatest ?psl = Greatest ?pl" by auto
    thus "t = s" unfolding t_def s_def pt_def using exl exsl by auto
  next
    case 2
    hence "\<not> (\<exists>t' \<le> time_index \<pi> l. (t', a) \<in> happ_seq)" using tl_ord by force
    with 2 t_def[simplified pt_def] s_def[simplified pt_def]
    show ?thesis by auto
  qed
  thus "last_snap_exec a (time_index \<pi> (Suc l)) = last_snap_exec' a (time_index \<pi> l)" 
    using s_def t_def by auto
  qed

lemma updated_exec_time_and_next: 
  assumes "Suc l < length (htpl \<pi>)"
  shows "exec_time a (time_index \<pi> (Suc l)) = (exec_time' a (time_index \<pi> l)) + (time_index \<pi> (Suc l) - time_index \<pi> l)"
  using subseq_last_snap_exec[OF assms] exec_time_def exec_time'_def by simp


lemma exec_time_and_epsilon:
  assumes nm: "mutex_valid_happ_seq"
      and s_at_t: "(t, a) \<in> happ_seq"
      and mutex: "mutex_snap a b"
      and s_not_b: "a \<noteq> b"
    shows "exec_time b t \<ge> \<epsilon> \<and> exec_time b t > 0"
proof (cases "\<exists>u < t. (u, b) \<in> happ_seq")
  case True

  have "\<forall>u. (u, b) \<in> happ_seq \<longrightarrow> \<not> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> t \<noteq> u)" using assms unfolding mutex_valid_happ_seq_def nm_happ_seq_def mutex_snap_def[symmetric] by blast

  from s_at_t
  have "t \<in> timepoint_set" using a_in_B_iff_t_in_htps by fast
  then obtain j where
    j: "t = ti j"
    "j < card timepoint_set" using time_index_img_set[OF fp] by force
  
  have P_iff: "(\<lambda>t'. t' < t \<and> b \<in> B t') = (\<lambda>t'. \<exists>i < card timepoint_set. ti i = t' \<and> i < j \<and> b \<in> B (ti i))" (is "?P = ?P'")
  proof -
    have "(\<lambda>t'. t' < t \<and> b \<in> B t') = (\<lambda>t'. t' \<in> timepoint_set \<and> t' < t \<and> b \<in> B t')" using a_in_B_iff_t_in_htps by fast
    also have "... = (\<lambda>t'. \<exists>i < card timepoint_set. ti i = t' \<and> t' < t \<and> b \<in> B (ti i))" using time_index_img_set[OF fp] by force
    also have "... = (\<lambda>t'. \<exists>i < card timepoint_set. ti i = t' \<and> i < j \<and> b \<in> B (ti i))"
      unfolding j(1) 
      using time_index_strict_sorted_set'[where j = j] 
      using time_index_strict_sorted_set[OF _ j(2)] 
      by blast
    finally show ?thesis .
  qed
  
  obtain u where
    u: "u < t"
    "b \<in> B u"
    using True by blast
  hence "u \<in> timepoint_set" using a_in_B_iff_t_in_htps by fast
  hence "\<exists>i < card timepoint_set. i < j \<and> b \<in> B (ti i)" (is "Ex ?P2") using P_iff u by meson
  moreover
  have P2_int: "\<And>x. ?P2 x \<Longrightarrow> x \<le> j" using time_index_sorted_set' by auto
  ultimately
  have P2: "?P2 (Greatest ?P2)" using GreatestI_ex_nat[where P = ?P2] by blast

  have P_1: "?P (ti(Greatest ?P2))" 
  proof -
    from P2 time_index_strict_sorted_set[OF _ j(2)] 
    show ?thesis unfolding j(1) by blast
  qed
  
  have P_max: "x \<le> ti (Greatest ?P2)" if assm: "?P x" for x 
  proof -
    from assm P_iff
    have "\<exists>i<card timepoint_set. ti i = x \<and> i < j \<and> b \<in> B (ti i)" by meson
    then
    obtain i where
      i: "?P2 i"
      "x = ti i" by auto
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

  { assume a: "s \<in> (B t)" "b \<in> (B ?t)"

    have nm_cond: "t - ?t < \<epsilon> \<and> ?t - t < \<epsilon> \<and> (s \<noteq> b \<or> t \<noteq> ?t) \<or> (t = ?t \<and> s \<noteq> b) \<longrightarrow> \<not>msa s b" 
      using a nm[simplified nm_happ_seq_def] by auto
    hence "msa s b \<longrightarrow> (t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> (s = b \<and> t = ?t)) \<and> (t \<noteq> ?t \<or> s = b)" by auto
    hence "msa s b \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> (s = b \<and> t = ?t)" 
          "msa s b \<longrightarrow> (t \<noteq> ?t \<or> s = b)" by auto

    hence "\<not>(\<not>(s \<noteq> b \<or> t \<noteq> ?t) \<or> \<not>msa s b)
      \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>" by auto
    hence "((s \<noteq> b \<or> t \<noteq> ?t) \<and> msa s b)
      \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  using s_at_t b_at_t' by blast
    hence "(s \<noteq> b \<or> t \<noteq> ?t) \<and> msa s b
      \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  by blast  
    moreover
    have "s \<noteq> b \<longrightarrow> msa s b" using mutex by blast
    ultimately
    have "s \<noteq> b \<or> (t \<noteq> ?t \<and> msa s b)
      \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>" by blast
    moreover
    have "t \<noteq> ?t" using b_at_t' by auto
    ultimately
    consider "t - ?t \<ge> \<epsilon>" | "?t - t \<ge> \<epsilon>" sorry
  }
  note c = this
  
  have "t > ?t" using b_at_t' by blast
  moreover
  have "\<epsilon> \<ge> 0" using eps_range less_le_not_le by fastforce
  ultimately 
  have "t - ?t \<ge> \<epsilon>"  apply (cases rule: c) apply blast using order.trans by fastforce 
  thus ?thesis sorry
next
  case False
  have 1: "ti 0 \<le> u" if "B u \<noteq> {}" for u
  proof -
    have "u \<in> set timepoint_list" using that a_in_B_iff_t_in_htps set_htpl_eq_htps[OF fp] by fast
    hence "\<exists>i. ti i = u \<and> i < length timepoint_list" using time_index_img_list by force
    thus "ti 0 \<le> u" using time_index_sorted_list by blast
  qed
  with s_at_t
  have 2: "ti 0 \<le> t" by auto
  
  have 3: "Least (\<lambda>t. B t \<noteq> {}) = (ti 0)" 
  proof (rule Least_equality[OF _ 1])
    have "card timepoint_set > 0" using a_in_B_iff_t_in_htps s_at_t card_gt_0_iff finite_htps fp by fast
    hence "ti 0 \<in> timepoint_set" using time_index_img_set[OF fp] by blast
    thus "B (ti 0) \<noteq> {}" using a_in_B_iff_t_in_htps by fast
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

(* 
lemma exec_time_and_duration:
  assumes "at_end a \<in> B t"
      and a_in_actions: "a \<in> actions"
      and nso: "nso_\<pi>"
      and dp: "dp_\<pi>"
      and pap: "pap_\<pi>"
  shows "\<exists>t' d. (a, t', d) \<in> ran \<pi> \<and> exec_time (at_start a) t = d"
proof -
  have "\<exists>!(s,d). (a, s, d) \<in> ran \<pi> \<and> t = s + d" using at_end_in_happ_seqE' assms(1,2) nso dp pap by simp
  then obtain s d where
    sd: "(a, s, d) \<in> ran \<pi>" 
    "t = s + d" by auto
  with dp
  have wit: "s < t \<and> at_start a \<in> B s" unfolding plan_happ_seq_def durations_positive_def by force
  moreover
  have "t' \<le> s" if "t' < t" "at_start a \<in> B t'" for t'
  proof (rule ccontr)
    assume "\<not> t' \<le> s"
    hence st': "s < t'" by simp
    from that(2)
    obtain d' where
       t'd': "(a, t', d') \<in> ran \<pi>" 
      using at_start_in_happ_seqE' assms(2,3,4,5)  by blast
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
    shows "sat_dur_bounds a (exec_time (at_start a) t)"
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
  hence 1: "\<not>(\<exists>s < ti 0. B s \<noteq> {})" unfolding plan_happ_seq_def htps_def by blast
  
  have "ti 0 \<in> timepoint_set" using time_index_img_set[OF fp]  using some_happs by blast
  hence "B (ti 0) \<noteq> {}" unfolding plan_happ_seq_def unfolding htps_def by blast
  with 1
  have "Least (\<lambda>t'. B t' \<noteq> {}) = ti 0" by (meson Least_equality not_le_imp_less)
  with 1
  show ?thesis unfolding exec_time_def pt_def by (auto simp: Let_def)
qed  *)
end
end
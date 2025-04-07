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
assumes vp: "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon>"
    and pap: "plan_actions_in_problem \<pi> actions"
    and nso: "no_self_overlap \<pi>"
begin

lemma at_start_inj_on_plan: 
  assumes "pap_\<pi>"
  shows "inj_on at_start {a| a t d. (a, t, d) \<in> ran \<pi>}"
  using assms at_start_inj_on unfolding inj_on_def plan_actions_in_problem_def by blast

lemma at_end_inj_on_plan:
  assumes "pap_\<pi>"
  shows "inj_on at_end {a| a t d. (a, t, d) \<in> ran \<pi>}"
  using assms at_end_inj_on unfolding inj_on_def plan_actions_in_problem_def by blast

lemma snaps_disj_on_plan:
  assumes "pap_\<pi>"
  shows "at_start ` {a| a t d. (a, t, d) \<in> ran \<pi>} \<inter> at_end ` {a| a t d. (a, t, d) \<in> ran \<pi>} = {}"
  using assms snaps_disj unfolding plan_actions_in_problem_def by fast

lemma at_start_in_happ_seqE':
  assumes a_in_acts: "a \<in> actions"
      and pap: pap_\<pi>
      and nso: nso_\<pi>
      and dp: dp_\<pi>
      and sn: "(s, at_start a) \<in> plan_happ_seq \<pi> at_start at_end"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  using at_start_in_happ_seqE[OF _ at_start_inj_on at_end_inj_on snaps_disj sn a_in_acts nso]
  using dp[THEN dp_imp_dg0] pap unfolding plan_actions_in_problem_def by auto

lemma at_end_in_happ_seqE':
  assumes a_in_acts: "a \<in> actions"
      and pap: pap_\<pi>
      and nso: nso_\<pi>
      and dp: dp_\<pi>
      and sn: "(s, at_end a) \<in> plan_happ_seq \<pi> at_start at_end"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"
  using at_end_in_happ_seqE[OF _ at_start_inj_on at_end_inj_on snaps_disj sn a_in_acts nso]
  using dp[THEN dp_imp_dg0] pap unfolding plan_actions_in_problem_def by auto
  
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

definition "mutex_valid_happ_seq = nm_happ_seq pre adds dels"

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
subsubsection \<open>Proposition and execution state\<close>

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
  assumes "finite_\<pi>"
      and "Suc l < length htpl"
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
    try0
  with time_index_strict_sorted_list[rotated, OF \<open>Suc l < length htpl\<close>] s(1)
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
  have "s \<le> ti l" by fastforce
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
  shows "IES (ti(length htpl - 1)) = {}" (is "IES ?te = {}")
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
      hence "\<exists>a' t d. (s, at_start a) = (t, at_start a') \<and> (a', t, d) \<in> ran \<pi>" by blast
      thus ?thesis using at_start_inj_on[simplified inj_on_def] \<open>a \<in> actions\<close> pap[simplified plan_actions_in_problem_def] by blast
    next
      case 2
      hence "\<exists>a' t d. (s, at_start a) = (t + d, at_end a') \<and> (a', t, d) \<in> ran \<pi>" by auto
      with s(1) assms(1)[simplified plan_actions_in_problem_def] snaps_disj
      have False by blast
      thus ?thesis ..
    qed
    then obtain d where
      d: "(a, s, d) \<in> ran \<pi>"
      "(s + d, at_end a) \<in> happ_seq" using plan_happ_seq_def by fast
    with s(4) assms(2)[simplified durations_positive_def]
    have "s + d > ?te" by fastforce
    
    have "t \<le> ?te" if "t \<in> set htpl" for t
    proof -
      from that[simplified time_index_bij_betw_list[simplified bij_betw_def, THEN conjunct2, symmetric]]
      obtain n where
        n: "n < length htpl" "t = ti n" by blast
      show "t \<le> ?te"
      proof (cases "n < length htpl - 1")
        case True
        show ?thesis
          apply (subst n(2))
          apply (rule time_index_sorted_list)
          using True by simp+
      next
        case False
        hence "n = length htpl - 1" using n by linarith
        thus ?thesis using n by blast
      qed
    qed
    moreover
    
    from d(1) set_htpl_eq_htps[OF fpl] 
    have "s + d \<in> set htpl" unfolding htps_def by blast
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
    show ?thesis by fast
  next
    case (Suc nat)
    hence "0 < card timepoint_set" by auto
    from t(2)
    have "t \<in> timepoint_set" using a_in_B_iff_t_in_htps by fast
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
    using at_start_in_happ_seqE' assms by blast
  hence "(s + d, at_end a) \<in> happ_seq" unfolding plan_happ_seq_def by blast
  with durations_positive[simplified durations_positive_def] as_in_plan not_ended 
  have t_sd: "t \<le> s + d" by fastforce
  
  from snap_in_B
  obtain d' where
    at_in_plan: "(a, t, d') \<in> ran \<pi>" 
    using at_start_in_happ_seqE' assms by blast

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
    using at_end_in_happ_seqE' assms by blast
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
      using at_end_in_happ_seqE' assms by blast

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
  have "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)" using s' not_ending by auto
  ultimately
  show "a \<in> IES t" using s unfolding exec_state_sequence'_def by blast
next
  assume "a \<in> IES t"
  with exec_state_sequence'_def
  obtain s where  
    s: "a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)" by blast
  have "s < t" using not_starting s by force
  moreover 
  have "(\<nexists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)" using s' by auto
  ultimately
  show "a \<in> ES t" using s unfolding exec_state_sequence_def by blast
qed

  

end
end
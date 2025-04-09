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

end
end
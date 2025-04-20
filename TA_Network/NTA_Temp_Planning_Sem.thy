theory NTA_Temp_Planning_Sem
  imports Temporal_Planning_Base.Temporal_Plans
begin

lemma GreatestI_time: "P (k::'t::time) \<Longrightarrow> (\<And>y. P y \<Longrightarrow> y \<le> k) \<Longrightarrow> P (Greatest P)"
  apply (rule GreatestI2_order)
  by blast

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


lemma at_start_in_happ_seqE'':
  assumes a_in_acts: "a \<in> actions"
      and sn: "(s, at_start a) \<in> happ_seq"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  using assms at_start_in_happ_seqE' happ_seq_def by simp

lemma at_end_in_happ_seqE'':
  assumes a_in_acts: "a \<in> actions"
      and sn: "(s, at_end a) \<in> happ_seq"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"
  using assms at_end_in_happ_seqE' happ_seq_def by simp

subsubsection \<open>Mutual exclusivity on the happening sequence\<close>

lemma nm: mutex_valid_happ_seq
proof -
  have 1:"nm_anno_act_seq \<pi> at_start at_end pre adds dels \<epsilon>"
    using nso_mutex_cond nso valid_plan_durs(1)[OF vp] eps_range valid_plan_mutex[OF vp] by blast 
  thus ?thesis 
    apply -
    apply (subst (asm) nso_mutex_happ_seq)
    using pap unfolding plan_actions_in_problem_def apply blast
          apply (rule inj_on_subset)
           apply (rule at_start_inj_on)
    using pap unfolding plan_actions_in_problem_def apply blast
          apply (rule inj_on_subset)
           apply (rule at_end_inj_on)
    using pap unfolding plan_actions_in_problem_def apply blast
    using pap unfolding plan_actions_in_problem_def using snaps_disj apply fast
       apply (rule nso)
      apply (rule valid_plan_durs[OF vp])
     apply (rule eps_range)
    unfolding mutex_valid_happ_seq_def happ_seq_def 
    by assumption
qed

lemma mutex_not_in_same_instant:
  assumes "(t, a) \<in> happ_seq"
      and "(t, b) \<in> happ_seq"
      and "a \<noteq> b"
    shows "\<not>mutex_snap a b"
  using nm assms unfolding mutex_valid_happ_seq_def nm_happ_seq_def mutex_snap_def
  by blast

lemma mutex_same_instant_is_same:
  assumes "(t, a) \<in> happ_seq"
      and "(t, b) \<in> happ_seq"
      and "mutex_snap a b"
    shows "a = b" 
  using mutex_not_in_same_instant assms by blast

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

definition locked_by where
"locked_by p \<equiv> {a \<in> actions. p \<in> over_all a}"

(* Move to other locale *)
definition open_active_count where
"open_active_count t a \<equiv> card {s. s < t \<and> (s, at_start a) \<in> happ_seq} - card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"

(* Currently the number of active instances is either 0 or 1. I.e. this is equivalent to the sequence of
  execution states *)

definition "locked_before t p \<equiv> \<Sum>(open_active_count t ` locked_by p)"        

definition open_closed_active_count where
"open_closed_active_count t a \<equiv> card {s. s < t \<and> (s, at_start a) \<in> happ_seq} - (card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq} - (if (t, at_start a) \<in> happ_seq then 1 else 0))"

definition "locked_in_instant t p \<equiv> \<Sum>(open_closed_active_count t ` locked_by p)"              

definition closed_active_count where
"closed_active_count t a \<equiv> card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq} - card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"

definition "locked_after t p \<equiv> \<Sum>(closed_active_count t ` locked_by p)"        

definition "all_open_active_count t \<equiv> \<Sum>{open_active_count t a|a. True}"

find_theorems name: "Set*size"

lemma finite_htps: "finite (htps \<pi>)"
  using finite_htps valid_plan_finite[OF vp] by blast

lemma finite_happ_seq: "finite happ_seq"
  using finite_happ_seq valid_plan_finite[OF vp] happ_seq_def by auto

lemma finite_start_tps: "finite {s'. (s', at_start a) \<in> happ_seq}"
proof -
  have "{(s', at_start a)| s'. (s', at_start a) \<in> happ_seq} \<subseteq> happ_seq" by blast
  hence "finite {(s', at_start a)| s'. (s', at_start a) \<in> happ_seq}" using finite_subset finite_happ_seq by auto
  from finite_imageI[OF this, where h = fst]
  show "finite {s'. (s', at_start a) \<in> happ_seq}" unfolding image_Collect by auto
qed

lemma finite_end_tps: "finite {s'. (s', at_end a) \<in> happ_seq}"
proof -
  have "{(s', at_end a)| s'. (s', at_end a) \<in> happ_seq} \<subseteq> happ_seq" by blast
  hence "finite {(s', at_end a)| s'. (s', at_end a) \<in> happ_seq}" using finite_subset finite_happ_seq by auto
  from finite_imageI[OF this, where h = fst]
  show "finite {s'. (s', at_end a) \<in> happ_seq}" unfolding image_Collect by auto
qed

lemma plan_durations: "(a, t, d) \<in> ran \<pi> \<Longrightarrow> 0 \<le> d" using valid_plan_durs[OF vp] unfolding durations_ge_0_def by blast
lemmas plan_overlap_cond = nso[THEN no_self_overlap_ran]

lemma open_active_count_ran:
  assumes a_in_acts: "a \<in> actions" 
  shows "open_active_count t a \<in> {0, 1}"
proof -
  have finite_started: "finite {s'. s' < t \<and> (s', at_start a) \<in> happ_seq}" using finite_start_tps by auto
  have finite_ended: "finite {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using finite_end_tps by auto
  have "\<not>(1 < open_active_count t a)"
  proof 
    assume "1 < open_active_count t a"
    hence 1: "2 \<le> card {s'. s' < t \<and> (s', at_start a) \<in> happ_seq} - card {s. s < t \<and> (s, at_end a) \<in> happ_seq}" 
      using finite_ended finite_started unfolding open_active_count_def by simp

    define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
    hence n1: "n + 2 \<le> card {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using 1 by simp
      
    define start_list where "start_list = sorted_list_of_set {s. s < t \<and> (s, at_start a) \<in> happ_seq}"
    have start_list_len: "length start_list = card {s. s < t \<and> (s, at_start a) \<in> happ_seq}" unfolding start_list_def length_sorted_list_of_set by blast
    have n_start_list: "n + 2 \<le> length start_list" using n1 unfolding length_sorted_list_of_set using start_list_def by simp
    have start_list_sorted: "sorted start_list" using sorted_sorted_list_of_set start_list_def by blast
    have start_list_distinct: "distinct start_list" using distinct_sorted_list_of_set start_list_def by blast
    have set_start_list: "set start_list = {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using start_list_def set_sorted_list_of_set finite_started by blast

    define end_list where "end_list = sorted_list_of_set {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
    have end_list_len: "length end_list = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" unfolding end_list_def length_sorted_list_of_set by blast
    have n_end_list: "n = length end_list" using n_def unfolding length_sorted_list_of_set[symmetric] using end_list_def by blast
    have end_list_sorted: "sorted end_list" using sorted_sorted_list_of_set end_list_def by blast
    have end_list_distinct: "distinct end_list" using distinct_sorted_list_of_set end_list_def by blast
    have set_end_list: "set end_list = {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using end_list_def set_sorted_list_of_set finite_ended by blast
    
    have start_list_end_list_len: "length end_list + 2 \<le> length start_list" using n_end_list n_start_list by blast

    have start_list_nth_happ_seqE: "(start_list ! i, at_start a) \<in> happ_seq" if "i < length start_list" for i 
    proof -
      have "start_list ! i \<in> set start_list" using that by auto
      hence "start_list ! i \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set finite_started start_list_def by blast
      thus ?thesis by blast
    qed

    have start_list_nth_planE: "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! i = t" if "i < length start_list" for i 
      using start_list_nth_happ_seqE[OF that] at_start_in_happ_seqE''[OF a_in_acts] by simp

    have start_list_nth_ran: "start_list ! i < t" if "i < length start_list" for i
    proof -
      have "start_list ! i \<in> set start_list" using that by auto
      hence "start_list ! i \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set finite_started start_list_def by blast
      thus ?thesis by simp
    qed

    have start_list_planI: "\<exists>n < length start_list. start_list ! n = t'" if "(a, t', d') \<in> ran \<pi>" "t' < t" for t' d'
    proof -
      have "t' \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using that happ_seq_def plan_happ_seq_def by fast
      hence "t' \<in> set start_list" using start_list_def finite_started set_sorted_list_of_set by simp
      thus ?thesis using in_set_conv_nth by metis
    qed
    
    have end_list_nth_happ_seqE: "(end_list ! i, at_end a) \<in> happ_seq" if "i < length end_list" for i 
    proof -
      have "end_list ! i \<in> set end_list" using that by auto
      hence "end_list ! i \<in> {s. s < t \<and> (s, at_end a) \<in> happ_seq}" using set_sorted_list_of_set finite_ended end_list_def by blast
      thus ?thesis by blast
    qed

    have end_list_nth_planE: "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> end_list ! i = t + d" if "i < length end_list" for i 
      using end_list_nth_happ_seqE[OF that] at_end_in_happ_seqE''[OF a_in_acts] by simp

    have end_list_nth_ran: "end_list ! i < t" if "i < length end_list" for i
    proof -
      from that
      have "end_list ! i \<in> set end_list" using that by auto
      hence "end_list ! i \<in> {s. s < t \<and> (s, at_end a) \<in> happ_seq}" using set_sorted_list_of_set finite_ended end_list_def by blast
      thus ?thesis by simp
    qed

    have end_list_planI: "\<exists>n < length end_list. end_list ! n = t' + d'" if "(a, t', d') \<in> ran \<pi>" "t' + d' < t" for t' d'
    proof -
      have "t' + d'\<in> {s. s < t \<and> (s, at_end a) \<in> happ_seq}" using that happ_seq_def plan_happ_seq_def by fast
      hence "t' + d' \<in> set end_list" using end_list_def finite_ended set_sorted_list_of_set by simp
      thus ?thesis using in_set_conv_nth by metis
    qed

    have "\<forall>n \<le> i. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! n = t \<and> end_list ! n = t + d) 
                \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> start_list ! n = t \<longrightarrow> end_list ! n = t + d)
                \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> end_list ! n = t + d \<longrightarrow> start_list ! n = t)" if iel: "i < length end_list" for i
    proof -
      have isl: "i < length start_list" using start_list_end_list_len that by auto
      with iel
      show ?thesis
      proof (induction i)
        case 0
        from start_list_nth_planE 0 
        have tsds': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! 0 = t" by blast 
        then obtain ts ds where
          tsds: "start_list ! 0 = ts"
          "(a, ts, ds) \<in> ran \<pi>" by blast
        with tsds'
        have tsds'': "\<forall>ts' ds'. (a, ts', ds') \<in> ran \<pi> \<longrightarrow> start_list ! 0 = ts' \<longrightarrow> ts' = ts \<and> ds' = ds" by blast

        have tsds_t: "ts < t" using start_list_nth_ran tsds 0 by auto

        from end_list_nth_planE 0
        have tede': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> end_list ! 0 = t + d" by blast
        then obtain te de where
          tede: "end_list ! 0 = te + de"
          "(a, te, de) \<in> ran \<pi>" by blast
        with tede'
        have tede'': "\<forall>te' de'. (a, te', de') \<in> ran \<pi> \<longrightarrow> end_list ! 0 = te' + de' \<longrightarrow> te' = te \<and> de' = de" by blast

        have tede_t: "te + de < t" using end_list_nth_ran tede 0 by metis
        hence "te \<le> te + de" using plan_durations[OF tede(2)] by auto
        note tede_t = tede_t this
        hence "te < t" by order
        note tede_t = tede_t this

        from nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)]
        have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
        moreover
        from nso[THEN no_self_overlap_ran, OF tede(2) tsds(2)]
        have "ts = te \<and> ds = de \<or> ts < te \<or> te + de < ts" by blast
        ultimately
        consider "ts = te \<and> ds = de" | "te < ts" | "ts + ds < te" | "ts < te" | "te + de < ts" by blast
        thus ?case 
        proof cases
          case 1
          then show ?thesis using tede tsds tede'' tsds'' by blast
        next
          case 2
          from tede(1) 0 start_list_planI[OF tede(2)]
          have "\<exists>n < length start_list. start_list ! n = te" using tede_t by simp
          with 2 tsds
          show ?thesis using start_list_sorted sorted_nth_mono by fastforce
        next
          case 3
          hence "ts + ds < t" using tede_t by simp
          with end_list_planI[OF tsds(2)]
          obtain n where
            n: "n<length end_list" "end_list ! n = ts + ds" by auto
          have "ts + ds < te + de" using tede_t(2) 3 by order
          thus ?thesis using end_list_sorted[THEN sorted_nth_mono, OF _ n(1), of 0] n(2) tede(1) by simp
        next
          case 4
          show ?thesis 
          proof (cases "ts + ds < te")
            case True
            with tede_t end_list_planI[OF tsds(2)]
            obtain n where
              n: "n<length end_list" "end_list ! n = ts + ds" by fastforce
            with tede_t(2) True
            have "ts + ds < te + de" by order
            thus ?thesis using end_list_sorted[THEN sorted_nth_mono] n tede by fastforce
          next
            case False
            hence "te \<le> ts + ds" by simp
            with nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)] 4 
            show ?thesis by fastforce
          qed
        next
          case 5
          hence "te < t" using tede_t by auto
          with start_list_planI[OF tede(2)]
          obtain n where
            n: "n<length start_list" "start_list ! n = te" by blast
          have "te < ts" using 5 tede_t by order
          with n tsds(1)
          show ?thesis using start_list_sorted[THEN sorted_nth_mono] by fastforce
        qed
      next
        case (Suc i)
        have IH1: "\<forall>n\<le>i. \<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! n = t \<and> end_list ! n = t + d" using Suc by auto
        have IH2: "\<forall>n\<le>i. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> start_list ! n = t \<longrightarrow> end_list ! n = t + d)" using Suc by auto
        have IH3: "\<forall>n\<le>i. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> end_list ! n = t + d \<longrightarrow> start_list ! n = t)" using Suc by auto

        from start_list_nth_planE Suc(3)
        have tsds': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! (Suc i) = t" by blast 
        then obtain ts ds where
          tsds: "start_list ! (Suc i) = ts"
          "(a, ts, ds) \<in> ran \<pi>" by blast
        with tsds'
        have tsds': "\<forall>ts' ds'. (a, ts', ds') \<in> ran \<pi> \<longrightarrow> start_list ! Suc i = ts' \<longrightarrow> ts' = ts \<and> ds' = ds" by blast

        have tsds_t: "ts < t" using start_list_nth_ran tsds Suc by auto
        have "ts \<le> ts + ds" using plan_durations[OF tsds(2)] by auto
        note tsds_t = tsds_t this

        from end_list_nth_planE Suc(2)
        have tede': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> end_list ! (Suc i) = t + d" by blast
        then obtain te de where
          tede: "end_list ! (Suc i) = te + de"
          "(a, te, de) \<in> ran \<pi>" by blast
        with tede'
        have tede': "\<forall>te' de'. (a, te', de') \<in> ran \<pi> \<longrightarrow> end_list ! Suc i = te' + de' \<longrightarrow> te' = te \<and> de' = de" by blast

        have tede_t: "te + de < t" using end_list_nth_ran tede Suc by metis
        hence "te \<le> te + de" using plan_durations[OF tede(2)] by auto
        note tede_t = tede_t this
        hence "te < t" by order
        note tede_t = tede_t this

        from nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)]
        have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
        moreover
        from nso[THEN no_self_overlap_ran, OF tede(2) tsds(2)]
        have "ts = te \<and> ds = de \<or> ts < te \<or> te + de < ts" by blast
        ultimately
        consider "ts = te \<and> ds = de" | "te < ts" | "ts + ds < te" | "ts < te" | "te + de < ts" by blast
        hence step: "(\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! Suc i = t \<and> end_list ! Suc i = t + d) \<and> 
                (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> start_list ! Suc i = t \<longrightarrow> end_list ! Suc i = t + d) \<and> 
                (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> end_list ! Suc i = t + d \<longrightarrow> start_list ! Suc i = t)" 
        proof cases
          case 1
          then show ?thesis using tede tsds tede' tsds' by blast
        next
          case 2
          show ?thesis
          proof (cases "te + de < ts")
            case True
            from tede start_list_planI tede_t
            obtain n where 
              n: "n < length start_list" "start_list ! n = te" by auto
            with 2 tsds 
            have "start_list ! n < start_list ! (Suc i)" by auto
            hence "\<not>start_list ! (Suc i) \<le> start_list ! n" by simp
            with sorted_nth_mono[OF start_list_sorted, OF _ n(1)]
            have "\<not> Suc i \<le> n" by auto
            hence n_Suc: "n < Suc i" by simp
            hence "n \<le> i" by simp
            with IH2 n tede(2)
            have "end_list ! n = te + de" by blast
            with tede(1) 
            have "end_list ! n = end_list ! Suc i" by simp
            with end_list_distinct 
            have False using Suc(2) n_Suc unfolding distinct_conv_nth by simp 
            thus ?thesis by auto 
          next
            case False
            hence "ts \<le> te + de" by simp
            with 2 nso[THEN no_self_overlap_ran, OF tede(2) tsds(2)]
            show ?thesis by fastforce
          qed
        next
          case 3
          hence tsds_tede: "ts + ds < te + de"  using tede_t by order
          with tsds(2)[THEN end_list_planI] tede_t 
          obtain n where
            n: "n<length end_list" "end_list ! n = ts + ds" by fastforce

          from sorted_nth_mono[OF end_list_sorted, OF _ n(1)] 
          have "\<forall>i. \<not>(end_list ! i \<le> end_list ! n) \<longrightarrow> \<not>i \<le> n" by blast
          with tede(1) n(2) tsds_tede
          have "\<not>Suc i \<le> n" by simp
          hence n_Suc_i: "n < Suc i" by auto
          hence "n \<le> i" by simp
          with IH3 n tsds(2)
          have "start_list ! n = ts" by simp
          with tsds(1)
          have "start_list ! n = start_list ! Suc i" by simp
          hence False using Suc(3) n_Suc_i start_list_distinct[simplified distinct_conv_nth] by auto
          thus ?thesis by simp
        next
          case 4
          show ?thesis 
          proof (cases "ts + ds < te")
            case True
            hence tsds_tede: "ts + ds < te + de"  using tede_t by order
            with tsds(2)[THEN end_list_planI] tede_t 
            obtain n where
              n: "n<length end_list" "end_list ! n = ts + ds" by fastforce
  
            from sorted_nth_mono[OF end_list_sorted, OF _ n(1)] 
            have "\<forall>i. \<not>(end_list ! i \<le> end_list ! n) \<longrightarrow> \<not>i \<le> n" by blast
            with tede(1) n(2) tsds_tede
            have "\<not>Suc i \<le> n" by simp
            hence n_Suc_i: "n < Suc i" by auto
            hence "n \<le> i" by simp
            with IH3 n tsds(2)
            have "start_list ! n = ts" by simp
            with tsds(1)
            have "start_list ! n = start_list ! Suc i" by simp
            hence False using Suc(3) n_Suc_i start_list_distinct[simplified distinct_conv_nth] by auto
            thus ?thesis by simp
          next
            case False
            hence "te \<le> ts + ds" by simp
            with nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)] 4
            show ?thesis by fastforce
          qed
        next
          case 5
          from tede start_list_planI tede_t
          obtain n where 
            n: "n < length start_list" "start_list ! n = te" by auto
          with 5 tsds tede_t
          have "start_list ! n < start_list ! (Suc i)" by order
          hence "\<not>start_list ! (Suc i) \<le> start_list ! n" by simp
          with sorted_nth_mono[OF start_list_sorted, OF _ n(1)]
          have "\<not> Suc i \<le> n" by auto
          hence n_Suc: "n < Suc i" by simp
          hence "n \<le> i" by simp
          with IH2 n tede(2)
          have "end_list ! n = te + de" by blast
          with tede(1) 
          have "end_list ! n = end_list ! Suc i" by simp
          with end_list_distinct 
          have False using Suc(2) n_Suc unfolding distinct_conv_nth by simp 
          thus ?thesis by auto 
        qed
        show ?case 
          apply (intro allI impI)
          subgoal for n
            apply (cases "n < Suc i")
            apply (intro conjI)
            using IH1 apply simp
            using IH2 apply simp
            using IH3 apply simp
            using step by simp
          done
      qed
    qed
    hence end_start_paired: 
      "\<forall>n < length end_list. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> start_list ! n = t \<and> end_list ! n = t + d)" 
      "\<forall>n < length end_list.(\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> start_list ! n = t \<longrightarrow> end_list ! n = t + d)" 
      "\<forall>n < length end_list. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> end_list ! n = t + d \<longrightarrow> start_list ! n = t)" by simp_all
    
    have n_ord: "\<forall>i < n. start_list ! i < start_list ! n"
    proof -
      have "\<forall>i < n. start_list ! i \<le> start_list ! n" using start_list_sorted sorted_nth_mono n_start_list by fastforce
      moreover
      have "\<forall>i < n. start_list ! i \<noteq> start_list ! n" using start_list_distinct unfolding distinct_conv_nth using n_start_list by simp
      ultimately
      show ?thesis by force
    qed

    have n_starts_after: "\<forall>i < n. end_list ! i < start_list ! n"
    proof -
      {fix i
        assume i: "i < n"
        hence sisn: "start_list ! i < start_list ! n" using n_ord by simp
        with end_start_paired(1) end_list_len n_def i
        obtain ti di where
          tidi: "(a, ti, di) \<in> ran \<pi> " 
          "start_list ! i = ti" 
          "end_list ! i = ti + di" by auto
        from start_list_nth_planE[of n] n_start_list
        obtain tn dn where
          tndn: "(a, tn, dn) \<in> ran \<pi>" 
          "start_list ! n = tn" by auto
      
        assume "end_list ! i \<ge> start_list ! n"
        with nso[THEN no_self_overlap_ran, OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
        have "False" by fastforce
      }
      thus ?thesis by fastforce
    qed

    have n_Suc_n: "start_list ! n < start_list ! Suc n" 
    proof -
      have "start_list ! n \<le> start_list ! Suc n" using start_list_sorted sorted_nth_mono n_start_list by fastforce
      moreover
      have "start_list ! n \<noteq> start_list ! Suc n" using start_list_distinct unfolding distinct_conv_nth using n_start_list by simp
      ultimately
      show ?thesis by force
    qed

    have sn_t: "start_list ! Suc n < t" using start_list_nth_ran n_start_list by simp

    obtain tn dn where
      tndn: "(a, tn, dn) \<in> ran \<pi>"
      "start_list ! n = tn" using start_list_nth_planE[of n] n_start_list by auto

    obtain tsn dsn where
      tsndsn: "(a, tsn, dsn) \<in> ran \<pi>"
      "start_list ! Suc n = tsn" using start_list_nth_planE[of "Suc n"] n_start_list by auto

    show False 
    proof (cases "tn + dn < t")
      case True
      with tndn
      have "tn + dn \<in> set end_list" using set_end_list unfolding happ_seq_def plan_happ_seq_def by fast
      then obtain n' where
        "end_list ! n' = tn + dn" 
        "n' < length end_list" unfolding in_set_conv_nth by blast
      hence "tn + dn < start_list ! n" using n_starts_after n_end_list by metis
      moreover
      have "start_list ! n \<le> tn + dn" using tndn plan_durations by simp
      ultimately
      show ?thesis by simp
    next
      case False
      thus ?thesis using plan_overlap_cond[OF tndn(1) tsndsn(1)] sn_t n_Suc_n tndn(2) tsndsn(2) by fastforce
    qed
  qed
  thus ?thesis by fastforce
qed


    (* have "start_list ! i \<le> end_list ! i \<and> end_list ! i < start_list ! (Suc i)" if "i < length end_list" for i
      using that
    proof (induction i)
      case 0
      have s0_le_e0: "start_list ! 0 \<le> end_list ! 0" 
      proof (rule ccontr)
        assume "\<not> start_list ! 0 \<le> end_list ! 0"
        hence t_ord: "end_list ! 0 < start_list ! 0" by simp
        
        have st_0: "0 < length start_list" using 0 start_list_end_list_len by auto

        have "end_list ! 0 \<in> set end_list" using 0 by simp
        hence 1: "end_list ! 0 \<in> {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" unfolding set_sorted_list_of_set[OF finite_ended] end_list_def by blast
        hence "(end_list ! 0, at_end a) \<in> happ_seq" by simp
        then obtain d t' where
          atd: "end_list ! 0 = t' + d"
          "(a, t', d) \<in> ran \<pi>" using at_end_in_happ_seqE' a_in_acts unfolding happ_seq_def by blast
        hence t'_start: "(t', at_start a) \<in> happ_seq" unfolding happ_seq_def plan_happ_seq_def by auto

        have t': "t' \<le> end_list ! 0" using atd valid_plan_durs(1)[OF vp, simplified durations_ge_0_def] by simp
        hence t'_t: "t' < t" using 1 by auto
        
        have "t' < start_list ! 0" using t_ord atd valid_plan_durs(1)[OF vp, simplified durations_ge_0_def]
          by (metis add.commute add_less_cancel_left add_strict_increasing2)

        have "t' \<in> {s'. s' < t \<and> (s', at_start a) \<in> happ_seq}" using t'_start t'_t by simp
        hence "t' \<in> set start_list" using start_list_def set_sorted_list_of_set finite_started by blast
        then obtain n' where
          "start_list ! n' = t'" 
          "n' < length start_list" unfolding in_set_conv_nth by blast
        hence "start_list ! 0 \<le> t'" using sorted_nth_mono[OF start_list_sorted, of 0 n'] by simp
        with t' t_ord
        show False by simp
      qed
      moreover
      have "end_list ! 0 < start_list ! Suc 0"
      proof (rule ccontr)
        assume "\<not> end_list ! 0 < start_list ! Suc 0"
        hence t_ord: "start_list ! 1 \<le> end_list ! 0" by simp

        
        have 1: "1 < length start_list" using 0 start_list_end_list_len by auto
        hence "start_list ! 1 \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set[OF finite_started]
          unfolding start_list_def using in_set_conv_nth by auto
        hence "(start_list ! 1, at_start a) \<in> happ_seq" by simp
        from at_start_in_happ_seqE'[OF a_in_acts this[simplified happ_seq_def]]
        obtain d where
          d: "(a, start_list ! 1, d) \<in> ran \<pi>" by auto
        hence "0 \<le> d" using valid_plan_durs vp durations_ge_0_def by fast
        note d = d this

        hence end_of_start: "(start_list ! 1 + d, at_end a) \<in> happ_seq" unfolding plan_happ_seq_def happ_seq_def by blast

        have e: "end_list ! 0 \<in> set end_list" using 0 by simp
        hence e_0: "end_list ! 0 < t" unfolding set_sorted_list_of_set[OF finite_ended] end_list_def by simp
  
        show False
        proof (cases "start_list ! 1 + d < end_list ! 0")
          case True
          
          hence st_t: "start_list ! 1 + d < t" using e_0 by simp
          hence "start_list ! 1 + d \<in> set end_list" unfolding set_sorted_list_of_set[OF finite_ended] end_list_def 
            using end_of_start by simp
          then obtain n' where
            n': "end_list ! n' = start_list ! 1 + d" 
            "n' < length end_list" unfolding in_set_conv_nth by blast
          with True
          have "n' < 0" using end_list_sorted sorted_nth_mono by fastforce
          thus ?thesis by auto 
        next
          case False
          hence r: "end_list ! 0 \<le> start_list ! 1 + d" by auto

          have "(end_list ! 0, at_end a) \<in> happ_seq" using e set_sorted_list_of_set finite_ended unfolding end_list_def by blast
          from at_end_in_happ_seqE''[OF a_in_acts this] 
          obtain t' d' where
            t'd': "(a, t', d') \<in> ran \<pi>"
            "end_list ! 0 = t' + d'" by auto
          with r
          have r': "t' + d' \<le> start_list ! 1 + d" by simp

          show ?thesis 
          proof (cases "start_list ! 1 = t'"; cases "d = d'")
            assume "start_list ! 1 = t'" "d = d'"
            have "start_list ! 0 \<le> start_list ! 1"  using 0 start_list_end_list_len 
              apply -
              apply (rule sorted_nth_mono[OF start_list_sorted])
              by auto
            moreover
            have "start_list ! 0 \<noteq> start_list ! 1" using start_list_distinct
              by (metis \<open>1 < length start_list\<close> less_numeral_extra(1) order.strict_iff_order sorted_wrt_nth_less start_list_sorted strict_sorted_iff)
            ultimately
            have "start_list ! 0 < start_list ! 1" by simp
            from start_list_nthE 0 start_list_end_list_len
            obtain t0 d0 where
              t0d0: "(a, t0, d0) \<in> ran \<pi>"
                "start_list ! 0 = t0" by fastforce
            show False
            proof (cases "t0 + d0 < end_list ! 0")
              case True
              with e_0
              have "t0 + d0 \<in> {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using t0d0 unfolding happ_seq_def plan_happ_seq_def by auto
              hence "t0 + d0 \<in> set end_list" using set_sorted_list_of_set finite_ended end_list_def by blast
              then obtain n0 where
                "end_list ! n0 = t0 + d0" 
                "n0 < length end_list" using in_set_conv_nth by metis
              hence "end_list ! 0 \<le> t0 + d0" using sorted_nth_mono[OF end_list_sorted] by fastforce 
              thus False using True by simp
            next
              case False
              hence t0d0': "end_list ! 0 \<le> t0 + d0" by simp
              from s0_le_e0 t0d0
              have "t0 \<le> end_list ! 0" by simp
              with nso[THEN no_self_overlap_spec, OF t0d0(1) t'd'(1)] \<open>start_list ! 1 = t'\<close> \<open>start_list ! 0 < start_list ! 1\<close> t0d0
              have "\<not> (t0 \<le> t' \<and> t' \<le> t0 + d0)" by fastforce
              with \<open>start_list ! 1 = t'\<close> \<open>start_list ! 0 < start_list ! 1\<close> \<open>start_list ! 0 = t0\<close>
              have "t0 + d0 < t'" by auto
              with False t'd' \<open>start_list ! 1 = t'\<close> t_ord
              show ?thesis by order
            qed
          next
            assume "start_list ! 1 = t'" "d \<noteq> d'"
            with r nso[THEN no_self_overlap_spec, OF d(1) t'd'(1)] t'd'(2)
            have "\<not> (t' \<le> start_list ! 1 + d)" by blast
            with d \<open>start_list ! 1 = t'\<close> valid_plan_durs(1)[OF vp, simplified durations_ge_0_def]
            show ?thesis by simp
          next
            assume a: "start_list ! 1 \<noteq> t'" "d = d'"
            with r nso[THEN no_self_overlap_spec, OF d(1) t'd'(1)] t'd'(2)
            have "\<not> (start_list ! 1 \<le> t' \<and> t' \<le> start_list ! 1 + d)" by simp
            thus ?thesis by (metis a(2) add_le_cancel_right d(1) no_self_overlap_spec nso r' t'd'(1,2) t_ord)
          next
            assume a: "start_list ! 1 \<noteq> t'" "d \<noteq> d'"
            with nso[THEN no_self_overlap_spec, OF d(1) t'd'(1)]
            have "\<not> (start_list ! 1 \<le> t' \<and> t' \<le> start_list ! 1 + d)" by simp
            then consider "start_list ! 1 > t'" | "start_list ! 1 + d < t'" by auto
            
            thus ?thesis
              apply cases
              using r  t_ord unfolding t'd' d
               apply (metis d(1) nless_le no_self_overlap_spec nso t'd'(1))
              by (metis durations_ge_0_def leD le_add_same_cancel1 order.trans r t'd'(1,2) valid_plan_def vp)
          qed
        qed
      qed
      ultimately show ?case by simp
    next
      case (Suc i)

      then show ?case sorry
    qed *)

lemma open_closed_active_count_alt:
  assumes "a \<in> actions"
  shows "open_closed_active_count t a = (open_active_count t a - (if (t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<in> happ_seq then 1 else 0))"
proof -
  have finite_ending: "finite {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}" using finite_end_tps by auto
  have finite_ended: "finite {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using finite_end_tps by auto
  
  

  show ?thesis
  proof (cases "(t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<in> happ_seq")
    case True
    have "{s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq} = insert t {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using True by auto
    hence "card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq} = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq} + 1" using True finite_ending finite_ended by simp
    then show ?thesis using True unfolding open_closed_active_count_def open_active_count_def by auto
  next
    case False
    then consider
      "(t, at_start a) \<in> happ_seq" | "(t, at_end a) \<notin> happ_seq" by blast
    thus ?thesis 
    proof cases
      case 1
      then show ?thesis sorry
    next
      case 2
      hence "{s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq} = {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" 
        apply -
        apply (rule equalityI)
         apply (rule subsetI)
        subgoal for x
          apply (cases "x < t")
           apply simp
          by auto
        by auto
      thus ?thesis unfolding open_closed_active_count_def open_active_count_def using 2 
    qed
    then show ?thesis sorry
  qed
qed
lemma open_closed_active_count_ran:
  assumes "a \<in> actions" 
  shows "open_closed_active_count t a \<in> {0, 1}"
proof -
  have "\<not>(1 < open_closed_active_count t a)" sorry
  moreover
  have "\<not>(open_active_count t a < 0)" sorry
  ultimately
  show ?thesis by fastforce
qed

lemma closed_active_count_ran:
  assumes "a \<in> actions" 
  shows "closed_active_count t a \<in> {0, 1}"
  sorry

lemma locked_before_and_in_instant:
  "locked_before t p - card {a \<in> actions. (t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<in> happ_seq} = locked_in_instant t p"
proof -
  have "locked_before t p - locked_in_instant t p = \<Sum>((\<lambda>a. card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}) ` locked_by p) - \<Sum>((\<lambda>a. card {s. s < t \<and> (s, at_start a) \<in> happ_seq}) ` locked_by p)" 
    unfolding locked_before_def locked_in_instant_def open_active_count_def open_closed_active_count_def 
    unfolding image_iff
qed

lemma locked_in_instant_and_after:
  "locked_in_instant t p + card {a \<in> actions. (t, at_start a) \<in> happ_seq \<and> (t, at_end a) \<notin> happ_seq} = locked_after t p"
  sorry

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


lemma exec_time_and_separation:
  assumes  a_at_t: "(t, a) \<in> happ_seq"
      and mutex: "mutex_snap a b"
    shows "exec_time b t \<ge> \<epsilon> \<and> exec_time b t > 0"
proof (cases "\<exists>u < t. (u, b) \<in> happ_seq")
  case True

  have "\<forall>u. (u, b) \<in> happ_seq \<longrightarrow> \<not> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> t \<noteq> u)" using assms nm 
    unfolding mutex_valid_happ_seq_def nm_happ_seq_def mutex_snap_def[symmetric] by blast

  from a_at_t
  have "t \<in> htps \<pi>" using a_in_B_iff_t_in_htps unfolding happ_seq_def by fast
  then obtain j where
    j: "t = time_index \<pi> j"
    "j < card (htps \<pi>)" using time_index_img_set[OF valid_plan_finite[OF vp]] by blast
  
  have P_iff: "(\<lambda>t'. t' < t \<and> (t', b) \<in> happ_seq) = (\<lambda>t'. \<exists>i < card (htps \<pi>). time_index \<pi> i = t' \<and> i < j \<and> (time_index \<pi> i, b) \<in> happ_seq)" (is "?P = ?P'")
  proof -
    have "(\<lambda>t'. t' < t \<and> (t', b) \<in> happ_seq) = (\<lambda>t'. t' \<in> htps \<pi> \<and> t' < t \<and> (t', b) \<in> happ_seq)" using a_in_B_iff_t_in_htps unfolding happ_seq_def by fast
    also have "... = (\<lambda>t'. \<exists>i < card (htps \<pi>). time_index \<pi> i = t' \<and> t' < t \<and> (time_index \<pi> i, b) \<in> happ_seq)" using time_index_img_set[OF valid_plan_finite[OF vp]] by force
    also have "... = (\<lambda>t'. \<exists>i < card (htps \<pi>). time_index \<pi> i = t' \<and> i < j \<and> (time_index \<pi> i, b) \<in> happ_seq)"
      unfolding j(1) 
      using time_index_strict_sorted_set'[where j = j] 
      using time_index_strict_sorted_set[OF _ j(2)] 
      by blast
    finally show ?thesis .
  qed
  
  obtain u where
    u: "u < t"
    "(u, b) \<in> happ_seq"
    using True by blast
  hence "u \<in> htps \<pi>" using a_in_B_iff_t_in_htps happ_seq_def by fast
  hence "\<exists>i < card (htps \<pi>). i < j \<and> (time_index \<pi> i, b) \<in> happ_seq" (is "Ex ?P2") using P_iff u by meson
  moreover
  have P2_int: "\<And>x. ?P2 x \<Longrightarrow> x \<le> j" using time_index_sorted_set' by auto
  ultimately
  have P2: "?P2 (Greatest ?P2)" using GreatestI_ex_nat[where P = ?P2] by blast

  have P_1: "?P (time_index \<pi> (Greatest ?P2))" 
  proof -
    from P2 time_index_strict_sorted_set[OF _ j(2)] 
    show ?thesis unfolding j(1) by blast
  qed
  
  have P_max: "x \<le> time_index \<pi> (Greatest ?P2)" if assm: "?P x" for x 
  proof -
    from assm P_iff
    have "\<exists>i<card (htps \<pi>). time_index \<pi> i = x \<and> i < j \<and> (time_index \<pi> i, b) \<in> happ_seq" by meson
    then
    obtain i where
      i: "?P2 i"
      "x = time_index \<pi> i" by auto
    moreover
    have "i \<le> Greatest ?P2" using Greatest_le_nat[where P = ?P2] i(1) P2_int by blast
    moreover
    have "Greatest ?P2 < card (htps \<pi>)" using P2 ..
    ultimately
    show "x \<le> time_index \<pi> (Greatest ?P2)" using time_index_sorted_set by blast
  qed

  have "?P (Greatest ?P)" 
    apply (rule GreatestI_time)
     apply (rule P_1)
    using P_max by simp
  moreover
  have 1: "last_snap_exec b t = (GREATEST t'. t' < t \<and> (t', b) \<in> happ_seq)" using True unfolding pt_def by auto
  ultimately
  have b_at_t': "(\<lambda>u. u < t \<and> (u, b) \<in> happ_seq) (last_snap_exec b t)" (is "?t < t \<and> (?t, b) \<in> happ_seq") by auto

  { assume a: "(t, a) \<in> happ_seq" "(?t, b) \<in> happ_seq"

    have nm_cond: "t - ?t < \<epsilon> \<and> ?t - t < \<epsilon> \<and> (a \<noteq> b \<or> t \<noteq> ?t) \<or> (t = ?t \<and> a \<noteq> b) \<longrightarrow> \<not>mutex_snap a b" 
      using a nm unfolding mutex_valid_happ_seq_def nm_happ_seq_def mutex_snap_def by auto
    hence "mutex_snap a b \<longrightarrow> (t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> (a = b \<and> t = ?t)) \<and> (t \<noteq> ?t \<or> a = b)" by auto
    hence "mutex_snap a b \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> (a = b \<and> t = ?t)" 
          "mutex_snap a b \<longrightarrow> (t \<noteq> ?t \<or> a = b)" by auto

    hence "\<not>(\<not>(a \<noteq> b \<or> t \<noteq> ?t) \<or> \<not>mutex_snap a b) \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>" by auto
    hence "((a \<noteq> b \<or> t \<noteq> ?t) \<and> mutex_snap a b) \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  using a_at_t b_at_t' by blast
    hence "(a \<noteq> b \<or> t \<noteq> ?t) \<and> mutex_snap a b \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  by blast  
    moreover
    have "a \<noteq> b \<longrightarrow> mutex_snap a b" using mutex by blast
    ultimately
    have "a \<noteq> b \<or> (t \<noteq> ?t \<and> mutex_snap a b) \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>" by blast
    moreover
    have "t \<noteq> ?t" using b_at_t' by auto
    ultimately
    consider "t - ?t \<ge> \<epsilon>" | "?t - t \<ge> \<epsilon>" using mutex by blast
  }
  note c = this
  
  have t: "t > ?t" using b_at_t' by blast
  moreover
  have "\<epsilon> \<ge> 0" using eps_range less_le_not_le by fastforce
  ultimately 
  have "t - ?t \<ge> \<epsilon>"  
    apply (cases rule: c) 
    subgoal using assms by simp 
    subgoal using b_at_t' by simp 
    subgoal by blast 
    apply (drule order.trans)
     apply assumption
    by auto
  thus ?thesis
    apply -
    apply (rule conjI)
     apply (subst exec_time_def)
     apply simp
    using t unfolding exec_time_def by fastforce
next
  case False
  have 1: "time_index \<pi> 0 \<le> u" if "\<exists>h. (u, h) \<in> happ_seq" for u
  proof -
    have "u \<in> set (htpl \<pi>)" using that a_in_B_iff_t_in_htps set_htpl_eq_htps valid_plan_finite[OF vp] unfolding happ_seq_def by fast
    hence "\<exists>i. time_index \<pi> i = u \<and> i < length (htpl \<pi>)" using time_index_img_list by force
    thus "time_index \<pi> 0 \<le> u" using time_index_sorted_list by blast
  qed
  with a_at_t
  have 2: "time_index \<pi> 0 \<le> t" by auto
  
  have 3: "Least (\<lambda>t. \<exists>x. (t, x) \<in> happ_seq) = (time_index \<pi> 0)" 
  proof (rule Least_equality[OF _ 1])
    have "card (htps \<pi>) > 0" using a_in_B_iff_t_in_htps a_at_t card_gt_0_iff finite_htps valid_plan_finite vp unfolding happ_seq_def by fast
    hence "time_index \<pi> 0 \<in> htps \<pi>" using time_index_img_set valid_plan_finite vp by blast
    thus "\<exists>x. (time_index \<pi> 0, x) \<in> happ_seq" using a_in_B_iff_t_in_htps happ_seq_def by fast
  qed

  have "last_snap_exec b t = (LEAST t'. \<exists>x. (t', x) \<in> happ_seq) - (\<epsilon> + c)" using False unfolding pt_def by argo
  from this[simplified 3]
  have "last_snap_exec b t = time_index \<pi> 0 - (\<epsilon> + c)" .
  hence 4: "t - last_snap_exec b t = \<epsilon> + c + t - time_index \<pi> 0" by auto
  with 2
  have "0 < c + t - time_index \<pi> 0" using c by (simp add: add_strict_increasing)
  with 4
  have "\<epsilon> < t - last_snap_exec b t" unfolding 4
    by auto
  thus ?thesis unfolding exec_time_def Let_def using eps_range 
    apply -
    apply (rule conjI)
     apply simp
    by order
qed


lemma exec_time_when_ending:
  assumes a_in_actions: "a \<in> actions"
      and ending: "(t, at_end a) \<in> happ_seq"
      and not_starting: "(t, at_start a) \<notin> happ_seq"
  shows "\<exists>t' d. (a, t', d) \<in> ran \<pi> \<and> exec_time (at_start a) t = d"
proof -
  have "\<exists>!(s,d). (a, s, d) \<in> ran \<pi> \<and> t = s + d" using at_end_in_happ_seqE' a_in_actions ending unfolding happ_seq_def by simp
  then obtain s d where
    sd: "(a, s, d) \<in> ran \<pi>" 
    "t = s + d" by auto
  hence "s \<le> t \<and> (s, at_start a) \<in> happ_seq" 
    unfolding happ_seq_def plan_happ_seq_def 
    using valid_plan_durs(1)[OF vp] unfolding durations_ge_0_def by auto
  hence s: "s < t \<and> (s, at_start a) \<in> happ_seq" using not_starting apply (cases "s < t") by auto
  moreover
  have "t' \<le> s" if "t' < t" "(t', at_start a) \<in> happ_seq" for t'
  proof (rule ccontr)
    assume "\<not> t' \<le> s"
    hence st': "s < t'" by simp
    with that(2)
    obtain d' where
       t'd': "(a, t', d') \<in> ran \<pi>" 
      using at_start_in_happ_seqE'[OF a_in_actions] unfolding happ_seq_def by blast
    thus False using that st' sd nso[THEN no_self_overlap_spec] by force
  qed
  ultimately
  have "(GREATEST s. s < t \<and> (s, at_start a) \<in> happ_seq) = s" unfolding Greatest_def happ_seq_def by fastforce
  hence "exec_time (at_start a) t = d" using sd(2) s unfolding exec_time_def pt_def by auto
  thus ?thesis using sd(1) by blast
qed

lemma exec_time_sat_dur_const:
  assumes a_in_actions: "a \<in> actions"
      and ending: "(t, at_end a) \<in> happ_seq"
      and not_starting: "(t, at_start a) \<notin> happ_seq"
    shows "satisfies_duration_bounds lower upper a (exec_time (at_start a) t)"
  using exec_time_when_ending[OF assms(1, 2, 3)] valid_plan_durs(2)[OF vp]
  unfolding durations_valid_def by blast
  

lemma exec_time_at_init:
  assumes some_happs: "0 < card (htps \<pi>)"
  shows "exec_time b (time_index \<pi> 0) = \<epsilon> + c"
proof -
  have "\<forall>i < card (htps \<pi>). time_index \<pi> 0 \<le> time_index \<pi> i" using time_index_sorted_set by blast
  hence "\<forall>t \<in> htps \<pi>. time_index \<pi> 0 \<le> t" using time_index_img_set[OF valid_plan_finite[OF vp]] by force 
  hence "\<not>(\<exists>s \<in> htps \<pi>. s < time_index \<pi> 0)" by auto
  hence 1: "\<not>(\<exists>s < time_index \<pi> 0. \<exists>x. (s, x) \<in> happ_seq)" unfolding happ_seq_def plan_happ_seq_def htps_def by blast
  
  have "time_index \<pi> 0 \<in> htps \<pi>" using time_index_img_set[OF valid_plan_finite[OF vp]] using some_happs by blast
  hence "\<exists>x. (time_index \<pi> 0, x) \<in> happ_seq" unfolding happ_seq_def plan_happ_seq_def unfolding htps_def by blast
  with 1
  have "Least (\<lambda>t'. \<exists>x. (t', x) \<in> happ_seq) = time_index \<pi> 0"
    apply -
    apply (rule Least_equality)
     apply simp
    by force
  with 1
  show ?thesis unfolding exec_time_def pt_def by (auto simp: Let_def)
qed


end
end
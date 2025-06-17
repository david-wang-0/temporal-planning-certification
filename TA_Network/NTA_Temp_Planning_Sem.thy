theory NTA_Temp_Planning_Sem
  imports Temporal_Planning_Base.Temporal_Plans
          "HOL-Library.Multiset"
          Temporal_Planning_Base.ListMisc
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

definition "app_effs S M \<equiv> apply_effects adds dels M S"

definition "inv_seq \<equiv> plan_inv_seq \<pi> over_all"

definition "plan_invs_before t \<equiv> invs_at inv_seq t"

definition "plan_state_seq \<equiv> SOME MS. valid_state_seq MS \<and> MS 0 = init \<and> goal \<subseteq> MS (length (htpl \<pi>))"

definition "action_list \<equiv> SOME xs. set xs = actions \<and> distinct xs"

lemma valid_state_seqE: 
  assumes "valid_state_seq MS"
    and "i < length (htpl \<pi>)"
    and "apply_effects adds dels (MS i) (happ_at (plan_happ_seq \<pi> at_start at_end) (time_index \<pi> i)) = MS (Suc i) \<Longrightarrow> invs_at (plan_inv_seq \<pi> over_all) (time_index \<pi> i) \<subseteq> MS i \<Longrightarrow> \<Union> (pre ` happ_at (plan_happ_seq \<pi> at_start at_end) (time_index \<pi> i)) \<subseteq> MS i \<Longrightarrow> thesis"
  shows thesis
  apply (insert assms(1)) unfolding valid_state_seq_def valid_state_sequence_def Let_def
  apply (drule spec)
  apply (drule mp[OF _ assms(2)])
  apply (erule conjE)+
  using assms(3) by blast

lemma set_action_list: "set action_list = actions"
  unfolding action_list_def using finite_actions[THEN finite_distinct_list, THEN someI_ex] by blast

lemma distinct_action_list: "distinct action_list"
  unfolding action_list_def using finite_actions[THEN finite_distinct_list, THEN someI_ex] by blast


lemma length_action_list: "length action_list = card actions" 
  using set_action_list distinct_action_list distinct_card by metis

lemma plan_state_seq_valid: "valid_state_seq plan_state_seq \<and> plan_state_seq 0 = init \<and> goal \<subseteq> plan_state_seq (length (htpl \<pi>))"
    apply (insert vp[THEN valid_plan_state_seq])
  unfolding valid_state_seq_def[symmetric]
  unfolding plan_state_seq_def
    apply (erule someI2_ex[where Q = "\<lambda>M. valid_state_seq M \<and> M 0 = init \<and> goal \<subseteq> M (length (htpl \<pi>))"])
  by blast
  
  
lemmas plan_state_seq_props = plan_state_seq_valid[simplified valid_state_seq_def valid_state_sequence_def Let_def]

lemma plan_state_seq_happ_pres:
  assumes "i < length (htpl \<pi>)"
  shows "\<Union> (pre ` happ_at happ_seq (time_index \<pi> i)) \<subseteq> plan_state_seq i"
  using assms plan_state_seq_props 
  unfolding Let_def unfolding happ_seq_def by blast

lemma at_start_in_happ_seqI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "(t, at_start a) \<in> happ_seq"
  using assms unfolding happ_seq_def plan_happ_seq_def by blast

lemma at_start_in_happ_seqE'':
  assumes a_in_acts: "a \<in> actions"
      and sn: "(s, at_start a) \<in> happ_seq"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  using assms at_start_in_happ_seqE' happ_seq_def by simp

lemma at_end_in_happ_seqI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "(t + d, at_end a) \<in> happ_seq"
  using assms unfolding happ_seq_def plan_happ_seq_def by blast
  

lemma at_end_in_happ_seqE'':
  assumes a_in_acts: "a \<in> actions"
      and sn: "(s, at_end a) \<in> happ_seq"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"
  using assms at_end_in_happ_seqE' happ_seq_def by simp

lemma a_in_plan_is_in_actions:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "a \<in> actions" using assms pap unfolding plan_actions_in_problem_def by blast

lemmas actions_at_time_index_exhaustive_cases' = actions_at_time_index_exhaustive_cases[OF vp[THEN valid_plan_finite] _ pap, of _ at_start at_end, simplified happ_seq_def[symmetric]]

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

subsubsection \<open>Time index and happenings\<close>

lemma time_index_happ_at:
  assumes "i < length (htpl \<pi>)"
  shows "\<exists>h. (time_index \<pi> i, h) \<in> happ_seq"
  apply (insert time_index_htpsD[OF vp[THEN valid_plan_finite] assms])
  apply (erule htpsE)
  unfolding happ_seq_def
   apply (rule exI)
   apply (rule in_happ_seqI)
   apply simp
  apply (rule exI)
  apply (erule ssubst)
  by (erule in_happ_seqI)


subsubsection \<open>Execution state\<close>

text \<open>Binary, but could be changed to count the active instances.\<close>

text \<open>Superseded by active count\<close>

definition exec_state_sequence::"('time \<times> 'action) set" where
"exec_state_sequence \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s < t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' < t)}"

definition exec_state_sequence'::"('time \<times> 'action) set" where
"exec_state_sequence' \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> happ_seq \<and> s \<le> t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> happ_seq \<and> s \<le> s' \<and> s' \<le> t)}"

abbreviation "ES t \<equiv> {a. (t, a) \<in> exec_state_sequence}"

abbreviation "IES t \<equiv> {a. (t, a) \<in> exec_state_sequence'}"


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

text \<open>The cases for snap-actions that occur at a timepoint\<close>
definition "is_instant_action t a \<equiv> (t, at_start a) \<in> happ_seq \<and> (t, at_end a) \<in> happ_seq"
definition "is_starting_action t a \<equiv> (t, at_start a) \<in> happ_seq \<and> (t, at_end a) \<notin> happ_seq"
definition "is_ending_action t a \<equiv> (t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<in> happ_seq"
definition "is_not_happening_action t a \<equiv> (t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<notin> happ_seq"

lemma is_instant_actionI: "(t, at_start a) \<in> happ_seq \<Longrightarrow> (t, at_end a) \<in> happ_seq \<Longrightarrow> is_instant_action t a"
  using is_instant_action_def by simp

lemma is_instant_action_dests: 
  assumes "is_instant_action t a" 
  shows "(t, at_start a) \<in> happ_seq" "(t, at_end a) \<in> happ_seq"
  using is_instant_action_def assms by blast+

lemma is_starting_actionI: "(t, at_start a) \<in> happ_seq \<Longrightarrow> (t, at_end a) \<notin> happ_seq \<Longrightarrow> is_starting_action t a"
  using is_starting_action_def by simp

lemma is_starting_action_dests: 
  assumes "is_starting_action t a" 
  shows "(t, at_start a) \<in> happ_seq" "(t, at_end a) \<notin> happ_seq"
  using is_starting_action_def assms by blast+

lemma is_ending_actionI: "(t, at_start a) \<notin> happ_seq \<Longrightarrow> (t, at_end a) \<in> happ_seq \<Longrightarrow> is_ending_action t a"
  using is_ending_action_def by simp

lemma is_ending_action_dests: 
  assumes "is_ending_action t a" 
  shows "(t, at_start a) \<notin> happ_seq" "(t, at_end a) \<in> happ_seq"
  using is_ending_action_def assms by blast+

lemma is_not_happening_actionI: "(t, at_start a) \<notin> happ_seq \<Longrightarrow> (t, at_end a) \<notin> happ_seq \<Longrightarrow> is_not_happening_action t a"
  using is_not_happening_action_def by simp

lemma is_not_happening_action_dests: 
  assumes "is_not_happening_action t a" 
  shows "(t, at_start a) \<notin> happ_seq" "(t, at_end a) \<notin> happ_seq"
  using is_not_happening_action_def assms by blast+

lemma action_happening_cases:
  assumes "is_instant_action t a \<Longrightarrow> thesis"
          "is_starting_action t a \<Longrightarrow> thesis"
          "is_ending_action t a \<Longrightarrow> thesis"
          "is_not_happening_action t a \<Longrightarrow> thesis"
shows thesis
  using assms unfolding is_instant_action_def is_starting_action_def is_ending_action_def is_not_happening_action_def by blast

lemmas action_happening_case_defs = is_instant_action_def is_starting_action_def is_ending_action_def is_not_happening_action_def 
lemmas action_happening_case_dests = is_instant_action_dests is_starting_action_dests is_ending_action_dests is_not_happening_action_dests

lemma htps_action_happening_cases:
  assumes "t \<in> htps \<pi>"
      and "\<And>a. a \<in> actions \<Longrightarrow> is_starting_action t a \<Longrightarrow> thesis"
      and "\<And>a. a \<in> actions \<Longrightarrow> is_ending_action t a \<Longrightarrow> thesis"
      and "\<And>a. a \<in> actions \<Longrightarrow> is_instant_action t a \<Longrightarrow> thesis"
    shows thesis
proof -
  presume "\<exists>a \<in> actions. is_starting_action t a \<or> is_ending_action t a \<or> is_instant_action t a"
  thus thesis using assms by blast
next
  show "\<exists>a\<in>actions. is_starting_action t a \<or> is_ending_action t a \<or> is_instant_action t a" 
    apply (insert assms(1))
    apply (erule htpsE; (frule a_in_plan_is_in_actions, erule ssubst))
    unfolding action_happening_case_defs
     apply (drule at_start_in_happ_seqI, blast)
    by (drule at_end_in_happ_seqI, blast) 
qed

lemmas time_index_action_happening_cases = time_index_htpsD[OF vp[THEN valid_plan_finite], THEN htps_action_happening_cases]

lemma action_happening_disj: 
  "\<not>(is_instant_action t n \<and> is_starting_action t n)"
  "\<not>(is_instant_action t n \<and> is_ending_action t n)"
  "\<not>(is_instant_action t n \<and> is_not_happening_action t n)"
  "\<not>(is_starting_action t n \<and> is_ending_action t n)"
  "\<not>(is_starting_action t n \<and> is_not_happening_action t n)"
  "\<not>(is_ending_action t n \<and> is_not_happening_action t n)"
  "is_instant_action t n \<Longrightarrow> \<not>is_starting_action t n \<and> \<not>is_ending_action t n \<and> \<not>is_not_happening_action t n"
  "is_starting_action t n \<Longrightarrow> \<not>is_instant_action t n \<and> \<not>is_ending_action t n \<and> \<not>is_not_happening_action t n"
  "is_ending_action t n \<Longrightarrow> \<not>is_instant_action t n \<and> \<not>is_starting_action t n \<and> \<not>is_not_happening_action t n"
  "is_not_happening_action t n \<Longrightarrow> \<not>is_instant_action t n \<and> \<not>is_starting_action t n \<and> \<not>is_ending_action t n"
  using action_happening_case_defs by blast+


context
  fixes t::'time
    and a::'action
begin

lemma finite_open_started: "finite {s'. s' < t \<and> (s', at_start a) \<in> happ_seq}" using finite_start_tps by auto
lemma finite_closed_started: "finite {s'. s' \<le> t \<and> (s', at_start a) \<in> happ_seq}" using finite_start_tps by auto
lemma finite_open_ended: "finite {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using finite_end_tps by auto
lemma finite_closed_ended: "finite {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}" using finite_end_tps by auto
(* Maybe it is a bad idea to put these definitions into a block with the "a \<in> actions" assumption *)
subsection \<open>Counting the various sets of active actions\<close>
definition open_active_count where
"open_active_count \<equiv> card {s. s < t \<and> (s, at_start a) \<in> happ_seq} - card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"

definition closed_active_count where
"closed_active_count \<equiv> card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq} - card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"

text \<open>The other two cases are constructed by counting the occurrences of an action starting and ending. 
This one needs to take into account the edge case of an action being schedule with a duration of 0.
An action running with a duration of 0 is not considered to be active for checking invariants.  

There are two cases, namely simple actions which have no invariants, and durative actions, whose invariants hold 
between their end and start, excluding the actual timepoint. This exclusion is seen in the formalisation
by Abdulaziz and Koller. Their notion of \<^emph>\<open>invariants at\<close> is equivalent to our notion of \<^emph>\<open>invariants before\<close>.

Semantically, "invariants at" are the invariants which must be satisfied by the state \<^emph>\<open>at\<close> a 
timepoint. There are two significant states, namely the one that the snap-actions/happenings will be 
applied to and the state that they have been applied to. The state \<^emph>\<open>at\<close> the timepoint is the former.

Note, that there are more than two states, if snap-actions are applied sequentially. Snap-actions are 
essentially applied sequentially, because there is no true concurrency in this formalisation. \<close>
definition open_closed_active_count where
"open_closed_active_count \<equiv> open_active_count - (if is_ending_action t a then 1 else 0)"

definition closed_open_active_count where
"closed_open_active_count \<equiv> open_active_count + (if is_starting_action t a then 1 else 0)"

definition active_count'' where
"active_count'' \<equiv> open_active_count + (if is_starting_action t a then 1 else 0) - (if is_ending_action t a then 1 else 0)"

subsubsection \<open>Properties of these sets\<close>

definition open_start_list where "open_start_list \<equiv> sorted_list_of_set {s. s < t \<and> (s, at_start a) \<in> happ_seq}"
definition closed_start_list where "closed_start_list \<equiv> sorted_list_of_set {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}"

definition open_end_list where "open_end_list \<equiv> sorted_list_of_set {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
definition closed_end_list where "closed_end_list \<equiv> sorted_list_of_set {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"
   
lemma open_start_list_len: "length (open_start_list) = card {s. s < t \<and> (s, at_start a) \<in> happ_seq}" unfolding open_start_list_def length_sorted_list_of_set by blast
lemma open_start_list_sorted: "sorted (open_start_list)" using sorted_sorted_list_of_set open_start_list_def by simp
lemma open_start_list_distinct: "distinct (open_start_list)" using distinct_sorted_list_of_set open_start_list_def by auto
lemma set_open_start_list: "set (open_start_list) = {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using open_start_list_def set_sorted_list_of_set finite_open_started by auto
context 
  assumes a_in_acts: "a \<in> actions"
begin

lemma open_start_list_nth_happ_seqE: "((open_start_list) ! i, at_start a) \<in> happ_seq" if "i < length (open_start_list)" for i 
proof -
  have "(open_start_list) ! i \<in> set (open_start_list)" using that by auto
  hence "(open_start_list) ! i \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set finite_open_started open_start_list_def by simp
  thus ?thesis by blast
qed

lemma open_start_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (open_start_list) ! i = t'" if "i < length (open_start_list)" for i 
  using open_start_list_nth_happ_seqE[OF that, THEN at_start_in_happ_seqE''[OF a_in_acts]] by simp

lemma open_start_list_nth_ran: "(open_start_list) ! i < t" if "i < length (open_start_list)" for i
proof -
  have "(open_start_list) ! i \<in> set (open_start_list)" using that by auto
  hence "(open_start_list) ! i \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set finite_open_started open_start_list_def by auto
  thus ?thesis by simp
qed

lemma open_start_list_planI: "\<exists>n < length (open_start_list). (open_start_list) ! n = t'" if "(a, t', d') \<in> ran \<pi>" "t' < t" for t' d'
proof -
  have "t' \<in> {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using that happ_seq_def plan_happ_seq_def by fast
  hence "t' \<in> set (open_start_list)" using open_start_list_def finite_open_started set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed
   
lemma closed_start_list_len: "length (closed_start_list) = card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" unfolding closed_start_list_def length_sorted_list_of_set by blast
lemma closed_start_list_sorted: "sorted (closed_start_list)" using sorted_sorted_list_of_set closed_start_list_def by simp
lemma closed_start_list_distinct: "distinct (closed_start_list)" using distinct_sorted_list_of_set closed_start_list_def by auto
lemma set_closed_start_list: "set (closed_start_list) = {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" using closed_start_list_def set_sorted_list_of_set finite_closed_started by auto

lemma closed_start_list_nth_happ_seqE: "((closed_start_list) ! i, at_start a) \<in> happ_seq" if "i < length (closed_start_list)" for i 
proof -
  have "(closed_start_list) ! i \<in> set (closed_start_list)" using that by auto
  hence "(closed_start_list) ! i \<in> {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set finite_closed_started closed_start_list_def by simp
  thus ?thesis by blast
qed

lemma closed_start_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (closed_start_list) ! i = t'" if "i < length (closed_start_list)" for i 
  using closed_start_list_nth_happ_seqE[OF that, THEN at_start_in_happ_seqE''[OF a_in_acts]] by simp

lemma closed_start_list_nth_ran: "(closed_start_list) ! i \<le> t" if "i < length (closed_start_list)" for i
proof -
  have "(closed_start_list) ! i \<in> set (closed_start_list)" using that by auto
  hence "(closed_start_list) ! i \<in> {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" using set_sorted_list_of_set finite_closed_started closed_start_list_def by auto
  thus ?thesis by simp
qed

lemma closed_start_list_planI: "\<exists>n < length (closed_start_list). (closed_start_list) ! n = t'" if "(a, t', d') \<in> ran \<pi>" "t' \<le> t" for t' d'
proof -
  have "t' \<in> {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" using that happ_seq_def plan_happ_seq_def by fast
  hence "t' \<in> set (closed_start_list)" using closed_start_list_def finite_closed_started set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed

lemma open_end_list_len: "length (open_end_list) = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" unfolding open_end_list_def length_sorted_list_of_set by blast
lemma open_end_list_sorted: "sorted (open_end_list)" using sorted_sorted_list_of_set open_end_list_def by auto
lemma open_end_list_distinct: "distinct (open_end_list)" using distinct_sorted_list_of_set open_end_list_def by auto
lemma set_open_end_list: "set (open_end_list) = {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" using open_end_list_def set_sorted_list_of_set finite_open_ended by auto

lemma open_end_list_nth_happ_seqE: "((open_end_list) ! i, at_end a) \<in> happ_seq" if "i < length (open_end_list)" for i 
proof -
  have "(open_end_list) ! i \<in> set (open_end_list)" using that by auto
  hence "(open_end_list) ! i \<in> {s. s < t \<and> (s, at_end a) \<in> happ_seq}" using set_sorted_list_of_set finite_open_ended open_end_list_def by simp
  thus ?thesis by blast
qed

lemma open_end_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (open_end_list) ! i = t' + d" if "i < length (open_end_list)" for i 
  using open_end_list_nth_happ_seqE[OF that] at_end_in_happ_seqE''[OF a_in_acts] by simp

lemma open_end_list_nth_ran: "(open_end_list) ! i < t" if "i < length (open_end_list)" for i
proof -
  from that
  have "(open_end_list) ! i \<in> set (open_end_list)" using that by auto
  hence "(open_end_list) ! i \<in> {s. s < t \<and> (s, at_end a) \<in> happ_seq}" using set_sorted_list_of_set finite_open_ended open_end_list_def by auto
  thus ?thesis by simp
qed

lemma open_end_list_planI: "\<exists>n < length (open_end_list). (open_end_list) ! n = t' + d'" if "(a, t', d') \<in> ran \<pi>" "t' + d' < t" for t' d'
proof -
  have "t' + d'\<in> {s. s < t \<and> (s, at_end a) \<in> happ_seq}" using that happ_seq_def plan_happ_seq_def by fast
  hence "t' + d' \<in> set (open_end_list)" using open_end_list_def finite_open_ended set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed

lemma closed_end_list_len: "length (closed_end_list) = card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}" unfolding closed_end_list_def length_sorted_list_of_set by blast
lemma closed_end_list_sorted: "sorted (closed_end_list)" using sorted_sorted_list_of_set closed_end_list_def by auto
lemma closed_end_list_distinct: "distinct (closed_end_list)" using distinct_sorted_list_of_set closed_end_list_def by auto
lemma set_closed_end_list: "set (closed_end_list) = {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}" using closed_end_list_def set_sorted_list_of_set finite_closed_ended by auto

lemma closed_end_list_nth_happ_seqE: "((closed_end_list) ! i, at_end a) \<in> happ_seq" if "i < length (closed_end_list)" for i 
proof -
  have "(closed_end_list) ! i \<in> set (closed_end_list)" using that by auto
  hence "(closed_end_list) ! i \<in> {s. s \<le> t \<and> (s, at_end a) \<in> happ_seq}" using set_sorted_list_of_set finite_closed_ended closed_end_list_def by simp
  thus ?thesis by blast
qed

lemma closed_end_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (closed_end_list) ! i = t' + d" if "i < length (closed_end_list)" for i 
  using closed_end_list_nth_happ_seqE[OF that] at_end_in_happ_seqE''[OF a_in_acts] by simp

lemma closed_end_list_nth_ran: "(closed_end_list) ! i \<le> t" if "i < length (closed_end_list)" for i
proof -
  from that
  have "(closed_end_list) ! i \<in> set (closed_end_list)" using that by auto
  hence "(closed_end_list) ! i \<in> {s. s \<le> t \<and> (s, at_end a) \<in> happ_seq}" using set_sorted_list_of_set finite_closed_ended closed_end_list_def by auto
  thus ?thesis by simp
qed

lemma closed_end_list_planI: "\<exists>n < length (closed_end_list). (closed_end_list) ! n = t' + d'" if "(a, t', d') \<in> ran \<pi>" "t' + d' \<le> t" for t' d'
proof -
  have "t' + d'\<in> {s. s \<le> t \<and> (s, at_end a) \<in> happ_seq}" using that happ_seq_def plan_happ_seq_def by fast
  hence "t' + d' \<in> set (closed_end_list)" using closed_end_list_def finite_closed_ended set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed

subsubsection \<open>Properties\<close>

lemma open_start_open_end_paired: "\<forall>n \<le> i. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<and> open_end_list ! n = t + d) 
          \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<longrightarrow> open_end_list ! n = t + d)
          \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! n = t + d \<longrightarrow> open_start_list ! n = t)" if iel: "i < length open_end_list" and isl: "i < length open_start_list" for i
  using that
proof (induction i)
  case 0
  from open_start_list_nth_planE 0 
  have tsds': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! 0 = t" by blast 
  then obtain ts ds where
    tsds: "open_start_list ! 0 = ts"
    "(a, ts, ds) \<in> ran \<pi>" by blast
  with tsds'
  have tsds'': "\<forall>ts' ds'. (a, ts', ds') \<in> ran \<pi> \<longrightarrow> open_start_list ! 0 = ts' \<longrightarrow> ts' = ts \<and> ds' = ds" by blast

  have tsds_t: "ts < t" using open_start_list_nth_ran tsds 0 by auto

  from open_end_list_nth_planE 0
  have tede': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_end_list ! 0 = t + d" by blast
  then obtain te de where
    tede: "open_end_list ! 0 = te + de"
    "(a, te, de) \<in> ran \<pi>" by blast
  with tede'
  have tede'': "\<forall>te' de'. (a, te', de') \<in> ran \<pi> \<longrightarrow> open_end_list ! 0 = te' + de' \<longrightarrow> te' = te \<and> de' = de" by blast

  have tede_t: "te + de < t" using open_end_list_nth_ran tede 0 by metis
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
    from tede(1) 0 open_start_list_planI[OF tede(2)]
    have "\<exists>n < length open_start_list. open_start_list ! n = te" using tede_t by simp
    with 2 tsds
    show ?thesis using open_start_list_sorted sorted_nth_mono by fastforce
  next
    case 3
    hence "ts + ds < t" using tede_t by simp
    with open_end_list_planI[OF tsds(2)]
    obtain n where
      n: "n<length open_end_list" "open_end_list ! n = ts + ds" by auto
    have "ts + ds < te + de" using tede_t(2) 3 by order
    thus ?thesis using open_end_list_sorted[THEN sorted_nth_mono, OF _ n(1), of 0] n(2) tede(1) by simp
  next
    case 4
    show ?thesis 
    proof (cases "ts + ds < te")
      case True
      with tede_t open_end_list_planI[OF tsds(2)]
      obtain n where
        n: "n<length open_end_list" "open_end_list ! n = ts + ds" by fastforce
      with tede_t(2) True
      have "ts + ds < te + de" by order
      thus ?thesis using open_end_list_sorted[THEN sorted_nth_mono] n tede by fastforce
    next
      case False
      hence "te \<le> ts + ds" by simp
      with nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)] 4 
      show ?thesis by fastforce
    qed
  next
    case 5
    hence "te < t" using tede_t by auto
    with open_start_list_planI[OF tede(2)]
    obtain n where
      n: "n<length open_start_list" "open_start_list ! n = te" by blast
    have "te < ts" using 5 tede_t by order
    with n tsds(1)
    show ?thesis using open_start_list_sorted[THEN sorted_nth_mono] by fastforce
  qed
next
  case (Suc i)
  have IH1: "\<forall>n\<le>i. \<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<and> open_end_list ! n = t + d" using Suc by auto
  have IH2: "\<forall>n\<le>i. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<longrightarrow> open_end_list ! n = t + d)" using Suc by auto
  have IH3: "\<forall>n\<le>i. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! n = t + d \<longrightarrow> open_start_list ! n = t)" using Suc by auto

  from open_start_list_nth_planE Suc(3)
  have tsds': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! (Suc i) = t" by blast 
  then obtain ts ds where
    tsds: "open_start_list ! (Suc i) = ts"
    "(a, ts, ds) \<in> ran \<pi>" by blast
  with tsds'
  have tsds': "\<forall>ts' ds'. (a, ts', ds') \<in> ran \<pi> \<longrightarrow> open_start_list ! Suc i = ts' \<longrightarrow> ts' = ts \<and> ds' = ds" by blast

  have tsds_t: "ts < t" using open_start_list_nth_ran tsds Suc by auto
  have "ts \<le> ts + ds" using plan_durations[OF tsds(2)] by auto
  note tsds_t = tsds_t this

  from open_end_list_nth_planE Suc(2)
  have tede': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_end_list ! (Suc i) = t + d" by blast
  then obtain te de where
    tede: "open_end_list ! (Suc i) = te + de"
    "(a, te, de) \<in> ran \<pi>" by blast
  with tede'
  have tede': "\<forall>te' de'. (a, te', de') \<in> ran \<pi> \<longrightarrow> open_end_list ! Suc i = te' + de' \<longrightarrow> te' = te \<and> de' = de" by blast

  have tede_t: "te + de < t" using open_end_list_nth_ran tede Suc by metis
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
  hence step: "(\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! Suc i = t \<and> open_end_list ! Suc i = t + d) \<and> 
          (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! Suc i = t \<longrightarrow> open_end_list ! Suc i = t + d) \<and> 
          (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! Suc i = t + d \<longrightarrow> open_start_list ! Suc i = t)" 
  proof cases
    case 1
    then show ?thesis using tede tsds tede' tsds' by blast
  next
    case 2
    show ?thesis
    proof (cases "te + de < ts")
      case True
      from tede open_start_list_planI tede_t
      obtain n where 
        n: "n < length open_start_list" "open_start_list ! n = te" by auto
      with 2 tsds 
      have "open_start_list ! n < open_start_list ! (Suc i)" by auto
      hence "\<not>open_start_list ! (Suc i) \<le> open_start_list ! n" by simp
      with sorted_nth_mono[OF open_start_list_sorted, OF _ n(1)]
      have "\<not> Suc i \<le> n" by auto
      hence n_Suc: "n < Suc i" by simp
      hence "n \<le> i" by simp
      with IH2 n tede(2)
      have "open_end_list ! n = te + de" by blast
      with tede(1) 
      have "open_end_list ! n = open_end_list ! Suc i" by simp
      with open_end_list_distinct 
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
    with tsds(2)[THEN open_end_list_planI] tede_t 
    obtain n where
      n: "n<length open_end_list" "open_end_list ! n = ts + ds" by fastforce

    from sorted_nth_mono[OF open_end_list_sorted, OF _ n(1)] 
    have "\<forall>i. \<not>(open_end_list ! i \<le> open_end_list ! n) \<longrightarrow> \<not>i \<le> n" by blast
    with tede(1) n(2) tsds_tede
    have "\<not>Suc i \<le> n" by simp
    hence n_Suc_i: "n < Suc i" by auto
    hence "n \<le> i" by simp
    with IH3 n tsds(2)
    have "open_start_list ! n = ts" by simp
    with tsds(1)
    have "open_start_list ! n = open_start_list ! Suc i" by simp
    hence False using Suc(3) n_Suc_i open_start_list_distinct[simplified distinct_conv_nth] by auto
    thus ?thesis by simp
  next
    case 4
    show ?thesis 
    proof (cases "ts + ds < te")
      case True
      hence tsds_tede: "ts + ds < te + de"  using tede_t by order
      with tsds(2)[THEN open_end_list_planI] tede_t 
      obtain n where
        n: "n<length open_end_list" "open_end_list ! n = ts + ds" by fastforce

      from sorted_nth_mono[OF open_end_list_sorted, OF _ n(1)] 
      have "\<forall>i. \<not>(open_end_list ! i \<le> open_end_list ! n) \<longrightarrow> \<not>i \<le> n" by blast
      with tede(1) n(2) tsds_tede
      have "\<not>Suc i \<le> n" by simp
      hence n_Suc_i: "n < Suc i" by auto
      hence "n \<le> i" by simp
      with IH3 n tsds(2)
      have "open_start_list ! n = ts" by simp
      with tsds(1)
      have "open_start_list ! n = open_start_list ! Suc i" by simp
      hence False using Suc(3) n_Suc_i open_start_list_distinct[simplified distinct_conv_nth] by auto
      thus ?thesis by simp
    next
      case False
      hence "te \<le> ts + ds" by simp
      with nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)] 4
      show ?thesis by fastforce
    qed
  next
    case 5
    from tede open_start_list_planI tede_t
    obtain n where 
      n: "n < length open_start_list" "open_start_list ! n = te" by auto
    with 5 tsds tede_t
    have "open_start_list ! n < open_start_list ! (Suc i)" by order
    hence "\<not>open_start_list ! (Suc i) \<le> open_start_list ! n" by simp
    with sorted_nth_mono[OF open_start_list_sorted, OF _ n(1)]
    have "\<not> Suc i \<le> n" by auto
    hence n_Suc: "n < Suc i" by simp
    hence "n \<le> i" by simp
    with IH2 n tede(2)
    have "open_end_list ! n = te + de" by blast
    with tede(1) 
    have "open_end_list ! n = open_end_list ! Suc i" by simp
    with open_end_list_distinct 
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

lemma open_active_count_ran:
  shows "open_active_count \<in> {0, 1}"
proof -
  have "\<not>1 < open_active_count"
  proof 
    assume "1 < open_active_count"
    hence 1: "2 \<le> card {s'. s' < t \<and> (s', at_start a) \<in> happ_seq} - card {s. s < t \<and> (s, at_end a) \<in> happ_seq}" 
      using finite_open_ended finite_open_started using open_active_count_def by auto

    define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
    hence n1: "n + 2 \<le> card {s. s < t \<and> (s, at_start a) \<in> happ_seq}" using 1 by simp
    
    have open_start_list_len: "length open_start_list = card {s. s < t \<and> (s, at_start a) \<in> happ_seq}" unfolding open_start_list_def length_sorted_list_of_set by blast
    have n_open_start_list: "n + 2 \<le> length open_start_list" using n1 unfolding length_sorted_list_of_set using open_start_list_def by simp

    have open_end_list_len: "length open_end_list = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}" unfolding open_end_list_def length_sorted_list_of_set by blast
    have n_open_end_list: "n = length open_end_list" using n_def unfolding length_sorted_list_of_set[symmetric] using open_end_list_def by simp
    
    have open_start_list_open_end_list_len: "length open_end_list + 2 \<le> length open_start_list" using n_open_end_list n_open_start_list by blast

    hence end_start_paired: 
      "\<forall>n < length open_end_list. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<and> open_end_list ! n = t + d)" 
      "\<forall>n < length open_end_list.(\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<longrightarrow> open_end_list ! n = t + d)" 
      "\<forall>n < length open_end_list. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! n = t + d \<longrightarrow> open_start_list ! n = t)" 
      using open_start_open_end_paired by simp_all
    
    have n_ord: "\<forall>i < n. open_start_list ! i < open_start_list ! n"
    proof -
      have "\<forall>i < n. open_start_list ! i \<le> open_start_list ! n" using open_start_list_sorted sorted_nth_mono n_open_start_list by fastforce
      moreover
      have "\<forall>i < n. open_start_list ! i \<noteq> open_start_list ! n" using open_start_list_distinct unfolding distinct_conv_nth using n_open_start_list by simp
      ultimately
      show ?thesis by force
    qed

    have n_starts_after: "\<forall>i < n. open_end_list ! i < open_start_list ! n"
    proof -
      {fix i
        assume i: "i < n"
        hence sisn: "open_start_list ! i < open_start_list ! n" using n_ord by simp
        with end_start_paired(1) open_end_list_len n_def i
        obtain ti di where
          tidi: "(a, ti, di) \<in> ran \<pi> " 
          "open_start_list ! i = ti" 
          "open_end_list ! i = ti + di" by auto
        from open_start_list_nth_planE[of n] n_open_start_list
        obtain tn dn where
          tndn: "(a, tn, dn) \<in> ran \<pi>" 
          "open_start_list ! n = tn" by auto
      
        assume "open_end_list ! i \<ge> open_start_list ! n"
        with nso[THEN no_self_overlap_ran, OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
        have "False" by fastforce
      }
      thus ?thesis by fastforce
    qed

    have n_Suc_n: "open_start_list ! n < open_start_list ! Suc n" 
    proof -
      have "open_start_list ! n \<le> open_start_list ! Suc n" using open_start_list_sorted sorted_nth_mono n_open_start_list by fastforce
      moreover
      have "open_start_list ! n \<noteq> open_start_list ! Suc n" using open_start_list_distinct unfolding distinct_conv_nth using n_open_start_list by simp
      ultimately
      show ?thesis by force
    qed

    have sn_t: "open_start_list ! Suc n < t" using open_start_list_nth_ran n_open_start_list by simp

    obtain tn dn where
      tndn: "(a, tn, dn) \<in> ran \<pi>"
      "open_start_list ! n = tn" using open_start_list_nth_planE[of n] n_open_start_list by auto

    obtain tsn dsn where
      tsndsn: "(a, tsn, dsn) \<in> ran \<pi>"
      "open_start_list ! Suc n = tsn" using open_start_list_nth_planE[of "Suc n"] n_open_start_list by auto

    show False 
    proof (cases "tn + dn < t")
      case True
      with tndn
      have "tn + dn \<in> set open_end_list" using set_open_end_list unfolding happ_seq_def plan_happ_seq_def by fast
      then obtain n' where
        "open_end_list ! n' = tn + dn" 
        "n' < length open_end_list" unfolding in_set_conv_nth by blast
      hence "tn + dn < open_start_list ! n" using n_starts_after n_open_end_list by metis
      moreover
      have "open_start_list ! n \<le> tn + dn" using tndn plan_durations by simp
      ultimately
      show ?thesis by simp
    next
      case False
      thus ?thesis using plan_overlap_cond[OF tndn(1) tsndsn(1)] sn_t n_Suc_n tndn(2) tsndsn(2) by fastforce
    qed
  qed
  thus ?thesis by fastforce
qed

lemma open_active_count_cases:
assumes "open_active_count = 0 \<Longrightarrow> thesis"
    and "open_active_count = 1 \<Longrightarrow> thesis"
  shows "thesis" using assms open_active_count_ran by auto

lemma closed_start_closed_end_paired: "\<forall>n \<le> i. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! n = t \<and> closed_end_list ! n = t + d) 
          \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! n = t \<longrightarrow> closed_end_list ! n = t + d)
          \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! n = t + d \<longrightarrow> closed_start_list ! n = t)" 
  if iel: "i < length closed_end_list" and isl: "i < length closed_start_list" for i
  using that
proof (induction i)
  case 0
  from closed_start_list_nth_planE 0 
  have tsds': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! 0 = t" by blast 
  then obtain ts ds where
    tsds: "closed_start_list ! 0 = ts"
    "(a, ts, ds) \<in> ran \<pi>" by blast
  with tsds'
  have tsds'': "\<forall>ts' ds'. (a, ts', ds') \<in> ran \<pi> \<longrightarrow> closed_start_list ! 0 = ts' \<longrightarrow> ts' = ts \<and> ds' = ds" by blast

  have tsds_t: "ts \<le> t" using closed_start_list_nth_ran tsds 0 by auto

  from closed_end_list_nth_planE 0
  have tede': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! 0 = t + d" by blast
  then obtain te de where
    tede: "closed_end_list ! 0 = te + de"
    "(a, te, de) \<in> ran \<pi>" by blast
  with tede'
  have tede'': "\<forall>te' de'. (a, te', de') \<in> ran \<pi> \<longrightarrow> closed_end_list ! 0 = te' + de' \<longrightarrow> te' = te \<and> de' = de" by blast

  have tede_t: "te + de \<le> t" using closed_end_list_nth_ran tede 0 by metis
  hence "te \<le> te + de" using plan_durations[OF tede(2)] by auto
  note tede_t = tede_t this
  hence "te \<le> t" by order
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
    from tede(1) 0 closed_start_list_planI[OF tede(2)]
    have "\<exists>n < length closed_start_list. closed_start_list ! n = te" using tede_t by simp
    with 2 tsds
    show ?thesis using closed_start_list_sorted sorted_nth_mono by fastforce
  next
    case 3
    hence "ts + ds \<le> t" using tede_t by simp
    with closed_end_list_planI[OF tsds(2)]
    obtain n where
      n: "n<length closed_end_list" "closed_end_list ! n = ts + ds" by auto
    have "ts + ds < te + de" using tede_t(2) 3 by order
    thus ?thesis using closed_end_list_sorted[THEN sorted_nth_mono, OF _ n(1), of 0] n(2) tede(1) by simp
  next
    case 4
    show ?thesis 
    proof (cases "ts + ds < te")
      case True
      with tede_t closed_end_list_planI[OF tsds(2)]
      obtain n where
        n: "n<length closed_end_list" "closed_end_list ! n = ts + ds" by fastforce
      with tede_t(2) True
      have "ts + ds < te + de" by order
      thus ?thesis using closed_end_list_sorted[THEN sorted_nth_mono] n tede by fastforce
    next
      case False
      hence "te \<le> ts + ds" by simp
      with nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)] 4 
      show ?thesis by fastforce
    qed
  next
    case 5
    hence "te \<le> t" using tede_t by auto
    with closed_start_list_planI[OF tede(2)]
    obtain n where
      n: "n<length closed_start_list" "closed_start_list ! n = te" by blast
    have "te < ts" using 5 tede_t by order
    with n tsds(1)
    show ?thesis using closed_start_list_sorted[THEN sorted_nth_mono] by fastforce
  qed
next
  case (Suc i)
  have IH1: "\<forall>n\<le>i. \<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! n = t \<and> closed_end_list ! n = t + d" using Suc by auto
  have IH2: "\<forall>n\<le>i. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! n = t \<longrightarrow> closed_end_list ! n = t + d)" using Suc by auto
  have IH3: "\<forall>n\<le>i. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! n = t + d \<longrightarrow> closed_start_list ! n = t)" using Suc by auto

  from closed_start_list_nth_planE Suc(3)
  have tsds': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! (Suc i) = t" by blast 
  then obtain ts ds where
    tsds: "closed_start_list ! (Suc i) = ts"
    "(a, ts, ds) \<in> ran \<pi>" by blast
  with tsds'
  have tsds': "\<forall>ts' ds'. (a, ts', ds') \<in> ran \<pi> \<longrightarrow> closed_start_list ! Suc i = ts' \<longrightarrow> ts' = ts \<and> ds' = ds" by blast

  have tsds_t: "ts \<le> t" using closed_start_list_nth_ran tsds Suc by auto
  have "ts \<le> ts + ds" using plan_durations[OF tsds(2)] by auto
  note tsds_t = tsds_t this

  from closed_end_list_nth_planE Suc(2)
  have tede': "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! (Suc i) = t + d" by blast
  then obtain te de where
    tede: "closed_end_list ! (Suc i) = te + de"
    "(a, te, de) \<in> ran \<pi>" by blast
  with tede'
  have tede': "\<forall>te' de'. (a, te', de') \<in> ran \<pi> \<longrightarrow> closed_end_list ! Suc i = te' + de' \<longrightarrow> te' = te \<and> de' = de" by blast

  have tede_t: "te + de \<le> t" using closed_end_list_nth_ran tede Suc by metis
  hence "te \<le> te + de" using plan_durations[OF tede(2)] by auto
  note tede_t = tede_t this
  hence "te \<le> t" by order
  note tede_t = tede_t this

  from nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)]
  have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
  moreover
  from nso[THEN no_self_overlap_ran, OF tede(2) tsds(2)]
  have "ts = te \<and> ds = de \<or> ts < te \<or> te + de < ts" by blast
  ultimately
  consider "ts = te \<and> ds = de" | "te < ts" | "ts + ds < te" | "ts < te" | "te + de < ts" by blast
  hence step: "(\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! Suc i = t \<and> closed_end_list ! Suc i = t + d) \<and> 
          (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! Suc i = t \<longrightarrow> closed_end_list ! Suc i = t + d) \<and> 
          (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! Suc i = t + d \<longrightarrow> closed_start_list ! Suc i = t)" 
  proof cases
    case 1
    then show ?thesis using tede tsds tede' tsds' by blast
  next
    case 2
    show ?thesis
    proof (cases "te + de < ts")
      case True
      from tede closed_start_list_planI tede_t
      obtain n where 
        n: "n < length closed_start_list" "closed_start_list ! n = te" by auto
      with 2 tsds 
      have "closed_start_list ! n < closed_start_list ! (Suc i)" by auto
      hence "\<not>closed_start_list ! (Suc i) \<le> closed_start_list ! n" by simp
      with sorted_nth_mono[OF closed_start_list_sorted, OF _ n(1)]
      have "\<not> Suc i \<le> n" by auto
      hence n_Suc: "n < Suc i" by simp
      hence "n \<le> i" by simp
      with IH2 n tede(2)
      have "closed_end_list ! n = te + de" by blast
      with tede(1) 
      have "closed_end_list ! n = closed_end_list ! Suc i" by simp
      with closed_end_list_distinct 
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
    with tsds(2)[THEN closed_end_list_planI] tede_t 
    obtain n where
      n: "n<length closed_end_list" "closed_end_list ! n = ts + ds" by fastforce

    from sorted_nth_mono[OF closed_end_list_sorted, OF _ n(1)] 
    have "\<forall>i. \<not>(closed_end_list ! i \<le> closed_end_list ! n) \<longrightarrow> \<not>i \<le> n" by blast
    with tede(1) n(2) tsds_tede
    have "\<not>Suc i \<le> n" by simp
    hence n_Suc_i: "n < Suc i" by auto
    hence "n \<le> i" by simp
    with IH3 n tsds(2)
    have "closed_start_list ! n = ts" by simp
    with tsds(1)
    have "closed_start_list ! n = closed_start_list ! Suc i" by simp
    hence False using Suc(3) n_Suc_i closed_start_list_distinct[simplified distinct_conv_nth] by auto
    thus ?thesis by simp
  next
    case 4
    show ?thesis 
    proof (cases "ts + ds < te")
      case True
      hence tsds_tede: "ts + ds < te + de"  using tede_t by order
      with tsds(2)[THEN closed_end_list_planI] tede_t 
      obtain n where
        n: "n<length closed_end_list" "closed_end_list ! n = ts + ds" by fastforce

      from sorted_nth_mono[OF closed_end_list_sorted, OF _ n(1)] 
      have "\<forall>i. \<not>(closed_end_list ! i \<le> closed_end_list ! n) \<longrightarrow> \<not>i \<le> n" by blast
      with tede(1) n(2) tsds_tede
      have "\<not>Suc i \<le> n" by simp
      hence n_Suc_i: "n < Suc i" by auto
      hence "n \<le> i" by simp
      with IH3 n tsds(2)
      have "closed_start_list ! n = ts" by simp
      with tsds(1)
      have "closed_start_list ! n = closed_start_list ! Suc i" by simp
      hence False using Suc(3) n_Suc_i closed_start_list_distinct[simplified distinct_conv_nth] by auto
      thus ?thesis by simp
    next
      case False
      hence "te \<le> ts + ds" by simp
      with nso[THEN no_self_overlap_ran, OF tsds(2) tede(2)] 4
      show ?thesis by fastforce
    qed
  next
    case 5
    from tede closed_start_list_planI tede_t
    obtain n where 
      n: "n < length closed_start_list" "closed_start_list ! n = te" by auto
    with 5 tsds tede_t
    have "closed_start_list ! n < closed_start_list ! (Suc i)" by order
    hence "\<not>closed_start_list ! (Suc i) \<le> closed_start_list ! n" by simp
    with sorted_nth_mono[OF closed_start_list_sorted, OF _ n(1)]
    have "\<not> Suc i \<le> n" by auto
    hence n_Suc: "n < Suc i" by simp
    hence "n \<le> i" by simp
    with IH2 n tede(2)
    have "closed_end_list ! n = te + de" by blast
    with tede(1) 
    have "closed_end_list ! n = closed_end_list ! Suc i" by simp
    with closed_end_list_distinct 
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

lemma closed_active_count_ran:
  shows "closed_active_count \<in> {0, 1}"
proof -
  have "\<not>1 < closed_active_count"
  proof 
    assume "1 < closed_active_count"
    hence 1: "2 \<le> card {s'. s' \<le> t \<and> (s', at_start a) \<in> happ_seq} - card {s. s \<le> t \<and> (s, at_end a) \<in> happ_seq}" 
      using finite_closed_ended finite_closed_started using closed_active_count_def by auto

    define n where "n = card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"
    hence n1: "n + 2 \<le> card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" using 1 by simp
    
    have closed_start_list_len: "length closed_start_list = card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}" unfolding closed_start_list_def length_sorted_list_of_set by blast
    have n_closed_start_list: "n + 2 \<le> length closed_start_list" using n1 unfolding length_sorted_list_of_set using closed_start_list_def by simp

    have closed_end_list_len: "length closed_end_list = card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}" unfolding closed_end_list_def length_sorted_list_of_set by blast
    have n_closed_end_list: "n = length closed_end_list" using n_def unfolding length_sorted_list_of_set[symmetric] using closed_end_list_def by simp
    
    have closed_start_list_closed_end_list_len: "length closed_end_list + 2 \<le> length closed_start_list" using n_closed_end_list n_closed_start_list by blast

    hence end_start_paired: 
      "\<forall>n < length closed_end_list. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! n = t \<and> closed_end_list ! n = t + d)" 
      "\<forall>n < length closed_end_list.(\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! n = t \<longrightarrow> closed_end_list ! n = t + d)" 
      "\<forall>n < length closed_end_list. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! n = t + d \<longrightarrow> closed_start_list ! n = t)" 
      using closed_start_closed_end_paired by simp_all
    
    have n_ord: "\<forall>i < n. closed_start_list ! i < closed_start_list ! n"
    proof -
      have "\<forall>i < n. closed_start_list ! i \<le> closed_start_list ! n" using closed_start_list_sorted sorted_nth_mono n_closed_start_list by fastforce
      moreover
      have "\<forall>i < n. closed_start_list ! i \<noteq> closed_start_list ! n" using closed_start_list_distinct unfolding distinct_conv_nth using n_closed_start_list by simp
      ultimately
      show ?thesis by force
    qed

    have n_starts_after: "\<forall>i < n. closed_end_list ! i < closed_start_list ! n"
    proof -
      {fix i
        assume i: "i < n"
        hence sisn: "closed_start_list ! i < closed_start_list ! n" using n_ord by simp
        with end_start_paired(1) closed_end_list_len n_def i
        obtain ti di where
          tidi: "(a, ti, di) \<in> ran \<pi> " 
          "closed_start_list ! i = ti" 
          "closed_end_list ! i = ti + di" by auto
        from closed_start_list_nth_planE[of n] n_closed_start_list
        obtain tn dn where
          tndn: "(a, tn, dn) \<in> ran \<pi>" 
          "closed_start_list ! n = tn" by auto
      
        assume "closed_end_list ! i \<ge> closed_start_list ! n"
        with nso[THEN no_self_overlap_ran, OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
        have "False" by fastforce
      }
      thus ?thesis by fastforce
    qed

    have n_Suc_n: "closed_start_list ! n < closed_start_list ! Suc n" 
    proof -
      have "closed_start_list ! n \<le> closed_start_list ! Suc n" using closed_start_list_sorted sorted_nth_mono n_closed_start_list by fastforce
      moreover
      have "closed_start_list ! n \<noteq> closed_start_list ! Suc n" using closed_start_list_distinct unfolding distinct_conv_nth using n_closed_start_list by simp
      ultimately
      show ?thesis by force
    qed

    have sn_t: "closed_start_list ! Suc n \<le> t" using closed_start_list_nth_ran n_closed_start_list by simp

    obtain tn dn where
      tndn: "(a, tn, dn) \<in> ran \<pi>"
      "closed_start_list ! n = tn" using closed_start_list_nth_planE[of n] n_closed_start_list by auto

    obtain tsn dsn where
      tsndsn: "(a, tsn, dsn) \<in> ran \<pi>"
      "closed_start_list ! Suc n = tsn" using closed_start_list_nth_planE[of "Suc n"] n_closed_start_list by auto

    show False 
    proof (cases "tn + dn \<le> t")
      case True
      with tndn
      have "tn + dn \<in> set closed_end_list" using set_closed_end_list unfolding happ_seq_def plan_happ_seq_def by fast
      then obtain n' where
        "closed_end_list ! n' = tn + dn" 
        "n' < length closed_end_list" unfolding in_set_conv_nth by blast
      hence "tn + dn < closed_start_list ! n" using n_starts_after n_closed_end_list by metis
      moreover
      have "closed_start_list ! n \<le> tn + dn" using tndn plan_durations by simp
      ultimately
      show ?thesis by simp
    next
      case False
      thus ?thesis using plan_overlap_cond[OF tndn(1) tsndsn(1)] sn_t n_Suc_n tndn(2) tsndsn(2) by fastforce
    qed
  qed
  thus ?thesis by fastforce
qed

lemma closed_active_count_cases:
  assumes "closed_active_count = 0 \<Longrightarrow> thesis"
      and "closed_active_count = 1 \<Longrightarrow> thesis"
    shows thesis using assms closed_active_count_ran by auto

lemma open_closed_active_count_ran:
  shows "open_closed_active_count \<in> {0, 1}"
proof -
  have "\<not>open_closed_active_count > 1"
  proof 
    assume a: "1 < open_closed_active_count"
    hence "1 < open_active_count" unfolding open_closed_active_count_def by simp
    thus False using open_active_count_ran by auto
  qed
  thus ?thesis by auto
qed

lemma open_closed_active_count_cases:
  assumes "open_closed_active_count = 0 \<Longrightarrow> thesis"
      and "open_closed_active_count = 1 \<Longrightarrow> thesis"
    shows thesis using assms open_closed_active_count_ran by auto

lemma open_active_count_1E:
  assumes "open_active_count = 1"
  shows "\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d'"
proof -
  define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
  have open_end_list_n: "length open_end_list = n" using n_def open_end_list_len by simp
  have open_start_list_n: "length open_start_list = n + 1" using n_def assms open_start_list_len open_active_count_def by linarith

  have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<and> open_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<longrightarrow> open_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! i = t + d \<longrightarrow> open_start_list ! i = t)" 
    using open_start_list_n open_end_list_n open_start_open_end_paired by auto  

  from open_start_list_nth_planE[of n] open_start_list_n
  obtain tn dn where
    tndn: "(a, tn, dn) \<in> ran \<pi>" 
    "open_start_list ! n = tn" by auto

  have n_ord: "\<forall>i < n. open_start_list ! i < open_start_list ! n"
  proof -
    have "\<forall>i < n. open_start_list ! i \<le> open_start_list ! n" using open_start_list_sorted sorted_nth_mono open_start_list_n by fastforce
    moreover
    have "\<forall>i < n. open_start_list ! i \<noteq> open_start_list ! n" using open_start_list_distinct unfolding distinct_conv_nth using open_start_list_n by simp
    ultimately
    show ?thesis by force
  qed

  have n_starts_after: "\<forall>i < n. open_end_list ! i < open_start_list ! n"
  proof -
    {fix i
      assume i: "i < n"
      hence sisn: "open_start_list ! i < open_start_list ! n" using n_ord by simp
      with end_start_paired(1) open_end_list_len n_def i
      obtain ti di where
        tidi: "(a, ti, di) \<in> ran \<pi> " 
        "open_start_list ! i = ti" 
        "open_end_list ! i = ti + di" by auto
    
      assume "open_end_list ! i \<ge> open_start_list ! n"
      with nso[THEN no_self_overlap_ran, OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
      have "False" by fastforce
    }
    thus ?thesis by fastforce
  qed

  { assume "tn + dn < t"
    from open_end_list_planI[OF tndn(1) this] open_end_list_n
    obtain i where "i < n" "open_end_list ! i = tn + dn" by blast
    moreover
    have "tn \<le> tn + dn" using plan_durations tndn by simp
    ultimately
    have False using n_starts_after tndn by auto
  }
  thus ?thesis using tndn open_start_list_nth_ran[of n] open_start_list_n by force
qed

lemma open_ended_le_open_started: "card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq} \<le> card {s. s < t \<and> (s, at_start a) \<in> happ_seq}"
proof -
  {
    assume a: "card {s. s < t \<and> (s, at_start a) \<in> happ_seq} < card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
    define n where "n = card {s'. s' < t \<and> (s', at_start a) \<in> happ_seq}"
    have open_start_list_n: "length open_start_list = n" unfolding open_start_list_len n_def open_active_count_def by blast
    have open_end_list_n: "length open_end_list > n" using n_def open_end_list_len a by argo
    
    have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<and> open_end_list ! i = t + d)" 
         "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<longrightarrow> open_end_list ! i = t + d)" 
         "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! i = t + d \<longrightarrow> open_start_list ! i = t)" 
      using open_start_list_n open_end_list_n open_start_open_end_paired by auto

    have n_ord: "\<forall>i < n. open_end_list ! i < open_end_list ! n"
    proof -
      have "\<forall>i < n. open_end_list ! i \<le> open_end_list ! n" using open_end_list_sorted sorted_nth_mono open_end_list_n by fastforce
      moreover
      have "\<forall>i < n. open_end_list ! i \<noteq> open_end_list ! n" using open_end_list_distinct unfolding distinct_conv_nth using open_end_list_n by simp
      ultimately
      show ?thesis by force
    qed

    from open_end_list_nth_planE[of n] open_end_list_n
    obtain tn dn where
      tndn: "(a, tn, dn) \<in> ran \<pi>" 
      "open_end_list ! n = tn + dn" by blast
    {
      have 1: "tn + dn < t" using open_end_list_nth_ran tndn open_end_list_n by force
      moreover 
      have 2: "0 \<le> dn" using plan_durations tndn by simp
      moreover
      have 3: "tn < t" using 1 2 by (meson add_increasing2 leD leI)
      ultimately
      have "tn + dn < t" "0 \<le> dn" "tn < t" by auto
    } note tndn_ord = this
    
    from open_start_list_planI[OF tndn(1)] tndn_ord
    obtain i where
      i: "i<length open_start_list" "open_start_list ! i = tn" by blast
    with end_start_paired(2) tndn(1) open_start_list_n
    have "open_end_list ! i = tn + dn" by blast
    with tndn(2) n_ord i(1) open_start_list_n
    have False by auto
  }
  thus ?thesis by fastforce
qed

lemma open_active_count_0E:
  assumes "open_active_count = 0"
  shows "\<not>(\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d')"
proof 
  assume "\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d'"
  then obtain t' d' where
    td: "(a, t', d') \<in> ran \<pi>"
    "t' < t"
    "t \<le> t' + d'" by auto

  define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
  have open_end_list_n: "length open_end_list = n" using n_def open_end_list_len by simp
  have open_start_list_n: "length open_start_list = n" using assms unfolding open_start_list_len n_def open_active_count_def le_imp_diff_is_add[OF open_ended_le_open_started] by simp

  have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<and> open_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<longrightarrow> open_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! i = t + d \<longrightarrow> open_start_list ! i = t)" 
    using open_start_list_n open_end_list_n open_start_open_end_paired by auto

  from open_start_list_planI td open_start_list_n
  obtain i where
    i: "i < length open_start_list" "open_start_list ! i = t'" by blast

  with open_start_list_n td(1) end_start_paired(2)
  have "open_end_list ! i = t' + d'" by blast
  hence "t' + d' < t" using open_end_list_nth_ran i(1) unfolding open_start_list_n open_end_list_n by fastforce

  with td(3)
  show False by simp
qed

lemma closed_active_count_1E:
  assumes "closed_active_count = 1"
  shows "\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d'"
proof -
  define n where "n = card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"
  have closed_end_list_n: "length closed_end_list = n" using n_def closed_end_list_len by simp
  have closed_start_list_n: "length closed_start_list = n + 1" using n_def assms closed_start_list_len closed_active_count_def by linarith

  have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<and> closed_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<longrightarrow> closed_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! i = t + d \<longrightarrow> closed_start_list ! i = t)" 
    using closed_start_list_n closed_end_list_n closed_start_closed_end_paired by auto  

  from closed_start_list_nth_planE[of n] closed_start_list_n
  obtain tn dn where
    tndn: "(a, tn, dn) \<in> ran \<pi>" 
    "closed_start_list ! n = tn" by auto

  have n_ord: "\<forall>i < n. closed_start_list ! i < closed_start_list ! n"
  proof -
    have "\<forall>i < n. closed_start_list ! i \<le> closed_start_list ! n" using closed_start_list_sorted sorted_nth_mono closed_start_list_n by fastforce
    moreover
    have "\<forall>i < n. closed_start_list ! i \<noteq> closed_start_list ! n" using closed_start_list_distinct unfolding distinct_conv_nth using closed_start_list_n by simp
    ultimately
    show ?thesis by force
  qed

  have n_starts_after: "\<forall>i < n. closed_end_list ! i < closed_start_list ! n"
  proof -
    {fix i
      assume i: "i < n"
      hence sisn: "closed_start_list ! i < closed_start_list ! n" using n_ord by simp
      with end_start_paired(1) closed_end_list_len n_def i
      obtain ti di where
        tidi: "(a, ti, di) \<in> ran \<pi> " 
        "closed_start_list ! i = ti" 
        "closed_end_list ! i = ti + di" by auto
    
      assume "closed_end_list ! i \<ge> closed_start_list ! n"
      with nso[THEN no_self_overlap_ran, OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
      have "False" by fastforce
    }
    thus ?thesis by fastforce
  qed

  { assume "tn + dn \<le> t"
    from closed_end_list_planI[OF tndn(1) this] closed_end_list_n
    obtain i where "i < n" "closed_end_list ! i = tn + dn" by blast
    moreover
    have "tn \<le> tn + dn" using plan_durations tndn by simp
    ultimately
    have False using n_starts_after tndn by auto
  }
  thus ?thesis using tndn closed_start_list_nth_ran[of n] closed_start_list_n by force
qed

lemma closed_ended_le_closed_started: "card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq} \<le> card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq}"
proof -
  {
    assume a: "card {s. s \<le> t \<and> (s, at_start a) \<in> happ_seq} < card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"
    define n where "n = card {s'. s' \<le> t \<and> (s', at_start a) \<in> happ_seq}"
    have closed_start_list_n: "length closed_start_list = n" unfolding closed_start_list_len n_def closed_active_count_def by blast
    have closed_end_list_n: "length closed_end_list > n" using n_def closed_end_list_len a by argo
    
    have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<and> closed_end_list ! i = t + d)" 
         "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<longrightarrow> closed_end_list ! i = t + d)" 
         "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! i = t + d \<longrightarrow> closed_start_list ! i = t)" 
      using closed_start_list_n closed_end_list_n closed_start_closed_end_paired by auto

    have n_ord: "\<forall>i < n. closed_end_list ! i < closed_end_list ! n"
    proof -
      have "\<forall>i < n. closed_end_list ! i \<le> closed_end_list ! n" using closed_end_list_sorted sorted_nth_mono closed_end_list_n by fastforce
      moreover
      have "\<forall>i < n. closed_end_list ! i \<noteq> closed_end_list ! n" using closed_end_list_distinct unfolding distinct_conv_nth using closed_end_list_n by simp
      ultimately
      show ?thesis by force
    qed

    from closed_end_list_nth_planE[of n] closed_end_list_n
    obtain tn dn where
      tndn: "(a, tn, dn) \<in> ran \<pi>" 
      "closed_end_list ! n = tn + dn" by blast
    {
      have 1: "tn + dn \<le> t" using closed_end_list_nth_ran tndn closed_end_list_n by force
      moreover 
      have 2: "0 \<le> dn" using plan_durations tndn by simp
      moreover
      have 3: "tn \<le> t" using 1 2
        by (meson dual_order.trans le_add_same_cancel1)
      ultimately
      have "tn + dn \<le> t" "0 \<le> dn" "tn \<le> t" by auto
    } note tndn_ord = this
    
    from closed_start_list_planI[OF tndn(1)] tndn_ord
    obtain i where
      i: "i<length closed_start_list" "closed_start_list ! i = tn" by blast
    with end_start_paired(2) tndn(1) closed_start_list_n
    have "closed_end_list ! i = tn + dn" by blast
    with tndn(2) n_ord i(1) closed_start_list_n
    have False by auto
  }
  thus ?thesis by fastforce
qed

lemma closed_active_count_0E:
  assumes "closed_active_count = 0"
  shows "\<not>(\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d')"
proof 
  assume "\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d'"
  then obtain t' d' where
    td: "(a, t', d') \<in> ran \<pi>"
    "t'\<le> t"
    "t < t' + d'" by auto

  define n where "n = card {s'. s' \<le> t \<and> (s', at_end a) \<in> happ_seq}"
  have closed_end_list_n: "length closed_end_list = n" using n_def closed_end_list_len by simp
  have closed_start_list_n: "length closed_start_list = n" using assms unfolding closed_start_list_len n_def closed_active_count_def le_imp_diff_is_add[OF closed_ended_le_closed_started] by simp

  have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<and> closed_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<longrightarrow> closed_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! i = t + d \<longrightarrow> closed_start_list ! i = t)" 
    using closed_start_list_n closed_end_list_n closed_start_closed_end_paired by auto

  from closed_start_list_planI td closed_start_list_n
  obtain i where
    i: "i < length closed_start_list" "closed_start_list ! i = t'" by blast

  with closed_start_list_n td(1) end_start_paired(2)
  have "closed_end_list ! i = t' + d'" by blast
  hence "t' + d' \<le> t" using closed_end_list_nth_ran i(1) unfolding closed_start_list_n closed_end_list_n by fastforce

  with td(3)
  show False by simp
qed
  

lemma open_active_count_1_iff:
  "open_active_count = 1 \<longleftrightarrow> (\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d')"
  using open_active_count_1E open_active_count_ran open_active_count_0E by blast

lemma open_active_count_0_iff:
  "open_active_count = 0 \<longleftrightarrow> \<not>(\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d')"
  using open_active_count_1E open_active_count_ran open_active_count_0E by blast

lemma open_active_count_1_if_ending:
  assumes "is_ending_action t a"
    shows "open_active_count = 1" 
  apply (subst open_active_count_1_iff)
  apply (insert assms)
  unfolding is_ending_action_def
  apply (erule conjE)
  apply (frule at_end_in_happ_seqE''[OF a_in_acts])
  apply -
  apply (drule ex1_implies_ex)
  apply (elim exE)
  subgoal for x
    apply (induction x)
    subgoal for t' d
      apply (subst (asm) prod.case)+
      apply (cases "t' < t")
       apply blast
      apply (erule conjE)
      apply (frule at_start_in_happ_seqI)
      using assms plan_durations by fastforce
    done
  done

lemma open_active_count_0_if_start_scheduled:
  assumes "(t, at_start a) \<in> happ_seq"
    shows "open_active_count = 0"
proof -
  have "open_active_count \<noteq> 1"
  proof
    assume "open_active_count = 1"
    then obtain t' d' where
      "(a, t', d') \<in> ran \<pi>" "t' < t" "t \<le> t' + d'" 
      using open_active_count_1_iff by auto
    moreover
    obtain d'' where
      "(a, t, d'') \<in> ran \<pi>" using assms(1) at_start_in_happ_seqE'' a_in_acts by blast 
    ultimately
    show False using nso[THEN no_self_overlap_ran] by fastforce
  qed
  thus ?thesis using open_active_count_ran by simp
qed


lemma closed_active_count_1_iff:
  "closed_active_count = 1 \<longleftrightarrow> (\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d')"
  using closed_active_count_1E closed_active_count_ran closed_active_count_0E by blast

lemma closed_active_count_0_iff:
  "closed_active_count = 0 \<longleftrightarrow> \<not>(\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d')"
  using closed_active_count_1E closed_active_count_ran closed_active_count_0E by blast

lemma closed_active_count_0_if_end_scheduled:
  assumes "(t, at_end a) \<in> happ_seq"
    shows "closed_active_count = 0" 
proof -
  have "closed_active_count \<noteq> 1"
  proof
    assume "closed_active_count = 1"
    with closed_active_count_1_iff
    obtain ta da where
      tada: "(a, ta, da) \<in> ran \<pi>" 
        "ta \<le> t" 
        "t < ta + da" by blast
    moreover
    obtain te de where
      tede: "(a, te, de) \<in> ran \<pi>" 
        "te + de = t" using assms(1) at_end_in_happ_seqE'' a_in_acts by blast
    have "te \<le> te + de" using plan_durations tede by auto
    hence  "te \<le> t" using at_start_in_happ_seqI[OF tede(1)] tede(2) assms apply (cases "te = te + de") by auto
    ultimately
    have "te + de < ta \<or> ta + da < te"  using nso_double_act_spec[OF nso valid_plan_durs(1)[OF vp] tada(1) tede(1)] tada(3) tede(2) by auto
    then consider "te + de < ta" | "ta + da < te" by auto
    thus False using \<open>t < ta + da\<close> \<open>te + de = t\<close> \<open>ta \<le> t\<close> \<open>te \<le> t\<close> apply cases by auto
  qed
  thus ?thesis using closed_active_count_ran by simp
qed

lemma closed_active_count_1_if_starting:
  assumes "(t, at_start a) \<in> happ_seq"
      and "(t, at_end a) \<notin> happ_seq"
    shows "closed_active_count = 1"
proof -
  from assms(1)
  obtain d where
    d: "(a, t, d) \<in> ran \<pi>" using at_start_in_happ_seqE'' a_in_acts by blast
  hence "0 \<le> d" using plan_durations by simp
  moreover
  have "(t + d, at_end a) \<in> happ_seq" using at_end_in_happ_seqI d by simp
  ultimately
  have "t < t + d" using assms(2) apply (cases "d = 0") by auto
  with d
  show ?thesis using closed_active_count_1_iff by blast
qed


lemma open_active_count_eq_closed_active_count_if_only_instant_acts:
  assumes "(t, at_start a) \<in> happ_seq \<longleftrightarrow> (t, at_end a) \<in> happ_seq"
    shows "open_active_count = closed_active_count"
proof -
  consider "(t, at_start a) \<in> happ_seq \<and> (t, at_end a) \<in> happ_seq" | "(t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<notin> happ_seq"  using assms by auto
  thus ?thesis
  proof cases
    case 1
    then show ?thesis using open_active_count_0_if_start_scheduled closed_active_count_0_if_end_scheduled by simp
  next
    case 2
    have "open_active_count = 1" if "closed_active_count = 1"
    proof -
      from that closed_active_count_1_iff
      obtain tc dc where
        tcdc: "(a, tc, dc) \<in> ran \<pi>" "tc \<le> t" "t < tc + dc" by blast
      from at_start_in_happ_seqI tcdc 2
      have "tc < t" by fastforce
      thus ?thesis using open_active_count_1_iff tcdc by fastforce
    qed
    moreover
    have "open_active_count = 0" if "closed_active_count = 0"
    proof -
      { assume "open_active_count = 1"
        with open_active_count_1_iff
        obtain t1 d1 where
          t1d1: "(a, t1, d1) \<in> ran \<pi>" "t1 < t" "t \<le> t1 + d1" by auto
        from at_end_in_happ_seqI[OF t1d1(1)] t1d1(3) 2
        have "t < t1 + d1" apply (cases "t = t1 + d1") by auto
        hence "closed_active_count = 1" using closed_active_count_1_iff t1d1 by auto
      }
      thus ?thesis using that open_active_count_ran by auto
    qed
    ultimately
    show ?thesis using open_active_count_ran closed_active_count_ran by auto
  qed
qed

lemma only_instant_acts_if_open_active_count_eq_closed_active_count: 
  assumes "open_active_count = closed_active_count"
  shows "(t, at_start a) \<in> happ_seq \<longleftrightarrow> (t, at_end a) \<in> happ_seq"
proof -
  { assume "open_active_count = 0" "closed_active_count = 0"
    with open_active_count_0_iff closed_active_count_0_iff
    have start_cond: "(\<nexists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d')" 
     and end_cond: "(\<nexists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d')" by auto
    { assume "(t, at_start a) \<in> happ_seq"
      with at_start_in_happ_seqE'' a_in_acts
      obtain ds where
        ds: "(a, t, ds) \<in> ran \<pi>" by blast
      moreover
      have "0 \<le> ds" using plan_durations ds by auto
      ultimately
      have "t = t + ds" using end_cond by fastforce
      with ds
      have "(t, at_end a) \<in> happ_seq" using at_end_in_happ_seqI by fastforce
    }
    moreover
    { assume "(t, at_end a) \<in> happ_seq"
      with at_end_in_happ_seqE'' a_in_acts
      obtain te de where
        tede: "(a, te, de) \<in> ran \<pi>" "t = te + de" by blast
      moreover
      have "0 \<le> de" using plan_durations tede by auto
      ultimately
      have "te = t" using start_cond by fastforce
      with tede
      have "(t, at_start a) \<in> happ_seq" using at_start_in_happ_seqI by fastforce
    }
    ultimately
    have "(t, at_start a) \<in> happ_seq \<longleftrightarrow> (t, at_end a) \<in> happ_seq" by auto
  }
  moreover
  { assume "open_active_count = 1" "closed_active_count = 1"
    with open_active_count_1_iff closed_active_count_1_iff
    obtain t1 d1 t2 d2 where
        t1d1: "(a, t1, d1) \<in> ran \<pi>" "t1 < t" "t \<le> t1 + d1"
    and t2d2: "(a, t2, d2) \<in> ran \<pi>" "t2 \<le> t" "t < t2 + d2" by auto
    from no_self_overlap_ran[OF nso t1d1(1) t2d2(1)] no_self_overlap_ran[OF nso t2d2(1) t1d1(1)]
    have "t1 \<noteq> t2 \<or> d1 \<noteq> d2 \<Longrightarrow> (t2 < t1 \<or> t1 + d1 < t2) \<and> (t1 < t2 \<or> t2 + d2 < t1)" by blast
    with t1d1(2,3) t2d2(2,3)
    have "t1 \<noteq> t2 \<or> d1 \<noteq> d2 \<Longrightarrow> False" by auto 
    hence td: "(a, t1, d1) \<in> ran \<pi>" "t1 < t" "t < t1 + d1" using t1d1 t2d2 by auto
    { assume "(t, at_start a) \<in> happ_seq"
      with at_start_in_happ_seqE'' a_in_acts 
      obtain d where
        "(a, t, d) \<in> ran \<pi>" by blast
      from no_self_overlap_spec[OF nso td(1) this] td(2,3)
      have "False" by fastforce
    }
    moreover
    { assume "(t, at_end a) \<in> happ_seq"
      with at_end_in_happ_seqE'' a_in_acts 
      obtain te de where
        tede: "(a, te, de) \<in> ran \<pi>" "te + de = t" by blast
      hence "0 \<le> de" using plan_durations by auto 
      note tede = tede this
      from no_self_overlap_ran[OF nso tede(1) td(1)] no_self_overlap_ran[OF nso td(1) tede(1)]
      have "te \<noteq> t1 \<or> de \<noteq> d1 \<Longrightarrow> (t1 < te \<or> te + de < t1) \<and> (te < t1 \<or> t1 + d1 < te)" by auto
      with tede td
      have False using add_strict_increasing2 by fastforce
    }
    ultimately
    have "(t, at_start a) \<in> happ_seq \<longleftrightarrow> (t, at_end a) \<in> happ_seq" by blast
  }
  ultimately
  show ?thesis using open_active_count_ran closed_active_count_ran assms by auto
qed

lemma open_active_count_eq_closed_active_count_iff_only_instant_acts:
  "open_active_count = closed_active_count \<longleftrightarrow> ((t, at_start a) \<in> happ_seq \<longleftrightarrow> (t, at_end a) \<in> happ_seq)"
  using open_active_count_eq_closed_active_count_if_only_instant_acts 
    only_instant_acts_if_open_active_count_eq_closed_active_count by blast

  text \<open>closed_open_active_count\<close>
lemma closed_open_active_count_ran:
  "closed_open_active_count \<in> {0, 1}"
proof -
  have "\<not>1 < closed_open_active_count"
  proof (rule notI)
    assume "1 < closed_open_active_count"
    hence "open_active_count = 1 \<and> is_starting_action t a" unfolding closed_open_active_count_def
      by (rule contrapos_pp) (use open_active_count_ran in auto)
    thus False using open_active_count_0_if_start_scheduled is_starting_action_def by auto
  qed
  thus ?thesis by auto
qed

lemma closed_open_active_count_cases:
  assumes "closed_open_active_count = 0 \<Longrightarrow> thesis"
          "closed_open_active_count = 1 \<Longrightarrow> thesis"
        shows thesis using closed_open_active_count_ran assms by blast

lemma closed_open_active_count_1_if_starting:
  assumes "is_starting_action t a"
  shows "closed_open_active_count = 1"
  using assms closed_open_active_count_ran 
  unfolding closed_open_active_count_def by auto

lemma closed_open_active_count_conv_open_active_count:
  "closed_open_active_count = 1 \<Longrightarrow> is_starting_action t a \<and> open_active_count = 0 \<or> (\<not>is_starting_action t a \<and> open_active_count = 1)"
  "closed_open_active_count = 0 \<Longrightarrow> \<not>is_starting_action t a \<and> open_active_count = 0"
  unfolding closed_open_active_count_def by (auto elim: open_active_count_cases, presburger+)
    
end
end

subsubsection \<open>Sets of actions and snap actions happening\<close>


definition instant_actions_at where
"instant_actions_at t \<equiv> {a \<in> actions. is_instant_action t a}"

definition ending_actions_at where
"ending_actions_at t \<equiv> {a \<in> actions. is_ending_action t a}"

definition starting_actions_at where
"starting_actions_at t \<equiv> {a \<in> actions. is_starting_action t a}"
(* technically a \<in> actions not necessary *)

definition "instant_snaps_at t = at_start ` instant_actions_at t \<union> at_end ` instant_actions_at t"

definition "starting_snaps_at t = at_start ` starting_actions_at t"

definition "ending_snaps_at t =  at_end ` ending_actions_at t"


subsubsection \<open>Counting how many actions have locked a proposition\<close>

definition locked_by where
"locked_by p \<equiv> filter (\<lambda>a. p \<in> over_all a) action_list"

definition "locked_before t p \<equiv> sum_list (map (open_active_count t) (locked_by p))"

definition "locked_during t p \<equiv> sum_list (map (open_closed_active_count t) (locked_by p))"

definition "locked_after t p \<equiv> sum_list (map (closed_active_count t) (locked_by p))"


subsubsection \<open>Alternative Definition\<close>

lemma locked_by_alt: "{a \<in> actions. p \<in> over_all a} = set (locked_by p)"
  unfolding locked_by_def set_filter set_action_list by blast

text \<open>Relating the ideas of an action being active at, during and after a timepoint.\<close>

lemma ending_timepoint_count_le_open_active_count:
  "(\<Sum>a\<leftarrow>xs. if is_ending_action t a then 1 else 0) \<le> sum_list (map (open_active_count t) xs)" 
  if "set xs \<subseteq> actions"
    using that 
    apply (induction xs)
     apply simp
    subgoal for x xs
      apply (subst sum_list.eq_foldr)+
      apply (subst list.map)+
      apply (subst foldr.simps)+
      apply (subst comp_apply)+
      apply (subst sum_list.eq_foldr[symmetric])+
      apply (cases "(t, at_start x) \<notin> happ_seq \<and> (t, at_end x) \<in> happ_seq")
      using open_active_count_1_if_ending apply simp
      using open_active_count_ran is_ending_action_def by auto
    done

lemma locked_during_and_before: "locked_during t p = locked_before t p - sum_list (map (\<lambda>a. (if is_ending_action t a then 1 else 0)) (locked_by p))"
proof -
  have 2: "sum_list (map (open_closed_active_count t) xs) = sum_list (map (open_active_count t) xs) - (\<Sum>a\<leftarrow>xs. if is_ending_action t a then 1 else 0)" if "set xs \<subseteq> actions" for xs
    using that
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    then show ?case apply (subst sum_list.eq_foldr)+
      apply (subst list.map)+
      apply (subst foldr.simps)+
      apply (subst comp_apply)+
      apply (subst sum_list.eq_foldr[symmetric])+
      apply (subst open_closed_active_count_def)
      apply (cases "is_ending_action t x")
      subgoal 
        apply simp
        apply (subst add_diff_assoc2)
        using open_active_count_1_if_ending 
        unfolding is_ending_action_def 
         apply simp
        apply (subst add_diff_assoc)
        using ending_timepoint_count_le_open_active_count 
        unfolding is_ending_action_def by auto
      subgoal unfolding is_ending_action_def
        apply (subst if_not_P)
         apply assumption
        apply (subst if_not_P)
         apply assumption
        apply simp
        apply (subst add_diff_assoc[symmetric]) 
        using ending_timepoint_count_le_open_active_count unfolding is_ending_action_def by auto
      done
  qed
  have "set (locked_by p) \<subseteq> actions" using locked_by_alt by auto
  thus ?thesis unfolding locked_during_def locked_before_def using 2 by simp
qed

lemma locked_before_and_during: "locked_before t p = locked_during t p + sum_list (map (\<lambda>a. (if is_ending_action t a then 1 else 0)) (locked_by p))"
proof -
  have 2: "sum_list (map (open_active_count t) xs) = sum_list (map (open_closed_active_count t) xs) + (\<Sum>a\<leftarrow>xs. if is_ending_action t a then 1 else 0)" if "set xs \<subseteq> actions" for xs
    using that
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    then show ?case apply (subst sum_list.eq_foldr)+
      apply (subst list.map)+
      apply (subst foldr.simps)+
      apply (subst comp_apply)+
      apply (subst sum_list.eq_foldr[symmetric])+
      apply (subst open_closed_active_count_def)
      apply (cases "(t, at_start x) \<notin> happ_seq \<and> (t, at_end x) \<in> happ_seq")
      unfolding is_ending_action_def
      subgoal
        apply simp
        using open_active_count_1_if_ending is_ending_action_def
        by simp
      subgoal
        apply (subst if_not_P)
         apply assumption
        apply (subst if_not_P)
         apply assumption
        by simp
      done
  qed
  have "set (locked_by p) \<subseteq> actions" using locked_by_alt by auto
  thus ?thesis unfolding locked_during_def locked_before_def using 2 by simp
qed

lemma locked_after_and_during: "locked_after t p = locked_during t p + sum_list (map (\<lambda>a. (if is_starting_action t a then 1 else 0)) (locked_by p))"
proof -
  have "sum_list (map (closed_active_count t) xs) =
        sum_list (map (open_active_count t) xs) - (\<Sum>a\<leftarrow>xs. if is_ending_action t a then 1 else 0) + (\<Sum>a\<leftarrow>xs. if is_starting_action t a then 1 else 0)" if "set xs \<subseteq> actions" for xs 
    using that
    apply (induction xs)
     apply simp
    subgoal for x xs 
      apply (subst sum_list.eq_foldr)+
      apply (subst list.map)+
      apply (subst foldr.simps)+
      apply (subst comp_apply)+
      apply (subst sum_list.eq_foldr[symmetric])+
      apply (cases "(t, at_start x) \<in> happ_seq"; cases "(t, at_end x) \<in> happ_seq")
         apply simp
      subgoal using open_active_count_0_if_start_scheduled closed_active_count_0_if_end_scheduled action_happening_case_defs by simp
      subgoal unfolding action_happening_case_defs
        apply (subst if_not_P, simp)
        apply (subst (2) if_P, simp)
        apply (subst closed_active_count_1_if_starting, simp, simp, simp)
        apply (subst open_active_count_0_if_start_scheduled; simp)
        done
      subgoal unfolding action_happening_case_defs
        apply (subst if_P, simp)
        apply (subst (2) if_not_P, simp)
        apply (subst closed_active_count_0_if_end_scheduled, simp, simp, simp)
        apply (subst open_active_count_1_if_ending; simp add: is_ending_action_def)
        done
      subgoal unfolding action_happening_case_defs
        apply (subst if_not_P, simp)
        apply (subst (2) if_not_P, simp)
        apply (subst open_active_count_eq_closed_active_count_if_only_instant_acts, simp, simp, simp)
        apply (subst add_diff_assoc)
        using ending_timepoint_count_le_open_active_count 
        unfolding is_ending_action_def by simp+
      done
    done
  moreover
  have "set (locked_by p) \<subseteq> actions" using locked_by_alt by auto
  ultimately
  show ?thesis unfolding locked_during_and_before locked_after_def locked_before_def by simp
qed

text \<open>Range\<close>


lemma locked_before_ran: "locked_before t p \<le> card actions"
proof -
  have "\<forall>x \<in> set (map (open_active_count t) (locked_by p)). x \<le> 1"
    unfolding locked_by_def
    unfolding set_map set_filter set_action_list 
    apply (rule ballI)
    subgoal for x
      apply (erule imageE)
      apply (erule CollectE)
      subgoal for a
        apply (erule conjE)
        apply (drule open_active_count_ran[ where t = t])
        by auto
      done
    done
  from sum_list_max[OF this]
  show ?thesis unfolding locked_before_def 
    apply -
    apply (subst (asm) length_map)
    apply (subst (asm) (2) locked_by_def)
    apply (insert length_filter_le[where xs = action_list, simplified length_action_list])
    using order_trans by auto
qed

lemma locked_during_ran: "locked_during t p \<le> card actions"
proof -
  have "\<forall>x \<in> set (map (open_closed_active_count t) (locked_by p)). x \<le> 1"
    unfolding locked_by_def
    unfolding set_map set_filter set_action_list 
    apply (rule ballI)
    subgoal for x
      apply (erule imageE)
      apply (erule CollectE)
      subgoal for a
        apply (erule conjE)
        apply (drule open_closed_active_count_ran[ where t = t])
        by auto
      done
    done
  from sum_list_max[OF this]
  show ?thesis unfolding locked_during_def 
    apply -
    apply (subst (asm) length_map)
    apply (subst (asm) (2) locked_by_def)
    apply (insert length_filter_le[where xs = action_list, simplified length_action_list])
    using order_trans by auto
qed

lemma locked_after_ran: "locked_after t p \<le> card actions"
proof -
  have "\<forall>x \<in> set (map (closed_active_count t) (locked_by p)). x \<le> 1"
    unfolding locked_by_def
    unfolding set_map set_filter set_action_list 
    apply (rule ballI)
    subgoal for x
      apply (erule imageE)
      apply (erule CollectE)
      subgoal for a
        apply (erule conjE)
        apply (drule closed_active_count_ran[ where t = t])
        by auto
      done
    done
  from sum_list_max[OF this]
  show ?thesis unfolding locked_after_def 
    apply -
    apply (subst (asm) length_map)
    apply (subst (asm) (2) locked_by_def)
    apply (insert length_filter_le[where xs = action_list, simplified length_action_list])
    using order_trans by auto
qed

lemma open_active_count_initial_is_0: "open_active_count (time_index \<pi> 0) a = 0"
proof -
  find_theorems name: "no*init*ti"
  have "{s. s < time_index \<pi> 0 \<and> (s, at_start a) \<in> happ_seq} = {}" (is "?S = {}")
  proof -
    { fix x
      assume "x \<in> ?S"
      hence False 
        apply -
        apply (elim CollectE conjE)
        unfolding happ_seq_def
        apply (drule happ_seq_conv_htps)
        apply (drule time_indexI_htps[rotated])
        using vp valid_plan_finite apply blast
        using time_index_sorted_set[of 0]
        by fastforce
    }
    thus ?thesis by blast
  qed
  moreover
  have "{s'. s' < time_index \<pi> 0 \<and> (s', at_end a) \<in> happ_seq} = {}" (is "?S = {}")
  proof -
    { fix x
      assume "x \<in> ?S"
      hence False 
        apply -
        apply (elim CollectE conjE)
        unfolding happ_seq_def
        apply (drule happ_seq_conv_htps)
        apply (drule time_indexI_htps[rotated])
        using vp valid_plan_finite apply blast
        using time_index_sorted_set[of 0]
        by fastforce
    }
    thus ?thesis by blast
  qed
  ultimately
  show ?thesis unfolding open_active_count_def by presburger
qed

find_theorems name: "closed_active_count"

find_theorems "time_index"

lemma closed_active_count_final_is_0: 
  assumes "a \<in> actions"
  shows "closed_active_count (time_index \<pi> (length (htpl \<pi>) - 1)) a = 0"
proof (cases "length (htpl \<pi>)")
  case 0
  hence "ran \<pi> = {}"
    using empty_acts_if_empty_htpl_finite vp valid_plan_finite by blast
  then show ?thesis 
    unfolding closed_active_count_def happ_seq_def plan_happ_seq_def by simp
next
  case (Suc nat)
  show ?thesis 
    apply (subst closed_active_count_0_iff)
     apply (rule assms)
    apply (rule notI)
    apply (elim exE conjE)
    subgoal for t d
      using no_actions_after_final_timepoint[OF vp[THEN valid_plan_finite]]
      using Suc  apply simp
      using in_happ_seqI by fast
    done
qed

lemma closed_active_count_is_open_active_count_if_nothing_happens:
  assumes "s < t"
    and "\<not>(\<exists>s' h. s < s' \<and> s' < t \<and> (s', h) \<in> happ_seq)" 
  shows "closed_active_count s a = open_active_count t a"
proof -
  have "{sa. sa \<le> s \<and> (sa, at_start a) \<in> happ_seq} = {s. s < t \<and> (s, at_start a) \<in> happ_seq}"
    apply (intro equalityI subsetI)
    subgoal using assms(1) by auto
    subgoal for x
      apply (cases "x \<le> s")
      using assms(2) by auto
    done
  moreover
  have "{s'. s' \<le> s \<and> (s', at_end a) \<in> happ_seq} = {s'. s' < t \<and> (s', at_end a) \<in> happ_seq}"
    apply (intro equalityI subsetI)
    subgoal using assms(1) by auto
    subgoal for x
      apply (cases "x \<le> s")
      using assms(2) by auto
    done
  ultimately
  show ?thesis unfolding open_active_count_def closed_active_count_def by simp
qed

lemma closed_active_count_on_indexed_timepoint_is_open_active_count_Suc:
  assumes "Suc i < length (htpl \<pi>)"
  shows "closed_active_count (time_index \<pi> i) a = open_active_count (time_index \<pi> (Suc i)) a"
  apply (rule closed_active_count_is_open_active_count_if_nothing_happens)
   apply (rule time_index_strict_sorted_list, (simp add: assms)+)
  using no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite] assms]
  unfolding happ_seq_def by fast

lemma locked_after_is_locked_before_if_nothing_happens:
  assumes "s < t"
    and "\<not>(\<exists>s' h. s < s' \<and> s' < t \<and> (s', h) \<in> happ_seq)" 
  shows "locked_after s p = locked_before t p"
  unfolding locked_after_def locked_before_def
  using closed_active_count_is_open_active_count_if_nothing_happens assms by simp

lemma locked_after_indexed_timepoint_is_locked_before_Suc:
  assumes "Suc i < length (htpl \<pi>)"
  shows "locked_after (time_index \<pi> i) p = locked_before (time_index \<pi> (Suc i)) p"
  apply (rule locked_after_is_locked_before_if_nothing_happens)
   apply (rule time_index_strict_sorted_list, (simp add: assms)+)
  using no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite] assms]
  unfolding happ_seq_def by fast

lemma locked_before_initial_is_0:
  shows "locked_before (time_index \<pi> 0) p = 0"
  unfolding locked_before_def using open_active_count_initial_is_0 by simp

lemma locked_after_final_is_0:
  "locked_after (time_index \<pi> (length (htpl \<pi>) - 1)) p = 0"
  unfolding locked_after_def using closed_active_count_final_is_0 locked_by_def set_action_list by auto

subsubsection \<open>Counting the number of active actions in total\<close>

definition "active_before t \<equiv> sum_list (map (open_active_count t) action_list)"

definition "active_after t \<equiv> sum_list (map (closed_active_count t) action_list)"

definition "active_during t \<equiv> sum_list (map (closed_open_active_count t) action_list)"

definition "active_during_minus_ended t \<equiv> sum_list (map (active_count'' t) action_list)"

lemma active_before_less_if_scheduled:
  assumes "(t, at_start a) \<in> happ_seq"
      and "a \<in> actions"
  shows "active_before t < card actions"
proof -
  have "open_active_count t a = 0" using assms open_active_count_0_if_start_scheduled by blast
  moreover
  have "open_active_count t a \<in> set (map (open_active_count t) action_list)" using set_action_list assms by simp
  moreover
  have "\<forall>x \<in> set (map (open_active_count t) action_list). x \<in> {0, 1}" using open_active_count_ran set_action_list by auto
  ultimately
  show ?thesis
    unfolding active_before_def
    using sum_list_binary_less_than_length_if[where xs = "map (open_active_count t) action_list"] length_action_list[symmetric]
    by simp
qed

find_theorems name:"closed_open_active"

subsubsection \<open>Relating the notions of active actions\<close>

lemma active_after_is_before_if_nothing_happens:
  assumes "s < t"
    and "\<not>(\<exists>s' h. s < s' \<and> s' < t \<and> (s', h) \<in> happ_seq)" 
  shows "active_after s = active_before t"
  unfolding active_after_def active_before_def 
  using closed_active_count_is_open_active_count_if_nothing_happens assms by auto

lemma active_after_indexed_timepoint_is_active_before_Suc: 
  assumes "Suc i < length (htpl \<pi>)"
  shows "active_after (time_index \<pi> i) = active_before (time_index \<pi> (Suc i))"
  apply (rule active_after_is_before_if_nothing_happens)
   apply (rule time_index_strict_sorted_list, (simp add: assms)+)
  using no_actions_between_indexed_timepoints[OF vp[THEN valid_plan_finite] assms]
  unfolding happ_seq_def by fast

lemma active_before_initial_is_0: "active_before (time_index \<pi> 0) = 0"
  unfolding active_before_def using open_active_count_initial_is_0 by auto

lemma active_after_final_is_0:  "active_after (time_index \<pi> (length (htpl \<pi>) - 1)) = 0"
  unfolding active_after_def  using closed_active_count_final_is_0 set_action_list by simp

lemma active_during_conv_active_before: 
  "active_during t = active_before t + card (starting_actions_at t)"
proof -
  have "sum_list (map (closed_open_active_count t) action_list) = 
        sum_list (map (open_active_count t) action_list) + card (starting_actions_at t)"
  proof -
    have "sum_list (map (closed_open_active_count t) action_list) = 
        sum_list (map (\<lambda>a. open_active_count t a + (if is_starting_action t a then 1 else 0)) action_list)"
    proof -
      have "map (closed_open_active_count t) action_list =
            map (\<lambda>a. open_active_count t a + (if is_starting_action t a then 1 else 0)) action_list" (is "map ?f ?xs = map ?g ?xs")
        apply (subst map_eq_conv[of ?f ?xs ?g])
        apply (subst set_action_list)
        apply (intro ballI impI)
        subgoal for x
          apply (rule closed_open_active_count_cases, assumption)
          by (frule closed_open_active_count_conv_open_active_count[rotated]; force)+
        done
      thus ?thesis by argo
    qed
    also
    have "... = sum_list (map (open_active_count t) action_list) + card (starting_actions_at t)"
    proof -
      have "set (filter (is_starting_action t) action_list) = starting_actions_at t"
        unfolding starting_actions_at_def using set_action_list by auto
      hence "(\<Sum>a\<leftarrow>action_list. if is_starting_action t a then 1 else 0)  = card (starting_actions_at t)"
        unfolding starting_actions_at_def
        apply (subst foldr_map_filter)
        apply (subst distinct_sum_list_1_conv_card_set)
        using distinct_action_list by auto
      thus ?thesis by (simp add: sum_list_addf)
    qed
    finally 
    show ?thesis .
  qed
  thus ?thesis using active_during_def active_before_def by simp
qed

lemma active_during_ran:
  "active_during t \<le> card actions"
proof -
  have 1: "sum_list (map (closed_open_active_count t) action_list) \<le> length (map (closed_open_active_count t) action_list) * 1"
    using set_action_list closed_open_active_count_ran[where t = t] by (fastforce intro: sum_list_max)
    
  show ?thesis
    unfolding active_during_def
    apply (subst (2) set_action_list[symmetric])
    apply (subst distinct_card[OF distinct_action_list])
    using 1 by simp
qed

subsubsection \<open>Relating the invariant sequence to the number of locks\<close>


definition invs_after::"('proposition, 'time) invariant_sequence" where
"invs_after \<equiv> {(tp, over_all a) | a t d tp. (a, t, d) \<in> ran \<pi> \<and> (t \<le> tp \<and> tp < t + d)}"

definition "plan_invs_after \<equiv> invs_at invs_after"

text \<open>Invariants active during a timepoint are a special case again, because of the
definition of @{term locked_during}.\<close>
definition invs_during::"('proposition, 'time) invariant_sequence" where
"invs_during \<equiv> {(tp, over_all a) | a t d tp. (a, t, d) \<in> ran \<pi> \<and> (t < tp \<and> tp < t + d)}"

definition "plan_invs_during \<equiv> invs_at invs_during"

lemma in_invs_before_iff_locked_before: "p \<in> plan_invs_before t \<longleftrightarrow> 0 < locked_before t p"
proof (rule iffI)
  assume "p \<in> plan_invs_before t"
  then obtain a ta da where 
    tada: "(a, ta, da) \<in> ran \<pi>" 
    "p \<in> over_all a" 
    "ta < t" 
    "t \<le> ta + da" 
    unfolding plan_invs_before_def inv_seq_def invs_at_def plan_inv_seq_def by blast
  from tada(1) pap plan_actions_in_problem_def
  have a_in_acts: "a \<in> actions" by fast
  with tada
  have a_locks: "a \<in> set (locked_by p)" using locked_by_alt by blast
  have a_count: "open_active_count t a = 1" using open_active_count_1_iff tada a_in_acts by auto

  from a_count a_locks
  have e: "\<exists>x. x \<in> set (map (open_active_count t) (locked_by p)) \<and> 0 < x" by fastforce
  show "0 < locked_before t p" 
  proof -
    { assume "locked_before t p = 0"
      hence "\<forall>x \<in> set (map (open_active_count t) (locked_by p)). x = 0" 
        unfolding locked_before_def sum_list_eq_0_iff by blast
      with e
      have False by auto
    }
    thus ?thesis by blast
  qed
next
  assume a: "0 < locked_before t p" 
  have "\<exists>x. x \<in> set (map (open_active_count t) (locked_by p)) \<and> 0 < x"
  proof -
    { assume "\<forall>x \<in> set (map (open_active_count t) (locked_by p)). 0 = x"
      hence "0 = locked_before t p" unfolding locked_before_def sum_list_eq_0_iff by simp
      with a 
      have False by simp
    }
    thus ?thesis by fastforce
  qed
  then obtain a where
    a_in_actions[simp]: 
      "a \<in> actions"
    and a: 
      "p \<in> over_all a" 
      "0 < open_active_count t a"
    using locked_by_alt by auto
  hence "open_active_count t a = 1" using open_active_count_ran by force
  with open_active_count_1_iff
  obtain ta da where
    tada: "(a, ta, da) \<in> ran \<pi>" "ta < t" "t \<le> ta + da" by auto  
  show "p \<in> plan_invs_before t" unfolding plan_invs_before_def invs_at_def inv_seq_def plan_inv_seq_def using tada a(1) by auto
qed

lemma in_invs_after_iff_locked_after: "p \<in> plan_invs_after t \<longleftrightarrow> 0 < locked_after t p"
proof (rule iffI)
  assume "p \<in> plan_invs_after t"
  then obtain a ta da where 
    tada: "(a, ta, da) \<in> ran \<pi>" 
    "p \<in> over_all a" 
    "ta \<le> t" 
    "t < ta + da" 
    unfolding plan_invs_after_def  invs_at_def invs_after_def by blast
  from tada(1) pap plan_actions_in_problem_def
  have a_in_acts: "a \<in> actions" by fast
  with tada
  have a_locks: "a \<in> set (locked_by p)" using locked_by_alt by blast
  have a_count: "closed_active_count t a = 1" using closed_active_count_1_iff tada a_in_acts by auto

  from a_count a_locks
  have e: "\<exists>x. x \<in> set (map (closed_active_count t) (locked_by p)) \<and> 0 < x" by fastforce
  show "0 < locked_after t p" 
  proof -
    { assume "locked_after t p = 0"
      hence "\<forall>x \<in> set (map (closed_active_count t) (locked_by p)). x = 0" 
        unfolding locked_after_def sum_list_eq_0_iff by blast
      with e
      have False by auto
    }
    thus ?thesis by blast
  qed
next
  assume a: "0 < locked_after t p" 
  have "\<exists>x. x \<in> set (map (closed_active_count t) (locked_by p)) \<and> 0 < x"
  proof -
    { assume "\<forall>x \<in> set (map (closed_active_count t) (locked_by p)). 0 = x"
      hence "0 = locked_after t p" unfolding locked_after_def sum_list_eq_0_iff by simp
      with a 
      have False by simp
    }
    thus ?thesis by fastforce
  qed
  then obtain a where
    a_in_actions[simp]: 
      "a \<in> actions"
    and a: 
      "p \<in> over_all a" 
      "0 < closed_active_count t a"
    using locked_by_alt by auto
  hence "closed_active_count t a = 1" using closed_active_count_ran by force
  with closed_active_count_1_iff
  obtain ta da where
    tada: "(a, ta, da) \<in> ran \<pi>" "ta \<le> t" "t < ta + da" by auto  
  show "p \<in> plan_invs_after t" unfolding plan_invs_after_def invs_at_def invs_after_def using tada a(1) by auto
qed

lemma in_invs_during_iff_locked_during: "p \<in> plan_invs_during t \<longleftrightarrow> 0 < locked_during t p"
proof (rule iffI)
  assume "p \<in> plan_invs_during t"
  then obtain a ta da where 
    tada: "(a, ta, da) \<in> ran \<pi>" 
    "p \<in> over_all a" 
    "ta < t" 
    "t < ta + da"
    unfolding plan_invs_during_def  invs_at_def invs_during_def by blast
  from tada(1) pap plan_actions_in_problem_def
  have a_in_acts: "a \<in> actions" by fast
  with tada
  have a_locks: "a \<in> set (locked_by p)" using locked_by_alt by blast
  have a_closed_active: "closed_active_count t a = 1" using closed_active_count_1_iff tada a_in_acts by fastforce
  have a_open_active: "open_active_count t a = 1" using open_active_count_1_iff tada a_in_acts by fastforce

  have "(t, at_start a) \<in> happ_seq \<longleftrightarrow> (t, at_end a) \<in> happ_seq" using a_closed_active a_open_active open_active_count_eq_closed_active_count_iff_only_instant_acts[OF a_in_acts, of t] by argo  
  moreover
  have not_starting: "(t, at_start a) \<notin> happ_seq" using open_active_count_0_if_start_scheduled a_in_acts a_open_active by auto
  ultimately
  have not_ending: "(t, at_end a) \<notin> happ_seq" by simp

  have a_in_open_closed: "open_closed_active_count t a = 1" unfolding open_closed_active_count_def using a_open_active not_starting not_ending is_ending_action_def by simp

  show "0 < locked_during t p"
  proof -
    { assume "0 = locked_during t p"
      hence "\<forall>x \<in> set (map (open_closed_active_count t) (locked_by p)). 0 = x" 
        unfolding locked_during_def sum_list_eq_0_iff by auto
      hence False using a_locks a_in_open_closed by simp
    }
    thus ?thesis by auto
  qed
next
  assume a: "0 < locked_during t p" 
  have "\<exists>x. x \<in> set (map (open_closed_active_count t) (locked_by p)) \<and> 0 < x"
  proof -
    { assume "\<forall>x \<in> set (map (open_closed_active_count t) (locked_by p)). 0 = x"
      hence "0 = locked_during t p" unfolding locked_during_def sum_list_eq_0_iff by simp
      with a 
      have False by simp
    }
    thus ?thesis by fastforce
  qed
  then obtain a where
    a_in_actions[simp]: 
      "a \<in> actions"
    and a: 
      "p \<in> over_all a" 
      "0 < open_closed_active_count t a"
    using locked_by_alt by auto
  hence ocac: "open_closed_active_count t a = 1" using open_closed_active_count_ran by force
  hence oac: "open_active_count t a = 1" using open_closed_active_count_def open_active_count_ran by force

  from ocac oac
  consider "(t, at_start a) \<in> happ_seq" | "(t, at_end a) \<notin> happ_seq" unfolding open_closed_active_count_def is_ending_action_def by fastforce
  then consider "(t, at_start a) \<in> happ_seq" "(t, at_end a) \<notin> happ_seq" | "(t, at_start a) \<in> happ_seq" "(t, at_end a) \<in> happ_seq"| "(t, at_start a) \<notin> happ_seq" "(t, at_end a) \<notin> happ_seq" by argo
  hence not_starting_or_ending: "(t, at_start a) \<notin> happ_seq \<and> (t, at_end a) \<notin> happ_seq"
    apply cases 
    subgoal using open_active_count_0_if_start_scheduled oac by auto
    subgoal using open_active_count_eq_closed_active_count_iff_only_instant_acts oac closed_active_count_0_if_end_scheduled by force
    subgoal by simp
    done

  from open_active_count_1E[OF _ oac]
  obtain t' d' where
    t'd': "(a, t', d') \<in> ran \<pi>" "t' < t" "t \<le> t' + d'" by auto
  with not_starting_or_ending[THEN conjunct2]
  have t_le_t'd': "t < t' + d'" using at_end_in_happ_seqI apply (cases "t = t' + d'") by auto
  show "p \<in> plan_invs_during t" unfolding plan_invs_during_def invs_during_def invs_at_def using a(1) t'd' t_le_t'd' by auto
qed

subsubsection \<open>Connecting the different invariant states\<close>

lemma invs_after_invariant_if:
  assumes "s < u"
      and "\<not>(\<exists>t h. s < t \<and> t < u \<and> (t, h) \<in> happ_seq)"
    shows "plan_invs_after s = plan_invs_before u"
  apply (intro equalityI subsetI)
  subgoal for p
    unfolding plan_invs_after_def plan_invs_before_def invs_after_def inv_seq_def plan_inv_seq_def invs_at_def
    apply (elim UnionE CollectE exE conjE)
    subgoal for P P' a t d s'
      apply (rule UnionI)
       apply (rule CollectI)
       apply (rule exI)
       apply (rule conjI)
        apply assumption
       apply (rule CollectI)
       apply (rule exI[of _ a])
       apply (rule exI[of _ t])
       apply (rule exI[of _ d])
      apply (rule exI[of _ u])
       apply (intro conjI)
          apply blast
         apply blast
      using assms apply simp
      apply (cases "u \<le> t + d")  apply assumption
      using at_end_in_happ_seqI assms by force
    done
  subgoal for p
    unfolding plan_invs_after_def plan_invs_before_def invs_after_def inv_seq_def plan_inv_seq_def invs_at_def
    apply (elim UnionE CollectE exE conjE)
    subgoal for P P' a t d u'
      apply (rule UnionI)
       apply (rule CollectI)
       apply (rule exI)
       apply (rule conjI)
        apply assumption
       apply (rule CollectI)
       apply (rule exI[of _ a])
       apply (rule exI[of _ t])
       apply (rule exI[of _ d])
       apply (rule exI[of _ s])
       apply (intro conjI)
          apply blast
         apply blast
        apply (cases "t \<le> s")  apply blast
      using at_start_in_happ_seqI using assms apply fastforce
      using assms apply simp
      by blast
    done
  done

lemma invs_between_indexed_timepoints_invariant:
  assumes "Suc l < length (htpl \<pi>)"
  shows "plan_invs_after (time_index \<pi> l) = plan_invs_before (time_index \<pi> (Suc l))"
  apply (rule invs_after_invariant_if)
  using time_index_strict_sorted_list assms apply fastforce
  using no_actions_between_indexed_timepoints[OF valid_plan_finite[OF vp] assms] 
  unfolding happ_seq_def by fast

lemma invs_during_hold_after:
  "plan_invs_during t \<subseteq> plan_invs_after t"
  unfolding plan_invs_during_def plan_invs_after_def invs_at_def invs_during_def invs_after_def
  by fastforce

lemma plan_invs_afterE:
  assumes "p \<in> plan_invs_after t"
      and "\<And>P a ta d . p \<in> over_all a \<Longrightarrow> (a, ta, d) \<in> ran \<pi> \<Longrightarrow> ta \<le> t \<Longrightarrow> t < ta + d \<Longrightarrow> thesis"
    shows thesis
  using assms unfolding plan_invs_after_def invs_at_def invs_after_def
  apply -
  apply (elim conjE CollectE UnionE exE)
  by simp

lemma plan_invs_afterI:
  assumes "\<exists>P a ta d. p \<in> over_all a \<and> (a, ta, d) \<in> ran \<pi> \<and> ta \<le> t \<and> t < ta + d"
  shows "p \<in> plan_invs_after t"
  using assms unfolding plan_invs_after_def invs_at_def invs_after_def by auto

lemma plan_invs_after_iff:
  "p \<in> plan_invs_after t \<longleftrightarrow> (\<exists>P a ta d. p \<in> over_all a \<and> (a, ta, d) \<in> ran \<pi> \<and> ta \<le> t \<and> t < ta + d)"
  apply (rule iffI)
   apply (erule plan_invs_afterE) 
   apply auto[1]
  using plan_invs_afterI by auto

lemma no_invs_after_end:
  assumes "0 < length (htpl \<pi>)"
  shows "plan_invs_after (time_index \<pi> (length (htpl \<pi>) - 1)) = {}"
  apply (rule ccontr)
  apply (subst (asm) ex_in_conv[symmetric])
  apply (erule exE)
  apply (erule plan_invs_afterE)
  apply (drule at_end_in_happ_seqI)
  using no_actions_after_final_timepoint[OF valid_plan_finite[OF vp] assms]
  unfolding happ_seq_def by fast

lemma snap_does_not_delete_inv:
  assumes "(t, h) \<in> happ_seq"
  shows "((dels h - adds h) \<inter> plan_invs_during t) = {}"
proof-
  from assms
  have "t \<in> htps \<pi>" using a_in_B_iff_t_in_htps happ_seq_def by fast
  then obtain l where
    l: "l < length (htpl \<pi>)"
    "time_index \<pi> l = t" using time_index_img_set[OF valid_plan_finite[OF vp]] unfolding card_htps_len_htpl by force
  then consider "Suc l = length (htpl \<pi>)" | "Suc l < length (htpl \<pi>)" by linarith
  thus ?thesis
  proof cases
    case 1
    hence "l = length (htpl \<pi>) - 1" using l by auto
    hence "plan_invs_after (time_index \<pi> l) = {}" using no_invs_after_end 1 by fastforce
    then show ?thesis using invs_during_hold_after l by blast
  next
    case 2
    with invs_between_indexed_timepoints_invariant
    have "plan_invs_after (time_index \<pi> l) = plan_invs_before (time_index \<pi> (Suc l))" by simp
    moreover
    have "plan_invs_before (time_index \<pi> (Suc l)) \<subseteq> plan_state_seq (Suc l)" 
      using plan_state_seq_props 2 unfolding Let_def plan_invs_before_def inv_seq_def by simp
    moreover
    have "plan_state_seq (Suc l) = apply_effects adds dels (plan_state_seq l) (happ_at (plan_happ_seq \<pi> at_start at_end) (time_index \<pi> l))" 
      using plan_state_seq_props l(1) unfolding Let_def by simp
    ultimately
    have "plan_invs_after (time_index \<pi> l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` happ_at happ_seq (time_index \<pi> l))" 
      unfolding apply_effects_def happ_seq_def by simp
    hence 1: "plan_invs_during (time_index \<pi> l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` happ_at happ_seq (time_index \<pi> l))" using invs_during_hold_after l by auto

    have h_happens: "h \<in> happ_at happ_seq (time_index \<pi> l)" using assms l by simp
    hence "plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` happ_at happ_seq (time_index \<pi> l)) 
            = plan_state_seq l - (\<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> dels h) \<union> \<Union> (adds ` happ_at happ_seq (time_index \<pi> l)) \<union> adds h" by auto
    hence "plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` happ_at happ_seq (time_index \<pi> l)) 
            = plan_state_seq l - (\<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> dels h) \<union> \<Union> (adds ` (happ_at happ_seq (time_index \<pi> l) - {h})) \<union> adds h" by auto
    moreover
    have "dels h \<inter> \<Union> (adds ` (happ_at happ_seq (time_index \<pi> l) - {h})) = {}"
    proof -
      {
        fix s
        assume "s \<in> (happ_at happ_seq (time_index \<pi> l) - {h})" 
        hence "\<not> mutex_snap_action pre adds dels s h" using nm unfolding mutex_valid_happ_seq_def nm_happ_seq_def using h_happens by blast
        hence "dels h \<inter> adds s = {}" unfolding mutex_snap_action_def by auto
      }
      thus ?thesis by auto
    qed
    ultimately
    have "plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` happ_at happ_seq (time_index \<pi> l)) 
            = plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` (happ_at happ_seq (time_index \<pi> l) - {h})) - dels h \<union> adds h" by auto
    from 1[simplified this]
    have "plan_invs_during (time_index \<pi> l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` (happ_at happ_seq (time_index \<pi> l) - {h})) - dels h \<union> adds h" .
    hence "plan_invs_during (time_index \<pi> l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` (happ_at happ_seq (time_index \<pi> l) - {h})) - (dels h - adds h) \<union> adds h" by blast
    hence "plan_invs_during (time_index \<pi> l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at happ_seq (time_index \<pi> l)) \<union> \<Union> (adds ` (happ_at happ_seq (time_index \<pi> l) - {h})) \<union> adds h - (dels h - adds h)" by blast
    thus ?thesis using l by auto
  qed
qed

subsection \<open>Execution times\<close>

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


lemma instant_act_in_happ_seqE:
  assumes a_in_actions: "a \<in> actions"
      and ending: "(t, at_end a) \<in> happ_seq"
      and starting: "(t, at_start a) \<in> happ_seq"
    shows "(a, t, 0) \<in> ran \<pi>"
proof -
  from at_start_in_happ_seqE''  assms
  have "\<exists>!ds. (a, t, ds) \<in> ran \<pi>" by blast
  then obtain ds where
    tds: "(a, t, ds) \<in> ran \<pi>"
    "\<forall>d. (a, t, d) \<in> ran \<pi> \<longrightarrow> d = ds" by blast

  have ds_ran: "0 \<le> ds" using plan_durations tds by blast

  from at_end_in_happ_seqE'' assms
  have "\<exists>!(te, de). (a, te, de) \<in> ran \<pi> \<and> t = te + de" by simp
  then obtain te de where
    tede: "(a, te, de) \<in> ran \<pi>"
    "t = te + de"
    "\<forall>t' d'. (a, t', d') \<in> ran \<pi> \<and> t = t' + d' \<longrightarrow> (t' = te \<and> d' = de)" by blast

  have de_ran: "0 \<le> de" using plan_durations tede by blast

  have "t = te \<and> de = 0" by (metis add_cancel_right_right nso nso_start_end prod.inject tds(1) tede(1,2) valid_plan_durs(1) vp)
  thus ?thesis using tede by blast
qed

lemma ending_act_sat_dur_bounds:
  assumes a_in_actions: "a \<in> actions"
      and ending: "is_ending_action t a"
    shows "satisfies_duration_bounds lower upper a (exec_time (at_start a) t)"
  using exec_time_when_ending valid_plan_durs(2)[OF vp] assms 
  unfolding is_ending_action_def durations_valid_def by blast

lemma instant_act_sat_dur_bounds:
  assumes a_in_actions: "a \<in> actions"
      and is_instant: "is_instant_action t a"
    shows "satisfies_duration_bounds lower upper a 0"
  using valid_plan_durs(2)[OF vp] instant_act_in_happ_seqE assms
  unfolding durations_valid_def is_instant_action_def by blast

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

subsection \<open>Propositional states, updates, and commutativity\<close>

lemma prop_state_upd_combine_if:                        
  assumes "\<And>a b. a \<in> h \<Longrightarrow> b \<in> h \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> mutex_snap a b"
      and "h1 \<union> h2 = h"
  shows "(app_effs h2 o app_effs h1) M  = app_effs h M"
proof -
  from assms
  have ab_not_int: "\<And>a b. a \<in> h \<Longrightarrow> b \<in> h \<Longrightarrow> a \<noteq> b \<Longrightarrow> adds a \<inter> dels b = {}" unfolding mutex_snap_def mutex_snap_action_def by simp
  have not_int: "\<Union> (adds ` h1) \<inter> (\<Union> (dels ` h2) - \<Union> (adds ` h2)) = {}"
  proof -
    { fix p 
      assume a1: "p \<in> \<Union> (adds ` h1)" 
      assume a2: "p \<in> \<Union> (dels ` h2)" "p \<notin> \<Union> (adds ` h2)"

      from a1 obtain a1 where
        a1: "a1 \<in> h1"
        "p \<in> adds a1" by blast
      hence a1h: "a1 \<in> h" using assms by blast
      moreover
      from a2 obtain a2 where
        a2: "a2 \<in> h2"
        "p \<in> dels a2"
        "p \<notin> adds a2" by blast
      hence a2h: "a2 \<in> h" using assms by blast
      moreover
      have "a1 \<noteq> a2" using a1 a2 by blast
      ultimately
      have "adds a1 \<inter> dels a2 = {}" using ab_not_int by simp
      with a1 a2
      have False by blast
    }
    thus ?thesis by blast
  qed

  have "app_effs h2 (app_effs h1 M) = M - \<Union> (dels ` h1) \<union> \<Union> (adds ` h1) - \<Union> (dels ` h2) \<union> \<Union> (adds ` h2)" unfolding app_effs_def apply_effects_def by blast
  also have "... = M - \<Union> (dels ` h1) \<union> \<Union> (adds ` h1) - (\<Union> (dels ` h2) - \<Union> (adds ` h2)) \<union> \<Union> (adds ` h2)" by blast
  also have "... = M - \<Union> (dels ` h1) - (\<Union> (dels ` h2) - \<Union> (adds ` h2)) \<union> \<Union> (adds ` h1) \<union> \<Union> (adds ` h2)" using not_int by blast
  also have "... = M - (\<Union> (dels ` h1) \<union> \<Union> (dels ` h2)) \<union> \<Union> (adds ` h1) \<union> \<Union> (adds ` h2)" by blast
  also have "... = M - \<Union> (dels ` h) \<union> \<Union> (adds ` h)" using assms(2) by blast
  finally show ?thesis unfolding app_effs_def apply_effects_def comp_def by simp
qed

lemma mutex_pre_app: 
  assumes "(t, a) \<in> happ_seq"
      and "(t, b) \<in> happ_seq"
      and "a \<noteq> b"
    shows "pre a \<inter> (dels b \<union> adds b) = {}"
  using nm assms unfolding mutex_valid_happ_seq_def nm_happ_seq_def
  unfolding mutex_snap_def mutex_snap_action_def by blast

lemma happ_combine:
  assumes "h1 \<union> h2 \<subseteq> happ_at happ_seq t"
  shows "(app_effs h2 o app_effs h1) M = app_effs (h1 \<union> h2) M"
  apply (rule prop_state_upd_combine_if)
  using nm assms unfolding mutex_valid_happ_seq_def nm_happ_seq_def
  unfolding mutex_snap_def
  by blast+



lemma acts_in_prob: "(a, t, d) \<in> ran \<pi> \<Longrightarrow> a \<in> actions" using pap unfolding plan_actions_in_problem_def by auto

subsection \<open>Restating happenings\<close>

lemma happ_at_is_union_of_starting_ending_instant:
  "happ_at happ_seq t = instant_snaps_at t \<union> ending_snaps_at t \<union> starting_snaps_at t"
  apply (intro equalityI subsetI)
  subgoal for x
    apply (drule in_happ_atD)
    unfolding happ_seq_def
    apply (drule in_happ_seqE')
    apply (elim exE)
    subgoal for a t d
      apply (elim conjE disjE)
      subgoal  
        apply (frule at_start_in_happ_seqI)
        apply (frule acts_in_prob)
        apply (cases "(t, at_end a) \<in> happ_seq")
        unfolding instant_snaps_at_def instant_actions_at_def is_instant_action_def starting_snaps_at_def is_starting_action_def starting_actions_at_def by auto
        apply (frule at_end_in_happ_seqI)
        apply (frule acts_in_prob)
      apply (cases "(t + d, at_start a) \<in> happ_seq")
      unfolding instant_snaps_at_def instant_actions_at_def is_instant_action_def ending_snaps_at_def is_ending_action_def ending_actions_at_def by auto
        done
      apply (elim UnE)
      unfolding instant_snaps_at_def instant_actions_at_def starting_snaps_at_def starting_actions_at_def ending_snaps_at_def ending_actions_at_def
      unfolding action_happening_case_defs by auto

lemma app_start_instant_dist: "(app_effs (starting_snaps_at t) o app_effs (instant_snaps_at t)) M = app_effs (instant_snaps_at t \<union> starting_snaps_at t) M"
  apply (rule prop_state_upd_combine_if[OF _ HOL.refl])
  subgoal for a b
    unfolding instant_snaps_at_def starting_snaps_at_def instant_actions_at_def starting_actions_at_def
    using nm unfolding mutex_valid_happ_seq_def nm_happ_seq_def
    unfolding mutex_snap_def
    unfolding action_happening_case_defs by auto
    done

lemma app_all_dist: "(app_effs (ending_snaps_at t) o app_effs (starting_snaps_at t) o app_effs (instant_snaps_at t)) M = app_effs (happ_at happ_seq t) M"
  apply (subst comp_assoc)
  apply (subst app_start_instant_dist[THEN ext])
  apply (rule prop_state_upd_combine_if)
  subgoal for a b
    using nm unfolding mutex_valid_happ_seq_def nm_happ_seq_def unfolding mutex_snap_def by blast
  subgoal unfolding instant_snaps_at_def starting_snaps_at_def ending_snaps_at_def 
    unfolding instant_actions_at_def starting_actions_at_def ending_actions_at_def
    unfolding action_happening_case_defs
    apply (rule equalityI)
     apply blast
    apply (rule subsetI)
    subgoal for b
      apply (drule in_happ_atD)
      apply (erule in_happ_seqE[of _ _ \<pi> at_start at_end, simplified happ_seq_def[symmetric]])
      subgoal for a t' d
        apply (erule subst)
        apply (erule ssubst)
       apply (frule at_start_in_happ_seqI)
        using pap[simplified plan_actions_in_problem_def]
        by fast
      subgoal for a t' d
        apply (erule subst)
        apply (erule ssubst)
       apply (frule at_end_in_happ_seqI)
        using pap[simplified plan_actions_in_problem_def]
        by fast
      done
    done
  done

lemma ending_actions_at_conv_ending_indexes: 
  "ending_actions_at t = set (filter (is_ending_action t) action_list)"
  unfolding ending_actions_at_def set_filter set_action_list ..

lemma sum_list_0: "\<forall>x \<in> set xs. f x = 0 \<Longrightarrow> (\<Sum>x\<leftarrow>xs. f x) = (0::nat)"
  by simp

lemma locked_before_and_during_if_none_ending:
  assumes "ending_actions_at t = {}"
  shows "locked_before t p = locked_during t p"
  unfolding locked_before_and_during
  apply (subst sum_list_0)
  using assms[simplified ending_actions_at_conv_ending_indexes]
  unfolding locked_by_def by auto

definition "inst_upd_state i \<equiv> app_effs (instant_snaps_at (time_index \<pi> i)) (plan_state_seq i)"

definition "inst_start_upd_state i \<equiv> ((app_effs (starting_snaps_at (time_index \<pi> i))) o (app_effs (instant_snaps_at (time_index \<pi> i)))) (plan_state_seq i)"

definition "upd_state i \<equiv> app_effs (happ_at happ_seq (time_index \<pi> i)) (plan_state_seq i)"

lemma state_seq_Suc_is_upd:
  assumes "i < length (htpl \<pi>)"
  shows "plan_state_seq (Suc i) = upd_state i"
  using plan_state_seq_valid valid_state_seqE assms
  unfolding upd_state_def happ_seq_def app_effs_def by blast

lemma no_instant_imp_state_is_inst_upd:
  assumes "instant_snaps_at (time_index \<pi> i) = {}"
  shows "plan_state_seq i = inst_upd_state i"
  unfolding inst_upd_state_def app_effs_def apply_effects_def
  using assms by blast

end                       
end
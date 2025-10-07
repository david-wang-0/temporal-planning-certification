theory Temporal_Plans_Theory
  imports Temporal_Plans_Instances ListMisc
begin

context temp_plan_for_actions_with_unique_snaps_nso_dg0
begin                                  
lemma at_start_of_act_in_happ_seq_exD: 
    assumes in_happ_seq: "(s, at_start a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> actions"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  proof (rule ex_ex1I)
    from in_happ_seq in_happ_seq_exD
    have "\<exists>(a', t, d) \<in> ran \<pi>. (at_start a' = at_start a \<and> s = t \<or> at_end a' = at_start a \<and> s = t + d)"
      by blast
    hence  "\<exists>(a', t, d) \<in> ran \<pi>. at_start a' = at_start a \<and> s = t" 
      using a_in_actions acts_in_prob
      using at_start_inj_on_acts snaps_disj_on_acts 
      unfolding inj_on_def snaps_disj_on_def by blast
    moreover
    have "\<forall>(a', t, d) \<in> ran \<pi>. at_start a = at_start a' \<longrightarrow> a = a'" 
      using a_in_actions acts_in_prob
      using at_start_inj_on_acts 
      unfolding inj_on_def by blast
    ultimately
    show "\<exists>x. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t" by auto
  next
    have "t = t' \<and> d = d'" 
         if "(a, t, d) \<in> ran \<pi> \<and> s = t" 
        and "(a, t', d') \<in> ran \<pi> \<and> s = t'" for t d t' d'
      using that nso dg0 nso_no_double_start by blast
    thus "\<And>x y. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t 
    \<Longrightarrow> case y of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> x = y" by blast
  qed

  lemma at_end_of_act_in_happ_seq_exD:
    assumes in_happ_seq: "(s, at_end a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> actions"
      shows "\<exists>!(t,d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"
  proof -
    define pair where "pair = (SOME (t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d)"
    from in_happ_seq[simplified plan_happ_seq_def]
    consider "(s, at_end a) \<in> {(t, at_start a)|a t d. (a, t, d) \<in> ran \<pi>}" 
        | "(s, at_end a) \<in>  {(t + d, at_end a) |a t d. (a, t, d) \<in> ran \<pi>}"
        by blast
      then
    have some_in_ran: "(a, pair) \<in> ran \<pi> 
      \<and> s = fst pair + snd pair"
    proof cases
      case 1
      hence "\<exists>a' d. (s, at_end a) = (s, at_start a') \<and> (a', s, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" 
        using a_in_actions unfolding plan_actions_def by auto
      thus ?thesis 
        using a_in_actions acts_in_prob
        using snaps_disj_on_acts unfolding snaps_disj_on_def  by blast
    next
      case 2
      hence  "\<exists>a' t d. (s, at_end a) = (t + d, at_end a') \<and> (a', t, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" 
        using a_in_actions unfolding plan_actions_def by blast
      then obtain a' t d where
        "(s, at_end a) = (t + d, at_end a')" "(a', t, d) \<in> ran \<pi>" "a' \<in> plan_actions" by blast
      hence "(a, t, d) \<in> ran \<pi> \<and> s = t + d"
        using a_in_actions at_end_inj_on_acts acts_in_prob unfolding inj_on_def by blast
      thus ?thesis using some_eq_ex[where P = "\<lambda>(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"] pair_def by auto
    qed
    moreover
    have "p = pair" if td_def: "p = (t, d)" and td_in_ran: "(a, t, d) \<in> ran \<pi>" and td_eq_s: "t + d = s" for t d p
    proof -
      obtain t' d' where
        t'd'_def: "pair = (t', d')" by fastforce
      with some_in_ran
      have t'd'_in_ran: "(a, t', d') \<in> ran \<pi>"
        and t'd'_eq_s: "s = t' + d'" by simp+
  
      from td_eq_s t'd'_eq_s
      have td_t'd': "t + d = t' + d'" by simp
      with nso_ends td_in_ran t'd'_in_ran
      have "t = t'" "d = d'" by blast+
      thus "p = pair" using t'd'_def td_def by simp
    qed
    ultimately
    show ?thesis apply - by (rule ex1I, auto)
  qed
end

context temp_plan_for_problem_impl
begin

abbreviation snaps::"'action \<Rightarrow> 'snap_action set" where
"snaps a \<equiv> {at_start a, at_end a}"

definition snap_actions::"'snap_action set" where
"snap_actions \<equiv> (at_start ` actions) \<union> (at_end ` actions)"

definition "plan_invs_before t \<equiv> invs_at plan_inv_seq t"

definition "plan_state_seq \<equiv> SOME MS. valid_state_sequence MS \<and> MS 0 = init \<and> goal \<subseteq> MS (length htpl)"

definition "action_list \<equiv> SOME xs. set xs = actions \<and> distinct xs"


lemma set_action_list: "set action_list = actions"
  unfolding action_list_def using finite_actions[THEN finite_distinct_list, THEN someI_ex] by blast

lemma distinct_action_list: "distinct action_list"
  unfolding action_list_def using finite_actions[THEN finite_distinct_list, THEN someI_ex] by blast


lemma length_action_list: "length action_list = card actions" 
  using set_action_list distinct_action_list distinct_card by metis

lemma plan_state_seq_valid: "valid_state_sequence plan_state_seq \<and> plan_state_seq 0 = init \<and> goal \<subseteq> plan_state_seq (length htpl)"
    apply (insert valid_plan_state_seq)
  unfolding valid_state_sequence_def[symmetric]
  unfolding plan_state_seq_def
  using someI2_ex
    apply (erule someI2_ex[where Q = "\<lambda>M. valid_state_sequence M \<and> M 0 = init \<and> goal \<subseteq> M (length htpl)"])
  by blast
  
lemmas plan_state_seq_props = plan_state_seq_valid[simplified valid_state_sequence_def valid_state_sequence_def Let_def]

lemma plan_state_seq_happ_pres:
  assumes "i < length htpl"
  shows "\<Union> (pre ` happ_at plan_happ_seq (time_index i)) \<subseteq> plan_state_seq i"
  using assms plan_state_seq_props 
  unfolding Let_def by blast

lemma at_start_in_happ_seqI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "(t, at_start a) \<in> plan_happ_seq"
  using assms unfolding plan_happ_seq_def by blast

lemma at_end_in_happ_seqI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "(t + d, at_end a) \<in> plan_happ_seq"
  using assms unfolding plan_happ_seq_def by blast
  
lemma a_in_plan_is_in_actions:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "a \<in> actions" using assms acts_in_prob  by auto


subsubsection \<open>Execution state\<close>

text \<open>Binary, but could be changed to count the active instances.\<close>

text \<open>Superseded by active count\<close>

definition exec_state_sequence::"('time \<times> 'action) set" where
"exec_state_sequence \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s < t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)}"

lemma in_exec_state_sequenceI:
  assumes "x = (t, a)"
    "a \<in> actions"
    "(s, at_start a) \<in> plan_happ_seq"
    "s < t"
    "\<nexists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t"
  shows "x \<in> exec_state_sequence"
  unfolding exec_state_sequence_def
  using assms by blast

definition exec_state_sequence'::"('time \<times> 'action) set" where
"exec_state_sequence' \<equiv> {(t, a) |s t a. a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s \<le> t 
                  \<and> \<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> t)}"

abbreviation "ES t \<equiv> {a. (t, a) \<in> exec_state_sequence}"

abbreviation "IES t \<equiv> {a. (t, a) \<in> exec_state_sequence'}"

lemma in_ESI:
  assumes "a \<in> actions"
    "(s, at_start a) \<in> plan_happ_seq"
    "s < t"
    "\<nexists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t"
  shows "a \<in> ES t"
  using assms by (auto intro: in_exec_state_sequenceI)


lemma inc_es_is_next_es:
  assumes "Suc l < length htpl"
  shows "IES (time_index l) = ES (time_index (Suc l))"
proof (rule equalityI; rule subsetI)
  fix a
  assume "a \<in> IES (time_index l)"
  then obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s \<le> time_index l"
    "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> time_index l)"
    unfolding exec_state_sequence'_def by blast
  from this(2) 
  have "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < time_index (Suc l))"
    using time_index_strict_sorted_list[rotated, OF assms] no_actions_between_indexed_timepoints[OF assms]
    unfolding plan_happ_seq_def by fastforce
  with time_index_strict_sorted_list[OF lessI \<open>Suc l < length htpl\<close>] s(1)
  show "a \<in> ES (time_index (Suc l))" 
    by - (rule in_ESI, auto)
    
    
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
  have "s \<le> time_index l" unfolding plan_happ_seq_def by fastforce
  moreover
  have "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> time_index l)" 
  proof (rule notI)
    assume "\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> time_index l"
    with time_index_strict_sorted_list assms
    have "\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < time_index (Suc l)" by fastforce
    with s(4)
    show "False" by blast
  qed
  ultimately
  show "a \<in> IES (time_index l)" using s(1,2) exec_state_sequence'_def by blast
qed

lemma last_ies_empty:
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
      using at_start_of_act_in_happ_seq_exD unfolding plan_happ_seq_def by fast
    then
    have "\<exists>d. (a, s, d) \<in> ran \<pi>"
    proof cases
      case 1
      hence "\<exists>a' t d. (s, at_start a) = (t, at_start a') \<and> (a', t, d) \<in> ran \<pi>" by blast
      thus ?thesis using at_start_inj_on_acts[simplified inj_on_def] \<open>a \<in> actions\<close> 
          acts_in_prob by blast
    next
      case 2
      hence "\<exists>a' t d. (s, at_start a) = (t + d, at_end a') \<and> (a', t, d) \<in> ran \<pi>" by auto
      with s(1) 
      have False using pap snaps_disj_on_acts unfolding snaps_disj_on_def plan_actions_in_problem_def plan_actions_def by fast
      thus ?thesis ..
    qed
    then obtain d where
      d: "(a, s, d) \<in> ran \<pi>"
      "(s + d, at_end a) \<in> plan_happ_seq" using plan_happ_seq_def by fast
    with s(4) valid_plan_durs
    have "s + d \<ge> ?te" unfolding durations_ge_0_def by fastforce
    
    have "t \<le> ?te" if "t \<in> set htpl" for t
    proof -
      from that[simplified time_index_bij_betw_list[simplified bij_betw_def, THEN conjunct2, symmetric]]
      obtain n where
        n: "n < length htpl" "t = time_index n" by blast
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
    from d(1) htps_set_htpl
    have "s + d \<in> set htpl" unfolding htps_def by blast
    ultimately
    show False unfolding exec_state_sequence'_def 
      using \<open>time_index (length htpl - 1) \<le> s + d\<close> a d 
      using dual_order.trans s(3,4) by blast
  qed
  thus "IES ?te = {}" by blast
qed

lemma first_es_empty:
    shows "ES (time_index 0) = {}"
proof (rule ccontr)
  assume "ES (time_index 0) \<noteq> {}"
  then obtain a where
    a: "a \<in> ES (time_index 0)" by blast

  then obtain t where
    t: "t < time_index 0"
    "(t, at_start a) \<in> plan_happ_seq" unfolding exec_state_sequence_def by fast

  show False
  proof (cases "card htps")
    case 0
    with time_index_img_set vp
    have "htps = {}" unfolding valid_plan_def by fastforce
    with t(2) a_in_B_iff_t_in_htps
    show ?thesis by fast
  next
    case (Suc nat)
    hence "0 < card htps" by auto
    from t(2)
    have "t \<in> htps" using a_in_B_iff_t_in_htps by fast
    then obtain i where
      i: "t = time_index i" 
      "i < card htps" using time_index_img_set by blast
    have "0 \<le> i" by simp
    with i(2)
    have "time_index 0 \<le> time_index i" using time_index_sorted_set by blast
    with i(1) t
    show ?thesis by simp
  qed
qed

lemma not_executing_when_starting:
  assumes snap_in_B: "(t, at_start a) \<in> plan_happ_seq"
      and a_in_actions: "a \<in> actions"
  shows "a \<notin> ES t"
proof (rule notI)
  assume "a \<in> ES t"
  then obtain s where
    started: "a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s < t"
    and not_ended: "\<not>(\<exists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)"
    unfolding exec_state_sequence_def by blast
  
  then obtain d where
    as_in_plan: "(a, s, d) \<in> ran \<pi>"
    using at_start_of_act_in_happ_seq_exD by blast 
  hence "(s + d, at_end a) \<in> plan_happ_seq" using in_happ_seqI by blast
  hence t_sd: "t \<le> s + d" using valid_plan_durs(1) as_in_plan not_ended 
    unfolding durations_ge_0_def by fastforce
  
  obtain d' where
    at_in_plan: "(a, t, d') \<in> ran \<pi>" 
    using at_start_of_act_in_happ_seq_exD assms by blast

  from started as_in_plan t_sd at_in_plan
  show False using no_self_overlap_spec by fastforce
qed

lemma execution_state_unchanging:
  assumes not_starting: "(t, at_start a) \<notin> plan_happ_seq"
      and not_ending:   "(t, at_end a) \<notin> plan_happ_seq"
    shows "a \<in> ES t \<longleftrightarrow> a \<in> IES t"
proof (rule iffI)
  assume "a \<in> ES t"
  with exec_state_sequence_def
  obtain s where
    s: "a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s < t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)" by blast
  have "s \<le> t" using s by auto
  moreover
  have "(\<nexists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> t)" using s' not_ending by auto
  ultimately
  show "a \<in> IES t" using s unfolding exec_state_sequence'_def by blast
next
  assume "a \<in> IES t"
  with exec_state_sequence'_def
  obtain s where  
    s: "a \<in> actions \<and> (s, at_start a) \<in> plan_happ_seq \<and> s \<le> t" 
    and s': "(\<nexists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' \<le> t)" by blast
  have "s < t" using not_starting s
    using order_le_imp_less_or_eq by blast
  moreover 
  have "(\<nexists>s'. (s', at_end a) \<in> plan_happ_seq \<and> s \<le> s' \<and> s' < t)" using s' by auto
  ultimately
  show "a \<in> ES t" using s unfolding exec_state_sequence_def by blast
qed

subsubsection \<open>Invariant states\<close>

lemma finite_start_tps: "finite {s'. (s', at_start a) \<in> plan_happ_seq}"
proof -
  have "{(s', at_start a)| s'. (s', at_start a) \<in> plan_happ_seq} \<subseteq> plan_happ_seq" by blast
  hence "finite {(s', at_start a)| s'. (s', at_start a) \<in> plan_happ_seq}" using finite_subset finite_happ_seq by auto
  from finite_imageI[OF this, where h = fst]
  show "finite {s'. (s', at_start a) \<in> plan_happ_seq}" unfolding image_Collect by auto
qed

lemma finite_end_tps: "finite {s'. (s', at_end a) \<in> plan_happ_seq}"
proof -
  have "{(s', at_end a)| s'. (s', at_end a) \<in> plan_happ_seq} \<subseteq> plan_happ_seq" by blast
  hence "finite {(s', at_end a)| s'. (s', at_end a) \<in> plan_happ_seq}" using finite_subset finite_happ_seq by auto
  from finite_imageI[OF this, where h = fst]
  show "finite {s'. (s', at_end a) \<in> plan_happ_seq}" unfolding image_Collect by auto
qed

lemma plan_durations: "(a, t, d) \<in> ran \<pi> \<Longrightarrow> 0 \<le> d" using valid_plan_durs
  unfolding durations_ge_0_def by blast

text \<open>The cases for snap-actions that occur at a timepoint\<close>
definition "is_instant_action t a \<equiv> (t, at_start a) \<in> plan_happ_seq \<and> (t, at_end a) \<in> plan_happ_seq"
definition "is_starting_action t a \<equiv> (t, at_start a) \<in> plan_happ_seq \<and> (t, at_end a) \<notin> plan_happ_seq"
definition "is_ending_action t a \<equiv> (t, at_start a) \<notin> plan_happ_seq \<and> (t, at_end a) \<in> plan_happ_seq"
definition "is_not_happening_action t a \<equiv> (t, at_start a) \<notin> plan_happ_seq \<and> (t, at_end a) \<notin> plan_happ_seq"

lemma is_instant_actionI: "(t, at_start a) \<in> plan_happ_seq \<Longrightarrow> (t, at_end a) \<in> plan_happ_seq \<Longrightarrow> is_instant_action t a"
  using is_instant_action_def by simp

lemma is_instant_action_dests: 
  assumes "is_instant_action t a" 
  shows "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<in> plan_happ_seq"
  using is_instant_action_def assms by blast+

lemma is_instant_action_planE:
  assumes "is_instant_action t a"
      and a: "a \<in> actions"
    shows "(a, t, 0) \<in> ran \<pi>"
proof -
  from assms is_instant_action_def
  have "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<in> plan_happ_seq" by auto
   obtain ds where
    ds: "(a, t, ds) \<in> ran \<pi>" using a at_start_of_act_in_happ_seq_exD \<open>(t, at_start a) \<in> plan_happ_seq\<close> by blast
    

  from \<open>(t, at_end a) \<in> plan_happ_seq\<close> at_end_of_act_in_happ_seq_exD a
  obtain te de where
    tede: "(a, te, de) \<in> ran \<pi>" "t = te + de" by blast

  from nso_start_end[OF ds tede(1)] tede
  have "ds = 0" by auto
  thus ?thesis using ds by simp
qed

lemma is_starting_actionI: "(t, at_start a) \<in> plan_happ_seq \<Longrightarrow> (t, at_end a) \<notin> plan_happ_seq \<Longrightarrow> is_starting_action t a"
  using is_starting_action_def by simp

lemma is_starting_action_dests: 
  assumes "is_starting_action t a" 
  shows "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<notin> plan_happ_seq"
  using is_starting_action_def assms by blast+

lemma is_starting_action_plan_exD:
  assumes "is_starting_action t a"
      and a: "a \<in> actions"
    shows "\<exists>da. (a, t, da) \<in> ran \<pi> \<and> 0 < da"
proof -
  from assms is_starting_action_def
  have "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<notin> plan_happ_seq" by auto
  then obtain d where
    d: "(a, t, d) \<in> ran \<pi>" using a at_start_of_act_in_happ_seq_exD by blast
  moreover
  have "0 < d"
  proof -
    have "0 \<le> d" using d plan_durations by auto
    moreover
    { assume "0 = d"
      hence False using at_end_in_happ_seqI d \<open>(t, at_end a) \<notin>  plan_happ_seq\<close> by force
    }
    ultimately
    show ?thesis by force
  qed
  ultimately
  show ?thesis by blast
qed

lemma is_ending_actionI: "(t, at_start a) \<notin> plan_happ_seq \<Longrightarrow> (t, at_end a) \<in> plan_happ_seq \<Longrightarrow> is_ending_action t a"
  using is_ending_action_def by simp

lemma is_ending_action_dests: 
  assumes "is_ending_action t a" 
  shows "(t, at_start a) \<notin> plan_happ_seq" "(t, at_end a) \<in> plan_happ_seq"
  using is_ending_action_def assms by blast+

lemma is_ending_action_planE:
  assumes "is_ending_action t a"
      and a: "a \<in> actions"
    shows "\<exists>ta da. (a, ta, da) \<in> ran \<pi> \<and> ta < t \<and> t = ta + da"
proof -
  from assms is_ending_action_def
  have "(t, at_start a) \<notin> plan_happ_seq" "(t, at_end a) \<in> plan_happ_seq" by auto
  then obtain ta da where
    tada: "(a, ta, da) \<in> ran \<pi>" "t = ta + da" using a at_end_of_act_in_happ_seq_exD by blast
  moreover
  have "0 < da"
  proof -
    have "0 \<le> da" using tada plan_durations by auto
    moreover
    { assume "0 = da"
      hence False using at_start_in_happ_seqI tada \<open>(t, at_start a) \<notin> plan_happ_seq\<close> by force
    }
    ultimately
    show ?thesis by force
  qed
  ultimately
  show ?thesis by fastforce
qed

lemma is_not_happening_actionI: "(t, at_start a) \<notin> plan_happ_seq \<Longrightarrow> (t, at_end a) \<notin> plan_happ_seq \<Longrightarrow> is_not_happening_action t a"
  using is_not_happening_action_def by simp

lemma is_not_happening_action_dests: 
  assumes "is_not_happening_action t a" 
  shows "(t, at_start a) \<notin> plan_happ_seq" "(t, at_end a) \<notin> plan_happ_seq"
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
  assumes "t \<in> htps"
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

lemmas time_index_action_happening_cases = time_index_htpsD[OF, THEN htps_action_happening_cases]

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

lemma finite_open_started: "finite {s'. s' < t \<and> (s', at_start a) \<in> plan_happ_seq}" using finite_start_tps by auto
lemma finite_closed_started: "finite {s'. s' \<le> t \<and> (s', at_start a) \<in> plan_happ_seq}" using finite_start_tps by auto
lemma finite_open_ended: "finite {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}" using finite_end_tps by auto
lemma finite_closed_ended: "finite {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}" using finite_end_tps by auto
(* Maybe it is a bad idea to put these definitions into a block with the "a \<in> actions" assumption *)
subsection \<open>Counting the various sets of active actions\<close>
definition open_active_count where
"open_active_count \<equiv> card {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq} - card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"

definition closed_active_count where
"closed_active_count \<equiv> card {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq} - card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}"

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

definition open_start_list where "open_start_list \<equiv> sorted_list_of_set {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}"
definition closed_start_list where "closed_start_list \<equiv> sorted_list_of_set {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}"

definition open_end_list where "open_end_list \<equiv> sorted_list_of_set {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"
definition closed_end_list where "closed_end_list \<equiv> sorted_list_of_set {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}"
   
lemma open_start_list_len: "length (open_start_list) = card {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" unfolding open_start_list_def length_sorted_list_of_set by blast
lemma open_start_list_sorted: "sorted (open_start_list)" using sorted_sorted_list_of_set open_start_list_def by simp
lemma open_start_list_distinct: "distinct (open_start_list)" using distinct_sorted_list_of_set open_start_list_def by auto
lemma set_open_start_list: "set (open_start_list) = {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" using open_start_list_def set_sorted_list_of_set finite_open_started by auto
context 
  assumes a_in_acts: "a \<in> actions"
begin

lemma open_start_list_nth_happ_seqE: "((open_start_list) ! i, at_start a) \<in> plan_happ_seq" if "i < length (open_start_list)" for i 
proof -
  have "(open_start_list) ! i \<in> set (open_start_list)" using that by auto
  hence "(open_start_list) ! i \<in> {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" using set_sorted_list_of_set finite_open_started open_start_list_def by simp
  thus ?thesis by blast
qed

lemma open_start_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (open_start_list) ! i = t'" 
  if "i < length (open_start_list)" for i 
  using open_start_list_nth_happ_seqE that at_start_of_act_in_happ_seq_exD a_in_acts by simp

lemma open_start_list_nth_ran: "(open_start_list) ! i < t" if "i < length (open_start_list)" for i
proof -
  have "(open_start_list) ! i \<in> set (open_start_list)" using that by auto
  hence "(open_start_list) ! i \<in> {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" using set_sorted_list_of_set finite_open_started open_start_list_def by auto
  thus ?thesis by simp
qed

lemma open_start_list_planI: "\<exists>n < length (open_start_list). (open_start_list) ! n = t'" 
  if "(a, t', d') \<in> ran \<pi>" "t' < t" for t' d'
proof -
  have "t' \<in> {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" using that plan_happ_seq_def plan_happ_seq_def by fast
  hence "t' \<in> set (open_start_list)" using open_start_list_def finite_open_started set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed
   
lemma closed_start_list_len: "length (closed_start_list) = card {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" 
    unfolding closed_start_list_def length_sorted_list_of_set by blast
lemma closed_start_list_sorted: "sorted (closed_start_list)" 
    using sorted_sorted_list_of_set closed_start_list_def by simp
lemma closed_start_list_distinct: "distinct (closed_start_list)" 
    using distinct_sorted_list_of_set closed_start_list_def by auto
lemma set_closed_start_list: "set (closed_start_list) = {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" 
    using closed_start_list_def set_sorted_list_of_set finite_closed_started by auto

lemma closed_start_list_nth_happ_seqE: "((closed_start_list) ! i, at_start a) \<in> plan_happ_seq" if "i < length (closed_start_list)" for i 
proof -
  have "(closed_start_list) ! i \<in> set (closed_start_list)" using that by auto
  hence "(closed_start_list) ! i \<in> {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" using set_sorted_list_of_set finite_closed_started closed_start_list_def by simp
  thus ?thesis by blast
qed

lemma closed_start_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (closed_start_list) ! i = t'" if "i < length (closed_start_list)" for i 
  using closed_start_list_nth_happ_seqE  that at_start_of_act_in_happ_seq_exD a_in_acts by simp

lemma closed_start_list_nth_ran: "(closed_start_list) ! i \<le> t" if "i < length (closed_start_list)" for i
proof -
  have "(closed_start_list) ! i \<in> set (closed_start_list)" using that by auto
  hence "(closed_start_list) ! i \<in> {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" 
    using set_sorted_list_of_set finite_closed_started closed_start_list_def by auto
  thus ?thesis by simp
qed

lemma closed_start_list_planI: "\<exists>n < length (closed_start_list). (closed_start_list) ! n = t'" if "(a, t', d') \<in> ran \<pi>" "t' \<le> t" for t' d'
proof -
  have "t' \<in> {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" 
    using that plan_happ_seq_def plan_happ_seq_def by fast
  hence "t' \<in> set (closed_start_list)" 
    using closed_start_list_def finite_closed_started set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed

lemma open_end_list_len: "length (open_end_list) = card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}" 
  unfolding open_end_list_def length_sorted_list_of_set by blast
lemma open_end_list_sorted: "sorted (open_end_list)" 
  using sorted_sorted_list_of_set open_end_list_def by auto
lemma open_end_list_distinct: "distinct (open_end_list)" 
  using distinct_sorted_list_of_set open_end_list_def by auto
lemma set_open_end_list: "set (open_end_list) = {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}" 
  using open_end_list_def set_sorted_list_of_set finite_open_ended by auto

lemma open_end_list_nth_happ_seqE: "((open_end_list) ! i, at_end a) \<in> plan_happ_seq" if "i < length (open_end_list)" for i 
proof -
  have "(open_end_list) ! i \<in> set (open_end_list)" using that by auto
  hence "(open_end_list) ! i \<in> {s. s < t \<and> (s, at_end a) \<in> plan_happ_seq}" 
    using set_sorted_list_of_set finite_open_ended open_end_list_def by simp
  thus ?thesis by blast
qed

lemma open_end_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (open_end_list) ! i = t' + d" if "i < length (open_end_list)" for i 
  using open_end_list_nth_happ_seqE that at_end_of_act_in_happ_seq_exD a_in_acts by simp

lemma open_end_list_nth_ran: "(open_end_list) ! i < t" if "i < length (open_end_list)" for i
proof -
  from that
  have "(open_end_list) ! i \<in> set (open_end_list)" using that by auto
  hence "(open_end_list) ! i \<in> {s. s < t \<and> (s, at_end a) \<in> plan_happ_seq}" 
    using set_sorted_list_of_set finite_open_ended open_end_list_def by auto
  thus ?thesis by simp
qed

lemma open_end_list_planI: "\<exists>n < length (open_end_list). (open_end_list) ! n = t' + d'" if "(a, t', d') \<in> ran \<pi>" "t' + d' < t" for t' d'
proof -
  have "t' + d'\<in> {s. s < t \<and> (s, at_end a) \<in> plan_happ_seq}" 
    using that plan_happ_seq_def plan_happ_seq_def by fast
  hence "t' + d' \<in> set (open_end_list)" 
    using open_end_list_def finite_open_ended set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed

lemma closed_end_list_len: "length (closed_end_list) = card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}" 
  unfolding closed_end_list_def length_sorted_list_of_set by blast
lemma closed_end_list_sorted: "sorted (closed_end_list)" 
  using sorted_sorted_list_of_set closed_end_list_def by auto
lemma closed_end_list_distinct: "distinct (closed_end_list)" 
  using distinct_sorted_list_of_set closed_end_list_def by auto
lemma set_closed_end_list: "set (closed_end_list) = {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}" 
  using closed_end_list_def set_sorted_list_of_set finite_closed_ended by auto

lemma closed_end_list_nth_happ_seqE: "((closed_end_list) ! i, at_end a) \<in> plan_happ_seq"
  if "i < length (closed_end_list)" for i 
proof -
  have "(closed_end_list) ! i \<in> set (closed_end_list)" using that by auto
  hence "(closed_end_list) ! i \<in> {s. s \<le> t \<and> (s, at_end a) \<in> plan_happ_seq}" 
    using set_sorted_list_of_set finite_closed_ended closed_end_list_def by simp
  thus ?thesis by blast
qed

lemma closed_end_list_nth_planE: "\<exists>!(t', d). (a, t', d) \<in> ran \<pi> \<and> (closed_end_list) ! i = t' + d" 
  if "i < length (closed_end_list)" for i 
  using closed_end_list_nth_happ_seqE that at_end_of_act_in_happ_seq_exD a_in_acts by simp

lemma closed_end_list_nth_ran: "(closed_end_list) ! i \<le> t" if "i < length (closed_end_list)" for i
proof -
  from that
  have "(closed_end_list) ! i \<in> set (closed_end_list)" using that by auto
  hence "(closed_end_list) ! i \<in> {s. s \<le> t \<and> (s, at_end a) \<in> plan_happ_seq}" 
    using set_sorted_list_of_set finite_closed_ended closed_end_list_def by auto
  thus ?thesis by simp
qed

lemma closed_end_list_planI: "\<exists>n < length (closed_end_list). (closed_end_list) ! n = t' + d'" if "(a, t', d') \<in> ran \<pi>" "t' + d' \<le> t" for t' d'
proof -
  have "t' + d'\<in> {s. s \<le> t \<and> (s, at_end a) \<in> plan_happ_seq}" 
    using that plan_happ_seq_def plan_happ_seq_def by fast
  hence "t' + d' \<in> set (closed_end_list)" 
    using closed_end_list_def finite_closed_ended set_sorted_list_of_set by simp
  thus ?thesis using in_set_conv_nth by metis
qed

subsubsection \<open>Properties\<close>

lemma open_start_open_end_paired: "\<forall>n \<le> i. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<and> open_end_list ! n = t + d) 
          \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<longrightarrow> open_end_list ! n = t + d)
          \<and> (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! n = t + d \<longrightarrow> open_start_list ! n = t)" 
    if iel: "i < length open_end_list"
    and isl: "i < length open_start_list" for i
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

  from no_self_overlap_ran[OF tsds(2) tede(2)]
  have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
  moreover
  from no_self_overlap_ran[OF tede(2) tsds(2)]
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
      with no_self_overlap_ran[OF tsds(2) tede(2)] 4 
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

  from no_self_overlap_ran[OF tsds(2) tede(2)]
  have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
  moreover
  from no_self_overlap_ran[OF tede(2) tsds(2)]
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
      with 2 no_self_overlap_ran[OF tede(2) tsds(2)]
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
      with no_self_overlap_ran[OF tsds(2) tede(2)] 4
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
    hence 1: "2 \<le> card {s'. s' < t \<and> (s', at_start a) \<in> plan_happ_seq} - card {s. s < t \<and> (s, at_end a) \<in> plan_happ_seq}" 
      using finite_open_ended finite_open_started using open_active_count_def by auto

    define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"
    hence n1: "n + 2 \<le> card {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" using 1 by simp
    
    have open_start_list_len: "length open_start_list = card {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}" 
      unfolding open_start_list_def length_sorted_list_of_set by blast
    have n_open_start_list: "n + 2 \<le> length open_start_list" using n1 unfolding length_sorted_list_of_set 
      using open_start_list_def by simp

    have open_end_list_len: "length open_end_list = card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}" 
      unfolding open_end_list_def length_sorted_list_of_set by blast
    have n_open_end_list: "n = length open_end_list" using n_def 
      unfolding length_sorted_list_of_set[symmetric] using open_end_list_def by simp
    
    have open_start_list_open_end_list_len: "length open_end_list + 2 \<le> length open_start_list" 
      using n_open_end_list n_open_start_list by blast

    hence end_start_paired: 
      "\<forall>n < length open_end_list. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<and> open_end_list ! n = t + d)" 
      "\<forall>n < length open_end_list.(\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! n = t \<longrightarrow> open_end_list ! n = t + d)" 
      "\<forall>n < length open_end_list. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! n = t + d \<longrightarrow> open_start_list ! n = t)" 
      using open_start_open_end_paired by simp_all
    
    have n_ord: "\<forall>i < n. open_start_list ! i < open_start_list ! n"
    proof -
      have "\<forall>i < n. open_start_list ! i \<le> open_start_list ! n" 
        using open_start_list_sorted sorted_nth_mono n_open_start_list by fastforce
      moreover
      have "\<forall>i < n. open_start_list ! i \<noteq> open_start_list ! n" using open_start_list_distinct 
        unfolding distinct_conv_nth using n_open_start_list by simp
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
        with no_self_overlap_ran[OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
        have "False" by fastforce
      }
      thus ?thesis by fastforce
    qed

    have n_Suc_n: "open_start_list ! n < open_start_list ! Suc n" 
    proof -
      have "open_start_list ! n \<le> open_start_list ! Suc n" 
        using open_start_list_sorted sorted_nth_mono n_open_start_list by fastforce
      moreover
      have "open_start_list ! n \<noteq> open_start_list ! Suc n" using open_start_list_distinct 
        unfolding distinct_conv_nth using n_open_start_list by simp
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
      have "tn + dn \<in> set open_end_list" using set_open_end_list unfolding plan_happ_seq_def by fast
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
      thus ?thesis using no_self_overlap_spec[OF tndn(1) tsndsn(1)] sn_t n_Suc_n tndn(2) tsndsn(2) by fastforce
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

  from no_self_overlap_ran[OF tsds(2) tede(2)]
  have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
  moreover
  from no_self_overlap_ran[OF tede(2) tsds(2)]
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
      with no_self_overlap_ran[OF tsds(2) tede(2)] 4 
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

  from no_self_overlap_ran[OF tsds(2) tede(2)]
  have "ts = te \<and> ds = de \<or> te < ts \<or> ts + ds < te" by blast
  moreover
  from no_self_overlap_ran[OF tede(2) tsds(2)]
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
      with 2 no_self_overlap_ran[OF tede(2) tsds(2)]
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
      with no_self_overlap_ran[OF tsds(2) tede(2)] 4
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
    hence 1: "2 \<le> card {s'. s' \<le> t \<and> (s', at_start a) \<in> plan_happ_seq} - card {s. s \<le> t \<and> (s, at_end a) \<in> plan_happ_seq}" 
      using finite_closed_ended finite_closed_started using closed_active_count_def by auto

    define n where "n = card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}"
    hence n1: "n + 2 \<le> card {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" using 1 by simp
    
    have closed_start_list_len: "length closed_start_list = card {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}" unfolding closed_start_list_def length_sorted_list_of_set by blast
    have n_closed_start_list: "n + 2 \<le> length closed_start_list" using n1 unfolding length_sorted_list_of_set using closed_start_list_def by simp

    have closed_end_list_len: "length closed_end_list = card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}" unfolding closed_end_list_def length_sorted_list_of_set by blast
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
        with no_self_overlap_ran[OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
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
      have "tn + dn \<in> set closed_end_list" using set_closed_end_list unfolding plan_happ_seq_def by fast
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
      thus ?thesis using no_self_overlap_spec[OF tndn(1) tsndsn(1)] sn_t n_Suc_n tndn(2) tsndsn(2) by fastforce
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
  define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"
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
      with no_self_overlap_ran[OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
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

lemma open_ended_le_open_started: "card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq} \<le> card {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}"
proof -
  {
    assume a: "card {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq} < card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"
    define n where "n = card {s'. s' < t \<and> (s', at_start a) \<in> plan_happ_seq}"
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
      have "\<forall>i < n. open_end_list ! i \<noteq> open_end_list ! n" using open_end_list_distinct 
        unfolding distinct_conv_nth using open_end_list_n by simp
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

  define n where "n = card {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"
  have open_end_list_n: "length open_end_list = n" using n_def open_end_list_len by simp
  have open_start_list_n: "length open_start_list = n" using assms 
    unfolding open_start_list_len n_def open_active_count_def 
      le_imp_diff_is_add[OF open_ended_le_open_started] by simp

  have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<and> open_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_start_list ! i = t \<longrightarrow> open_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> open_end_list ! i = t + d \<longrightarrow> open_start_list ! i = t)" 
    using open_start_list_n open_end_list_n open_start_open_end_paired by auto

  from open_start_list_planI td open_start_list_n
  obtain i where
    i: "i < length open_start_list" "open_start_list ! i = t'" by blast

  with open_start_list_n td(1) end_start_paired(2)
  have "open_end_list ! i = t' + d'" by blast
  hence "t' + d' < t" using open_end_list_nth_ran i(1) 
    unfolding open_start_list_n open_end_list_n by fastforce

  with td(3)
  show False by simp
qed

lemma closed_active_count_1E:
  assumes "closed_active_count = 1"
  shows "\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d'"
proof -
  define n where "n = card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}"
  have closed_end_list_n: "length closed_end_list = n" using n_def closed_end_list_len by simp
  have closed_start_list_n: "length closed_start_list = n + 1" using n_def assms 
closed_start_list_len closed_active_count_def by linarith

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
    have "\<forall>i < n. closed_start_list ! i \<le> closed_start_list ! n" 
      using closed_start_list_sorted sorted_nth_mono closed_start_list_n by fastforce
    moreover
    have "\<forall>i < n. closed_start_list ! i \<noteq> closed_start_list ! n" using closed_start_list_distinct 
      unfolding distinct_conv_nth using closed_start_list_n by simp
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
      with no_self_overlap_ran[OF tidi(1) tndn(1)] tidi(2,3) tndn(2) sisn
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

lemma closed_ended_le_closed_started: "card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq} \<le> card {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq}"
proof -
  {
    assume a: "card {s. s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq} < card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}"
    define n where "n = card {s'. s' \<le> t \<and> (s', at_start a) \<in> plan_happ_seq}"
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

  define n where "n = card {s'. s' \<le> t \<and> (s', at_end a) \<in> plan_happ_seq}"
  have closed_end_list_n: "length closed_end_list = n" using n_def closed_end_list_len by simp
  have closed_start_list_n: "length closed_start_list = n" using assms 
    unfolding closed_start_list_len n_def 
      closed_active_count_def le_imp_diff_is_add[OF closed_ended_le_closed_started] by simp

  have end_start_paired: "\<forall>i<n. (\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<and> closed_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_start_list ! i = t \<longrightarrow> closed_end_list ! i = t + d)" 
       "\<forall>i<n. (\<forall>t d. (a, t, d) \<in> ran \<pi> \<and> closed_end_list ! i = t + d \<longrightarrow> closed_start_list ! i = t)" 
    using closed_start_list_n closed_end_list_n closed_start_closed_end_paired by auto

  from closed_start_list_planI td closed_start_list_n
  obtain i where
    i: "i < length closed_start_list" "closed_start_list ! i = t'" by blast

  with closed_start_list_n td(1) end_start_paired(2)
  have "closed_end_list ! i = t' + d'" by blast
  hence "t' + d' \<le> t" using closed_end_list_nth_ran i(1) 
    unfolding closed_start_list_n closed_end_list_n by fastforce

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
  apply (frule at_end_of_act_in_happ_seq_exD[OF _ a_in_acts])
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
  assumes "(t, at_start a) \<in> plan_happ_seq"
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
      "(a, t, d'') \<in> ran \<pi>" using assms(1) at_start_of_act_in_happ_seq_exD a_in_acts by blast 
    ultimately
    show False using no_self_overlap_ran by fastforce
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
  assumes "(t, at_end a) \<in> plan_happ_seq"
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
        "te + de = t" using assms(1) at_end_of_act_in_happ_seq_exD a_in_acts by blast
    have "te \<le> te + de" using plan_durations tede by auto
    hence  "te \<le> t" using at_start_in_happ_seqI[OF tede(1)] tede(2) assms apply (cases "te = te + de") by auto
    ultimately
    have "te + de < ta \<or> ta + da < te"  using nso_double_act_spec[OF tada(1) tede(1)] tada(3) tede(2) by auto
    then consider "te + de < ta" | "ta + da < te" by auto
    thus False using \<open>t < ta + da\<close> \<open>te + de = t\<close> \<open>ta \<le> t\<close> \<open>te \<le> t\<close> apply cases by auto
  qed
  thus ?thesis using closed_active_count_ran by simp
qed

lemma closed_active_count_0_happening_casesE:
  assumes "closed_active_count = 0"
      and "is_not_happening_action t a \<Longrightarrow> thesis"
      and "is_ending_action t a \<Longrightarrow> thesis"
      and "is_instant_action t a \<Longrightarrow> thesis"
    shows thesis
proof -
  presume "is_starting_action t a \<Longrightarrow> thesis"
  thus thesis using assms action_happening_cases by auto
next
  assume "is_starting_action t a"
  hence "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<notin>  plan_happ_seq" using is_starting_action_def by auto
  with at_start_of_act_in_happ_seq_exD \<open>a \<in> actions\<close>
  obtain d where
    d: "(a, t, d) \<in> ran \<pi>" by blast
  moreover
  have "0 < d"
  proof -
    have "0 \<le> d" using d plan_durations by auto
    moreover
    { assume "0 = d"
      hence False using at_end_in_happ_seqI d \<open>(t, at_end a) \<notin>  plan_happ_seq\<close> by force
    }
    ultimately
    show ?thesis by force
  qed
  moreover
  have "\<not>(\<exists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d')" using assms closed_active_count_0_iff by auto
  ultimately
  have "False" by auto
  thus thesis by simp
qed

lemma closed_active_count_1_if_starting:
  assumes "(t, at_start a) \<in> plan_happ_seq"
      and "(t, at_end a) \<notin> plan_happ_seq"
    shows "closed_active_count = 1"
proof -
  from assms(1)
  obtain d where
    d: "(a, t, d) \<in> ran \<pi>" using at_start_of_act_in_happ_seq_exD a_in_acts by blast
  hence "0 \<le> d" using plan_durations by simp
  moreover
  have "(t + d, at_end a) \<in> plan_happ_seq" using at_end_in_happ_seqI d by simp
  ultimately
  have "t < t + d" using assms(2) apply (cases "d = 0") by auto
  with d
  show ?thesis using closed_active_count_1_iff by blast
qed


lemma open_active_count_eq_closed_active_count_if_only_instant_acts:
  assumes "(t, at_start a) \<in> plan_happ_seq \<longleftrightarrow> (t, at_end a) \<in> plan_happ_seq"
    shows "open_active_count = closed_active_count"
proof -
  consider "(t, at_start a) \<in> plan_happ_seq \<and> (t, at_end a) \<in> plan_happ_seq" 
    | "(t, at_start a) \<notin> plan_happ_seq \<and> (t, at_end a) \<notin> plan_happ_seq"  using assms by auto
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
  shows "(t, at_start a) \<in> plan_happ_seq \<longleftrightarrow> (t, at_end a) \<in> plan_happ_seq"
proof -
  { assume "open_active_count = 0" "closed_active_count = 0"
    with open_active_count_0_iff closed_active_count_0_iff
    have start_cond: "(\<nexists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d')" 
     and end_cond: "(\<nexists>t' d'. (a, t', d') \<in> ran \<pi> \<and> t' \<le> t \<and> t < t' + d')" by auto
    { assume "(t, at_start a) \<in> plan_happ_seq"
      with at_start_of_act_in_happ_seq_exD a_in_acts
      obtain ds where
        ds: "(a, t, ds) \<in> ran \<pi>" by blast
      moreover
      have "0 \<le> ds" using plan_durations ds by auto
      ultimately
      have "t = t + ds" using end_cond by fastforce
      with ds
      have "(t, at_end a) \<in> plan_happ_seq" using at_end_in_happ_seqI by fastforce
    }
    moreover
    { assume "(t, at_end a) \<in> plan_happ_seq"
      with at_end_of_act_in_happ_seq_exD a_in_acts
      obtain te de where
        tede: "(a, te, de) \<in> ran \<pi>" "t = te + de" by blast
      moreover
      have "0 \<le> de" using plan_durations tede by auto
      ultimately
      have "te = t" using start_cond by fastforce
      with tede
      have "(t, at_start a) \<in> plan_happ_seq" using at_start_in_happ_seqI by fastforce
    }
    ultimately
    have "(t, at_start a) \<in> plan_happ_seq \<longleftrightarrow> (t, at_end a) \<in> plan_happ_seq" by auto
  }
  moreover
  { assume "open_active_count = 1" "closed_active_count = 1"
    with open_active_count_1_iff closed_active_count_1_iff
    obtain t1 d1 t2 d2 where
        t1d1: "(a, t1, d1) \<in> ran \<pi>" "t1 < t" "t \<le> t1 + d1"
    and t2d2: "(a, t2, d2) \<in> ran \<pi>" "t2 \<le> t" "t < t2 + d2" by auto
    from no_self_overlap_ran[OF t1d1(1) t2d2(1)] no_self_overlap_ran[OF t2d2(1) t1d1(1)]
    have "t1 \<noteq> t2 \<or> d1 \<noteq> d2 \<Longrightarrow> (t2 < t1 \<or> t1 + d1 < t2) \<and> (t1 < t2 \<or> t2 + d2 < t1)" by blast
    with t1d1(2,3) t2d2(2,3)
    have "t1 \<noteq> t2 \<or> d1 \<noteq> d2 \<Longrightarrow> False" by auto 
    hence td: "(a, t1, d1) \<in> ran \<pi>" "t1 < t" "t < t1 + d1" using t1d1 t2d2 by auto
    { assume "(t, at_start a) \<in> plan_happ_seq"
      with at_start_of_act_in_happ_seq_exD a_in_acts 
      obtain d where
        "(a, t, d) \<in> ran \<pi>" by blast
      from no_self_overlap_spec[OF td(1) this] td(2,3)
      have "False" by fastforce
    }
    moreover
    { assume "(t, at_end a) \<in> plan_happ_seq"
      with at_end_of_act_in_happ_seq_exD a_in_acts 
      obtain te de where
        tede: "(a, te, de) \<in> ran \<pi>" "te + de = t" by blast
      hence "0 \<le> de" using plan_durations by auto 
      note tede = tede this
      from no_self_overlap_ran[OF tede(1) td(1)] no_self_overlap_ran[OF td(1) tede(1)]
      have "te \<noteq> t1 \<or> de \<noteq> d1 \<Longrightarrow> (t1 < te \<or> te + de < t1) \<and> (te < t1 \<or> t1 + d1 < te)" by auto
      with tede td
      have False using add_strict_increasing2 by fastforce
    }
    ultimately
    have "(t, at_start a) \<in> plan_happ_seq \<longleftrightarrow> (t, at_end a) \<in> plan_happ_seq" by blast
  }
  ultimately
  show ?thesis using open_active_count_ran closed_active_count_ran assms by auto
qed

lemma open_active_count_eq_closed_active_count_iff_only_instant_acts:
  "open_active_count = closed_active_count \<longleftrightarrow> ((t, at_start a) \<in> plan_happ_seq \<longleftrightarrow> (t, at_end a) \<in> plan_happ_seq)"
  using open_active_count_eq_closed_active_count_if_only_instant_acts 
    only_instant_acts_if_open_active_count_eq_closed_active_count by blast

lemma closed_active_count_1_happening_casesE:
  assumes "closed_active_count = 1"
      and "is_starting_action t a \<Longrightarrow> thesis"
      and "is_not_happening_action t a \<Longrightarrow> thesis"
    shows thesis
proof -
  presume "is_ending_action t a \<Longrightarrow> False" "is_instant_action t a \<Longrightarrow> False"
  thus thesis using assms action_happening_cases by auto
next
  assume "is_ending_action t a"
  with is_ending_action_planE \<open>a \<in> actions\<close>
  obtain te de where
    tede: "(a, te, de) \<in> ran \<pi>" "te < t" "t = te + de" by blast

  from assms closed_active_count_1E
  obtain ta da where
    tada: "(a, ta, da) \<in> ran \<pi>" "ta \<le> t" "t < ta + da" by blast

  from nso_double_act_spec[OF tede(1) tada(1)] 
  have "te \<noteq> ta \<or> de \<noteq> da \<Longrightarrow> ta + da < te \<or> te + de < ta" by auto
  moreover
  have "te = ta \<Longrightarrow> de \<noteq> da" using tede tada by auto
  ultimately
  have "ta + da < te \<or> te + de < ta" by auto
  with tede tada 
  show False apply - by (erule disjE; order)
next
  assume "is_instant_action t a"
  with is_instant_action_planE \<open>a \<in> actions\<close>
  have t0: "(a, t, 0) \<in> ran \<pi>" by auto

  from assms closed_active_count_1E
  obtain ta da where
    tada: "(a, ta, da) \<in> ran \<pi>" "ta \<le> t" "t < ta + da" by blast
  with nso_double_act_spec[OF t0 tada(1)] 
  show False by fastforce
qed

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

lemma closed_open_active_count_conv_open_active_count:
  "closed_open_active_count = 1 \<Longrightarrow> is_starting_action t a \<and> open_active_count = 0 \<or> (\<not>is_starting_action t a \<and> open_active_count = 1)"
  "closed_open_active_count = 0 \<Longrightarrow> \<not>is_starting_action t a \<and> open_active_count = 0"
  unfolding closed_open_active_count_def by (auto elim: open_active_count_cases, presburger+)

lemma closed_open_active_count_1_if_starting:
  assumes "is_starting_action t a"
  shows "closed_open_active_count = 1"
  using assms closed_open_active_count_ran 
  unfolding closed_open_active_count_def by auto

lemma closed_open_active_count_is_open_active_count_if_not_starting:
  assumes "\<not>is_starting_action t a"
  shows "closed_open_active_count = open_active_count"
  apply (rule closed_open_active_count_cases)
  using assms closed_open_active_count_conv_open_active_count by auto

(* active_count'' *)
lemma active_count''_ran:
  "active_count'' \<in> {0, 1}"
proof -
  have "\<not>1 < active_count''"
  proof (rule notI)
    assume "1 < active_count''"
    hence "open_active_count = 1 \<and> is_starting_action t a" unfolding active_count''_def
      by (rule contrapos_pp) (use open_active_count_ran in auto)
    thus False using open_active_count_0_if_start_scheduled is_starting_action_def by auto
  qed
  thus ?thesis by auto
qed

lemma active_count''_cases:
  assumes "active_count'' = 0 \<Longrightarrow> thesis"
          "active_count'' = 1 \<Longrightarrow> thesis"
        shows thesis using active_count''_ran assms by blast

lemma active_count''_1_if_starting:
  assumes "is_starting_action t a"
  shows "active_count'' = 1"
  apply (insert assms active_count''_ran) 
  apply (frule action_happening_disj)
  unfolding active_count''_def 
  by auto

lemma active_count''_0_if_ending:
  assumes "is_ending_action t a"
  shows "active_count'' = 0"
  apply (insert assms active_count''_ran)
  apply (frule action_happening_disj)
  unfolding active_count''_def
  using open_active_count_ran by auto

lemma active_count''_alt_def:
  "active_count'' = closed_open_active_count - (if is_ending_action t a then 1 else 0)"
  unfolding active_count''_def closed_open_active_count_def by blast

lemma active_count''_is_closed_active_count:
  "active_count'' = closed_active_count"
  apply (rule action_happening_cases[of t a])
  subgoal using open_active_count_eq_closed_active_count_iff_only_instant_acts using active_count''_def action_happening_case_defs by simp
  subgoal using closed_active_count_1_if_starting  active_count''_1_if_starting is_starting_action_def by simp
  subgoal using active_count''_0_if_ending closed_active_count_0_if_end_scheduled is_ending_action_def by simp
  subgoal using open_active_count_eq_closed_active_count_iff_only_instant_acts using active_count''_def action_happening_case_defs by simp
  done

lemma active_count''_conv_closed_open_active_count:
  "active_count'' = 1 \<Longrightarrow> \<not>is_ending_action t a \<and> closed_open_active_count = 1"
  "active_count'' = 0 \<Longrightarrow> closed_open_active_count = 0 \<or> is_ending_action t a"
  unfolding active_count''_alt_def 
  by (fastforce intro: closed_open_active_count_cases)+
     
end
end

subsubsection \<open>Sets of actions and snap actions happening\<close>


definition instant_actions_at where
"instant_actions_at t \<equiv> {a \<in> actions. is_instant_action t a}"

definition ending_actions_at where
"ending_actions_at t \<equiv> {a \<in> actions. is_ending_action t a}"

definition starting_actions_at where
"starting_actions_at t \<equiv> {a \<in> actions. is_starting_action t a}"

definition not_happening_actions_at where
"not_happening_actions_at t \<equiv> {a \<in> actions. is_not_happening_action t a}"

lemmas actions_at_defs = instant_actions_at_def ending_actions_at_def starting_actions_at_def not_happening_actions_at_def

definition "instant_snaps_at t = at_start ` instant_actions_at t \<union> at_end ` instant_actions_at t"

definition "starting_snaps_at t = at_start ` starting_actions_at t"

definition "ending_snaps_at t =  at_end ` ending_actions_at t"

lemma instant_snaps_happening:
  "instant_snaps_at t \<subseteq> happ_at plan_happ_seq t"
  unfolding instant_snaps_at_def instant_actions_at_def is_instant_action_def by blast

lemma starting_snaps_happening:
  "starting_snaps_at t \<subseteq> happ_at plan_happ_seq t"
  unfolding starting_snaps_at_def starting_actions_at_def is_starting_action_def by blast

lemma ending_snaps_happening:
  "ending_snaps_at t \<subseteq> happ_at plan_happ_seq t"
  unfolding ending_snaps_at_def ending_actions_at_def is_ending_action_def by blast

lemma finite_instant_actions_at:
  "finite (instant_actions_at t)"
  unfolding instant_actions_at_def using finite_actions by auto

lemma finite_ending_actions_at:
  "finite (ending_actions_at t)"
  unfolding ending_actions_at_def using finite_actions by auto

lemma finite_starting_actions_at:
  "finite (starting_actions_at t)"
  unfolding starting_actions_at_def using finite_actions by auto


lemma all_actions_at: "actions = ending_actions_at t \<union> instant_actions_at t \<union> starting_actions_at t \<union> not_happening_actions_at t"
  using action_happening_cases ending_actions_at_def starting_actions_at_def instant_actions_at_def not_happening_actions_at_def by auto

lemma finite_not_happening_actions_at: "finite (not_happening_actions_at t)"
  using all_actions_at[of t] finite_subset[OF _ finite_actions]
  by blast

lemma ending_actions_at_less:
  assumes "instant_actions_at t \<union> starting_actions_at t \<union> not_happening_actions_at t \<noteq> {}"
  shows "ending_actions_at t \<subset> actions"
proof -
  consider x where "x \<in> instant_actions_at t" | x where "x \<in> starting_actions_at t" | x where "x \<in> not_happening_actions_at t" 
    using assms by auto
  hence "\<exists>x. x \<in> actions \<and> x \<notin> ending_actions_at t"
    apply cases
    subgoal apply (subst all_actions_at[of t])
      unfolding actions_at_defs using action_happening_disj by blast
    subgoal apply (subst all_actions_at[of t])
      unfolding actions_at_defs using action_happening_disj by blast
    subgoal apply (subst all_actions_at[of t])
      unfolding actions_at_defs using action_happening_disj by blast
    done
  thus ?thesis using all_actions_at by auto
qed

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
      apply (cases "(t, at_start x) \<notin> plan_happ_seq \<and> (t, at_end x) \<in> plan_happ_seq")
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
  have 2: "sum_list (map (open_active_count t) xs) = sum_list (map (open_closed_active_count t) xs) 
    + (\<Sum>a\<leftarrow>xs. if is_ending_action t a then 1 else 0)" if "set xs \<subseteq> actions" for xs
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
      apply (cases "(t, at_start x) \<notin> plan_happ_seq \<and> (t, at_end x) \<in> plan_happ_seq")
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
        sum_list (map (open_active_count t) xs) - (\<Sum>a\<leftarrow>xs. if is_ending_action t a then 1 else 0) 
      + (\<Sum>a\<leftarrow>xs. if is_starting_action t a then 1 else 0)" if "set xs \<subseteq> actions" for xs 
    using that
    apply (induction xs)
     apply simp
    subgoal for x xs 
      apply (subst sum_list.eq_foldr)+
      apply (subst list.map)+
      apply (subst foldr.simps)+
      apply (subst comp_apply)+
      apply (subst sum_list.eq_foldr[symmetric])+
      apply (cases "(t, at_start x) \<in> plan_happ_seq"; cases "(t, at_end x) \<in> plan_happ_seq")
         apply simp
      subgoal using open_active_count_0_if_start_scheduled 
          closed_active_count_0_if_end_scheduled action_happening_case_defs by simp
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

lemma locked_after_and_during': "locked_after t p = locked_during t p + card {a \<in> starting_actions_at t. p \<in> over_all a}"
proof -
  have "sum_list (map (\<lambda>a. (if is_starting_action t a then (1::nat) else 0)) (locked_by p)) = card {a \<in> starting_actions_at t. p \<in> over_all a}"
  proof -
    
    have "sum_list (map (\<lambda>a. (if is_starting_action t a then (1::nat) else 0)) (locked_by p)) = 
        sum_list (map (\<lambda>a. 1) (filter (is_starting_action t) (locked_by p)))
        + sum_list (map (\<lambda>a. 0) (filter (\<lambda>a. \<not>is_starting_action t a) (locked_by p)))"
      using sum_list_map_if' by blast
    also have "... = sum_list (map (\<lambda>a. 1) (filter (is_starting_action t) (locked_by p)))" using sum_list_0 by simp
    also have "... = card (set (filter (is_starting_action t) (locked_by p)))"
      apply (subst distinct_sum_list_1_conv_card_set)
      using distinct_filter unfolding locked_by_def using distinct_action_list by auto
    finally have "(\<Sum>a\<leftarrow>locked_by p. if is_starting_action t a then 1 else 0) = card (set (filter (is_starting_action t) (locked_by p)))" by auto
    moreover
    have "{a \<in> starting_actions_at t. p \<in> over_all a} = set (filter (is_starting_action t) (locked_by p))"
      unfolding set_filter locked_by_def set_action_list starting_actions_at_def by auto
    ultimately
    show ?thesis by auto
  qed
  thus ?thesis using locked_after_and_during by auto
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

lemma open_active_count_initial_is_0: "open_active_count (time_index 0) a = 0"
proof -
  find_theorems name: "no*init*ti"
  have "{s. s < time_index 0 \<and> (s, at_start a) \<in> plan_happ_seq} = {}" (is "?S = {}")
  proof -
    { fix x
      assume "x \<in> ?S"
      hence False 
        apply -
        apply (elim CollectE conjE)
        apply (drule happ_seq_conv_htps)
        apply (drule time_indexI_htps[rotated])
        using time_index_sorted_set[of 0]
        by fastforce
    }
    thus ?thesis by blast
  qed
  moreover
  have "{s'. s' < time_index 0 \<and> (s', at_end a) \<in> plan_happ_seq} = {}" (is "?S = {}")
  proof -
    { fix x
      assume "x \<in> ?S"
      hence False 
        apply -
        apply (elim CollectE conjE)
        apply (drule happ_seq_conv_htps)
        apply (drule time_indexI_htps[rotated])
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
  shows "closed_active_count (time_index (length htpl - 1)) a = 0"
proof (cases "length htpl")
  case 0
  hence "ran \<pi> = {}"
    using empty_acts_if_empty_htpl_finite vp valid_plan_finite by blast
  then show ?thesis 
    unfolding closed_active_count_def plan_happ_seq_def plan_happ_seq_def by simp
next
  case (Suc nat)
  show ?thesis 
    apply (subst closed_active_count_0_iff)
     apply (rule assms)
    apply (rule notI)
    apply (elim exE conjE)
    subgoal for t d
      using no_actions_after_final_timepoint[OF]
      using Suc  apply simp
      using in_happ_seqI by fast
    done
qed

lemma closed_active_count_is_open_active_count_if_nothing_happens:
  assumes "s < t"
    and "\<not>(\<exists>s' h. s < s' \<and> s' < t \<and> (s', h) \<in> plan_happ_seq)" 
  shows "closed_active_count s a = open_active_count t a"
proof -
  have "{sa. sa \<le> s \<and> (sa, at_start a) \<in> plan_happ_seq} = {s. s < t \<and> (s, at_start a) \<in> plan_happ_seq}"
    apply (intro equalityI subsetI)
    subgoal using assms(1) by auto
    subgoal for x
      apply (cases "x \<le> s")
      using assms(2) by auto
    done
  moreover
  have "{s'. s' \<le> s \<and> (s', at_end a) \<in> plan_happ_seq} = {s'. s' < t \<and> (s', at_end a) \<in> plan_happ_seq}"
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
  assumes "Suc i < length htpl"
  shows "closed_active_count (time_index i) a = open_active_count (time_index (Suc i)) a"
  apply (rule closed_active_count_is_open_active_count_if_nothing_happens)
   apply (rule time_index_strict_sorted_list, (simp add: assms)+)
  using no_actions_between_indexed_timepoints[OF assms]
  by fast

lemma locked_after_is_locked_before_if_nothing_happens:
  assumes "s < t"
    and "\<not>(\<exists>s' h. s < s' \<and> s' < t \<and> (s', h) \<in> plan_happ_seq)" 
  shows "locked_after s p = locked_before t p"
  unfolding locked_after_def locked_before_def
  using closed_active_count_is_open_active_count_if_nothing_happens assms by simp

lemma locked_after_indexed_timepoint_is_locked_before_Suc:
  assumes "Suc i < length htpl"
  shows "locked_after (time_index i) p = locked_before (time_index (Suc i)) p"
  apply (rule locked_after_is_locked_before_if_nothing_happens)
   apply (rule time_index_strict_sorted_list, (simp add: assms)+)
  using no_actions_between_indexed_timepoints[OF assms]
  by fast

lemma locked_before_initial_is_0:
  shows "locked_before (time_index 0) p = 0"
  unfolding locked_before_def using open_active_count_initial_is_0 by simp

lemma locked_after_final_is_0:
  "locked_after (time_index (length htpl - 1)) p = 0"
  unfolding locked_after_def using closed_active_count_final_is_0 locked_by_def set_action_list by auto

subsubsection \<open>Counting the number of active actions in total\<close>

definition "active_before t \<equiv> sum_list (map (open_active_count t) action_list)"

definition "active_after t \<equiv> sum_list (map (closed_active_count t) action_list)"

definition "active_during t \<equiv> sum_list (map (closed_open_active_count t) action_list)"

definition "active_during_minus_ended t \<equiv> sum_list (map (active_count'' t) action_list)"

lemma active_before_less_if_scheduled:
  assumes "(t, at_start a) \<in> plan_happ_seq"
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


subsubsection \<open>Relating the notions of active actions\<close>

lemma active_after_is_before_if_nothing_happens:
  assumes "s < t"
    and "\<not>(\<exists>s' h. s < s' \<and> s' < t \<and> (s', h) \<in> plan_happ_seq)" 
  shows "active_after s = active_before t"
  unfolding active_after_def active_before_def 
  using closed_active_count_is_open_active_count_if_nothing_happens assms by auto

lemma active_after_indexed_timepoint_is_active_before_Suc: 
  assumes "Suc i < length htpl"
  shows "active_after (time_index i) = active_before (time_index (Suc i))"
  apply (rule active_after_is_before_if_nothing_happens)
   apply (rule time_index_strict_sorted_list, (simp add: assms)+)
  using no_actions_between_indexed_timepoints[OF assms]
  by fast

lemma active_before_initial_is_0: "active_before (time_index 0) = 0"
  unfolding active_before_def using open_active_count_initial_is_0 by auto

lemma active_after_final_is_0:  "active_after (time_index (length htpl - 1)) = 0"
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

lemma active_during_minus_ended_ran:
  shows "active_during_minus_ended t \<le> card actions"
proof -
  have 1: "sum_list (map (active_count'' t) action_list) \<le> length (map (active_count'' t) action_list) * 1"
    using set_action_list active_count''_ran[where t = t] by (fastforce intro: sum_list_max)
    
  show ?thesis
    unfolding active_during_minus_ended_def
    apply (subst (2) set_action_list[symmetric])
    apply (subst distinct_card[OF distinct_action_list])
    using 1 by simp
qed

lemma active_during_conv_active_during_minus_ended:
  "active_during t = active_during_minus_ended t + card (ending_actions_at t)"
proof -
  have 1: "\<forall>x\<in>set action_list. (if is_ending_action t x then 1 else 0) \<le> closed_open_active_count t x"
  proof (intro ballI)
    fix x
    assume a: "x \<in> set action_list"
    show "(if is_ending_action t x then 1 else 0) \<le> closed_open_active_count t x"
    proof (cases "is_ending_action t x")
      case True
      hence "\<not>is_starting_action t x" using action_happening_disj by blast
      hence "closed_open_active_count t x = open_active_count t x" 
        using closed_open_active_count_is_open_active_count_if_not_starting a set_action_list by blast
      hence "closed_open_active_count t x = 1" using open_active_count_1_if_ending True a set_action_list by simp
      then show ?thesis by simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  
  have "sum_list (map (closed_open_active_count t) action_list) = sum_list (map (active_count'' t) action_list) + card (ending_actions_at t)"
  proof -
    have "sum_list (map (closed_open_active_count t) action_list) = 
        sum_list (map (\<lambda>a. active_count'' t a + (if is_ending_action t a then 1 else 0)) action_list)"
    proof (rule arg_cong[of _ _ sum_list])
      have "\<forall>x\<in>set action_list. closed_open_active_count t x = active_count'' t x + (if is_ending_action t x then 1 else 0)" 
        (is "Ball _ (\<lambda>x. ?f x = ?g x)")
        using 1 active_count''_alt_def set_action_list by simp
      thus "map (closed_open_active_count t) action_list =
            map (\<lambda>a. active_count'' t a + (if is_ending_action t a then 1 else 0)) action_list"
        using map_eq_conv[of ?f _ ?g]
        by simp
    qed
    also
    have "... = sum_list (map (active_count'' t) action_list) + card (ending_actions_at t)" 
    proof -
      have "set (filter (is_ending_action t) action_list) = ending_actions_at t"
        unfolding ending_actions_at_def using set_action_list by auto
      hence "card (ending_actions_at t) = (\<Sum>a\<leftarrow>action_list. if is_ending_action t a then 1 else 0)"
        unfolding ending_actions_at_def
        apply (subst foldr_map_filter)
        apply (subst distinct_sum_list_1_conv_card_set)
        using distinct_action_list by auto
      thus ?thesis by (simp add: sum_list_addf)
    qed
    finally 
    show ?thesis .
  qed
  thus ?thesis unfolding active_during_def active_during_minus_ended_def by auto
qed

lemma active_after_conv_active_during_minus_ended:
  "active_after t = active_during_minus_ended t"
  unfolding active_after_def active_during_minus_ended_def
  apply (rule arg_cong[of _ _ sum_list])
  using active_count''_is_closed_active_count set_action_list by simp

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
    unfolding plan_invs_before_def invs_at_def plan_inv_seq_def by blast
  from tada(1) acts_in_prob
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
  show "p \<in> plan_invs_before t" unfolding plan_invs_before_def invs_at_def plan_inv_seq_def 
    using tada a(1) by auto
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
  from tada(1) acts_in_prob
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
  from tada(1) acts_in_prob
  have a_in_acts: "a \<in> actions" by fast
  with tada
  have a_locks: "a \<in> set (locked_by p)" using locked_by_alt by blast
  have a_closed_active: "closed_active_count t a = 1" using closed_active_count_1_iff tada a_in_acts by fastforce
  have a_open_active: "open_active_count t a = 1" using open_active_count_1_iff tada a_in_acts by fastforce

  have "(t, at_start a) \<in> plan_happ_seq \<longleftrightarrow> (t, at_end a) \<in> plan_happ_seq" using a_closed_active 
      a_open_active open_active_count_eq_closed_active_count_iff_only_instant_acts[OF a_in_acts, of t] by argo  
  moreover
  have not_starting: "(t, at_start a) \<notin> plan_happ_seq" 
      using open_active_count_0_if_start_scheduled a_in_acts a_open_active by auto
  ultimately
  have not_ending: "(t, at_end a) \<notin> plan_happ_seq" by simp

  have a_in_open_closed: "open_closed_active_count t a = 1" unfolding open_closed_active_count_def 
      using a_open_active not_starting not_ending is_ending_action_def by simp

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
  consider "(t, at_start a) \<in> plan_happ_seq" | "(t, at_end a) \<notin> plan_happ_seq" 
      unfolding open_closed_active_count_def is_ending_action_def by fastforce
  then consider "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<notin> plan_happ_seq" 
    | "(t, at_start a) \<in> plan_happ_seq" "(t, at_end a) \<in> plan_happ_seq"
    | "(t, at_start a) \<notin> plan_happ_seq" "(t, at_end a) \<notin> plan_happ_seq" by argo
  hence not_starting_or_ending: "(t, at_start a) \<notin> plan_happ_seq \<and> (t, at_end a) \<notin> plan_happ_seq"
    apply cases 
    subgoal using open_active_count_0_if_start_scheduled oac by auto
    subgoal using open_active_count_eq_closed_active_count_iff_only_instant_acts oac 
        closed_active_count_0_if_end_scheduled by force
    subgoal by simp
    done

  from open_active_count_1E[OF _ oac]
  obtain t' d' where
    t'd': "(a, t', d') \<in> ran \<pi>" "t' < t" "t \<le> t' + d'" by auto
  with not_starting_or_ending[THEN conjunct2]
  have t_le_t'd': "t < t' + d'" using at_end_in_happ_seqI apply (cases "t = t' + d'") by auto
  show "p \<in> plan_invs_during t" unfolding plan_invs_during_def invs_during_def invs_at_def 
    using a(1) t'd' t_le_t'd' by auto
qed

subsubsection \<open>Connecting the different invariant states\<close>

lemma invs_after_invariant_if:
  assumes "s < u"
      and "\<not>(\<exists>t h. s < t \<and> t < u \<and> (t, h) \<in> plan_happ_seq)"
    shows "plan_invs_after s = plan_invs_before u"
  apply (intro equalityI subsetI)
  subgoal for p
    unfolding plan_invs_after_def plan_invs_before_def invs_after_def plan_inv_seq_def invs_at_def
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
    unfolding plan_invs_after_def plan_invs_before_def invs_after_def plan_inv_seq_def invs_at_def
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
  assumes "Suc l < length htpl"
  shows "plan_invs_after (time_index l) = plan_invs_before (time_index (Suc l))"
  apply (rule invs_after_invariant_if)
  using time_index_strict_sorted_list assms apply fastforce
  using no_actions_between_indexed_timepoints assms
  by fast

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
  assumes "0 < length htpl"
  shows "plan_invs_after (time_index (length htpl - 1)) = {}"
  apply (rule ccontr)
  apply (subst (asm) ex_in_conv[symmetric])
  apply (erule exE)
  apply (erule plan_invs_afterE)
  apply (drule at_end_in_happ_seqI)
  using no_actions_after_final_timepoint assms 
  by fast

lemma snap_does_not_delete_inv:
  assumes "(t, h) \<in> plan_happ_seq"
  shows "((dels h - adds h) \<inter> plan_invs_during t) = {}"
proof-
  from assms
  have "t \<in> htps" using a_in_B_iff_t_in_htps plan_happ_seq_def by fast
  then obtain l where
    l: "l < length htpl"
    "time_index l = t" using time_index_img_set unfolding card_htps_len_htpl by force
  then consider "Suc l = length htpl" | "Suc l < length htpl" by linarith
  thus ?thesis
  proof cases
    case 1
    hence "l = length htpl - 1" using l by auto
    hence "plan_invs_after (time_index l) = {}" using no_invs_after_end 1 by fastforce
    then show ?thesis using invs_during_hold_after l by blast
  next
    case 2
    with invs_between_indexed_timepoints_invariant
    have "plan_invs_after (time_index l) = plan_invs_before (time_index (Suc l))" by simp
    moreover
    have "plan_invs_before (time_index (Suc l)) \<subseteq> plan_state_seq (Suc l)" 
      using plan_state_seq_props 2 unfolding Let_def plan_invs_before_def by simp
    moreover
    have "plan_state_seq (Suc l) = apply_effects (happ_at plan_happ_seq (time_index l)) (plan_state_seq l)" 
      using plan_state_seq_props l(1) unfolding Let_def plan_happ_seq_def[symmetric] by auto
    ultimately
    have "plan_invs_after (time_index l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` happ_at plan_happ_seq (time_index l))" 
      unfolding apply_effects_def by simp
    hence 1: "plan_invs_during (time_index l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` happ_at plan_happ_seq (time_index l))" using invs_during_hold_after l by auto

    have h_happens: "h \<in> happ_at plan_happ_seq (time_index l)" using assms l by simp
    hence "plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` happ_at plan_happ_seq (time_index l)) 
            = plan_state_seq l - (\<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> dels h) \<union> \<Union> (adds ` happ_at plan_happ_seq (time_index l)) \<union> adds h" by auto
    hence "plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` happ_at plan_happ_seq (time_index l)) 
            = plan_state_seq l - (\<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> dels h) \<union> \<Union> (adds ` (happ_at plan_happ_seq (time_index l) - {h})) \<union> adds h" by auto
    moreover
    have "dels h \<inter> \<Union> (adds ` (happ_at plan_happ_seq (time_index l) - {h})) = {}"
    proof -
      {
        fix s
        assume "s \<in> (happ_at plan_happ_seq (time_index l) - {h})" 
        hence "\<not> mutex_snap_action s h" using nm_happ_seq 
          unfolding nm_happ_seq_def nm_happ_seq_def 
          using h_happens by blast
        hence "dels h \<inter> adds s = {}" unfolding mutex_snap_action_def by auto
      }
      thus ?thesis by auto
    qed
    ultimately
    have "plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` happ_at plan_happ_seq (time_index l)) 
            = plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` (happ_at plan_happ_seq (time_index l) - {h})) - dels h \<union> adds h" by auto
    from 1[simplified this]
    have "plan_invs_during (time_index l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` (happ_at plan_happ_seq (time_index l) - {h})) - dels h \<union> adds h" .
    hence "plan_invs_during (time_index l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` (happ_at plan_happ_seq (time_index l) - {h})) - (dels h - adds h) \<union> adds h" by blast
    hence "plan_invs_during (time_index l) \<subseteq> plan_state_seq l - \<Union> (dels ` happ_at plan_happ_seq (time_index l)) \<union> \<Union> (adds ` (happ_at plan_happ_seq (time_index l) - {h})) \<union> adds h - (dels h - adds h)" by blast
    thus ?thesis using l by auto
  qed
qed

subsection \<open>Propositional states, updates, and commutativity\<close>

lemma prop_state_upd_combine_if:                        
  assumes "\<And>a b. a \<in> h \<Longrightarrow> b \<in> h \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> mutex_snap_action a b"
      and "h1 \<union> h2 = h"
  shows "(apply_effects h2 o apply_effects h1) M  = apply_effects h M"
proof -
  from assms
  have ab_not_int: "\<And>a b. a \<in> h \<Longrightarrow> b \<in> h \<Longrightarrow> a \<noteq> b \<Longrightarrow> adds a \<inter> dels b = {}" unfolding mutex_snap_action_def by simp
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

  have "apply_effects h2 (apply_effects h1 M) = M - \<Union> (dels ` h1) \<union> \<Union> (adds ` h1) - \<Union> (dels ` h2) \<union> \<Union> (adds ` h2)" unfolding apply_effects_def by blast
  also have "... = M - \<Union> (dels ` h1) \<union> \<Union> (adds ` h1) - (\<Union> (dels ` h2) - \<Union> (adds ` h2)) \<union> \<Union> (adds ` h2)" by blast
  also have "... = M - \<Union> (dels ` h1) - (\<Union> (dels ` h2) - \<Union> (adds ` h2)) \<union> \<Union> (adds ` h1) \<union> \<Union> (adds ` h2)" using not_int by blast
  also have "... = M - (\<Union> (dels ` h1) \<union> \<Union> (dels ` h2)) \<union> \<Union> (adds ` h1) \<union> \<Union> (adds ` h2)" by blast
  also have "... = M - \<Union> (dels ` h) \<union> \<Union> (adds ` h)" using assms(2) by blast
  finally show ?thesis unfolding apply_effects_def comp_def by simp
qed

lemma mutex_pre_app: 
  assumes "(t, a) \<in> plan_happ_seq"
      and "(t, b) \<in> plan_happ_seq"
      and "a \<noteq> b"
    shows "pre a \<inter> (dels b \<union> adds b) = {}"
  using nm_happ_seq assms unfolding nm_happ_seq_def nm_happ_seq_def
  unfolding mutex_snap_action_def by blast

lemma happ_combine:
  assumes "h1 \<union> h2 \<subseteq> happ_at plan_happ_seq t"
  shows "(apply_effects h2 o apply_effects h1) M = apply_effects (h1 \<union> h2) M"
  apply (rule prop_state_upd_combine_if)
  using nm_happ_seq assms unfolding nm_happ_seq_def nm_happ_seq_def
  by blast+

subsection \<open>Restating happenings\<close>

lemma happ_at_is_union_of_starting_ending_instant:
  "happ_at plan_happ_seq t = instant_snaps_at t \<union> ending_snaps_at t \<union> starting_snaps_at t"
  apply (intro equalityI subsetI)
  subgoal for x
    apply (drule in_happ_atD)
    apply (drule in_happ_seq_exD)
    apply (elim exE)
    subgoal for a t d
      apply (elim conjE disjE)
      subgoal  
        apply (frule at_start_in_happ_seqI)
        apply (frule acts_in_prob)
        apply (cases "(t, at_end a) \<in> plan_happ_seq")
        unfolding instant_snaps_at_def instant_actions_at_def is_instant_action_def starting_snaps_at_def is_starting_action_def starting_actions_at_def by auto
        apply (frule at_end_in_happ_seqI)
        apply (frule acts_in_prob)
      apply (cases "(t + d, at_start a) \<in> plan_happ_seq")
      unfolding instant_snaps_at_def instant_actions_at_def is_instant_action_def ending_snaps_at_def is_ending_action_def ending_actions_at_def by auto
        done
      apply (elim UnE)
      unfolding instant_snaps_at_def instant_actions_at_def starting_snaps_at_def starting_actions_at_def ending_snaps_at_def ending_actions_at_def
      unfolding action_happening_case_defs by auto

lemma app_start_instant_dist: "(apply_effects (starting_snaps_at t) o apply_effects (instant_snaps_at t)) M = apply_effects (instant_snaps_at t \<union> starting_snaps_at t) M"
  apply (rule prop_state_upd_combine_if[OF _ HOL.refl])
  subgoal for a b
    unfolding instant_snaps_at_def starting_snaps_at_def instant_actions_at_def starting_actions_at_def
    using nm_happ_seq unfolding nm_happ_seq_def nm_happ_seq_def
    unfolding action_happening_case_defs by auto
    done

lemma app_all_dist: "(apply_effects (ending_snaps_at t) o apply_effects (starting_snaps_at t) o apply_effects (instant_snaps_at t)) M = apply_effects (happ_at plan_happ_seq t) M"
  apply (subst comp_assoc)
  apply (subst app_start_instant_dist[THEN ext])
  apply (rule prop_state_upd_combine_if)
  subgoal for a b
    using nm_happ_seq unfolding nm_happ_seq_def nm_happ_seq_def by blast
  subgoal unfolding instant_snaps_at_def starting_snaps_at_def ending_snaps_at_def 
    unfolding instant_actions_at_def starting_actions_at_def ending_actions_at_def
    unfolding action_happening_case_defs
    apply (rule equalityI)
     apply blast
    apply (rule subsetI)
    subgoal for b
      apply (drule in_happ_atD)
      apply (erule in_happ_seqE[simplified plan_happ_seq_def[symmetric]])
      subgoal for a t' d
        apply (erule subst)
        apply (erule ssubst)
       apply (frule at_start_in_happ_seqI)
        using acts_in_prob
        by fast
      subgoal for a t' d
        apply (erule subst)
        apply (erule ssubst)
       apply (frule at_end_in_happ_seqI)
        using acts_in_prob
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

definition "inst_upd_state i \<equiv> apply_effects (instant_snaps_at (time_index i)) (plan_state_seq i)"

definition "inst_start_upd_state i \<equiv> ((apply_effects (starting_snaps_at (time_index i))) o (apply_effects (instant_snaps_at (time_index i)))) (plan_state_seq i)"

definition "upd_state i \<equiv> apply_effects (happ_at plan_happ_seq (time_index i)) (plan_state_seq i)"

lemma upd_state_conv_inst_start_upd_state:
  "upd_state i = apply_effects (ending_snaps_at (time_index i)) (inst_start_upd_state i)"
  unfolding upd_state_def inst_start_upd_state_def using app_all_dist by simp

lemma state_seq_Suc_is_upd_state:
  assumes "i < length htpl"
  shows "plan_state_seq (Suc i) = upd_state i"
  using plan_state_seq_valid valid_state_sequenceE assms
  unfolding upd_state_def plan_happ_seq_def by blast

lemma no_instant_imp_state_is_inst_upd:
  assumes "instant_snaps_at (time_index i) = {}"
  shows "plan_state_seq i = inst_upd_state i"
  unfolding inst_upd_state_def apply_effects_def
  using assms by blast

lemma pre_sat_by_arbitrary_intermediate_state:
  assumes i: "i < length htpl"
      and t: "t = time_index i"
      and h: "(t, h) \<in> plan_happ_seq"
      and snap: "S \<subseteq> happ_at plan_happ_seq t"
      and h_not_in_S: "h \<notin> S"
      and state: "state = apply_effects S (plan_state_seq i)"
    shows "pre h \<subseteq> state"
proof -
  have "pre h \<subseteq> plan_state_seq i" 
  proof -
    have "h \<in> happ_at plan_happ_seq t" using t h by simp
    thus ?thesis 
      using plan_state_seq_props i t by blast
  qed
  moreover
  have "pre h \<inter> (\<Union>(adds ` S) \<union> \<Union>(dels ` S)) = {}"
  proof -
    {fix b
      assume b: "b \<in> S"
      have happening: "(t, b) \<in> plan_happ_seq" using b snap by blast
      have not_eq: "b \<noteq> h" using h_not_in_S b by blast
      have "\<not>mutex_snap_action h b" using mutex_not_in_same_instant using happening not_eq h by blast
      hence "pre h \<inter> (adds b \<union> dels b) = {}" unfolding mutex_snap_action_def by auto
    }
    thus ?thesis by auto
  qed
  ultimately
  show ?thesis unfolding state apply_effects_def by auto
qed

lemma inv_sat_by_upd_state:
  assumes starting: "is_starting_action t a"
      and a: "a \<in> actions"
      and i: "i < length htpl"
      and t: "t = (time_index i)"
  shows "over_all a \<subseteq> upd_state i"
proof -
  have "over_all a \<subseteq> plan_state_seq (Suc i)"
  proof -
    from starting[THEN is_starting_action_dests(1)] at_start_of_act_in_happ_seq_exD[THEN ex1_implies_ex, THEN exE] a
    obtain d where
      d: "(a, t, d) \<in> ran \<pi>" by blast
    hence "0 \<le> d" using plan_durations by auto
    hence "0 < d" 
    proof -
      { assume "0 = d"
        with d have "(t, at_end a) \<in> plan_happ_seq" using in_happ_seqI plan_happ_seq_def by fastforce
        with starting
        have False using is_starting_action_dests by simp
      }
      thus ?thesis using \<open>0 \<le> d\<close> by fastforce
    qed
    note d = this d

    show ?thesis 
    proof (cases "over_all a = {}")
      case True
      then show ?thesis by simp
    next
      case False
      show ?thesis
      proof (rule subsetI)
        fix p
        assume "p \<in> over_all a"
        hence "p \<in> plan_invs_after t"
          unfolding plan_invs_after_def invs_at_def invs_after_def using d by fastforce
        hence "0 < locked_after t p" using in_invs_after_iff_locked_after by blast
  
        have "Suc i < length htpl"
        proof -
          { assume "i = length htpl - 1"
            with \<open>0 < locked_after t p\<close> t 
            have False using locked_after_final_is_0 by simp
          }
          thus ?thesis using i by fastforce
        qed
  
        have "0 < locked_before (time_index (Suc i)) p" 
          using \<open>0 < locked_after t p\<close> \<open>Suc i < length htpl\<close> locked_after_indexed_timepoint_is_locked_before_Suc t by simp
  
        hence "p \<in> plan_invs_before (time_index (Suc i))" using in_invs_before_iff_locked_before by blast
        hence "p \<in> invs_at plan_inv_seq (time_index (Suc i))"  unfolding plan_invs_before_def by simp
        with plan_state_seq_props \<open>Suc i < length htpl\<close>
        show "p \<in> plan_state_seq (Suc i)" by blast
      qed
    qed
  qed
  thus ?thesis using state_seq_Suc_is_upd_state i by blast
qed

end

end
theory NTA_Temp_Planning_Sem
  imports Temporal_Planning_Base.Temporal_Plans_Theory
          "HOL-Library.Multiset"
begin

lemma GreatestI_time: "P (k::'t::time) \<Longrightarrow> (\<And>y. P y \<Longrightarrow> y \<le> k) \<Longrightarrow> P (Greatest P)"
  apply (rule GreatestI2_order)
  by blast

locale nta_temp_planning = valid_temp_plan_unique_snaps_nso_fluent_mutex_happ_seq_for_some_fluents_and_actions 
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> props actions
    for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::"'proposition set"
    and goal::"'proposition set"
    and \<epsilon>::"'time"
    and \<pi>::"('i, 'action, 'time::time) temp_plan"
    and props::"'proposition set"
    and actions:: "'action set" +
fixes c::'time
assumes c: "0 < c" (* \<epsilon> + c is an initial delta transition. Necessary to not violate clock constraints
                      for mutual exclusivity. *)
begin


subsection \<open>Execution times\<close>
text \<open>These must be characterised w.r.t. some initial delay\<close>

definition pt::"'snap_action \<Rightarrow> ('time \<Rightarrow> 'time \<Rightarrow> bool) \<Rightarrow> 'time \<Rightarrow> 'time" where
"pt a co t \<equiv> if (\<exists>t'. co t' t \<and> (t', a) \<in> plan_happ_seq) 
  then (Greatest (\<lambda>t'. co t' t \<and> (t', a) \<in> plan_happ_seq)) 
  else (Least (\<lambda>t'. \<exists>a. (t', a) \<in> plan_happ_seq) - (\<epsilon> + c))"

abbreviation last_snap_exec::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"last_snap_exec a t \<equiv> pt a (<) t"

definition exec_time::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"exec_time a t \<equiv> (let t' = last_snap_exec a t in t - t')"

abbreviation last_snap_exec'::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"last_snap_exec' a t \<equiv> pt a (\<le>) t"

definition exec_time'::"'snap_action \<Rightarrow> 'time \<Rightarrow> 'time" where
"exec_time' a t \<equiv> (let t' = last_snap_exec' a t in t - t')"

 
lemma a_not_in_b_last_unchanged: "(t, a) \<notin> plan_happ_seq \<Longrightarrow> last_snap_exec' a t = last_snap_exec a t"
proof -
  assume "(t, a) \<notin> plan_happ_seq"
  have 1: "(GREATEST t'. t' < t \<and> (t', a) \<in> plan_happ_seq) = (GREATEST t'. t' \<le> t \<and> (t', a) \<in> plan_happ_seq)"
    if defined: "\<exists>t'\<le>t. (t', a) \<notin> plan_happ_seq"
  proof (rule classical)
    assume "(GREATEST t'. t' < t \<and> (t', a) \<in> plan_happ_seq) \<noteq> (GREATEST t'. t' \<le> t \<and> (t', a) \<in> plan_happ_seq)"
    then have "\<exists>t'. t' \<le> t \<and> \<not>(t' < t) \<and> (t', a) \<in> plan_happ_seq"
      using defined
      by (meson nless_le)
    then have "(t, a) \<in> plan_happ_seq" by auto
    with \<open>(t, a) \<notin> plan_happ_seq\<close>
    have "False" by simp
    thus "(GREATEST t'. t' < t \<and> (t', a) \<in> plan_happ_seq) = (GREATEST t'. t' \<le> t \<and> (t', a) \<in> plan_happ_seq)"
      by blast
  qed
  from \<open>(t, a) \<notin> plan_happ_seq\<close>
  have "(\<exists>t'<t. (t', a) \<in> plan_happ_seq) = (\<exists>t'\<le>t. (t', a) \<in> plan_happ_seq)"
    using nless_le by auto
  with \<open>(t, a) \<notin> plan_happ_seq\<close> 1
  show "last_snap_exec' a t = last_snap_exec a t"
    using pt_def by force
qed

lemma a_not_in_b_exec_time'_unchanged: "(t, a) \<notin> plan_happ_seq \<Longrightarrow> exec_time a t = exec_time' a t"
  using a_not_in_b_last_unchanged unfolding exec_time_def exec_time'_def by simp

lemma a_in_b_last_now: "(t, a) \<in> plan_happ_seq \<Longrightarrow> last_snap_exec' a t = t"
  using pt_def
  by (auto intro: Greatest_equality)

lemma a_in_b_exec_time'_0: "(t, a) \<in> plan_happ_seq \<Longrightarrow> exec_time' a t = 0"
  using a_in_b_last_now unfolding exec_time'_def by simp

lemma subseq_last_snap_exec:
  assumes llen: "(Suc l) < length htpl" 
shows "last_snap_exec a (time_index (Suc l)) = last_snap_exec' a (time_index l)"
proof -

  define t where 
    "t = last_snap_exec a (time_index (Suc l))"    

  define s where
    "s = last_snap_exec' a (time_index l)" 
  
  have cl: "length htpl = card htps" unfolding htpl_def by simp
  
  have tl_ord: "time_index l < time_index (Suc l)" 
    using time_index_strict_sorted_list llen by blast
  
  from t_def consider "\<exists>t'. t' < (time_index (Suc l)) \<and> (t', a) \<in> plan_happ_seq" 
    | "\<not>(\<exists>t'. t' < (time_index (Suc l)) \<and> (t', a) \<in> plan_happ_seq)" by auto
  hence "t = s"
  proof cases
    case 1 
    hence exsl: "Ex (\<lambda>t'. t' < time_index (Suc l) \<and> (t', a) \<in> plan_happ_seq)" (is "Ex ?psl") by blast
    have "\<forall>t'. t' < time_index (Suc l) \<and> (t', a) \<in> plan_happ_seq \<longrightarrow> t' \<le> time_index l"
      using time_index_sorted_list no_actions_between_indexed_timepoints llen
      by fastforce
    moreover
    have "\<forall>t'. t' \<le> time_index l \<and> (t', a) \<in> plan_happ_seq \<longrightarrow> t' < time_index (Suc l)" 
      using time_index_strict_sorted_list no_actions_between_indexed_timepoints llen by fastforce
    ultimately 
    have fa: "\<forall>t'. t' < time_index (Suc l) \<and> (t', a) \<in> plan_happ_seq \<longleftrightarrow> t' \<le> time_index l \<and> (t', a) \<in> plan_happ_seq" by blast
    with 1
    have exl: "Ex (\<lambda>t'. t' \<le> time_index l \<and> (t', a) \<in> plan_happ_seq)" (is "Ex ?pl") by blast
    from fa
    have "Greatest ?psl = Greatest ?pl" by auto
    thus "t = s" unfolding t_def s_def pt_def using exl exsl by auto
  next
    case 2
    hence "\<not> (\<exists>t' \<le> time_index l. (t', a) \<in> plan_happ_seq)" using tl_ord by force
    with 2 t_def[simplified pt_def] s_def[simplified pt_def]
    show ?thesis by auto
  qed
  thus "last_snap_exec a (time_index (Suc l)) = last_snap_exec' a (time_index l)" 
    using s_def t_def by auto
  qed

lemma updated_exec_time_and_next: 
  assumes "Suc l < length htpl"
  shows "exec_time a (time_index (Suc l)) = (exec_time' a (time_index l)) + (time_index (Suc l) - time_index l)"
  using subseq_last_snap_exec[OF assms] exec_time_def exec_time'_def by simp


lemma exec_time_and_separation:
  assumes  a_at_t: "(t, a) \<in> plan_happ_seq"
      and mutex: "mutex_snap_action a b"
    shows "exec_time b t \<ge> \<epsilon> \<and> exec_time b t > 0"
proof (cases "\<exists>u < t. (u, b) \<in> plan_happ_seq")
  case True

  have "\<forall>u. (u, b) \<in> plan_happ_seq \<longrightarrow> \<not> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> t \<noteq> u)" using assms nm_happ_seq 
    unfolding nm_happ_seq_def mutex_snap_action_def[symmetric] by blast

  from a_at_t
  have "t \<in> htps" using a_in_B_iff_t_in_htps unfolding plan_happ_seq_def by fast
  then obtain j where
    j: "t = time_index j"
    "j < card htps" using time_index_img_set by blast
  
  have P_iff: "(\<lambda>t'. t' < t \<and> (t', b) \<in> plan_happ_seq) = (\<lambda>t'. \<exists>i < card htps. time_index i = t' \<and> i < j \<and> (time_index i, b) \<in> plan_happ_seq)" (is "?P = ?P'")
  proof -
    have "(\<lambda>t'. t' < t \<and> (t', b) \<in> plan_happ_seq) = (\<lambda>t'. t' \<in> htps \<and> t' < t \<and> (t', b) \<in> plan_happ_seq)" using a_in_B_iff_t_in_htps unfolding plan_happ_seq_def by fast
    also have "... = (\<lambda>t'. \<exists>i < card htps. time_index i = t' \<and> t' < t \<and> (time_index i, b) \<in> plan_happ_seq)" using time_index_img_set by force
    also have "... = (\<lambda>t'. \<exists>i < card htps. time_index i = t' \<and> i < j \<and> (time_index i, b) \<in> plan_happ_seq)"
      unfolding j(1) 
      using time_index_strict_sorted_set'[where j = j] 
      using time_index_strict_sorted_set[OF _ j(2)] 
      by blast
    finally show ?thesis .
  qed
  
  obtain u where
    u: "u < t"
    "(u, b) \<in> plan_happ_seq"
    using True by blast
  hence "u \<in> htps" using a_in_B_iff_t_in_htps plan_happ_seq_def by fast
  hence "\<exists>i < card htps. i < j \<and> (time_index i, b) \<in> plan_happ_seq" (is "Ex ?P2") using P_iff u by meson
  moreover
  have P2_int: "\<And>x. ?P2 x \<Longrightarrow> x \<le> j" using time_index_sorted_set' by auto
  ultimately
  have P2: "?P2 (Greatest ?P2)" using GreatestI_ex_nat[where P = ?P2] by blast

  have P_1: "?P (time_index (Greatest ?P2))" 
  proof -
    from P2 time_index_strict_sorted_set[OF _ j(2)] 
    show ?thesis unfolding j(1) by blast
  qed
  
  have P_max: "x \<le> time_index (Greatest ?P2)" if assm: "?P x" for x 
  proof -
    from assm P_iff
    have "\<exists>i<card htps. time_index i = x \<and> i < j \<and> (time_index i, b) \<in> plan_happ_seq" by meson
    then
    obtain i where
      i: "?P2 i"
      "x = time_index i" by auto
    moreover
    have "i \<le> Greatest ?P2" using Greatest_le_nat[where P = ?P2] i(1) P2_int by blast
    moreover
    have "Greatest ?P2 < card htps" using P2 ..
    ultimately
    show "x \<le> time_index (Greatest ?P2)" using time_index_sorted_set by blast
  qed

  have "?P (Greatest ?P)" 
    apply (rule GreatestI_time)
     apply (rule P_1)
    using P_max by simp
  moreover
  have 1: "last_snap_exec b t = (GREATEST t'. t' < t \<and> (t', b) \<in> plan_happ_seq)" using True unfolding pt_def by auto
  ultimately
  have b_at_t': "(\<lambda>u. u < t \<and> (u, b) \<in> plan_happ_seq) (last_snap_exec b t)" (is "?t < t \<and> (?t, b) \<in> plan_happ_seq") by auto

  { assume a: "(t, a) \<in> plan_happ_seq" "(?t, b) \<in> plan_happ_seq"

    have nm_cond: "t - ?t < \<epsilon> \<and> ?t - t < \<epsilon> \<and> (a \<noteq> b \<or> t \<noteq> ?t) \<or> (t = ?t \<and> a \<noteq> b) \<longrightarrow> \<not>mutex_snap_action a b" 
      using a nm_happ_seq unfolding nm_happ_seq_def by auto
    hence "mutex_snap_action a b \<longrightarrow> (t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> (a = b \<and> t = ?t)) \<and> (t \<noteq> ?t \<or> a = b)" by auto
    hence "mutex_snap_action a b \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon> \<or> (a = b \<and> t = ?t)" 
          "mutex_snap_action a b \<longrightarrow> (t \<noteq> ?t \<or> a = b)" by auto

    hence "\<not>(\<not>(a \<noteq> b \<or> t \<noteq> ?t) \<or> \<not>mutex_snap_action a b) \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>" by auto
    hence "((a \<noteq> b \<or> t \<noteq> ?t) \<and> mutex_snap_action a b) \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  using a_at_t b_at_t' by blast
    hence "(a \<noteq> b \<or> t \<noteq> ?t) \<and> mutex_snap_action a b \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>"  by blast  
    moreover
    have "a \<noteq> b \<longrightarrow> mutex_snap_action a b" using mutex by blast
    ultimately
    have "a \<noteq> b \<or> (t \<noteq> ?t \<and> mutex_snap_action a b) \<longrightarrow> t - ?t \<ge> \<epsilon> \<or> ?t - t \<ge> \<epsilon>" by blast
    moreover
    have "t \<noteq> ?t" using b_at_t' by auto
    ultimately
    consider "t - ?t \<ge> \<epsilon>" | "?t - t \<ge> \<epsilon>" using mutex by blast
  }
  note c = this
  
  have t: "t > ?t" using b_at_t' by blast
  moreover
  have "\<epsilon> \<ge> 0" using eps_ran less_le_not_le by fastforce
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
  have 1: "time_index 0 \<le> u" if "\<exists>h. (u, h) \<in> plan_happ_seq" for u
  proof -
    have "u \<in> set htpl" using that a_in_B_iff_t_in_htps htps_set_htpl valid_plan_finite unfolding plan_happ_seq_def by fast
    hence "\<exists>i. time_index i = u \<and> i < length htpl" using time_index_img_list by force
    thus "time_index 0 \<le> u" using time_index_sorted_list by blast
  qed
  with a_at_t
  have 2: "time_index 0 \<le> t" by auto
  
  have 3: "Least (\<lambda>t. \<exists>x. (t, x) \<in> plan_happ_seq) = (time_index 0)" 
  proof (rule Least_equality[OF _ 1])
    have "card htps > 0" apply (subst card_gt_0_iff) 
      using a_in_B_iff_t_in_htps a_at_t finite_htps valid_plan_finite unfolding plan_happ_seq_def by fast
    hence "time_index 0 \<in> htps" using time_index_img_set valid_plan_finite vp by blast
    thus "\<exists>x. (time_index 0, x) \<in> plan_happ_seq" using a_in_B_iff_t_in_htps plan_happ_seq_def by fast
  qed

  have "last_snap_exec b t = (LEAST t'. \<exists>x. (t', x) \<in> plan_happ_seq) - (\<epsilon> + c)" using False unfolding pt_def by argo
  from this[simplified 3]
  have "last_snap_exec b t = time_index 0 - (\<epsilon> + c)" .
  hence 4: "t - last_snap_exec b t = \<epsilon> + c + t - time_index 0" by auto
  with 2
  have "0 < c + t - time_index 0" using c by (simp add: add_strict_increasing)
  with 4
  have "\<epsilon> < t - last_snap_exec b t" unfolding 4
    by auto
  thus ?thesis unfolding exec_time_def Let_def using eps_ran
    apply -
    apply (rule conjI)
     apply simp
     by order
qed


lemma exec_time_when_ending:
  assumes a_in_actions: "a \<in> actions"
      and ending: "(t, at_end a) \<in> plan_happ_seq"
      and not_starting: "(t, at_start a) \<notin> plan_happ_seq"
  shows "\<exists>t' d. (a, t', d) \<in> ran \<pi> \<and> exec_time (at_start a) t = d"
proof -
  have "\<exists>!(s,d). (a, s, d) \<in> ran \<pi> \<and> t = s + d" using at_end_of_act_in_happ_seq_exD a_in_actions ending by simp
  then obtain s d where
    sd: "(a, s, d) \<in> ran \<pi>" 
    "t = s + d" by auto
  hence "s \<le> t \<and> (s, at_start a) \<in> plan_happ_seq" 
    unfolding plan_happ_seq_def plan_happ_seq_def 
    using valid_plan_durs(1)unfolding durations_ge_0_def by auto
  hence s: "s < t \<and> (s, at_start a) \<in> plan_happ_seq" using not_starting apply (cases "s < t") by auto
  moreover
  have "t' \<le> s" if "t' < t" "(t', at_start a) \<in> plan_happ_seq" for t'
  proof (rule ccontr)
    assume "\<not> t' \<le> s"
    hence st': "s < t'" by simp
    with that(2)
    obtain d' where
       t'd': "(a, t', d') \<in> ran \<pi>" 
      using at_start_of_act_in_happ_seq_exD a_in_actions unfolding plan_happ_seq_def by blast
    thus False using that st' sd no_self_overlap_spec by force
  qed
  ultimately
  have "(GREATEST s. s < t \<and> (s, at_start a) \<in> plan_happ_seq) = s" unfolding Greatest_def by force
  hence "exec_time (at_start a) t = d" using sd(2) s unfolding exec_time_def pt_def by auto
  thus ?thesis using sd(1) by blast
qed


lemma instant_act_in_happ_seqE:
  assumes a_in_actions: "a \<in> actions"
      and ending: "(t, at_end a) \<in> plan_happ_seq"
      and starting: "(t, at_start a) \<in> plan_happ_seq"
    shows "(a, t, 0) \<in> ran \<pi>"
proof -
  from at_start_of_act_in_happ_seq_exD  assms
  have "\<exists>!ds. (a, t, ds) \<in> ran \<pi>" by blast
  then obtain ds where
    tds: "(a, t, ds) \<in> ran \<pi>"
    "\<forall>d. (a, t, d) \<in> ran \<pi> \<longrightarrow> d = ds" by blast

  have ds_ran: "0 \<le> ds" using plan_durations tds by blast

  from at_end_of_act_in_happ_seq_exD assms
  have "\<exists>!(te, de). (a, te, de) \<in> ran \<pi> \<and> t = te + de" by simp
  then obtain te de where
    tede: "(a, te, de) \<in> ran \<pi>"
    "t = te + de"
    "\<forall>t' d'. (a, t', d') \<in> ran \<pi> \<and> t = t' + d' \<longrightarrow> (t' = te \<and> d' = de)" by blast

  have de_ran: "0 \<le> de" using plan_durations tede by blast

  have "t = te \<and> de = 0" by (metis add_cancel_right_right nso_start_end prod.inject tds(1) tede(1,2))
  thus ?thesis using tede by blast
qed

lemma ending_act_sat_dur_bounds:
  assumes a_in_actions: "a \<in> actions"
      and ending: "is_ending_action t a"
    shows "satisfies_duration_bounds a (exec_time (at_start a) t)"
  using exec_time_when_ending valid_plan_durs(2) assms 
  unfolding is_ending_action_def durations_valid_def by blast

lemma instant_act_sat_dur_bounds:
  assumes a_in_actions: "a \<in> actions"
      and is_instant: "is_instant_action t a"
    shows "satisfies_duration_bounds a 0"
  using valid_plan_durs(2) instant_act_in_happ_seqE assms
  unfolding durations_valid_def is_instant_action_def by blast

lemma exec_time_at_init:
  assumes some_happs: "0 < card htps"
  shows "exec_time b (time_index 0) = \<epsilon> + c"
proof -
  have "\<forall>i < card htps. time_index 0 \<le> time_index i" using time_index_sorted_set by blast
  hence "\<forall>t \<in> htps. time_index 0 \<le> t" using time_index_img_set by force 
  hence "\<not>(\<exists>s \<in> htps. s < time_index 0)" by auto
  hence 1: "\<not>(\<exists>s < time_index 0. \<exists>x. (s, x) \<in> plan_happ_seq)" unfolding plan_happ_seq_def plan_happ_seq_def htps_def by blast
  
  have "time_index 0 \<in> htps" using time_index_img_set using some_happs by blast
  hence "\<exists>x. (time_index 0, x) \<in> plan_happ_seq" unfolding plan_happ_seq_def plan_happ_seq_def unfolding htps_def by blast
  with 1
  have "Least (\<lambda>t'. \<exists>x. (t', x) \<in> plan_happ_seq) = time_index 0"
    apply -
    apply (rule Least_equality)
     apply simp
    by force
  with 1
  show ?thesis unfolding exec_time_def pt_def by (auto simp: Let_def)
qed

lemma action_happening_exec_times: 
  "is_not_happening_action t a \<Longrightarrow> exec_time (at_start a) t = exec_time' (at_start a) t"
  "is_not_happening_action t a \<Longrightarrow> exec_time (at_end a) t = exec_time' (at_end a) t"
  "is_starting_action t a \<Longrightarrow> exec_time (at_end a) t = exec_time' (at_end a) t"
  "is_starting_action t a \<Longrightarrow> exec_time' (at_start a) t = 0"
  "is_ending_action t a \<Longrightarrow> exec_time (at_start a) t = exec_time' (at_start a) t"
  "is_ending_action t a \<Longrightarrow> exec_time' (at_end a) t = 0"
  "is_instant_action t a \<Longrightarrow> exec_time' (at_start a) t = 0"
  "is_instant_action t a \<Longrightarrow> exec_time' (at_end a) t = 0"
  by (intro a_not_in_b_exec_time'_unchanged a_in_b_exec_time'_0, elim action_happening_case_dests)+

end

end
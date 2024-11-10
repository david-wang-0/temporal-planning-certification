theory Temporal_Plans
  imports Base
begin

datatype ('t :: time) lower_bound =
  GT 't |
  GE 't

datatype ('t :: time) upper_bound =
  LT 't |
  LE 't

section \<open>State sequences and happening sequences\<close>

type_synonym 'p state = "'p set"

type_synonym ('p) state_sequence = "nat \<Rightarrow> ('p state)"


text \<open>Invariants\<close>
type_synonym ('p, 't) invariant_sequence = "('t \<times> 'p set) set"

text \<open>An indexed sequence/array (or set)\<close>
type_synonym ('v) indexing = "nat \<Rightarrow> 'v"

locale temp_planning_problem = 
  fixes props::   "'proposition set"
    and actions:: "'action set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<Rightarrow> ('time::time) lower_bound"
    and upper::   "'action  \<Rightarrow> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and p::       "'proposition indexing"
    and act::     "'action indexing"
    and \<epsilon>::       "'time"
  assumes wf_init:  "init \<subseteq> props" 
      and wf_goal:  "goal \<subseteq> props"
      and wf_acts: "let 
          snap_props = \<lambda>s. pre s \<union> adds s \<union> dels s
        in (\<forall>a \<in> actions. 
          snap_props (at_start a) \<subseteq> props
        \<and> snap_props (at_end a) \<subseteq> props
        \<and> over_all a \<subseteq> props)"
      and at_start_inj_on: "inj_on at_start actions"
      and at_end_inj_on:   "inj_on at_end actions"
      and snaps_disj:   "(at_start ` actions) \<inter> (at_end ` actions) = {}"
      and prop_numbering:   "bij_betw p {n. n < card props} props"
      and action_numbering: "bij_betw act {n. n < card actions} actions"
      and some_props:       "card props > 0"
      and some_actions:     "card actions > 0"
      and eps_range:        "0 < \<epsilon>"
begin 

text \<open>Some additional definitions\<close>
definition apply_effects::"'proposition set \<Rightarrow> 'snap_action set \<Rightarrow> 'proposition set" where
"apply_effects M S \<equiv> (M - \<Union>(dels ` S)) \<union> \<Union>(adds ` S)"

definition mutex_snap_action::"'snap_action \<Rightarrow> 'snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  pre a \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  (adds a \<inter> dels b) \<noteq> {} \<or>
  pre b \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b \<inter> dels a) \<noteq> {}
)"

lemma mutex_snap_action_symm: "mutex_snap_action a b \<Longrightarrow> mutex_snap_action b a" 
  unfolding mutex_snap_action_def
  by (erule disjE; blast)+

abbreviation snaps::"'action \<Rightarrow> 'snap_action set" where
"snaps a \<equiv> {at_start a, at_end a}"

definition snap_actions::"'snap_action set" where
"snap_actions \<equiv> (at_start ` actions) \<union> (at_end ` actions)"

text \<open>Useful lemmas about the numberings\<close>

lemma act_inj_on: "inj_on act {n. n < card actions}"
  using action_numbering bij_betw_def by blast

lemmas act_inj_on_spec = act_inj_on[simplified inj_on_def, THEN bspec, THEN bspec, simplified mem_Collect_eq, THEN mp, rotated 2]

lemma act_img_actions: "act ` {n. n < card actions} = actions"
  using action_numbering[simplified bij_betw_def] by simp

lemma a_in_act_iff: "a \<in> actions \<longleftrightarrow> (\<exists>i < card actions. act i = a)"
  using act_img_actions by force

lemma act_pred: fixes P
  shows "(\<forall>a \<in> actions. P a) \<longleftrightarrow> (\<forall>i < card actions. P (act i))"
  using a_in_act_iff by auto

lemma act_dom: "m < card actions \<Longrightarrow> act m \<in> actions" 
  using act_img_actions by blast

lemma p_inj_on: "inj_on p {n. n < card props}"
  using prop_numbering bij_betw_def by blast

lemma p_img_props: "p ` {n. n < card props} = props"
  using prop_numbering[simplified bij_betw_def] by simp

lemma p_in_props_iff: "pr \<in> props \<longleftrightarrow> (\<exists>i < card props. p i = pr)"
  using p_img_props by force

lemma props_pred: fixes P
  shows "(\<forall>pr \<in> props. P pr) \<longleftrightarrow> (\<forall>i < card props. P (p i))"
  using p_in_props_iff by auto

lemma p_dom: "n < card props \<Longrightarrow> p n \<in> props" 
  using p_img_props by blast

end


locale temporal_plan = temp_planning_problem _ _ _ _ _ _ _ _ upper pre
  for upper::   "'action  \<Rightarrow> ('time::time) upper_bound" (* these are redefined to maintain type parameters *)
  and pre::     "'snap_action \<Rightarrow> 'proposition set" +
fixes \<pi>::       "'i \<rightharpoonup> ('action \<times> 'time \<times> 'time)"
begin
  
text \<open>Happening Time Points\<close>
definition htps::"'time set" where
"htps \<equiv> {t |a t d. (a, t, d) \<in> ran \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> ran \<pi>}"

definition htpl::"'time list" where
"htpl = sorted_list_of_set htps"

abbreviation time_index::"nat \<Rightarrow> 'time" where
"time_index \<equiv> ((!) htpl)"

text \<open>Happening Sequences\<close>

definition plan_happ_seq::"('time \<times> 'snap_action) set" where
"plan_happ_seq \<equiv> 
    {(t, at_start a) | a t d. (a, t, d) \<in> ran \<pi>} 
  \<union> {(t + d, at_end a) | a t d. (a, t, d) \<in> ran \<pi>}"

definition happ_at::"('time \<times> 'snap_action) set \<Rightarrow> 'time \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s. (t, s) \<in> B}"

text \<open>Invariants\<close>
definition plan_inv_seq::"('proposition, 'time) invariant_sequence" where
"plan_inv_seq \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('proposition, 'time) invariant_sequence \<Rightarrow> 'time \<Rightarrow> 'proposition set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"


subsubsection \<open>Non-mutex happening sequence\<close>

text \<open>This definition arose from the statement in \<^cite>\<open>Gigante2020\<close>, that every at-start 
snap-action interferes with itself for self-overlap. Therefore, we can assume the same for at-end
snap-actions. Moreover, in their definition of a planning problem, the assumption is made that 
no two actions share snap-actions. at-start(a) \<noteq> at-start(b) and at-start(a) \<noteq> at_end(b) and at-start(a) \<noteq> at-end(a).\<close>
definition nm_happ_seq::"('time \<times> 'snap_action) set \<Rightarrow> bool" where
"nm_happ_seq B \<equiv> 
  \<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> ((a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b) 
    \<and> (a = b \<longrightarrow> t = u))"

subsubsection \<open>Valid state sequence\<close>

definition complete_sequence::"'t set \<Rightarrow> 't indexing \<Rightarrow> bool" where
"complete_sequence T t \<equiv> (\<forall>i. (i < card T) \<longrightarrow> (t i) \<in> T) 
  \<and> (\<forall>s \<in> T. \<exists>i. i < card T \<and> s = t i)"

definition unique_increasing_sequence::"('t :: linorder) set \<Rightarrow> 't indexing \<Rightarrow> bool" where
"unique_increasing_sequence T t \<equiv>
    complete_sequence T t
  \<and> (\<forall>i j. i < j \<and> j < card T \<longrightarrow> (t i) < (t j))"
  
definition valid_state_sequence::"
  'proposition state_sequence 
\<Rightarrow> bool" where
"valid_state_sequence M \<equiv> (
  let 
    t = time_index;
    Inv = plan_inv_seq;
    B = plan_happ_seq
  in
    (\<forall>i. i < length htpl \<longrightarrow> (
      let 
        S = happ_at B (t i);
        pres = \<Union>(pre ` S);
        invs = invs_at Inv (t i)
      in
        apply_effects (M i) S = (M (Suc i))
        \<and> invs \<subseteq> (M i)
        \<and> pres \<subseteq> (M i)
        \<and> nm_happ_seq B
    ))
)"

text \<open>For the definition of a valid plan\<close>

definition no_self_overlap::"bool" where
"no_self_overlap \<equiv> \<not>(\<exists>i j a t d u e. i \<noteq> j
  \<and> i \<in> dom \<pi>
  \<and> j \<in> dom \<pi>
  \<and> Some (a, t, d) = \<pi> i
  \<and> Some (a, u, e) = \<pi> j
  \<and> t \<le> u \<and> u \<le> t + d)"

lemma no_self_overlap_spec:
  assumes no_self_overlap
    "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows
    "\<not>(t \<le> u \<and> u \<le> t + d)"
  using assms 
  unfolding no_self_overlap_def ran_def by force


definition plan_actions_in_problem::bool where
"plan_actions_in_problem \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> a \<in> actions"


definition satisfies_duration_bounds::"'action \<Rightarrow> 'time \<Rightarrow> bool" where
"satisfies_duration_bounds a t \<equiv> 
  let lb = (case (lower a) of 
    GT t' \<Rightarrow> t' < t
  | GE t' \<Rightarrow> t' \<le> t);
  ub = (case (upper a) of 
    LT t' \<Rightarrow> t < t'
  | LE t' \<Rightarrow> t \<le> t')
  in lb \<and> ub
"

definition durations_positive::bool where
"durations_positive \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> 0 < d"

definition durations_valid::bool where
"durations_valid \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> satisfies_duration_bounds a d"

definition valid_plan::"bool" where
"valid_plan \<equiv> \<exists>M. 
    valid_state_sequence M
    \<and> no_self_overlap
    \<and> M 0 = init
    \<and> M (length htpl) = goal
    \<and> plan_actions_in_problem
    \<and> durations_positive
    \<and> durations_valid"

end

context temporal_plan
begin           

definition finite_plan::bool where
"finite_plan \<equiv> finite (dom \<pi>)"

lemma a_in_B_iff_t_in_htps: "(\<exists>a. a \<in> happ_at plan_happ_seq t) \<longleftrightarrow> (t \<in> htps)"
proof
  assume "\<exists>a. a \<in> happ_at plan_happ_seq t"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" using happ_at_def by auto
  thus "t \<in> htps" using plan_happ_seq_def htps_def by auto
next
  assume "t \<in> local.htps"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" using plan_happ_seq_def htps_def by force
  thus "\<exists>a. a \<in> happ_at plan_happ_seq t" using happ_at_def by blast
qed


lemma at_start_in_happ_seqE: 
  assumes in_happ_seq: "(t, at_start a) \<in> plan_happ_seq"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap
      and durations_positive
      and plan_actions_in_problem
  shows "\<exists>!d. (a, t, d) \<in> ran \<pi>"
proof -
  have some_in_ran: "(a, t, SOME x. (a, t, x) \<in> ran \<pi>) \<in> ran \<pi>"
  proof -
    from in_happ_seq[simplified plan_happ_seq_def]
    consider "(t, at_start a) \<in> {(t, at_start a)|a t d. (a, t, d) \<in> ran \<pi>}" 
        | "(t, at_start a) \<in>  {(t + d, at_end a) |a t d. (a, t, d) \<in> ran \<pi>}"
        by blast
    then
    have "\<exists>d. (a, t, d) \<in> ran \<pi>"
    proof cases
      case 1
      with \<open>plan_actions_in_problem\<close>[simplified plan_actions_in_problem_def]
      have "\<exists>a' d. at_start a = at_start a'\<and> (a', t, d) \<in> ran \<pi> \<and> a' \<in> actions" by auto
      with 1 a_in_actions at_start_inj_on[simplified inj_on_def]
      show ?thesis by blast
    next
      case 2
      with \<open>plan_actions_in_problem\<close>[simplified plan_actions_in_problem_def]
      have "\<exists>a' t' d. (t, at_start a) = (t' + d, at_end a') \<and> (a', t', d) \<in> ran \<pi> \<and> a' \<in> actions" by blast
      with 2 a_in_actions snaps_disj
      have False by blast
      thus ?thesis ..
    qed
    thus ?thesis ..
  qed
  moreover
  have "d = (SOME x. (a, t, x) \<in> ran \<pi>)" if d_in_ran: "(a, t, d) \<in> ran \<pi>" for d
  proof -
    from some_in_ran
    obtain e where
      e: "(a, t, e) \<in> ran \<pi>"
      "e = (SOME x. (a, t, x) \<in> ran \<pi>)" by auto
    from e(1) d_in_ran
    obtain i j where
      ij: "\<pi> i = Some (a, t, d)"
      "\<pi> j = Some (a, t, e)" unfolding ran_def by blast
    have "d = e" 
    proof (cases "i = j")
      case True
      then show ?thesis using ij by auto
    next
      case False
      from \<open>durations_positive\<close>[simplified durations_positive_def] d_in_ran e(1)
      consider "t \<le> t + d" | "t \<le> t + e" by fastforce
      hence False 
        apply cases
        using False \<open>no_self_overlap\<close>[simplified no_self_overlap_def] ij 
        by fastforce+
      then show ?thesis by simp
    qed
    with e
    show ?thesis by simp
  qed
  ultimately
  show ?thesis by blast
qed

lemma at_end_in_happ_seqE:
  assumes in_happ_seq: "(s, at_end a) \<in> plan_happ_seq"
      and a_in_actions: "a \<in> actions"
      and no_self_overlap
      and durations_positive
      and plan_actions_in_problem
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
    with \<open>plan_actions_in_problem\<close>[simplified plan_actions_in_problem_def] 
    have "\<exists>a' d. (s, at_end a) = (s, at_start a') \<and> (a', s, d) \<in> ran \<pi> \<and> a' \<in> actions" by blast
    with snaps_disj 1 a_in_actions
    show ?thesis by blast
  next
    case 2
    with \<open>plan_actions_in_problem\<close>[simplified plan_actions_in_problem_def]
    have "\<exists>a' t d. (s, at_end a) = (t + d, at_end a') \<and>(a', t, d) \<in> ran \<pi> \<and> a' \<in> actions" by blast
    with at_end_inj_on[simplified inj_on_def] a_in_actions
    have "\<exists>t d. (a, t, d) \<in> ran \<pi> \<and> s = t + d" by blast
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
      
    with td_in_ran
    obtain i j where
      ij: "\<pi> i = Some (a, t, d)"
      "\<pi> j = Some (a, t', d')" unfolding ran_def by blast
    

    from td_eq_s t'd'_eq_s
    have td_t'd': "t + d = t' + d'" by simp
    show "p = pair"
    proof (cases "i = j")
      case True
      then show ?thesis using pair_def ij t'd'_def td_def by simp
    next
      case False
      consider "t \<le> t'" | "t' \<le> t" by fastforce
      thus ?thesis 
      proof cases
        case 1
        with \<open>durations_positive\<close>[simplified durations_positive_def] t'd'_in_ran td_t'd'
        have "t' \<le> t + d" by force
        with False ij 1
        show ?thesis using \<open>no_self_overlap\<close>[simplified no_self_overlap_def] by force
      next
        case 2
        with \<open>durations_positive\<close>[simplified durations_positive_def] td_in_ran td_t'd'
        have "t \<le> t' + d'" by (metis less_add_same_cancel1 order_less_imp_le)
        with False ij 2
        show ?thesis using \<open>no_self_overlap\<close>[simplified no_self_overlap_def] by force
      qed
    qed
  qed
  ultimately
  show ?thesis apply - by (rule ex1I, auto)
qed

lemma in_happ_seqE:
  assumes in_happ_seq: "(t, snap) \<in> plan_happ_seq"
  shows "\<exists>t d a. (a, t, d) \<in> ran \<pi> \<and> (at_start a = snap \<or> at_end a = snap)"
  using assms unfolding plan_happ_seq_def by blast


lemma finite_htps: 
  assumes "finite_plan"
    shows "finite htps"
proof -
  have 1: "finite ((\<lambda>(a, t, d). t) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). t + d) ` (ran \<pi>))"
    using \<open>finite_plan\<close>[simplified finite_plan_def]
    by (simp add: finite_ran)+
  moreover
  have "(\<lambda>(a, t, d). t) ` (ran \<pi>) = {t |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). t + d) ` (ran \<pi>)  = {t + d |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite htps" unfolding htps_def by auto
qed

find_theorems "sorted_key_list_of_set ?f ?A"

lemma set_htpl_eq_htps: 
  assumes finite_plan
  shows "htps = set htpl" 
  unfolding htpl_def set_sorted_list_of_set[OF finite_htps[OF assms(1)]]
  by blast


lemma time_index_bij_betw_list: "bij_betw time_index {n. n < length htpl} (set htpl)"
  using bij_betw_nth distinct_sorted_list_of_set htpl_def[symmetric] lessThan_def
  by metis

lemma time_index_inj_on_list: "inj_on time_index {n. n < length htpl}" 
  using bij_betw_def time_index_bij_betw_list by blast

lemma time_index_img_list: "time_index ` {n. n < length htpl} = set htpl"
  using time_index_bij_betw_list unfolding bij_betw_def by blast

lemma card_htps_len_htpl: "card htps = length htpl" using htpl_def by simp

lemma time_index_bij_betw_set:
  assumes "finite_plan"
  shows "bij_betw time_index {n. n < card htps} htps"
proof -
  have 3: "distinct htpl" unfolding htpl_def by simp
  show "bij_betw time_index {n. n < card htps} htps"
    apply (subst card_htps_len_htpl)
    apply (subst set_htpl_eq_htps[OF assms])
    using time_index_bij_betw_list
    by blast
qed

lemma time_index_inj_on_set:
  assumes "finite_plan"
  shows "inj_on time_index {n. n < card htps}" 
  using time_index_bij_betw_set[OF assms] bij_betw_def by blast

lemma time_index_img_set:
  assumes "finite_plan"
  shows "time_index ` {n. n < card htps} = htps" 
  using time_index_bij_betw_set[OF assms] unfolding bij_betw_def by blast


find_theorems name: "key*list*of*set"

thm strict_sorted_list_of_set

find_theorems name: "sorted*nth"

lemmas time_index_strict_sorted_list = strict_sorted_list_of_set[of htps, simplified htpl_def[symmetric], THEN sorted_wrt_nth_less]

lemma time_index_strict_mono_on_list: 
  "strict_mono_on {n. n < length htpl} time_index" 
  using time_index_strict_sorted_list unfolding monotone_on_def
  by blast

lemmas time_index_sorted_list = sorted_list_of_set(2)[of htps, simplified htpl_def[symmetric], THEN sorted_nth_mono]


lemma time_index_strict_sorted_list':
  assumes i: "i < length htpl"
      and ti: "time_index i < time_index j"
    shows "i < j"
proof (rule ccontr)
  assume "\<not> i < j"
  hence "j \<le> i" by simp
  hence "time_index j \<le> time_index i" using i time_index_sorted_list by simp
  thus False using ti by simp
qed

lemma time_index_sorted_list':
  assumes i: "i < length htpl"
      and ti: "time_index i \<le> time_index j"
    shows "i \<le> j"
proof (rule ccontr)
  assume "\<not> i \<le> j"
  hence "j < i" by simp
  hence "time_index j < time_index i" using i time_index_strict_sorted_list by simp
  thus False using ti by simp
qed

lemma time_index_mono_on_list:
  "mono_on {n. n < length htpl} time_index" 
  using time_index_sorted_list unfolding monotone_on_def by auto

lemmas time_index_strict_sorted_set = time_index_strict_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set = time_index_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_strict_sorted_set' = time_index_strict_sorted_list'[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set' = time_index_sorted_list'[simplified card_htps_len_htpl[symmetric]]

lemmas time_index_sorted = time_index_sorted_list time_index_sorted_set time_index_strict_sorted_list time_index_strict_sorted_set
  time_index_sorted_list' time_index_sorted_set' time_index_strict_sorted_list' time_index_strict_sorted_set'

lemma no_non_indexed_time_points: 
  assumes a: "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'. (time_index l) < t' \<and> t' < (time_index (Suc l)) \<and> t' \<in> set htpl)"
proof (rule notI)
  assume "\<exists>t'>time_index l. t' < time_index (Suc l) \<and> t' \<in> set htpl"
  with time_index_bij_betw_list
  obtain l' where
    l': "l' < length htpl"
    "time_index l < time_index l'"
    "time_index l' < time_index (Suc l)"
    by (metis in_set_conv_nth)
  hence "l' < (Suc l)"
    by (metis not_less_iff_gr_or_eq time_index_strict_sorted_list)
  moreover
  have "l < l'" using l'
    by (metis Suc_lessD linorder_neqE_nat order_less_asym' a time_index_strict_sorted_list)
  ultimately
  show "False" by simp
qed

lemma no_actions_between_indexed_timepoints: 
  assumes "finite_plan"
    "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'>time_index l. t' < time_index (Suc l) \<and> a \<in> happ_at plan_happ_seq t')"
  using no_non_indexed_time_points[OF assms(2)] 
    a_in_B_iff_t_in_htps finite_htps[OF assms(1)] htpl_def by auto


end

end
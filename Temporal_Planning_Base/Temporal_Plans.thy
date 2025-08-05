theory Temporal_Plans
  imports Base "Difference_Bound_Matrices.DBM"
begin


datatype ('t) lower_bound =
  GT 't |
  GE 't

datatype ('t) upper_bound =
  LT 't |
  LE 't

section \<open>Plan validity\<close>
text \<open>This and similar notions need to be used in multiple places. I formulate this to a 
sufficient level of abstraction.\<close>

type_synonym 'p state = "'p set"

type_synonym 'p state_sequence = "nat \<Rightarrow> ('p state)"

text \<open>Invariants\<close>
type_synonym ('p, 't) invariant_sequence = "('t \<times> 'p set) set"

datatype (action: 'a) snap_action = 
  AtStart 'a |
  AtEnd 'a


text \<open>Temporal plans could be multi-sets, lists or just the range of a partial function. 
It is only necessary that the entries do not have to be unique, because unique entries are a 
consequence of prohibiting self-overlap. I chose a partial function.\<close>
type_synonym ('i, 'a, 't) temp_plan = "'i \<rightharpoonup> ('a \<times> 't \<times> 't)"



section \<open>Characterisation of some ideas surrounding temporal planning\<close>

locale action_defs =
  fixes at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"

text \<open>First, we define things w.r.t. a plan\<close>
locale temp_plan_defs = action_defs at_start at_end over_all lower upper pre adds dels
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set" +
  fixes init::    "'proposition set"
    and goal::    "'proposition set"
    and \<epsilon>::       "'time"
    and \<pi>::       "('i, 'action, 'time) temp_plan"
  assumes eps_ran: "0 \<le> \<epsilon>"
begin

definition "plan_actions \<equiv> {a| a t d. (a, t, d) \<in> ran \<pi>}"

definition apply_effects::"'proposition set \<Rightarrow> 'snap_action set \<Rightarrow> 'proposition set" where
"apply_effects M S \<equiv> (M - \<Union>(dels ` S)) \<union> \<Union>(adds ` S)"

definition htps::"'time set" where
"htps \<equiv> {t |a t d. (a, t, d) \<in> ran \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> ran \<pi>}"

definition htpl::"'time list" where
"htpl = sorted_list_of_set htps"

definition time_index::"nat \<Rightarrow> 'time" where
"time_index \<equiv> ((!) htpl)"

text \<open>Happening Sequences\<close>

definition plan_happ_seq::"('time \<times> 'snap_action) set" where
"plan_happ_seq \<equiv> 
    {(t, at_start a) | a t d. (a, t, d) \<in> ran \<pi>}
  \<union> {(t + d, at_end a) | a t d. (a, t, d) \<in> ran \<pi>}"

abbreviation happ_at::"('time \<times> 'snap_action) set \<Rightarrow> 'time \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s. (t, s) \<in> B}"
    
text \<open>Invariants\<close>
definition plan_inv_seq::"('proposition, 'time) invariant_sequence" where
"plan_inv_seq \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('proposition, 'time) invariant_sequence \<Rightarrow> 'time \<Rightarrow> 'proposition set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"

subsubsection \<open>Mutual exclusivity\<close>

text \<open>We want to define a plan in an abstract manner. This needs to be more abstract.\<close>
definition mutex_snap_action::"'snap_action \<Rightarrow> 'snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  (pre a) \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  ((adds a) \<inter> (dels b)) \<noteq> {} \<or>
  (pre b) \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b) \<inter> (dels a) \<noteq> {}
)"

text \<open>This is the most general formulation of actions not interfering. This considers the tuples in the range 
of the plan to be actions. The contents may be the same (duplicate action/self-overlap), unless this is explicitly
prohibited. Therefore, the mutual exclusivity of actions refers to the index for equivalence of 
actions. We also need to check the case that the same action has a duration of 0.

\<close>
definition mutex_valid_plan::bool where
"mutex_valid_plan \<equiv> (\<forall>i j a ta da b tb db sa sb t u. 
  i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j 
  \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db)
  \<and> (sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da)
  \<and> (sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db)
  \<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
  \<longrightarrow> \<not>mutex_snap_action sa sb)
  \<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))
"

definition mutex_sched where
"mutex_sched a ta da b tb db \<equiv> \<forall>sa t sb u. 
  (sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da)
\<and> (sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db)
\<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
\<longrightarrow> \<not>mutex_snap_action sa sb"

definition mutex_valid_plan_alt::bool where
"mutex_valid_plan_alt \<equiv> (\<forall>i j a ta da b tb db. 
  i \<in> dom \<pi> 
\<and> j \<in> dom \<pi> 
\<and> i \<noteq> j 
\<and> \<pi> i = Some (a, ta, da) 
\<and> \<pi> j = Some (b, tb, db) 
\<longrightarrow> mutex_sched a ta da b tb db)
\<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))"

lemma mutex_valid_plan_eq: "mutex_valid_plan \<longleftrightarrow> mutex_valid_plan_alt"
  unfolding mutex_valid_plan_def mutex_valid_plan_alt_def mutex_sched_def 
  apply (rule iffI; intro conjI)
  by blast+

subsubsection \<open>Valid state sequence\<close>

definition valid_state_sequence::"'proposition state_sequence \<Rightarrow> bool" where
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
        \<and> pres \<subseteq> (M i)))
)"

definition satisfies_duration_bounds::"'action \<Rightarrow> 'time \<Rightarrow> bool" where
"satisfies_duration_bounds a t \<equiv> 
  let lb = (case (lower a) of 
    Some (GT t') \<Rightarrow> t' < t
  | Some (GE t') \<Rightarrow> t' \<le> t
  | None \<Rightarrow> True);
  ub = (case (upper a) of 
    Some (LT t') \<Rightarrow> t < t'
  | Some (LE t') \<Rightarrow> t \<le> t'
  | None \<Rightarrow> True)
  in lb \<and> ub
"
(* An action with a duration of 0 is an instant snap-action. We restrict this to 0 < d for some 
proofs, because of how some automata are constructed. *)
definition durations_ge_0::bool where
"durations_ge_0 \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> 0 \<le> d"


definition durations_valid::bool where
"durations_valid \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> satisfies_duration_bounds a d"

(* The validity of infinite plans is ill-defined. *)

definition finite_plan::bool where
"finite_plan \<equiv> finite (dom \<pi>)"

definition valid_plan::"bool" where
"valid_plan \<equiv> \<exists>M. 
    valid_state_sequence M
    \<and> M 0 = init
    \<and> goal \<subseteq> M (length htpl)
    \<and> durations_ge_0
    \<and> durations_valid
    \<and> mutex_valid_plan
    \<and> finite_plan"


definition no_self_overlap::"bool" where
"no_self_overlap \<equiv> \<not>(\<exists>i j a t d u e. i \<noteq> j
  \<and> i \<in> dom \<pi>
  \<and> j \<in> dom \<pi>
  \<and> Some (a, t, d) = \<pi> i
  \<and> Some (a, u, e) = \<pi> j
  \<and> t \<le> u \<and> u \<le> t + d)"

(* move this *)
definition mutex_valid_plan_inj::bool where
"mutex_valid_plan_inj \<equiv> 
  (\<forall>a ta da b tb db. 
      (a, ta, da) \<in> ran \<pi> 
    \<and> (b, tb, db) \<in> ran \<pi>
    \<and> (a, ta, da) \<noteq> (b, tb, db)
  \<longrightarrow> mutex_sched a ta da b tb db)
\<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))"

definition annotated_action_seq::"('time \<times> 'action snap_action) set" where
"annotated_action_seq \<equiv>                                       
    {(t, AtStart a) | a t d. (a, t, d) \<in> ran \<pi>}
  \<union> {(t + d, AtEnd a) | a t d. (a, t, d) \<in> ran \<pi>}"

abbreviation snap_at::"('time \<times> 'action snap_action) set \<Rightarrow> 'time \<Rightarrow> 'action snap_action set" where
"snap_at B t \<equiv> {s. (t, s) \<in> B}"

fun app_snap::"('snap_action \<Rightarrow> 'proposition set) \<Rightarrow> 'action snap_action \<Rightarrow> 'proposition set" where
"app_snap f (AtStart a) = f (at_start a)" |
"app_snap f (AtEnd a) = f (at_end a)"

definition pre_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"pre_imp x = app_snap pre x"

definition add_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"add_imp x = app_snap adds x"

definition del_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"del_imp x = app_snap dels x"

definition mutex_annotated_action where
"mutex_annotated_action a b = (
  (pre_imp a) \<inter> ((add_imp b) \<union> (del_imp b)) \<noteq> {} \<or>
  ((add_imp a) \<inter> (del_imp b)) \<noteq> {} \<or>
  (pre_imp b) \<inter> ((add_imp a) \<union> (del_imp a)) \<noteq> {} \<or>
  (add_imp b) \<inter> (del_imp a) \<noteq> {}
)"


definition nm_anno_act_seq where
"nm_anno_act_seq \<equiv> let B = annotated_action_seq in 
  (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> (t, a) \<in> B \<and> (u, b) \<in> B
    \<and> (a \<noteq> b \<or> t \<noteq> u) 
  \<longrightarrow> \<not>mutex_annotated_action a b)
  \<and> (\<forall>t a b. (t, a) \<in> B \<and> (t, b) \<in> B \<and> a \<noteq> b \<longrightarrow> \<not>mutex_annotated_action a b)"

text \<open>Rules\<close>


lemma in_happ_atD:
  assumes "x \<in> happ_at B t"
  shows "(t, x) \<in> B"
  using assms by (rule CollectD)

lemma in_happ_atI:
  assumes "(t, x) \<in> B"
  shows "x \<in> happ_at B t"
  using assms by (rule CollectI)

lemma a_in_B_iff_t_in_htps: "(\<exists>a. a \<in> happ_at plan_happ_seq t) \<longleftrightarrow> (t \<in> htps)"
proof
  assume "\<exists>a. a \<in> happ_at plan_happ_seq t"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" unfolding  plan_happ_seq_def by fast
  thus "t \<in> htps" unfolding plan_happ_seq_def htps_def by blast
next
  assume "t \<in> htps"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" unfolding plan_happ_seq_def htps_def by force
  thus "\<exists>a. a \<in> happ_at plan_happ_seq t" by blast
qed

text \<open>If something is in the happening sequence, then there must be an action in the plan.\<close>
lemma in_happ_seqE':
  assumes in_happ_seq: "(time, snap) \<in> plan_happ_seq"
  shows "\<exists>a t d. (a, t, d) \<in> ran \<pi> \<and> (at_start a = snap \<and> time = t \<or> at_end a = snap \<and> time = t + d)"
  using assms unfolding plan_happ_seq_def by blast

lemma in_happ_seqE:
  assumes "(time, snap) \<in> plan_happ_seq"
    and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> at_start a = snap \<Longrightarrow> time = t \<Longrightarrow> thesis"
    and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> at_end a = snap \<Longrightarrow> time = t + d \<Longrightarrow> thesis"
  shows thesis
  using in_happ_seqE' assms by blast

lemma in_happ_seqE_act:
  assumes in_happ_seq: "(time, snap) \<in> plan_happ_seq"
  shows "\<exists>a t d. (a, t, d) \<in> ran \<pi> \<and> (at_start a = snap \<or> at_end a = snap)"
  using assms unfolding plan_happ_seq_def by blast

lemma in_happ_seqI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "(t, at_start a) \<in> plan_happ_seq" "(t + d, at_end a) \<in> plan_happ_seq"
  using assms unfolding plan_happ_seq_def by blast+

lemma htpsE:
  assumes "time \<in> htps"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> time = t \<Longrightarrow> thesis"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> time = t + d \<Longrightarrow> thesis"
  shows thesis 
  using assms unfolding htps_def by blast 

lemma htpsI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "t \<in> htps" "t + d \<in> htps"
  unfolding htps_def using assms by blast+

lemma htps_conv_happ_seq_ex:
  assumes "t \<in> htps"
  shows "\<exists>h. (t, h) \<in> plan_happ_seq"
  using assms
  apply -
  apply (erule htpsE)
  using in_happ_seqI by blast+

lemma happ_seq_conv_htps:
  assumes "(t, h) \<in> plan_happ_seq"
  shows "t \<in> htps"
  using assms 
  apply -
  apply (erule in_happ_seqE)
  using htpsI by blast+
    
lemma time_index_bij_betw_list: "bij_betw time_index {n. n < length htpl} (set htpl)"
  using bij_betw_nth distinct_sorted_list_of_set htpl_def[symmetric] lessThan_def time_index_def
  by metis

lemma time_index_inj_on_list: "inj_on time_index {n. n < length htpl}" 
  using bij_betw_def time_index_bij_betw_list by blast

lemma time_index_img_list: "time_index ` {n. n < length htpl} = set htpl"
  using time_index_bij_betw_list unfolding bij_betw_def by blast

lemma card_htps_len_htpl: "card htps = length htpl" unfolding htpl_def by simp

lemmas time_index_strict_sorted_list = strict_sorted_list_of_set[of htps, simplified htpl_def[symmetric], THEN sorted_wrt_nth_less]

lemma time_index_strict_mono_on_list: 
  "strict_mono_on {n. n < length htpl} time_index" 
  using time_index_strict_sorted_list unfolding monotone_on_def time_index_def
  by blast

lemmas time_index_sorted_list = sorted_list_of_set(2)[of htps, simplified htpl_def[symmetric], THEN sorted_nth_mono]

lemma time_index_strict_sorted_list':
  assumes i: "i < length htpl"
      and ti: "time_index i < time_index j"
    shows "i < j"
proof (rule ccontr)
  assume "\<not> i < j"
  hence "j \<le> i" by simp
  hence "time_index j \<le> time_index i" using i time_index_sorted_list time_index_def by simp
  thus False using ti by simp
qed

lemma time_index_sorted_list':
  assumes i: "i < length htpl"
      and ti: "time_index i \<le> time_index j"
    shows "i \<le> j"
proof (rule ccontr)
  assume "\<not> i \<le> j"
  hence "j < i" by simp
  hence "time_index j < time_index i" using i time_index_strict_sorted_list time_index_def by simp
  thus False using ti by simp
qed

lemma time_index_mono_on_list:
  "mono_on {n. n < length htpl} time_index" 
  using time_index_sorted_list unfolding monotone_on_def time_index_def by auto

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
    unfolding time_index_def
    by (metis in_set_conv_nth)
  
  have "l' < (Suc l)" using l'(1, 3) time_index_strict_sorted_list' by simp
  moreover
  have "l < l'" using l'(2) time_index_strict_sorted_list' a by simp
  ultimately
  show "False" by simp
qed

text \<open> Relating ideas of plan validity\<close>

lemma anno_trans: 
  "pre (at_start a) = pre_imp (AtStart a)"
  "pre (at_end a) = pre_imp (AtEnd a)"
  "adds (at_start a) = add_imp (AtStart a)"
  "adds (at_end a) = add_imp (AtEnd a)"
  "dels (at_start a) = del_imp (AtStart a)"
  "dels (at_end a) = del_imp (AtEnd a)"
  unfolding pre_imp_def add_imp_def del_imp_def by simp+

lemma mutex_trans:
  "mutex_snap_action (at_start a) (at_start b) \<longleftrightarrow> mutex_annotated_action (AtStart a) (AtStart b)"
  "mutex_snap_action (at_start a) (at_end b) \<longleftrightarrow> mutex_annotated_action (AtStart a) (AtEnd b)"
  "mutex_snap_action (at_end a) (at_start b) \<longleftrightarrow> mutex_annotated_action (AtEnd a) (AtStart b)"
  "mutex_snap_action (at_end a) (at_end b) \<longleftrightarrow> mutex_annotated_action (AtEnd a) (AtEnd b)" 
  unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans[symmetric] by blast+
  
lemma inj_mutex_def:
  assumes inj: "inj_on \<pi> (dom \<pi>)"
  shows "mutex_valid_plan = mutex_valid_plan_inj"
proof -
  { fix i j
    assume "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j"
    hence "\<pi> i \<noteq> \<pi> j" using inj unfolding inj_on_def by blast
  } note domD = this
  have ran_dom_P_trans: "i \<in> dom \<pi> \<Longrightarrow> j \<in> dom \<pi> \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<pi> i = Some (a, ta, da) \<Longrightarrow> \<pi> j = Some (b, tb, db) \<Longrightarrow> P a ta da b tb db" 
    if "\<And>a ta da b tb db. (a, ta, da) \<in> ran \<pi> \<Longrightarrow> (b, tb, db) \<in> ran \<pi> \<Longrightarrow> (a, ta, da) \<noteq> (b, tb, db) \<Longrightarrow> P a ta da b tb db" 
    for i j a ta da b tb db P
      apply (drule domD, assumption+)
      apply (frule subst[where P = "\<lambda>x. x \<noteq> \<pi> j"], assumption)
      apply (frule subst[where P = "\<lambda>x. Some (a, ta, da) \<noteq> x" and s = "\<pi> j"], assumption)
      apply (drule ranI[of \<pi>])+
    using that by blast
  
  have "mutex_valid_plan" if "mutex_valid_plan_inj"
    using ran_dom_P_trans[where P = mutex_sched] that 
    unfolding mutex_valid_plan_eq mutex_valid_plan_alt_def mutex_valid_plan_inj_def
    apply -
    apply (rule conjI)
     apply (drule conjunct1)
    by blast+
  moreover
  
  { fix x y 
    assume "x \<in> ran \<pi>" "y \<in> ran \<pi>"  
    moreover
    assume "x \<noteq> y"
    ultimately
    have "\<forall>i j. \<pi> i = Some x \<and> \<pi> j = Some y \<longrightarrow> (i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j)" 
         "\<forall>i j. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> \<pi> i = Some x \<and> \<pi> j = Some y \<longrightarrow> i \<noteq> j" by auto
  } note domI = this
  have dom_ran_P_trans:  "P a ta da b tb db" 
      if sg: "\<And>i j. i \<in> dom \<pi> \<Longrightarrow> j \<in> dom \<pi> \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<pi> i = Some (a, ta, da) \<Longrightarrow> \<pi> j = Some (b, tb, db) \<Longrightarrow> P a ta da b tb db" 
      and as: "(a, ta, da) \<in> ran \<pi>" "(b, tb, db) \<in> ran \<pi>" "(a, ta, da) \<noteq> (b, tb, db)"
    for a ta da b tb db P
  proof -
    from as obtain i j where
      pi: "\<pi> i = Some (a, ta, da)"
      "\<pi> j = Some (b, tb, db)"
      unfolding ran_def by blast
    with domI as
    have ij: "i \<noteq> j" "i \<in> dom \<pi>" "j \<in> dom \<pi>" by presburger+
    with sg pi
    show ?thesis by blast
  qed
  
  have "mutex_valid_plan_inj" if "mutex_valid_plan" using that 
    unfolding mutex_valid_plan_eq mutex_valid_plan_alt_def mutex_valid_plan_inj_def
    using dom_ran_P_trans[where P = mutex_sched] by auto
  ultimately
  show ?thesis by blast
qed
end

locale finite_temp_plan = temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  assumes fp: finite_plan
begin

lemma finite_plan: 
  "finite (dom \<pi>)"
  "finite (ran \<pi>)"
  using fp finite_plan_def finite_ran by auto 
text \<open>Finite happening sequences\<close>

lemma finite_acts_imp_finite_happ_seq: "finite (plan_happ_seq)"
proof -
 have 1: "finite ((\<lambda>(a, t, d). (t, at_start a)) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). (t + d, at_end a)) ` (ran \<pi>))"
   using finite_plan by simp+
  moreover
  have "(\<lambda>(a, t, d). (t, at_start a)) ` (ran \<pi>) = {(t, at_start a) |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). (t + d, at_end a)) ` (ran \<pi>)  = {(t + d, at_end a) |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite plan_happ_seq" unfolding plan_happ_seq_def by auto
qed

lemma finite_happ_seq: "finite plan_happ_seq"
  using finite_acts_imp_finite_happ_seq finite_plan finite_plan_def by blast

text \<open>Indexing of timepoints and such with respect to a finite plan\<close>

lemma finite_htps: "finite htps"
proof -
 have 1: "finite ((\<lambda>(a, t, d). t) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). t + d) ` (ran \<pi>))"
   using finite_plan by simp+
  moreover
  have "(\<lambda>(a, t, d). t) ` (ran \<pi>) = {t |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). t + d) ` (ran \<pi>)  = {t + d |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite htps" unfolding htps_def by auto
qed


lemma htps_set_htpl: "htps = set htpl"
  using finite_htps htpl_def set_sorted_list_of_set[symmetric] by simp

lemma time_index_bij_betw_set: "bij_betw time_index {n. n < card htps} htps"
proof -
  have 3: "distinct htpl" unfolding htpl_def by simp
  show "bij_betw time_index {n. n < card htps} htps"
    using htps_set_htpl
    using time_index_bij_betw_list 
    using card_htps_len_htpl by auto
qed

lemma time_index_inj_on_set: "inj_on time_index {n. n < card htps}" 
  using time_index_bij_betw_set finite_plan bij_betw_def by blast

lemma time_index_img_set:
  "time_index ` {n. n < card htps} = htps" 
  using time_index_bij_betw_set finite_plan unfolding bij_betw_def by blast

lemmas time_index_strict_sorted_set = time_index_strict_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set = time_index_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_strict_sorted_set' = time_index_strict_sorted_list'[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set' = time_index_sorted_list'[simplified card_htps_len_htpl[symmetric]]

lemmas time_index_sorted = time_index_sorted_list time_index_sorted_set time_index_strict_sorted_list time_index_strict_sorted_set
  time_index_sorted_list' time_index_sorted_set' time_index_strict_sorted_list' time_index_strict_sorted_set'

lemma time_indexI_htps:
  assumes "t \<in> htps"
    shows "\<exists>i < card htps. time_index i = t"
  using time_index_img_set assms by force

lemma time_indexI_htpl:    
  assumes "t \<in> set (htpl)"
    shows "\<exists>i < length htpl. time_index i = t"
  using time_index_img_list assms by force

lemma time_index_htplD:
  assumes "i < length htpl"
    shows "time_index i \<in> set htpl" 
  using nth_mem assms unfolding time_index_def by blast

lemma time_index_htpsD:
  assumes "i < length htpl"
    shows "time_index i \<in> htps" 
  using time_index_img_set assms card_htps_len_htpl by auto
  

lemma exists_snaps_at_time_index:
  assumes "i < length htpl"
  shows "\<exists>a. (time_index i, at_start a) \<in> plan_happ_seq \<or> (time_index i, at_end a) \<in> plan_happ_seq"
  apply (insert time_index_htpsD[OF assms])
  apply (erule htpsE)
  subgoal for a t d
    apply (rule exI[of _ a])
    apply (rule disjI1)
    unfolding plan_happ_seq_def by blast
  subgoal for a t d
    apply (rule exI[of _ a])
    apply (rule disjI2)
    unfolding plan_happ_seq_def by blast
  done
lemma snaps_at_time_index_cases:
  assumes "i < length htpl"
    and "\<And>a. (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_snaps_at_time_index by blast

lemma snaps_at_time_index_exhaustive_cases:
  assumes "i < length htpl"
    and "\<And>a. (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<notin> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. (time_index i, at_start a) \<notin> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_snaps_at_time_index by blast
lemma no_actions_between_indexed_timepoints: 
  assumes "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'>time_index l. t' < time_index (Suc l) \<and> a \<in> happ_at plan_happ_seq t')"
  using no_non_indexed_time_points a_in_B_iff_t_in_htps finite_htps assms
  unfolding htpl_def by auto


lemma empty_acts_if_empty_htpl: 
  assumes len: "length htpl = 0"
  shows "card (ran \<pi>) = 0"
proof -
  { assume a: "card (ran \<pi>) \<noteq> 0"
    hence "card (ran \<pi>) > 0" by blast
    hence fr: "finite (ran \<pi>)" using card_ge_0_finite  by blast
    hence "ran \<pi> \<noteq> {}" using card_0_eq a by simp
    hence "\<exists>s. s \<in> ran \<pi>" by auto
    hence "\<exists>x. x \<in> htps" unfolding htps_def by auto
    hence "\<exists>x. x \<in> set htpl" using htps_set_htpl by blast 
    with len
    have False by simp
  }
  thus "card (ran \<pi>) = 0" by blast
qed

lemma empty_acts_if_empty_htpl_finite:
  assumes len: "length htpl = 0"
      and fp: "finite_plan"
    shows "ran \<pi> = {}"
  using assms empty_acts_if_empty_htpl finite_ran finite_plan_def by fastforce

lemma no_actions_after_final_timepoint:
  assumes "0 < length htpl"
    "time_index (length htpl - 1) < t"
  shows "happ_at plan_happ_seq t = {}"
proof -
  { assume "happ_at plan_happ_seq t \<noteq> {}"
    then obtain h where
      "(t, h) \<in> plan_happ_seq"
      "t \<in> htps" using a_in_B_iff_t_in_htps by blast
    hence "t \<in> set htpl" using htps_set_htpl assms by blast
    then obtain l where
      "l < length htpl"
      "time_index l = t" using time_index_img_list by force
    with time_index_sorted_list
    have "t \<le> time_index (length htpl - 1)" using assms time_index_def by auto
    with assms
    have False by simp
  }
  thus ?thesis by blast
qed
end

subsubsection \<open>Plan validity\<close>
text \<open>Plan validity is just a proposition\<close>
locale valid_temp_plan = temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  assumes vp: valid_plan
begin
subsubsection \<open>Finite Plans\<close>

lemma valid_plan_state_seq: "\<exists>M.  valid_state_sequence M \<and> M 0 = init \<and> goal \<subseteq> M (length htpl)"
  and valid_plan_durs: "durations_ge_0" 
    "durations_valid"
  and valid_plan_mutex: "mutex_valid_plan"
  and valid_plan_finite: "finite_plan" using vp unfolding valid_plan_def by blast+

sublocale finite_temp_plan using valid_plan_finite vp 
  by unfold_locales
end

text \<open>Plan validity is equivalent if actions behave equivalently\<close>

locale plan_validity_equivalence = temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> + 
    action_defs at_start' at_end' over_all lower upper pre' adds' dels'
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
    and at_start'::"'action \<Rightarrow> 'snap_action_1"
    and at_end'::  "'action  \<Rightarrow> 'snap_action_1"
    and pre'::     "'snap_action_1 \<Rightarrow> 'proposition set"
    and adds'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and dels'::    "'snap_action_1 \<Rightarrow> 'proposition set"  +
  assumes start_snap_replacement: 
    "\<forall>(a, t, d) \<in> ran \<pi>. pre (at_start a) = pre' (at_start' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. adds (at_start a) = adds' (at_start' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. dels (at_start a) = dels' (at_start' a)"
    and end_snap_replacement:
    "\<forall>(a, t, d) \<in> ran \<pi>. pre (at_end a) = pre' (at_end' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. adds (at_end a) = adds' (at_end' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. dels (at_end a) = dels' (at_end' a)"
begin


sublocale plan2: temp_plan_defs at_start' at_end' over_all lower upper pre' adds' dels' init goal \<epsilon> \<pi>
  by standard

lemma f_transfer_1: 
  assumes "\<forall>(a, t, d) \<in> ran \<pi>. f (at_start a) = f' (at_start' a)"
      and "\<forall>(a, t, d) \<in> ran \<pi>. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f ` happ_at plan_happ_seq t) \<subseteq> \<Union>(f' ` plan2.happ_at plan2.plan_happ_seq t)"
proof (rule subsetI)
  fix x
  assume "x \<in> \<Union> (f ` happ_at plan_happ_seq t)"
  then obtain h where
    x: "x \<in> f h"
    and x_happ: "(t, h) \<in> plan_happ_seq" by blast
  have "\<exists>h. x \<in> f' h \<and> h \<in> plan2.happ_at plan2.plan_happ_seq t" 
    apply (cases rule: in_happ_seqE[OF x_happ])
    using assms x unfolding plan2.plan_happ_seq_def by blast+
  thus "x \<in> \<Union> (f' ` plan2.happ_at plan2.plan_happ_seq t)" by blast
qed

lemma f_transfer_2:
  assumes "\<forall>(a, t, d) \<in> ran \<pi>. f (at_start a) = f' (at_start' a)"
      and "\<forall>(a, t, d) \<in> ran \<pi>. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f' ` plan2.happ_at plan2.plan_happ_seq t) \<subseteq> \<Union>(f ` happ_at plan_happ_seq t)"
proof (rule subsetI)
  fix x
  assume "x \<in> \<Union> (f' ` plan2.happ_at plan2.plan_happ_seq t)"
  then obtain h where
    x: "x \<in> f' h"
    and x_happ: "(t, h) \<in> plan2.plan_happ_seq" by blast
  have "\<exists>h. x \<in> f h \<and> h \<in> happ_at plan_happ_seq t" 
    apply (cases rule: plan2.in_happ_seqE[OF x_happ])
    using assms x unfolding plan_happ_seq_def by blast+
  thus "x \<in> \<Union> (f ` happ_at plan_happ_seq t)" by blast
qed

lemma f_transfer:
  assumes "\<forall>(a, t, d) \<in> ran \<pi>. f (at_start a) = f' (at_start' a)"
      and "\<forall>(a, t, d) \<in> ran \<pi>. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f ` happ_at plan_happ_seq t) = \<Union>(f' ` plan2.happ_at plan2.plan_happ_seq t)"
  apply (rule equalityI) using f_transfer_1[OF assms] f_transfer_2[OF assms] by auto

lemmas pre_transfer = f_transfer[OF start_snap_replacement(1) end_snap_replacement(1)]
lemmas adds_transfer = f_transfer[OF start_snap_replacement(2) end_snap_replacement(2)]
lemmas dels_transfer = f_transfer[OF start_snap_replacement(3) end_snap_replacement(3)]

lemma vss_equiv_if_snaps_functionally_equiv:
  "valid_state_sequence MS \<longleftrightarrow> plan2.valid_state_sequence MS"
  unfolding valid_state_sequence_def plan2.valid_state_sequence_def 
  using adds_transfer dels_transfer pre_transfer 
  unfolding Let_def 
  unfolding apply_effects_def plan2.apply_effects_def
  by simp

lemma in_happ_seq_trans_1:  
  assumes "h \<in> happ_at plan_happ_seq time" 
    shows "\<exists>h' \<in> plan2.happ_at plan2.plan_happ_seq time. pre h = pre' h' \<and> adds h = adds' h' \<and> dels h = dels' h'"
  apply (cases rule: in_happ_seqE[OF assms[simplified]])
  unfolding plan2.plan_happ_seq_def using start_snap_replacement apply blast
  using end_snap_replacement by fastforce

lemma in_happ_seqE1:
  assumes "h \<in> happ_at plan_happ_seq time" 
      and "\<And>h'. h' \<in> plan2.happ_at plan2.plan_happ_seq time \<Longrightarrow> pre h = pre' h' \<Longrightarrow> adds h = adds' h' \<Longrightarrow> dels h = dels' h' \<Longrightarrow> thesis"
    shows thesis
  using in_happ_seq_trans_1 assms by blast

lemma in_happ_seq_trans_2:  
  assumes "h \<in> plan2.happ_at plan2.plan_happ_seq time" 
    shows "\<exists>h' \<in> happ_at plan_happ_seq time. pre h' = pre' h \<and> adds h' = adds' h \<and> dels h' = dels' h"
  apply (rule plan2.in_happ_seqE[OF assms[simplified]])
  unfolding plan_happ_seq_def using start_snap_replacement apply blast
  using end_snap_replacement by fastforce

lemma in_happ_seqE2:  
  assumes "h \<in> plan2.happ_at plan2.plan_happ_seq time" 
      and "\<And>h'. h' \<in> happ_at plan_happ_seq time \<Longrightarrow> pre h' = pre' h \<Longrightarrow> adds h' = adds' h \<Longrightarrow> dels h' = dels' h \<Longrightarrow> thesis"
    shows thesis
  using assms in_happ_seq_trans_2 by blast

lemma mutex_snap_action_equiv:
  assumes a: "\<exists>t d. (a, t, d) \<in> ran \<pi>"
      and b: "\<exists>t d. (b, t, d) \<in> ran \<pi>"
      and h: "h = at_start a \<and> h' = at_start' a \<or> h = at_end a \<and> h' = at_end' a"
      and i: "i = at_start b \<and> i' = at_start' b \<or> i = at_end b \<and> i' = at_end' b"
    shows "mutex_snap_action h i
    \<longleftrightarrow> plan2.mutex_snap_action h' i'"
proof -
  have "pre h = pre' h'" using h a start_snap_replacement end_snap_replacement by auto
  moreover
  have "adds h = adds' h'" using h a start_snap_replacement end_snap_replacement by auto
  moreover 
  have "dels h = dels' h'" using h a start_snap_replacement end_snap_replacement by auto
  moreover
  have "pre i = pre' i'" using i b start_snap_replacement end_snap_replacement by auto
  moreover
  have "adds i = adds' i'" using i b start_snap_replacement end_snap_replacement by auto
  moreover 
  have "dels i = dels' i'" using i b start_snap_replacement end_snap_replacement by auto
  ultimately
  show ?thesis unfolding mutex_snap_action_def plan2.mutex_snap_action_def by simp
qed

lemma mutex_valid_plan_equiv_if_snaps_functionally_equiv:
  "mutex_valid_plan
\<longleftrightarrow> plan2.mutex_valid_plan"
proof -
  have "(\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a))
    \<longleftrightarrow> (\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> plan2.mutex_snap_action (at_start' a) (at_end' a))"
    using mutex_snap_action_equiv by fast
  moreover
  have "mutex_sched a ta da b tb db \<longleftrightarrow> plan2.mutex_sched a ta da b tb db" if 
    "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" 
    "\<pi> i = Some (a, ta, da)" 
    "\<pi> j = Some (b, tb, db)" for i j a ta da b tb db
   proof -
     have ab_ran: "\<exists>t d. (a, t, d) \<in> ran \<pi>" "\<exists>t d. (b, t, d) \<in> ran \<pi>" 
       using that ranI by fast+
    show ?thesis 
         proof 
      assume as: "mutex_sched a ta da b tb db"
      have "\<not> plan2.mutex_snap_action sa sb" 
        if "sa = at_start' a \<and> t = ta \<or> sa = at_end' a \<and> t = ta + da" 
           "sb = at_start' b \<and> u = tb \<or> sb = at_end' b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start' a \<and> t = ta" "sb = at_start' b \<and> u = tb" |
          "sa = at_start' a \<and> t = ta" "sb = at_end' b \<and> u = tb + db" | 
          "sa = at_end' a \<and> t = ta + da" "sb = at_start' b \<and> u = tb" |
          "sa = at_end' a \<and> t = ta + da" "sb = at_end' b \<and> u = tb + db" by argo
        thus ?thesis
        proof (cases)
          case 1
          with t as
          have "\<not>mutex_snap_action (at_start a) (at_start b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 1 by auto
        next
          case 2
          with t as
          have "\<not>mutex_snap_action (at_start a) (at_end b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 2 by auto
        next
          case 3
          with t as
          have "\<not>mutex_snap_action (at_end a) (at_start b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 3 by auto
        next
          case 4
          with t as
          have "\<not>mutex_snap_action (at_end a) (at_end b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 4 by auto
        qed
      qed
      thus "plan2.mutex_sched a ta da b tb db" 
        unfolding plan2.mutex_sched_def by blast
    next
      assume as: "plan2.mutex_sched a ta da b tb db"
      have "\<not> mutex_snap_action sa sb" 
        if "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da" 
           "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start a \<and> t = ta" "sb = at_start b \<and> u = tb" |
          "sa = at_start a \<and> t = ta" "sb = at_end b \<and> u = tb + db" | 
          "sa = at_end a \<and> t = ta + da" "sb = at_start b \<and> u = tb" |
          "sa = at_end a \<and> t = ta + da" "sb = at_end b \<and> u = tb + db" by argo
        thus ?thesis
        proof (cases)
          case 1
          with t as
          have "\<not>plan2.mutex_snap_action (at_start' a) (at_start' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 1 by auto
        next
          case 2
          with t as
          have "\<not>plan2.mutex_snap_action (at_start' a) (at_end' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 2 by auto
        next
          case 3
          with t as
          have "\<not>plan2.mutex_snap_action (at_end' a) (at_start' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 3 by auto
        next
          case 4
          with t as
          have "\<not>plan2.mutex_snap_action (at_end' a) (at_end' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 4 by auto
        qed
      qed
      thus "mutex_sched a ta da b tb db" 
        unfolding mutex_sched_def by blast
    qed
  qed
  hence "(\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched a ta da b tb db) 
  \<longleftrightarrow> (\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> plan2.mutex_sched a ta da b tb db)" by blast
  ultimately
  show ?thesis unfolding mutex_valid_plan_eq mutex_valid_plan_alt_def plan2.mutex_valid_plan_eq plan2.mutex_valid_plan_alt_def by argo
qed

lemma valid_plan_equiv_if_snaps_functionally_equiv:
  "valid_plan \<longleftrightarrow> plan2.valid_plan"
  unfolding valid_plan_def plan2.valid_plan_def
  using vss_equiv_if_snaps_functionally_equiv mutex_valid_plan_equiv_if_snaps_functionally_equiv
  by simp
end

text \<open>If there is no self overlap, then the mutex condition can be asserted on the annotated action sequence\<close>
locale no_self_overlap_temp_plan = temp_plan_defs +
  assumes nso: "no_self_overlap"
begin 
  
lemma no_self_overlap_spec:
  assumes "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows
    "\<not>(t \<le> u \<and> u \<le> t + d)"
  using assms nso
  unfolding no_self_overlap_def ran_def by force

lemma no_self_overlap_ran:
  assumes "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows
    "(t > u \<or> u > t + d)"
  using no_self_overlap_spec[OF assms] by fastforce
end



locale no_self_overlap_and_dur_ge0_temp_plan = 
  no_self_overlap_temp_plan +
  assumes dg0: durations_ge_0
begin

lemma nso_double_act_spec:
  assumes a: "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows "u + e < t \<or> t + d < u"
proof -
  from no_self_overlap_ran[OF a(1)] no_self_overlap_ran[OF a(2)] a
  have "u < t \<or> t + d < u" "t < u \<or> u + e < t" by blast+
  thus ?thesis by auto
qed

lemma nso_no_double_sched:
  assumes a: "(a, t, d) \<in> ran \<pi>"
    "(a, t, e) \<in> ran \<pi>"
  shows "d = e"
proof -
  from nso_double_act_spec assms
  have "d \<noteq> e \<Longrightarrow> t + e < t \<or> t + d < t" by blast
  with dg0[simplified durations_ge_0_def] a
  show ?thesis by force
qed

lemma nso_no_double_start:
  assumes a: "(a, t, d) \<in> ran \<pi>"
           "(b, t, e) \<in> ran \<pi>"
    and "(a, t, d) \<noteq> (b, t, e)"
  shows "a \<noteq> b"
  using assms nso_no_double_sched by blast

lemma nso_start_end:
  assumes a: "(a, t, d) \<in> ran \<pi>"
           "(b, s, e) \<in> ran \<pi>"
           "(a, t, d) \<noteq> (b, s, e)"
           "t = s + e"
  shows "a \<noteq> b"
proof 
  assume e: "a = b"
  hence "t \<noteq> s \<or> d \<noteq> e" using a by blast
  hence "t + d < s" using nso_double_act_spec[OF a(1) a(2)[simplified e[symmetric]]] a(4) by blast
  moreover
  have "0 \<le> e" "0 \<le> d" using dg0[simplified durations_ge_0_def] a(1,2) by auto
  ultimately
  show False using \<open>t = s + e\<close>
    apply (cases "e \<le> 0") 
    subgoal by auto 
    using linorder_not_less by fastforce
qed

lemma nso_ends:
  assumes  a: "(a, t, d) \<in> ran \<pi>"
           "(b, s, e) \<in> ran \<pi>"
           "(a, t, d) \<noteq> (b, s, e)"
           "t + d = s + e"
  shows "a \<noteq> b"
proof 
  assume e: "a = b"
  have ed: "0 \<le> e" "0 \<le> d" using dg0[simplified durations_ge_0_def] a(1,2) by auto
  moreover
  have "t \<noteq> s \<or> d \<noteq> e" using a e by blast
  then consider "s + e < t" | "t + d < s" 
    using nso_double_act_spec[OF a(1) a(2)[simplified e[symmetric]]] a(4) by blast
  hence "s + e < t + d \<or> t + d < s + e" apply (cases) using ed 
    by (simp add: add.commute add_strict_increasing2)+
  thus False using \<open>t + d = s + e\<close> by simp
qed

lemma nso_imp_inj:
  shows "inj_on \<pi> (dom \<pi>)"
proof -
{ fix i j
    assume i: "i \<in> dom \<pi>" and j: "j \<in> dom \<pi>"
    assume ij: "i \<noteq> j"
    obtain a ta da b tb db where
      pi: "\<pi> i = Some (a, ta, da)"
      "\<pi> j = Some (b, tb, db)"
      using i j by auto
    hence ij_ran: "(a, ta, da) \<in> ran \<pi>"
          "(b, tb, db) \<in> ran \<pi>" 
      by (auto intro: ranI)
    { assume "a = b"
      hence ab: "\<not>(ta \<le> tb \<and> tb \<le> ta + da)"
        and ba: "\<not>(tb \<le> ta \<and> ta \<le> tb + db)" using pi i j ij nso[simplified no_self_overlap_def] 
        by metis+
      consider "tb < ta" | "ta + da < tb" using ab by fastforce
      note lt_case1 = this
      consider "ta < tb" | "tb + db < ta" using ba by fastforce
      note lt_case2 = this
      have "ta \<noteq> tb"
        apply (cases rule: lt_case1; cases rule: lt_case2)
        using dg0[simplified durations_ge_0_def] ij_ran by force+
      }
    with pi
    have "\<pi> i \<noteq> \<pi> j" by auto
  } 
  thus ?thesis unfolding inj_on_def by blast
qed



lemma nso_mutex_eq_nm_anno_act_seq: "mutex_valid_plan \<longleftrightarrow> nm_anno_act_seq"
proof -
  have "mutex_valid_plan_inj \<longleftrightarrow> nm_anno_act_seq"
  proof
    assume mvp: mutex_valid_plan_inj
    have "\<not>mutex_annotated_action a b"
      if ne: "a \<noteq> b \<or> t \<noteq> u" and tu: "t - u < \<epsilon> \<and> u - t < \<epsilon>" 
      and a: "(t, a) \<in> annotated_action_seq" 
      and b: "(u, b) \<in> annotated_action_seq" for a b t u
    proof -
      consider aa ab where "a = AtStart aa" "b = AtStart ab"
        | aa ab where "a = AtStart aa" "b = AtEnd ab"
        | aa ab where "a = AtEnd aa" "b = AtStart ab"
        | aa ab where "a = AtEnd aa" "b = AtEnd ab" 
        by (cases a; cases b; blast)
      thus "\<not>mutex_annotated_action a b" 
      proof cases
        case 1
        with a b
        obtain da db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, u, db) \<in> ran \<pi>" unfolding annotated_action_seq_def by blast 
        have "(aa, t, da) \<noteq> (ab, u, db)" using ne 1 by blast
        hence "mutex_sched aa t da ab u db" using ta tb mvp unfolding mutex_valid_plan_inj_def by blast
        from this[simplified mutex_sched_def] tu
        have "\<not>mutex_snap_action (at_start aa) (at_start ab)" by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 1 .
      next
        case 2
        with a b
        obtain da tb db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, tb, db) \<in> ran \<pi>" "tb + db = u"
          unfolding annotated_action_seq_def by blast
        
        hence da: "0 \<le> da" and db: "0 \<le> db" using dg0 unfolding durations_ge_0_def by blast+
        show ?thesis
        proof (cases "(aa, t, da) = (ab, tb, db)")
          case True
          hence "da < \<epsilon>" using tb(2) tu by auto
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          thus ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa t da ab tb db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" unfolding mutex_sched_def using tu tb(2) by blast
          then show ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 3
        with a b
        obtain ta da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "ta + da = t"
          and tb: "(ab, u, db) \<in> ran \<pi>" 
          unfolding annotated_action_seq_def by fast
        
        show ?thesis
        proof (cases "(aa, ta, da) = (ab, u, db)")
          case True
          hence "da < \<epsilon>" using ta(2) tu by auto
          hence "\<not>mutex_snap_action (at_start aa) (at_end aa)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)"
            using True unfolding mutex_snap_action_def by auto
          thus ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa ta da ab u db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)" unfolding mutex_sched_def using tu ta(2) by blast
          then show ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 4
        with a b
        obtain ta tb da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "t = ta + da"
          and tb: "(ab, tb, db) \<in> ran \<pi>" "u = tb + db" unfolding annotated_action_seq_def by blast 
        hence "(aa, ta, da) \<noteq> (ab, tb, db)" using ne 4 by blast
        hence "mutex_sched aa ta da ab tb db" using ta tb mvp unfolding mutex_valid_plan_inj_def by blast
        hence "\<not>mutex_snap_action (at_end aa) (at_end ab)" unfolding mutex_sched_def using tu ta(2) tb(2) by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 4 by blast
      qed
    qed
    moreover
    have "\<not>mutex_annotated_action a b" 
      if a: "(t, a) \<in> annotated_action_seq" 
      and b: "(t, b) \<in> annotated_action_seq" 
      and ne: "a \<noteq> b" for t a b
    proof -
      consider aa ab where "a = AtStart aa" "b = AtStart ab"
        | aa ab where "a = AtStart aa" "b = AtEnd ab"
        | aa ab where "a = AtEnd aa" "b = AtStart ab"
        | aa ab where "a = AtEnd aa" "b = AtEnd ab" 
        by (cases a; cases b; blast)
      thus "\<not>mutex_annotated_action a b" 
      proof cases
        case 1
        with a b
        obtain da db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, t, db) \<in> ran \<pi>" unfolding annotated_action_seq_def by blast 
        hence "mutex_sched aa t da ab t db" using 1 mvp ne unfolding mutex_valid_plan_inj_def by blast
        from this[simplified mutex_sched_def] 
        have "\<not>mutex_snap_action (at_start aa) (at_start ab)" by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 1 by simp
      next
        case 2
        with a b
        obtain da tb db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, tb, db) \<in> ran \<pi>" "tb + db = t"
          unfolding annotated_action_seq_def by blast
        
        hence da: "0 \<le> da" and db: "0 \<le> db" using dg0 unfolding durations_ge_0_def by blast+
        show ?thesis
        proof (cases "(aa, t, da) = (ab, tb, db)")
          case True
          hence "da = 0" using tb(2) by simp
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          thus ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa t da ab tb db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" unfolding mutex_sched_def using tb(2) by blast
          then show ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 3
        with a b
        obtain ta da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "ta + da = t"
          and tb: "(ab, t, db) \<in> ran \<pi>" 
          unfolding annotated_action_seq_def by fast
        
        show ?thesis
        proof (cases "(aa, ta, da) = (ab, t, db)")
          case True
          hence "da = 0" using ta(2) by auto
          hence "\<not>mutex_snap_action (at_start aa) (at_end aa)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)"
            using True unfolding mutex_snap_action_def by auto
          thus ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa ta da ab t db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)" unfolding mutex_sched_def using ta(2) by blast
          then show ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 4
        with a b
        obtain ta tb da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "t = ta + da"
          and tb: "(ab, tb, db) \<in> ran \<pi>" "t = tb + db" unfolding annotated_action_seq_def by blast 
        have "aa \<noteq> ab" using ne 4 by blast
        hence "mutex_sched aa ta da ab tb db" using ta tb mvp unfolding mutex_valid_plan_inj_def by blast
        hence "\<not>mutex_snap_action (at_end aa) (at_end ab)" unfolding mutex_sched_def using ta(2) tb(2) by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 4 by blast
      qed
    qed
    ultimately
    show "nm_anno_act_seq" unfolding nm_anno_act_seq_def by (auto simp: Let_def)
  next
    assume naas: "nm_anno_act_seq"
    have "mutex_sched a ta da b tb db"
      if a: "(a, ta, da) \<in> ran \<pi>"
      and b: "(b, tb, db) \<in> ran \<pi>"
      and ne: "(a, ta, da) \<noteq> (b, tb, db)"
    for a ta da b tb db
    proof -
      
      from a b
      have aas: "(ta, AtStart a) \<in> annotated_action_seq" 
           "(tb, AtStart b) \<in> annotated_action_seq"
           "(ta + da, AtEnd a) \<in> annotated_action_seq" 
           "(tb + db, AtEnd b) \<in> annotated_action_seq" 
        unfolding annotated_action_seq_def by blast+


      have dadb: "0 \<le> da \<and> 0 \<le> db" using dg0 a b unfolding durations_ge_0_def by blast
    
      have "\<not>mutex_snap_action sa sb" 
        if sa:  "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da"
        and sb: "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db"
        and tu: "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for t u sa sb
      proof -
        { assume "ta - tb < \<epsilon> \<and> tb - ta < \<epsilon> \<or> ta = tb"
          then consider "ta - tb < \<epsilon> \<and> tb - ta < \<epsilon>" | "ta = tb" by blast
          hence "\<not>mutex_annotated_action (AtStart a) (AtStart b)" 
          proof cases
            case 1
            have "a \<noteq> b \<or> ta \<noteq> tb"
            proof (cases "a = b")
              case True
              hence "ta + da < tb \<or> tb + db < ta" using ne nso_double_act_spec nso dg0 a b by blast
              thus "a \<noteq> b \<or> ta \<noteq> tb" using dadb by auto
            qed simp
            thus ?thesis using 1 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with nso_no_double_start nso dg0 a b ne
            have "a \<noteq> b" by blast
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_start a) (at_start b)" using mutex_trans by simp
        } moreover
        { assume "ta - (tb + db) < \<epsilon> \<and> (tb + db) - ta < \<epsilon> \<or> ta = (tb + db)"
          then consider "ta - (tb + db) < \<epsilon> \<and> (tb + db) - ta < \<epsilon>" | "ta = tb + db " by blast
          hence "\<not>mutex_annotated_action (AtStart a) (AtEnd b)" 
          proof cases
            case 1
            thus ?thesis using aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with  nso dg0 a b ne
            have "a \<noteq> b" using nso_start_end by blast
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_start a) (at_end b)" using mutex_trans by blast
        } moreover
        { assume "(ta + da) - tb < \<epsilon> \<and> tb - (ta + da) < \<epsilon> \<or> (ta + da) = tb"
          then consider "(ta + da) - tb < \<epsilon> \<and> tb - (ta + da) < \<epsilon>" | "tb = (ta + da)" by blast
          hence "\<not>mutex_annotated_action (AtEnd a) (AtStart b)" 
          proof cases
            case 1
            thus ?thesis using 1 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with  nso dg0 a b ne
            have "a \<noteq> b" using nso_start_end by metis
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_end a) (at_start b)" using mutex_trans by blast
        } moreover
        { assume "(ta + da) - (tb + db) < \<epsilon> \<and> (tb + db) - (ta + da) < \<epsilon> \<or> (ta + da) = (tb + db)"
          then consider "(ta + da) - (tb + db) < \<epsilon> \<and> (tb + db) - (ta + da) < \<epsilon>" | "(tb + db) = (ta + da)" by argo
          hence "\<not>mutex_annotated_action (AtEnd a) (AtEnd b)" 
          proof cases
            case 1
            have "a \<noteq> b \<or> (ta + da) \<noteq> (tb + db)"
            proof (cases "a = b")
              case True
              hence "ta + da < tb \<or> tb + db < ta" using ne nso_double_act_spec nso dg0 a b by blast
              then consider "ta + da < tb" | "tb + db < ta" by auto
              hence "ta + da < tb + db \<or> tb + db < ta + da" 
                apply (cases) using dadb 
                by (metis add_less_same_cancel1 leD linorder_cases)+
              thus "a \<noteq> b \<or> (ta + da) \<noteq> (tb + db)" using dadb by auto
            qed simp
            thus ?thesis using 1 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with  nso dg0 a b ne
            have "a \<noteq> b" using nso_ends by metis
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_end a) (at_end b)" using mutex_trans by blast
        } ultimately
        show ?thesis using sa sb tu by fast
      qed
      thus ?thesis unfolding mutex_sched_def by blast
    qed
    moreover
    have "\<not>mutex_snap_action (at_start a) (at_end a)" 
      if "(a, t, d)\<in>ran \<pi>" "d = 0 \<or> d < \<epsilon>" for a t d
    proof -
      from that
      have as: "(t, AtStart a) \<in> annotated_action_seq"
           "(t + d, AtEnd a) \<in> annotated_action_seq" 
        unfolding annotated_action_seq_def by auto
      from that
      consider "d = 0" | "d < \<epsilon>" by blast
      hence "\<not>mutex_annotated_action (AtStart a) (AtEnd a)"
      proof cases
        case 1
        with as 
        have "AtStart a \<noteq> AtEnd a" "(t, AtStart a) \<in> annotated_action_seq" "(t, AtEnd a) \<in> annotated_action_seq" by auto
        thus ?thesis using naas unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      next
        case 2  
        moreover
        have "0 \<le> d" using that dg0 unfolding durations_ge_0_def by blast
        hence 1: "t - (t + d) < \<epsilon> \<and> (t + d) - t < \<epsilon>" using 2 
          by (metis add_cancel_right_right add_diff_cancel_left' add_strict_increasing2 diff_less_eq eps_ran less_add_same_cancel1 nless_le)
        from naas[simplified nm_anno_act_seq_def]
        have "\<And>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<Longrightarrow> (t, a) \<in> local.annotated_action_seq \<and> (u, b) \<in> local.annotated_action_seq \<and> (a = b \<longrightarrow> t \<noteq> u) \<longrightarrow> \<not> local.mutex_annotated_action a b" by (auto simp: Let_def)
        from this[OF 1]
        show ?thesis using as by blast
      qed
      thus ?thesis using mutex_trans by blast
    qed
    ultimately
    show mutex_valid_plan_inj unfolding mutex_valid_plan_inj_def by blast
  qed
  thus ?thesis using nso_imp_inj inj_mutex_def by blast
qed

 (*  lemma at_start_in_happ_seqE: 
    assumes in_happ_seq: "(s, at_start a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> plan_actions"
        and dg0: durations_ge_0
        and nso: no_self_overlap
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  proof (rule ex_ex1I)
    from in_happ_seq in_happ_seqE'
    have "\<exists>(a', t, d) \<in> ran \<pi>. (at_start a' = at_start a \<and> s = t \<or> at_end a' = at_start a \<and> s = t + d)"
      by blast
    with snaps_disj a_in_actions plan_actions_def
    have "\<exists>(a', t, d) \<in> ran \<pi>. at_start a' = at_start a \<and> s = t" by fast
    moreover
    have "\<forall>(a', t, d) \<in> ran \<pi>. at_start a = at_start a' \<longrightarrow> a = a'" 
      using at_start_inj_on a_in_actions plan_actions_def unfolding inj_on_def by blast
    ultimately
    show "\<exists>x. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t" by auto
  next
    have "t = t' \<and> d = d'" 
         if "(a, t, d) \<in> ran \<pi> \<and> s = t" 
        and "(a, t', d') \<in> ran \<pi> \<and> s = t'" for t d t' d'
      using that nso dg0 nso_no_double_start 
    thus "\<And>x y. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> case y of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> x = y" by blast
  qed

  lemma at_end_in_happ_seqE:
    assumes in_happ_seq: "(s, at_end a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> domain"
        and nso: "no_self_overlap"
        and dp: "durations_ge_0"
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
      with a_in_actions domain
      have "\<exists>a' d. (s, at_end a) = (s, at_start a') \<and> (a', s, d) \<in> ran \<pi> \<and> a' \<in> domain" by blast
      with snaps_disj 1 a_in_actions
      show ?thesis by blast
    next
      case 2
      with a_in_actions
      have "\<exists>a' t d. (s, at_end a) = (t + d, at_end a') \<and>(a', t, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" by blast
      with at_end_inj[simplified inj_on_def] a_in_actions domain
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
  
      from td_eq_s t'd'_eq_s
      have td_t'd': "t + d = t' + d'" by simp
      with nso_ends[OF nso dp td_in_ran t'd'_in_ran]
      have "t = t'" "d = d'" by blast+
      thus "p = pair" using t'd'_def td_def by simp
    qed
    ultimately
    show ?thesis apply - by (rule ex1I, auto)
  qed
 *)
end

locale unique_snaps_temp_plan = temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  assumes at_start_inj_on:  "inj_on at_start plan_actions"
      and at_end_inj_on:      "inj_on at_end plan_actions"
      and snaps_disj:         "(at_start ` plan_actions) \<inter> (at_end ` plan_actions) = {}"
begin 

subsubsection \<open>Non-Interference w.r.t the Happening Sequence\<close>


text \<open>This definition comes from the statement in \<^cite>\<open>gigante_decidability_2022\<close>, that every at-start 
snap-action interferes with itself for self-overlap. Therefore, we can assume the same for at-end
snap-actions. Moreover, in their definition of a planning problem, the assumption is made that 
no two actions share snap-actions. at-start(a) \<noteq> at-start(b) and at-start(a) \<noteq> at_end(b) and at-start(a) \<noteq> at-end(a).\<close>

definition nm_happ_seq::"('time \<times> 'snap_action) set \<Rightarrow> bool" where
"nm_happ_seq B \<equiv> 
  (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u
    \<and> (a \<noteq> b \<or> t \<noteq> u) \<longrightarrow> \<not>mutex_snap_action a b)
  \<and> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"

text \<open>Non-zero- vs. epsilon-separation for mutually exclusive snap actions\<close>
lemma eps_zero_imp_zero_sep: 
  assumes "\<epsilon> = 0"
  shows "nm_happ_seq B = (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)" 
  using assms unfolding nm_happ_seq_def by fastforce

lemma eps_gt_zero_imp_eps_sep:
  assumes "0 < \<epsilon>"
  shows "nm_happ_seq B = (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u
    \<and> (a \<noteq> b \<or> t \<noteq> u) \<longrightarrow> \<not>mutex_snap_action a b)"
proof -
  from assms
  have "(\<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> (a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)) \<Longrightarrow> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"
    by force
  thus ?thesis unfolding nm_happ_seq_def using assms by blast
qed
end

locale unique_snaps_and_dg0_temp_plan = unique_snaps_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  assumes dg0: durations_ge_0
begin

text \<open>If snap actions are uniquely identifiable, then the mutex condition on the happening sequence
is the same as that asserted on the annotated action sequence\<close>
lemma nm_anno_act_seq_eq_nm_happ_seq: "nm_anno_act_seq \<longleftrightarrow> nm_happ_seq plan_happ_seq"
proof 
  assume a: "nm_anno_act_seq"
  have "\<not>local.mutex_snap_action h i" 
      if ta: "(t, h) \<in> plan_happ_seq" 
      and tb: "(t, i) \<in> plan_happ_seq" 
      and ne: "h \<noteq> i" for h i t
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, t, e) \<in> ran \<pi>" "at_start b = i"
      | a d b u e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, u, e) \<in> ran \<pi>" "at_end b = i" "t = u + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, t, e) \<in> ran \<pi>" "at_start b = i"
      | a t' d b u e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "at_end b = i" "t = u + e" 
      apply (cases rule: in_happ_seqE[OF ta]; cases rule: in_happ_seqE[OF tb])
      by (blast, blast, blast, force)
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b" using ne 1 by auto
      hence "AtStart a \<noteq> AtStart b" by simp
      moreover
      have "(t, AtStart a) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtStart b) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtStart b)"using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "(t, AtStart a) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtEnd b) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtEnd b)"using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "(t, AtEnd a) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtStart b) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtStart b)"using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b" using ne 4 by auto
      hence "AtEnd a \<noteq> AtEnd b" by simp
      moreover
      have "(t, AtEnd a) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtEnd b) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by blast
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtEnd b)" using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  moreover
  have "\<not>local.mutex_snap_action h i"
    if tu: "t - u < \<epsilon> \<and> u - t < \<epsilon>" 
    and ta: "(t, h) \<in> plan_happ_seq" 
    and tb:"(u, i) \<in> plan_happ_seq" 
    and ne: "h \<noteq> i \<or> t \<noteq> u" for h i t u
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, u, e) \<in> ran \<pi>" "at_start b = i"
      | a d b u' e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, u', e) \<in> ran \<pi>" "at_end b = i" "u = u' + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "at_start b = i"
      | a t' d b u' e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, u', e) \<in> ran \<pi>" "at_end b = i" "u = u' + e" 
      apply (cases rule: in_happ_seqE[OF ta]; cases rule: in_happ_seqE[OF tb])
      by (blast, blast, blast, force)
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b \<or> t \<noteq> u" using ne 1 by auto
      hence "AtStart a \<noteq> AtStart b \<or> t \<noteq> u" by simp
      moreover
      have "(t, AtStart a) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtStart b) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtStart b)" using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "(t, AtStart a) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtEnd b) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtEnd b)"using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "(t, AtEnd a) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtStart b) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtStart b)" using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b \<or> t \<noteq> u" using ne 4 by auto
      hence "AtEnd a \<noteq> AtEnd b \<or> t \<noteq> u" by simp
      moreover
      have "(t, AtEnd a) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtEnd b) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by blast
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtEnd b)" using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  ultimately
  show "nm_happ_seq plan_happ_seq" unfolding nm_happ_seq_def by blast
next
  assume a: "nm_happ_seq plan_happ_seq"
  have "\<not>mutex_annotated_action h i" if 
    tu: "t - u < \<epsilon> \<and> u - t < \<epsilon>" 
    and th: "(t, h) \<in> annotated_action_seq" 
    and ti: "(u, i) \<in> annotated_action_seq" 
    and ne: "h \<noteq> i \<or> t \<noteq> u" for h i t u
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, u, e) \<in> ran \<pi>" "AtStart b = i"
      | a d b u' e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, u', e) \<in> ran \<pi>" "AtEnd b = i" "u = u' + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "AtStart b = i"
      | a t' d b u' e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, u', e) \<in> ran \<pi>" "AtEnd b = i" "u = u' + e" 
      using th ti unfolding annotated_action_seq_def by blast
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b \<or> t \<noteq> u" using ne 1 by auto
      hence "at_start a \<noteq> at_start b \<or> t \<noteq> u" using at_start_inj_on 1 plan_actions_def unfolding inj_on_def by blast
      moreover
      have "(t, at_start a) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      moreover
      have "(u, at_start b) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_start b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "(t, at_start a) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by blast 
      moreover
      have "(u, at_end b) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by blast
      moreover
      have "at_start a \<noteq> at_end b" using 2 snaps_disj plan_actions_def by fast
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_end b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "(t, at_end a) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by blast 
      moreover
      have "(u, at_start b) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by blast
      moreover
      have "at_end a \<noteq> at_start b" using 3 snaps_disj plan_actions_def by fast
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_start b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b \<or> t \<noteq> u" using ne 4 by auto
      hence "at_end a \<noteq> at_end b \<or> t \<noteq> u" using at_end_inj_on 4 plan_actions_def unfolding inj_on_def by blast
      moreover
      have "(t, at_end a) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by auto
      moreover
      have "(u, at_end b) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by blast
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_end b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  moreover
  have "\<not>mutex_annotated_action h i"
    if th: "(t, h) \<in> annotated_action_seq"
    and ti: "(t, i) \<in> annotated_action_seq"
    and ne: "h \<noteq> i" for h i t 
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, t, e) \<in> ran \<pi>" "AtStart b = i"
      | a d b u e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, u, e) \<in> ran \<pi>" "AtEnd b = i" "t = u + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, t, e) \<in> ran \<pi>" "AtStart b = i"
      | a t' d b u e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "AtEnd b = i" "t = u + e" 
      using th ti unfolding annotated_action_seq_def by auto
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b" using ne 1 by auto
      hence "at_start a \<noteq> at_start b" using at_start_inj_on 1 plan_actions_def unfolding inj_on_def by blast
      moreover
      have "(t, at_start a) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_start b) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_start b)"using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "at_start a \<noteq> at_end b" using snaps_disj 2 plan_actions_def by fast
      moreover
      have "(t, at_start a) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_end b) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_end b)"using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "at_end a \<noteq> at_start b" using snaps_disj 3 plan_actions_def by fast
      moreover
      have "(t, at_end a) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_start b) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_start b)" using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b" using ne 4 by auto
      hence "at_end a \<noteq> at_end b" using at_end_inj_on 4 plan_actions_def unfolding inj_on_def by blast
      moreover
      have "(t, at_end a) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_end b) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by blast
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_end b)" using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  ultimately
  show nm_anno_act_seq unfolding nm_anno_act_seq_def Let_def by blast
qed
end

subsection \<open>Fluents and Constants in a plan\<close>

locale plans_and_fluents_def = 
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  fixes props::   "'proposition set"
begin

text \<open>Actions only modify fluent propositions. The problem can have constants.\<close>
definition snap_mod_props where
"snap_mod_props s \<equiv> adds s \<union> dels s \<subseteq> props"

definition act_mod_props where
"act_mod_props a \<equiv>
    snap_mod_props (at_start a)
  \<and> snap_mod_props (at_end a)"

definition const_resp_plan where
"const_resp_plan \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. act_mod_props a)"

definition const_resp_happ_seq where
"const_resp_happ_seq \<equiv> \<forall>t. (\<forall>h \<in> happ_at plan_happ_seq t. snap_mod_props h)"

lemma cr_plan_imp_cr_hs: "const_resp_plan \<Longrightarrow> const_resp_happ_seq"
  unfolding const_resp_plan_def act_mod_props_def  plan_happ_seq_def const_resp_happ_seq_def
  by blast

text \<open>Actions only refer to fluent propositions. The entire problem is fluent.\<close>
abbreviation snap_ref_props where
"snap_ref_props s \<equiv> pre s \<union> adds s \<union> dels s \<subseteq> props"

definition act_ref_props where
"act_ref_props a \<equiv>
    snap_ref_props (at_start a) 
  \<and> snap_ref_props (at_end a)
  \<and> over_all a \<subseteq> props"

definition fluent_plan where
"fluent_plan \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. act_ref_props a)"

definition fluent_happ_seq where
"fluent_happ_seq \<equiv> \<forall>t. (\<forall>h \<in> happ_at plan_happ_seq t. snap_ref_props h)"

lemma fluent_plan_imp_fluent_happ_seq: "fluent_plan \<Longrightarrow> fluent_happ_seq"
  unfolding fluent_plan_def fluent_happ_seq_def act_ref_props_def plan_happ_seq_def 
  by blast


text \<open>Constants \<close>
abbreviation snap_consts where
"snap_consts s \<equiv> pre s \<union> adds s \<union> dels s - props"

abbreviation act_consts where
"act_consts a \<equiv> snap_consts (at_start a) \<union> snap_consts (at_end a) \<union> (over_all a - props)"

definition plan_consts where
"plan_consts \<equiv> \<Union>(act_consts ` {a|a t d. (a, t, d) \<in> ran \<pi>})"

definition happ_seq_consts where
"happ_seq_consts \<equiv> \<Union>(snap_consts ` {s|t s. (t, s) \<in> plan_happ_seq})"

lemma happ_seq_consts_const: "happ_seq_consts \<inter> props = {}" unfolding happ_seq_consts_def by auto

definition domain_consts where
"domain_consts \<equiv> plan_consts \<union> (goal - props) \<union> (init - props)"

(* move somewhere else *)

definition fluent_domain where
"fluent_domain actions \<equiv> \<forall>a \<in> actions. act_ref_props a"

definition const_valid_domain where
"const_valid_domain actions \<equiv> \<forall>a \<in> actions. act_mod_props a"

lemma fluent_imp_const_valid_dom: "fluent_domain actions \<Longrightarrow> const_valid_domain actions"
  unfolding fluent_domain_def const_valid_domain_def act_ref_props_def act_mod_props_def snap_mod_props_def by simp

text \<open>The restriction of a state to its props\<close>
definition fluent_state::"'proposition set \<Rightarrow> 'proposition set" where
"fluent_state S \<equiv> S \<inter> props"

definition fluent_state_seq::"'proposition state_sequence \<Rightarrow> bool" where
"fluent_state_seq M \<equiv> \<forall>i \<le> length htpl. (M i \<subseteq> props)"

lemma app_valid_snap_to_fluent_state:
  assumes "M \<subseteq> props"
      and "\<forall>s \<in> H. snap_mod_props s"
    shows "apply_effects M H \<subseteq> props"
proof -
  have "M - \<Union> (dels ` H) \<subseteq> props" using assms by blast
  moreover
  have "\<And>M. M \<subseteq> props \<Longrightarrow> M \<union> \<Union> (adds ` H) \<subseteq> props" using assms snap_mod_props_def by blast
  ultimately
  show ?thesis unfolding apply_effects_def by simp
qed

lemma app_fluent_valid_snaps:
  assumes "\<forall>s \<in> H. adds s \<union> dels s \<subseteq> props"
      and "apply_effects M H = M'"
    shows "apply_effects (M \<inter> props) H = (M' \<inter> props)" 
  using assms unfolding apply_effects_def by blast

lemma fluent_plan_is_const_valid: "fluent_plan \<Longrightarrow> const_resp_plan" 
  unfolding fluent_plan_def act_ref_props_def  
    const_resp_plan_def act_mod_props_def snap_mod_props_def 
  by blast

lemma fluent_plan_consts:
  assumes "fluent_plan"
  shows "plan_consts = {}"
  using assms unfolding fluent_plan_def plan_consts_def act_ref_props_def 
  by (auto simp: Let_def)

lemma cr_plan_consts:
  assumes "const_resp_plan"
  shows "plan_consts = \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - props"
  using assms unfolding const_resp_plan_def plan_consts_def act_mod_props_def snap_mod_props_def by fast

lemma cr_domain_consts:
  assumes "const_resp_plan"
  shows "domain_consts = \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - props \<union> (goal - props) \<union> (init - props)"
  using cr_plan_consts assms domain_consts_def by simp

lemma plan_and_happ_seq_consts:
  "plan_consts = (happ_seq_consts \<union> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})) - props"
  unfolding plan_consts_def happ_seq_consts_def 
  apply (rule equalityI; rule subsetI)
  subgoal for x
    unfolding plan_happ_seq_def by fast
  subgoal for x
    using in_happ_seqE_act by fast
  done

lemma cr_plan_cr_happ_seq:
  "const_resp_plan = const_resp_happ_seq" unfolding const_resp_plan_def const_resp_happ_seq_def 
  plan_happ_seq_def act_mod_props_def by fast

lemma cr_happ_seq_consts:
  assumes "const_resp_happ_seq"
  shows "happ_seq_consts = \<Union>(pre ` {s|t s. (t, s) \<in> plan_happ_seq}) - props"
  using assms unfolding const_resp_happ_seq_def  happ_seq_consts_def snap_mod_props_def
  by blast

lemma plan_consts_not_fluent:
  "props \<inter> plan_consts = {}" unfolding plan_consts_def by blast

lemma domain_consts_not_fluent:
  "props \<inter> domain_consts = {}" 
  using plan_consts_not_fluent domain_consts_def by blast
end

text \<open>
- Assume we have identified a set of fluents that a plan modifies.
- Assume that the constants that the goal refers to are a subset of those the initial state refers to.
- Assume that the constants that the plan refers to are a subset of those the initial state refers to.

The plan validity is equivalent if the 
\<close>
locale plan_and_fluents_restr =
  plans_and_fluents_def at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> props
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
    and props::  "'proposition set" + 
  assumes crp: const_resp_plan
    and goal_consts_in_init_consts: "goal - props \<subseteq> init - props"
    and plan_consts_in_init_consts: "plan_consts \<subseteq> init - props"
begin
text \<open>
The idea behind this abstraction is to maintain the shape of the plan, the time points, and the 
happening sequence, while changing which propositions exist in the states and are modified by the
happenings.

A plan that is "const_valid" (does not modify some constants, if they exist) can be used when
equality is a proposition. The same plan must be valid, if we restrict the preconditions to the set of fluents. 

It's part of a simple preprocessing step to reduce the number of propositions present.
\<close>

definition "over_all_restr = (\<lambda>a. over_all a \<inter> props)"
definition "pre_restr = (\<lambda>s. pre s \<inter> props)"

sublocale pf1: plans_and_fluents_def at_start at_end over_all_restr lower upper pre_restr adds dels "fluent_state init" "fluent_state goal" \<epsilon> \<pi> props
  using local.plans_and_fluents_def_axioms .

lemma crp_state_seq:
  assumes MS'_p: "\<forall>i \<le> length htpl. MS' i = MS i \<inter> props"
      and vss: "(valid_state_sequence MS)"
    shows "(pf1.valid_state_sequence MS' \<and> pf1.fluent_plan
    \<and> pf1.fluent_state_seq MS')"
proof -

  let ?B = "plan_happ_seq"
  let ?t = "time_index"

  let ?Inv = "plan_inv_seq"
  let ?Inv' = "pf1.plan_inv_seq"
  
  from crp cr_plan_imp_cr_hs
  have cr_hs: "\<forall>t. (\<forall>h \<in> happ_at ?B t. snap_mod_props h)" unfolding const_resp_happ_seq_def by blast

  have app_eff: "apply_effects (MS i) (happ_at ?B (?t i)) = MS (Suc i)"
       and invs: "invs_at ?Inv (?t i) \<subseteq> MS i"
       and pres: "\<Union> (pre ` happ_at ?B (?t i)) \<subseteq> MS i"
       if "i < length htpl" for i using that vss unfolding valid_state_sequence_def by (auto simp: Let_def)

  have "pf1.fluent_plan" 
    using crp 
    unfolding pf1.fluent_plan_def pf1.act_ref_props_def 
    unfolding over_all_restr_def pre_restr_def 
    unfolding pf1.const_resp_plan_def act_mod_props_def snap_mod_props_def by simp
  moreover
  have "pf1.valid_state_sequence MS'"
       "fluent_state_seq MS'" 
  proof -
    show "fluent_state_seq  MS'" using MS'_p unfolding fluent_state_seq_def by simp
    have "apply_effects (MS' i) (happ_at ?B (?t i)) = MS' (Suc i)" (is "apply_effects (MS' i) ?S = MS' (Suc i)")
       and "invs_at ?Inv' (?t i) \<subseteq> MS' i"
       and "\<Union> (pre_restr ` happ_at ?B (?t i)) \<subseteq> MS' i"
       if i_ran: "i < length htpl" for i
    proof -
      show "apply_effects (MS' i) ?S = MS' (Suc i)" 
      proof -
        have "\<Union>(adds ` ?S) \<subseteq> props" 
             "\<Union>(dels ` ?S) \<subseteq> props" using i_ran cr_hs 
          unfolding fluent_state_seq_def snap_mod_props_def by auto
        hence "\<forall>s\<in>happ_at plan_happ_seq (time_index i). snap_mod_props s" 
          unfolding snap_mod_props_def by blast
        thus "apply_effects (MS' i) ?S = MS' (Suc i)" 
          using app_fluent_valid_snaps[OF _ app_eff[OF that]] 
          using MS'_p that unfolding snap_mod_props_def by simp
      qed
      show "invs_at ?Inv' (?t i) \<subseteq> MS' i" 
      proof -
        have "invs_at pf1.plan_inv_seq (time_index i) = invs_at plan_inv_seq (time_index i) \<inter> props" 
          unfolding invs_at_def
          unfolding local.plan_inv_seq_def pf1.plan_inv_seq_def 
          unfolding over_all_restr_def by auto
        thus "invs_at ?Inv' (?t i) \<subseteq> MS' i" using invs MS'_p i_ran by auto
      qed
      show "\<Union> (pre_restr ` ?S) \<subseteq> MS' i" 
      proof -
        have "\<Union> (pre ` ?S) \<inter> props =  \<Union> (pre_restr ` ?S)" 
          unfolding plan_happ_seq_def pre_restr_def by auto
        thus "\<Union> (pre_restr ` ?S) \<subseteq> MS' i" using pres MS'_p i_ran by auto
      qed
    qed
    thus "pf1.valid_state_sequence MS'" unfolding pf1.valid_state_sequence_def by (auto simp: Let_def)
  qed
  ultimately
  show "pf1.valid_state_sequence MS' \<and> pf1.fluent_plan \<and> pf1.fluent_state_seq MS'" 
    by (auto intro: exI[where x = "\<lambda>i. (MS i \<inter> props)"])
qed

lemma crp_state_seq':
  assumes MS'_p: "\<forall>i \<le> length htpl. MS' i \<inter> props = MS i \<inter> props" 
                 "\<forall>i \<le> length htpl. (MS i - props) = (MS' i - props) \<union> domain_consts" 
    and vss: "pf1.valid_state_sequence MS'"
  shows "valid_state_sequence MS"
proof -

  let ?B = "plan_happ_seq"
  let ?t = "time_index"

  let ?Inv = "plan_inv_seq"
  let ?Inv' = "pf1.plan_inv_seq"

  let ?dc = "domain_consts"

  from MS'_p
  have MS'_p': "\<forall>i \<le> length htpl. MS' i \<union> ?dc = MS i" by auto

  from crp cr_plan_imp_cr_hs
  have cr_hs: "\<forall>t. (\<forall>h \<in> happ_at ?B t. snap_mod_props h)" unfolding const_resp_happ_seq_def by blast

  have app_eff: "apply_effects (MS' i) (happ_at ?B (?t i)) = MS' (Suc i)"
       and invs: "invs_at ?Inv' (?t i) \<subseteq> MS' i"
       and pres: "\<Union> (pre_restr ` happ_at ?B (?t i)) \<subseteq> MS' i"
       if "i < length htpl" for i using that vss unfolding pf1.valid_state_sequence_def Let_def by auto

  have dc: "?dc = 
    \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - props \<union> (goal - props) \<union> (init - props)" (is "?dc = ?dc'")
    using cr_domain_consts crp by fastforce
  have "apply_effects (MS i) (happ_at ?B (?t i)) = MS (Suc i)" (is "apply_effects (MS i) ?S = MS (Suc i)")
     and "invs_at ?Inv (?t i) \<subseteq> MS i"
     and "\<Union> (pre ` happ_at ?B (?t i)) \<subseteq> MS i"
     if i_ran: "i < length htpl" for i
  proof -
    show "apply_effects (MS i) ?S = MS (Suc i)" 
    proof -
      have "\<Union>(adds ` ?S) \<subseteq> props" (is "?as \<subseteq> props")
           "\<Union>(dels ` ?S) \<subseteq> props" (is "?ds \<subseteq> props") using i_ran cr_hs unfolding fluent_state_seq_def snap_mod_props_def by auto
      hence "?as \<inter> ?dc = {}"
            "?ds \<inter> ?dc = {}" using dc by auto
      moreover
      from app_eff i_ran
      have "(MS' i - ?ds) \<union> ?as = MS' (Suc i)" unfolding apply_effects_def by simp
      ultimately
      have "(MS' i \<union> ?dc) - ?ds \<union> ?as = MS' (Suc i) \<union> ?dc" by auto
      thus "apply_effects (MS i) ?S = MS (Suc i)" unfolding apply_effects_def using MS'_p' i_ran by simp
    qed
    show "invs_at ?Inv (?t i) \<subseteq> MS i" 
    proof -
      have "invs_at ?Inv (?t i) \<subseteq> invs_at ?Inv' (?t i) \<union> ?dc" 
        unfolding invs_at_def
        unfolding local.plan_inv_seq_def pf1.plan_inv_seq_def
        unfolding dc over_all_restr_def by auto
      hence "invs_at ?Inv (?t i) \<subseteq> MS' i \<union> ?dc" using invs i_ran by auto
      thus "invs_at ?Inv (?t i) \<subseteq> MS i" 
        apply -
        apply (erule subset_trans)
        using MS'_p' i_ran by auto
    qed
    show "\<Union> (pre ` ?S) \<subseteq> MS i" 
    proof -
      from pres i_ran
      have "\<Union> (pre_restr ` ?S) \<subseteq> MS' i" by simp
      hence "\<Union> (pre ` ?S) \<inter> props \<subseteq> MS' i" unfolding pre_restr_def by simp
      moreover
      from crp[simplified cr_plan_cr_happ_seq, THEN cr_happ_seq_consts]
      have "\<Union> (pre ` ?S) - props \<subseteq> happ_seq_consts - props" by auto
      hence "\<Union> (pre ` ?S) - props \<subseteq> ?dc" using plan_and_happ_seq_consts unfolding domain_consts_def by fast
      ultimately
      have "\<Union> (pre ` ?S) \<subseteq> MS' i \<union> ?dc" by blast
      thus "\<Union> (pre ` ?S) \<subseteq> MS i" using MS'_p' i_ran by simp
    qed
  qed
  thus "valid_state_sequence MS" unfolding valid_state_sequence_def by (auto simp: Let_def)
qed


(* 
text \<open>Move to other locale\<close>
lemma crp_nm_happ_seq_equiv: "nm_happ_seq (plan_happ_seq) 
  \<longleftrightarrow> pf1.nm_happ_seq (plan_happ_seq)"
proof -
  from crp
  have "const_resp_happ_seq" using cr_plan_cr_happ_seq by blast
  from this[simplified const_resp_happ_seq_def]
  have "\<forall>s t a b. a \<in> happ_at (plan_happ_seq) s \<and> b \<in> happ_at (plan_happ_seq) t
    \<longrightarrow> (mutex_snap_action a b \<longleftrightarrow> pf1.mutex_snap_action a b)" unfolding mutex_snap_action_def 
    apply -
    apply (intro allI; rule impI; rule iffI; erule conjE)
     apply (elim disjE)
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def snap_mod_props_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def snap_mod_props_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def by auto
    done
  thus ?thesis unfolding nm_happ_seq_def by blast
qed
 *)

text \<open>An attempt was made to remove these assumptions by proving that constants in a plan are
      indeed constant. However, this only works for the direction of the proof that does not 
      need it.\<close>

lemma crp_mutex_plan_equiv:
  "mutex_valid_plan \<longleftrightarrow> pf1.mutex_valid_plan"
proof -
  have mutex_equiv: "mutex_snap_action a b \<longleftrightarrow> pf1.mutex_snap_action a b"
    if "adds a \<subseteq> props" "dels a \<subseteq> props" "adds b \<subseteq> props" "dels b \<subseteq> props" for a b
  proof -
    have i: "\<And>x y s. x \<subseteq> s \<Longrightarrow> y \<subseteq> s \<Longrightarrow> x \<union> y \<subseteq> s" by blast
    have j: "y \<inter> s \<inter> x \<noteq> {}" if "y \<inter> x \<noteq> {}" "x \<subseteq> s" for x y s::"'a set"
    proof -
      from that
      obtain e where
        e: "e \<in> y \<inter> x" by blast
      moreover
      have "e \<in> s" using e that by blast
      ultimately
      have "e \<in> y \<inter> x \<inter> s" by blast
      thus ?thesis by blast
    qed

    have k: "\<And>x y s. y \<inter> s \<inter> x \<noteq> {} \<Longrightarrow> x \<subseteq> s \<Longrightarrow> y \<inter> x \<noteq> {}" by blast

    show ?thesis
      unfolding local.mutex_snap_action_def pf1.mutex_snap_action_def
      unfolding pre_restr_def
      apply (rule iffI; elim disjE)
      using that by blast+
  qed

  have mutex_equiv': "mutex_snap_action (f a) (g b)
    \<longleftrightarrow> pf1.mutex_snap_action (f a) (g b)" 
    if "\<exists>t d. (a, t, d)\<in>ran \<pi>" "\<exists>t d. (b, t, d)\<in>ran \<pi>" "f = at_start \<or> f = at_end" "g = at_start \<or> g = at_end" for a b f g
    using that
    apply -
    apply (elim disjE; rule mutex_equiv)
    using crp unfolding const_resp_plan_def act_mod_props_def snap_mod_props_def
    by blast+

  have mutex_self: "mutex_snap_action (at_start a) (at_end a) \<longleftrightarrow> pf1.mutex_snap_action (at_start a) (at_end a)" 
    if "\<exists>t d. (a, t, d)\<in>ran \<pi>" for a
    using that mutex_equiv'[of a a at_start at_end] by simp
  hence "(\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a))
    \<longleftrightarrow> (\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> pf1.mutex_snap_action (at_start a) (at_end a))"
    by fast
  moreover
  
  have mutex_sched: "mutex_sched a ta da b tb db \<longleftrightarrow> pf1.mutex_sched a ta da b tb db" if 
    "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)" for i j a ta da b tb db
  proof -
    have ab_ran: "\<exists>t d. (a, t, d) \<in> ran \<pi>" "\<exists>t d. (b, t, d) \<in> ran \<pi>" using that ranI by fast+
    show ?thesis
    proof 
      assume as: "mutex_sched a ta da b tb db"
      have "\<not> pf1.mutex_snap_action sa sb" 
        if "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da" 
           "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start a \<and> t = ta" "sb = at_start b \<and> u = tb" |
          "sa = at_start a \<and> t = ta" "sb = at_end b \<and> u = tb + db" | 
          "sa = at_end a \<and> t = ta + da" "sb = at_start b \<and> u = tb" |
          "sa = at_end a \<and> t = ta + da" "sb = at_end b \<and> u = tb + db" by argo
        thus ?thesis
          apply cases
          using t as[simplified mutex_sched_def] 
          by (auto simp: mutex_equiv'[OF ab_ran, symmetric])
      qed
      thus "pf1.mutex_sched a ta da b tb db" 
        unfolding pf1.mutex_sched_def by blast
  
    next
      assume as: "pf1.mutex_sched a ta da b tb db"
      have "\<not> mutex_snap_action sa sb" 
        if "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da" 
           "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start a \<and> t = ta" "sb = at_start b \<and> u = tb" |
          "sa = at_start a \<and> t = ta" "sb = at_end b \<and> u = tb + db" | 
          "sa = at_end a \<and> t = ta + da" "sb = at_start b \<and> u = tb" |
          "sa = at_end a \<and> t = ta + da" "sb = at_end b \<and> u = tb + db" by argo
        thus ?thesis
          apply cases
          using t as[simplified pf1.mutex_sched_def] 
          by (auto simp: mutex_equiv'[OF ab_ran])
      qed
      thus "mutex_sched a ta da b tb db" 
        unfolding mutex_sched_def by blast
    qed
  qed
  hence "(\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched a ta da b tb db) \<longleftrightarrow>
     (\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> pf1.mutex_sched a ta da b tb db)"
    by blast
  ultimately
  show ?thesis
    unfolding mutex_valid_plan_eq pf1.mutex_valid_plan_eq
    unfolding mutex_valid_plan_alt_def pf1.mutex_valid_plan_alt_def
    unfolding mutex_snap_action_def pf1.mutex_snap_action_def
    by auto
qed


lemma const_plan_equiv: 
    shows "valid_plan \<longleftrightarrow> pf1.valid_plan" 
  unfolding valid_plan_def pf1.valid_plan_def
proof
  assume "\<exists>M. valid_state_sequence M \<and>
        M 0 = init \<and>
        goal \<subseteq> M (length htpl) \<and>
        durations_ge_0 \<and> durations_valid \<and> 
        mutex_valid_plan \<and> 
        finite_plan"
  then obtain MS where
    vss: "valid_state_sequence MS"
    and init: "MS 0 = init"
    and goal: "goal \<subseteq> MS (length htpl)"
    and dur: "durations_ge_0 \<and> durations_valid"
    and mutex: "mutex_valid_plan"
    and finite: "finite_plan" by blast

  define MS' where "MS' = (\<lambda>i. if (i \<le> length htpl) then MS i \<inter> props else undefined)"  
  hence "\<forall>i \<le> length htpl. MS' i = MS i \<inter> props" by auto
  with vss 
  have vss': "pf1.valid_state_sequence MS'" 
    and fss': "fluent_state_seq MS'" 
    and fp: "pf1.fluent_plan"
    using crp_state_seq by auto

  from MS'_def goal
  have goal': "goal \<inter> props \<subseteq> MS' (length htpl)" by auto

  from MS'_def init
  have init': "init \<inter> props = MS' 0" by simp

  show "\<exists>M. pf1.valid_state_sequence M \<and>
      M 0 = fluent_state init \<and>
      fluent_state goal \<subseteq> M (length htpl) \<and>
      durations_ge_0 \<and> durations_valid \<and>
      pf1.mutex_valid_plan \<and>
      finite_plan"
    using vss' crp_mutex_plan_equiv dur init' goal' mutex finite 
    unfolding fluent_state_def by blast
next
  assume "\<exists>M. pf1.valid_state_sequence M \<and>
        M 0 = fluent_state init \<and>
        fluent_state goal \<subseteq> M (length htpl) \<and>
        durations_ge_0 \<and> durations_valid \<and>
        pf1.mutex_valid_plan \<and>
        finite_plan"
  then obtain MS' where
    vss': "pf1.valid_state_sequence MS'"
    and init': "MS' 0 = init \<inter> props"
    and goal': "goal \<inter> props \<subseteq> MS' (length htpl)"
    and dur: "durations_ge_0 \<and> durations_valid"
    and mutex: "pf1.mutex_valid_plan"
    and finite: "finite_plan" unfolding fluent_state_def by auto

  let ?dc = "domain_consts"

  define MS where "MS \<equiv> \<lambda>i. if (i \<le> length htpl) then MS' i \<union> ?dc else undefined"
  have "\<forall>i\<le>length htpl. MS i - props = (MS' i - props) \<union> ?dc"
  proof (rule allI; rule impI)
    fix i
    assume "i \<le> length htpl"
    hence "MS i = MS' i \<union> ?dc" using MS_def by simp
    hence "MS i - props = MS' i \<union> ?dc - props" by simp
    hence "MS i - props = (MS' i - props) \<union> (?dc - props)" by auto
    thus "MS i - props = (MS' i - props) \<union> ?dc" using domain_consts_not_fluent by fast
  qed
  hence vss: "valid_state_sequence MS" 
    using vss' MS_def crp_state_seq'[where MS = MS and MS' = MS'] by fastforce
  
  show "\<exists>M. valid_state_sequence M \<and>
        M 0 = init \<and> goal \<subseteq> M (length htpl) \<and> durations_ge_0 \<and> 
        durations_valid \<and>
        mutex_valid_plan \<and>
        finite_plan"
  proof (cases "length htpl")
    case 0
    define MS where "MS \<equiv> (\<lambda>x. init)" 
    
    have "goal \<inter> props \<subseteq> init \<inter> props" using init' goal' 0  by simp
    hence init_goal: "goal \<subseteq> init" using goal_consts_in_init_consts by blast
    have any: "\<forall>M. valid_state_sequence M"
      unfolding valid_state_sequence_def using 0 by (auto simp: Let_def)
    show ?thesis using init_goal MS_def any dur mutex crp_mutex_plan_equiv finite by auto
  next
    case (Suc nat)
    have init: "init = MS 0" unfolding MS_def domain_consts_def 
      using goal_consts_in_init_consts plan_consts_in_init_consts Suc using init' by auto
    moreover
    have goal: "goal \<subseteq> MS (length htpl)" unfolding MS_def using goal' 
      unfolding domain_consts_def by auto
    ultimately
    show ?thesis using dur mutex crp_mutex_plan_equiv finite vss by auto
  qed
qed
end

locale fluent_temp_plan = plans_and_fluents_def +
  assumes fluent_plan

locale plan_with_happ_seq_mutex = unique_snaps_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> 
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  assumes nm_happ_seq: "nm_happ_seq plan_happ_seq"


locale valid_plan_without_self_overlap = 
    valid_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
    no_self_overlap_and_dur_ge0_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
begin


sublocale anno: plan_validity_equivalence at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> AtStart AtEnd pre_imp add_imp del_imp
  apply unfold_locales
  unfolding pre_imp_def add_imp_def del_imp_def by auto

interpretation anno_valid: valid_temp_plan AtStart AtEnd over_all lower upper pre_imp add_imp del_imp init goal \<epsilon> \<pi> 
proof 
  show "anno.plan2.valid_plan" using vp anno.valid_plan_equiv_if_snaps_functionally_equiv by auto
qed

interpretation anno_nso: no_self_overlap_and_dur_ge0_temp_plan AtStart AtEnd over_all lower upper pre_imp add_imp del_imp init goal \<epsilon> \<pi>
  by unfold_locales

interpretation anno_unique: unique_snaps_and_dg0_temp_plan AtStart AtEnd over_all lower upper pre_imp add_imp del_imp init goal \<epsilon> \<pi>
  apply unfold_locales
  using dg0 unfolding inj_on_def by auto 

interpretation anno_nm_happ_seq: plan_with_happ_seq_mutex AtStart AtEnd over_all lower upper pre_imp add_imp del_imp init goal \<epsilon> \<pi>
proof 
  have "anno.plan2.nm_anno_act_seq" 
    using anno_nso.nso_mutex_eq_nm_anno_act_seq anno_valid.vp anno_valid.valid_plan_mutex by blast
  thus "anno_unique.nm_happ_seq anno.plan2.plan_happ_seq"
    using anno_unique.nm_anno_act_seq_eq_nm_happ_seq by auto
qed
end

locale valid_plan_restr_to_fluents = 
    valid_temp_plan at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
    plan_and_fluents_restr at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> props
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
    and props::  "'proposition set"
begin
lemma restr_plan_valid: "pf1.valid_plan" using vp by (simp add: const_plan_equiv)

interpretation vtp: valid_temp_plan at_start at_end over_all_restr lower upper pre_restr adds dels "fluent_state init" "fluent_state goal" \<epsilon> \<pi> 
  using restr_plan_valid by unfold_locales

interpretation ftp: fluent_temp_plan at_start at_end over_all_restr lower upper pre_restr adds dels "fluent_state init" "fluent_state goal" \<epsilon> \<pi> 
proof 
  show "pf1.fluent_plan"
  proof -
    obtain MS where "valid_state_sequence MS" using valid_plan_state_seq by blast
    moreover
    define MS' where "MS' \<equiv> \<lambda>i. if (i \<le> length htpl) then MS i \<inter> props else MS i" 
    ultimately
    show ?thesis using crp_state_seq[of MS' MS] by simp
  qed
qed
end



locale temp_plan_with_prop_related_assms = 
  unique_snaps_temp_plan +
  valid_temp_plan +
  no_self_overlap_temp_plan +
  fluent_temp_plan +
  plan_with_happ_seq_mutex


locale temp_plan_for_actions = 
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  fixes actions:: "'action set"
  assumes pap: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"


locale temp_planning_prob_without_self_overlap_with_finite_props_and_actions = 
  temp_plan_for_actions +
  fluent_temp_plan +
  unique_snaps_temp_plan +
  valid_temp_plan +
  no_self_overlap_temp_plan +
assumes some_props:       "card props > 0"
    and some_actions:     "card actions > 0"
    and finite_props:     "finite props"
    and finite_actions:   "finite actions"


(* 
locale temp_plan_for_actions = 
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
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
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  fixes actions:: "'action set"
  assumes pap: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
begin

lemma exists_actions_happening_at_time_index:
  assumes "i < length htpl"
  shows "\<exists>a \<in> actions. (time_index i, at_start a) \<in> plan_happ_seq \<or> (time_index i, at_end a) \<in> plan_happ_seq"
  apply (insert time_index_htpsD[OF assms])
  apply (erule htpsE)
  subgoal for a t d
    apply (rule bexI[of _ a])
    apply (rule disjI1)
    unfolding plan_happ_seq_def apply blast
    using pap by blast
  subgoal for a t d
    apply (rule bexI[of _ a])
    apply (rule disjI2)
    unfolding plan_happ_seq_def apply blast
    using pap by blast
  done
lemma actions_at_time_index_cases:
  assumes  "i < length htpl"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_actions_happening_at_time_index by blast

lemma actions_at_time_index_exhaustive_cases:
  assumes "i < length htpl"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<notin> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<notin> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_actions_happening_at_time_index by blast
end
 *)

locale temp_planning_problem =
  fixes init::    "'proposition set"
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

locale finite_temp_planning_problem = temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon>
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
    and \<epsilon>::       "'time" +
  fixes props:: "'proposition set"
    and actions:: "'action set"
  assumes some_props:       "card props > 0"
      and some_actions:     "card actions > 0"
      and finite_props:     "finite props"
      and finite_actions:   "finite actions"
      and eps_range:        "0 \<le> \<epsilon>"


locale finite_fluent_temp_planning_problem =
  finite_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> fluents actions 
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
    and fluents:: "'proposition set"
    and actions:: "'action set"
  + assumes finite_fluent_domain: "const_valid_domain fluents at_start at_end adds dels actions"


locale finite_props_temp_planning_problem = 
  finite_fluent_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions
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
    and props:: "'proposition set"
    and actions:: "'action set"      
  + assumes finite_props_domain: "fluent_domain props at_start at_end over_all pre adds dels actions"
        and init_props: "init \<subseteq> props"
        and goal_props: "goal \<subseteq> props"

locale unique_snaps_temp_planning_problem = 
finite_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions
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
    and actions:: "'action set" +
assumes at_start_inj_on: "inj_on at_start actions"
    and at_end_inj_on:   "inj_on at_end actions"
    and snaps_disj:      "(at_start ` actions) \<inter> (at_end ` actions) = {}"

(* Simplifications to make instantiation easier *)
locale finite_temp_planning_problem' = 
  finite_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions 
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
begin
  sublocale us: unique_snaps_temp_planning_problem 
    init goal AtStart AtEnd over_all lower upper 
    "pre_imp at_start at_end pre" "add_imp at_start at_end adds" "del_imp at_start at_end dels" \<epsilon> props actions 
  proof
    show "inj_on AtStart actions" "inj_on AtEnd actions" unfolding inj_on_def by blast+
    show "AtStart ` actions \<inter> AtEnd ` actions = {}" by blast
  qed
  
end

locale finite_fluent_temp_planning_problem' = 
  finite_temp_planning_problem' init goal at_start at_end over_all lower upper pre adds dels \<epsilon> fluents actions
  + finite_fluent_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> fluents actions
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
    and fluents:: "'proposition set"
    and actions:: "'action set"
begin

  definition "over_all' \<equiv> (\<lambda>a. over_all a \<inter> fluents)"
  definition "pre' \<equiv> (\<lambda>s. pre s \<inter> fluents)"
  definition "init' \<equiv> init \<inter> fluents"
  definition "goal' \<equiv> goal \<inter> fluents"
  
  sublocale fp: finite_props_temp_planning_problem 
    init' goal' at_start at_end over_all' lower upper 
    pre' adds dels \<epsilon> fluents actions
    apply standard
    using finite_fluent_domain
    unfolding fluent_domain_def act_ref_fluents_def 
      const_valid_domain_def act_mod_fluents_def inj_on_def 
      init'_def goal'_def over_all'_def pre'_def  snap_mod_fluents_def
    by auto

  abbreviation pre_imp'::"'action snap_action \<Rightarrow> 'proposition set" where
  "pre_imp' \<equiv> \<lambda>x. (pre_imp at_start at_end pre x \<inter> fluents)"

  abbreviation add_imp'::"'action snap_action \<Rightarrow> 'proposition set" where
  "add_imp' \<equiv> add_imp at_start at_end adds"
  
  abbreviation del_imp'::"'action snap_action \<Rightarrow> 'proposition set" where
  "del_imp' \<equiv> del_imp at_start at_end dels"

  sublocale fp: finite_props_temp_planning_problem
    init' goal' AtStart AtEnd over_all' lower upper
    pre_imp' add_imp' del_imp' \<epsilon> fluents actions
    apply standard
    unfolding fluent_domain_def act_ref_fluents_def 
      const_valid_domain_def act_mod_fluents_def inj_on_def 
    unfolding add_imp_def pre_imp_def del_imp_def init'_def goal'_def over_all'_def
    using finite_fluent_domain 
    unfolding const_valid_domain_def act_mod_fluents_def snap_mod_fluents_def 
    by auto
  
  sublocale us: unique_snaps_temp_planning_problem
      init' goal' AtStart AtEnd over_all' lower upper
      pre_imp' add_imp' del_imp' \<epsilon> fluents actions
    ..

  context
    fixes \<pi>::"('i, 'action, 'time) temp_plan"
    assumes plan_actions_in_problem: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
        and actions_wf: "\<forall>a \<in> actions. act_consts fluents at_start at_end over_all pre adds dels a \<subseteq> init - fluents"
        and dom_wf: "goal - fluents \<subseteq> init - fluents" 
  begin
  lemma valid_plan_in_finite_props:
    "valid_plan 
  \<longleftrightarrow> valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>"
    unfolding init'_def goal'_def over_all'_def pre'_def
  proof (rule const_plan_equiv[simplified fluent_state_def])
    show "const_resp_plan \<pi> fluents at_start at_end adds dels" using plan_actions_in_problem 
        finite_fluent_domain const_resp_plan_def const_valid_domain_def by fast
    show "plan_consts \<pi> fluents at_start at_end over_all pre adds dels \<subseteq> init - fluents" 
      using plan_actions_in_problem actions_wf unfolding plan_consts_def by blast
  qed (auto simp: dom_wf)

  lemma valid_plan_alt:
    "valid_plan
      \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd over_all' lower upper pre_imp' add_imp' del_imp' \<epsilon>"
  proof -
    have "valid_plan 
    \<longleftrightarrow> valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>"
      using valid_plan_in_finite_props plan_actions_in_problem actions_wf dom_wf by blast
    moreover
    have "valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>
    \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd over_all' lower upper pre_imp' (add_imp at_start at_end adds) (del_imp at_start at_end dels) \<epsilon>"
      apply (rule valid_plan_equiv_if_snaps_functionally_equiv)
      unfolding pre_imp_def add_imp_def del_imp_def pre'_def by simp+
    ultimately
    show ?thesis by simp
  qed
  end
end 

locale ta_temp_planning = 
  finite_props_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions  +
  unique_snaps_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions 
    for init::    "('proposition::linorder) set"
    and goal::    "'proposition set"
    and at_start::"('action::linorder)  \<Rightarrow> 'snap_action"
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
begin 

abbreviation snaps::"'action \<Rightarrow> 'snap_action set" where
"snaps a \<equiv> {at_start a, at_end a}"

definition snap_actions::"'snap_action set" where
"snap_actions \<equiv> (at_start ` actions) \<union> (at_end ` actions)"

text \<open>Useful lemmas about the numberings\<close>

definition "act \<equiv> (!) (sorted_list_of_set actions)"

definition "p \<equiv> (!) (sorted_list_of_set props)"

lemma act_bij_betw: "bij_betw act {n. n < card actions} actions"
  unfolding act_def
proof (rule bij_betw_nth)
  show "distinct (sorted_list_of_set actions)" by simp
  show "{n. n < card actions} = {..<length (sorted_list_of_set actions)}" by auto
  show "actions = set (sorted_list_of_set actions)" using finite_actions by simp
qed

lemma act_inj_on: "inj_on act {n. n < card actions}"
  using act_bij_betw unfolding bij_betw_def by blast

lemmas act_inj_on_spec = act_inj_on[simplified inj_on_def, THEN bspec, THEN bspec, simplified mem_Collect_eq, THEN mp, rotated 2]

lemma act_img_actions: "act ` {n. n < card actions} = actions"
  using act_bij_betw unfolding bij_betw_def by blast

lemma a_in_act_iff: "a \<in> actions \<longleftrightarrow> (\<exists>i < card actions. act i = a)"
  using act_img_actions by force

lemma act_pred: fixes P
  shows "(\<forall>a \<in> actions. P a) \<longleftrightarrow> (\<forall>i < card actions. P (act i))"
  using a_in_act_iff by auto

lemma act_dom: "m < card actions \<Longrightarrow> act m \<in> actions" 
  using act_img_actions by blast

lemma p_bij_betw: "bij_betw p {n. n < card props} props"
  unfolding p_def
proof (rule bij_betw_nth)
  show "distinct (sorted_list_of_set props)" by simp
  show "{n. n < card props} = {..<length (sorted_list_of_set props)}" by auto
  show "props = set (sorted_list_of_set props)" using finite_props by auto
qed
lemma p_inj_on: "inj_on p {n. n < card props}"
  using p_bij_betw unfolding bij_betw_def by blast

lemma p_img_props: "p ` {n. n < card props} = props"
  using p_bij_betw unfolding bij_betw_def by blast

lemma p_in_props_iff: "pr \<in> props \<longleftrightarrow> (\<exists>i < card props. p i = pr)"
  using p_img_props by force

lemma props_pred: fixes P
  shows "(\<forall>pr \<in> props. P pr) \<longleftrightarrow> (\<forall>i < card props. P (p i))"
  using p_in_props_iff by auto

lemma p_dom: "n < card props \<Longrightarrow> p n \<in> props" 
  using p_img_props by blast

lemma eps_cases: 
  assumes "\<epsilon> = 0 \<Longrightarrow> thesis"
      and "0 \<le> \<epsilon> \<Longrightarrow> thesis"
    shows "thesis"
  using assms eps_range by blast

end

(* To do: refactor with fixed plans *)


end
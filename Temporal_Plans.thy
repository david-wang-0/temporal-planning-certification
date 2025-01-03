theory Temporal_Plans
  imports Base
begin

datatype ('t :: time) lower_bound =
  GT 't |
  GE 't

datatype ('t :: time) upper_bound =
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
context
  fixes \<pi>::"('i, 'action, 'time::time) temp_plan"
    and fluents:: "'proposition set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> 'time lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and \<epsilon>::       "'time"
begin

text \<open>Don't know where to put this. Useful\<close>
definition plan_actions_in_problem where
"plan_actions_in_problem actions \<equiv> \<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"


definition apply_effects::"'proposition set \<Rightarrow> 'snap_action set \<Rightarrow> 'proposition set" where
"apply_effects M S \<equiv> (M - \<Union>(dels ` S)) \<union> \<Union>(adds ` S)"

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

abbreviation happ_at::"('time \<times> 'snap_action) set \<Rightarrow> 'time \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s. (t, s) \<in> B}"

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


text \<open>This definition arose from the statement in \<^cite>\<open>Gigante2020\<close>, that every at-start 
snap-action interferes with itself for self-overlap. Therefore, we can assume the same for at-end
snap-actions. Moreover, in their definition of a planning problem, the assumption is made that 
no two actions share snap-actions. at-start(a) \<noteq> at-start(b) and at-start(a) \<noteq> at_end(b) and at-start(a) \<noteq> at-end(a).\<close>

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

thm List.linorder_class.sorted_list_of_set.fold_insort_key.infinite
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

definition durations_positive::bool where
"durations_positive \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> 0 < d"

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

lemma no_self_overlap_ran:
  assumes no_self_overlap
    "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows
    "(t > u \<or> u > t + d)"
  using no_self_overlap_spec[OF assms] by fastforce


lemma nso_double_act_spec:
  assumes nso: no_self_overlap
    and dg0: durations_ge_0
    and a: "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows "u + e < t \<or> t + d < u"
proof -
  from no_self_overlap_ran[OF nso a(1) a(2)] no_self_overlap_ran[OF nso a(2) a(1)] a
  have "u < t \<or> t + d < u" "t < u \<or> u + e < t" by blast+
  thus ?thesis by auto
qed

lemma nso_no_double_sched:
  assumes nso: no_self_overlap
    and dg0: durations_ge_0
    and a: "(a, t, d) \<in> ran \<pi>"
    "(a, t, e) \<in> ran \<pi>"
  shows "d = e"
proof -
  from nso_double_act_spec[OF assms]
  have "d \<noteq> e \<Longrightarrow> t + e < t \<or> t + d < t" by blast
  with dg0[simplified durations_ge_0_def] a
  show ?thesis by force
qed

lemma nso_no_double_start:
  assumes nso: no_self_overlap
    and dg0: durations_ge_0
    and a: "(a, t, d) \<in> ran \<pi>"
           "(b, t, e) \<in> ran \<pi>"
    and "(a, t, d) \<noteq> (b, t, e)"
  shows "a \<noteq> b"
  using assms nso_no_double_sched by blast

lemma nso_start_end:
  assumes nso: no_self_overlap
    and dg0: durations_ge_0
    and a: "(a, t, d) \<in> ran \<pi>"
           "(b, s, e) \<in> ran \<pi>"
           "(a, t, d) \<noteq> (b, s, e)"
           "t = s + e"
  shows "a \<noteq> b"
proof 
  assume e: "a = b"
  hence "t \<noteq> s \<or> d \<noteq> e" using a by blast
  hence "t + d < s" using nso_double_act_spec[OF nso dg0 a(1) a(2)[simplified e[symmetric]]] a(4) by blast
  moreover
  have "0 \<le> e" "0 \<le> d" using dg0[simplified durations_ge_0_def] a(1,2) by auto
  ultimately
  show False using \<open>t = s + e\<close>
    apply (cases "e \<le> 0") 
    subgoal by auto 
    using linorder_not_less by fastforce
qed

lemma nso_ends:
  assumes nso: no_self_overlap
    and dg0: durations_ge_0
    and a: "(a, t, d) \<in> ran \<pi>"
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
    using nso_double_act_spec[OF nso dg0 a(1) a(2)[simplified e[symmetric]]] a(4) by blast
  hence "s + e < t + d \<or> t + d < s + e" apply (cases) using ed 
    by (simp add: add.commute add_strict_increasing2)+
  thus False using \<open>t + d = s + e\<close> by simp
qed

subsection \<open>Equivalent Notions of Mutual Exclusivity\<close>

text \<open>A plan without self-overlap has a simpler definition of non-interference\<close>
definition mutex_valid_plan_inj::bool where
"mutex_valid_plan_inj \<equiv> 
  (\<forall>a ta da b tb db. 
      (a, ta, da) \<in> ran \<pi> 
    \<and> (b, tb, db) \<in> ran \<pi>
    \<and> (a, ta, da) \<noteq> (b, tb, db)
  \<longrightarrow> mutex_sched a ta da b tb db)
\<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))"

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

lemma nso_imp_inj:
  assumes nso: no_self_overlap
      and dg0: durations_ge_0
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
"pre_imp = app_snap pre"

definition add_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"add_imp = app_snap adds"

definition del_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"del_imp = app_snap dels"

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
  

lemma nso_mutex_cond:
  assumes nso: no_self_overlap
      and dg0: local.durations_ge_0
      and eps_ran: "0 \<le> \<epsilon>"
    shows "mutex_valid_plan \<longleftrightarrow> nm_anno_act_seq"
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
  thus ?thesis using assms nso_imp_inj inj_mutex_def by blast
qed 


subsubsection \<open>Non-Interference w.r.t the Happening Sequence\<close>

definition nm_happ_seq::"('time \<times> 'snap_action) set \<Rightarrow> bool" where
"nm_happ_seq B \<equiv> 
  (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u
    \<and> (a \<noteq> b \<or> t \<noteq> u) \<longrightarrow> \<not>mutex_snap_action a b)
  \<and> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"

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

abbreviation "plan_actions \<equiv> {a| a t d. (a, t, d) \<in> ran \<pi>}"

context
  assumes at_start_inj: "inj_on at_start plan_actions"
      and at_end_inj: "inj_on at_end plan_actions"
      and snaps_disj: "at_start ` plan_actions \<inter> at_end ` plan_actions = {}"
begin
  
  lemma at_start_in_happ_seqE: 
    assumes in_happ_seq: "(s, at_start a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> plan_actions"
        and nso: no_self_overlap
        and dg0: durations_ge_0
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  proof (rule ex_ex1I)
    from in_happ_seq in_happ_seqE'
    have "\<exists>(a', t, d) \<in> ran \<pi>. (at_start a' = at_start a \<and> s = t \<or> at_end a' = at_start a \<and> s = t + d)"
      by blast
    with snaps_disj a_in_actions
    have "\<exists>(a', t, d) \<in> ran \<pi>. at_start a' = at_start a \<and> s = t" by fast
    moreover
    have "\<forall>(a', t, d) \<in> ran \<pi>. at_start a = at_start a' \<longrightarrow> a = a'" 
      using at_start_inj a_in_actions unfolding inj_on_def by blast
    ultimately
    show "\<exists>x. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t" by auto
  next
    have "t = t' \<and> d = d'" 
         if "(a, t, d) \<in> ran \<pi> \<and> s = t" 
        and "(a, t', d') \<in> ran \<pi> \<and> s = t'" for t d t' d'
      using that nso dg0 nso_no_double_start by blast
    thus "\<And>x y. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> case y of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> x = y" by blast
  qed

  lemma at_end_in_happ_seqE:
    assumes in_happ_seq: "(s, at_end a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> plan_actions"
        and nso: "no_self_overlap"
        and dp: "durations_positive"
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
      with a_in_actions
      have "\<exists>a' d. (s, at_end a) = (s, at_start a') \<and> (a', s, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" by blast
      with snaps_disj 1 a_in_actions
      show ?thesis by blast
    next
      case 2
      with a_in_actions
      have "\<exists>a' t d. (s, at_end a) = (t + d, at_end a') \<and>(a', t, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" by blast
      with at_end_inj[simplified inj_on_def] a_in_actions
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
          with dp[simplified durations_positive_def] t'd'_in_ran td_t'd'
          have "t' \<le> t + d" by force
          with False ij 1
          show ?thesis using nso[simplified no_self_overlap_def] by force
        next
          case 2
          with dp[simplified durations_positive_def] td_in_ran td_t'd'
          have "t \<le> t' + d'" by (metis add.commute less_add_same_cancel2 order_less_le)
          with False ij 2
          show ?thesis using nso[simplified no_self_overlap_def] by force 
        qed
      qed
    qed
    ultimately
    show ?thesis apply - by (rule ex1I, auto)
  qed


  lemma nso_mutex_happ_seq:
    assumes nso: no_self_overlap
        and dg0: local.durations_ge_0
        and eps_ran: "0 \<le> \<epsilon>"
      shows "nm_anno_act_seq \<longleftrightarrow> nm_happ_seq plan_happ_seq"
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
        have "a \<noteq> b" using ne at_start_inj 1 by auto
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
        have "a \<noteq> b" using ne at_start_inj 4 by auto
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
        hence "at_start a \<noteq> at_start b \<or> t \<noteq> u" using at_start_inj 1 unfolding inj_on_def by blast
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
        have "at_start a \<noteq> at_end b" using 2 snaps_disj by auto
        ultimately
        have "\<not>mutex_snap_action (at_start a) (at_end b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
        thus ?thesis using 2 mutex_trans by auto
      next
        case 3
        have "(t, at_end a) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by blast 
        moreover
        have "(u, at_start b) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by blast
        moreover
        have "at_end a \<noteq> at_start b" using 3 snaps_disj by auto
        ultimately
        have "\<not>mutex_snap_action (at_end a) (at_start b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
        thus ?thesis using 3 mutex_trans by auto
      next
        case 4
        have "a \<noteq> b \<or> t \<noteq> u" using ne 4 by auto
        hence "at_end a \<noteq> at_end b \<or> t \<noteq> u" using at_end_inj 4 unfolding inj_on_def by blast
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
        hence "at_start a \<noteq> at_start b" using at_start_inj 1 unfolding inj_on_def by blast
        moreover
        have "(t, at_start a) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
        moreover
        have "(t, at_start b) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
        ultimately
        have "\<not>mutex_snap_action (at_start a) (at_start b)"using a unfolding nm_happ_seq_def by (auto simp: Let_def)
        thus ?thesis using 1 mutex_trans by auto
      next
        case 2
        have "at_start a \<noteq> at_end b" using snaps_disj 2 by auto
        moreover
        have "(t, at_start a) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by auto
        moreover
        have "(t, at_end b) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by auto
        ultimately
        have "\<not>mutex_snap_action (at_start a) (at_end b)"using a unfolding nm_happ_seq_def by (auto simp: Let_def)
        thus ?thesis using 2 mutex_trans by auto
      next
        case 3
        have "at_end a \<noteq> at_start b" using snaps_disj 3 by auto
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
        hence "at_end a \<noteq> at_end b" using at_end_inj 4 unfolding inj_on_def by blast
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



subsection \<open>Indexing timepoints\<close>

text \<open>Basic facts about the indexing of timepoints\<close>
lemma time_index_bij_betw_list: "bij_betw time_index {n. n < length htpl} (set htpl)"
  using bij_betw_nth distinct_sorted_list_of_set htpl_def[symmetric] lessThan_def
  by metis

lemma time_index_inj_on_list: "inj_on time_index {n. n < length htpl}" 
  using bij_betw_def time_index_bij_betw_list by blast

lemma time_index_img_list: "time_index ` {n. n < length htpl} = set htpl"
  using time_index_bij_betw_list unfolding bij_betw_def by blast

lemma card_htps_len_htpl: "card htps= length htpl" unfolding htpl_def by simp

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
  
  have "l' < (Suc l)" using l'(1, 3) time_index_strict_sorted_list' by simp
  moreover
  have "l < l'" using l'(2) time_index_strict_sorted_list' a by simp
  ultimately
  show "False" by simp
qed


text \<open>Indexing of timepoints and such with respect to a finite plan\<close>

lemma finite_acts_imp_finite_htps:
  assumes "finite (ran \<pi>)"
    shows "finite htps"
proof -
 have 1: "finite ((\<lambda>(a, t, d). t) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). t + d) ` (ran \<pi>))"
   using assms by simp+
  moreover
  have "(\<lambda>(a, t, d). t) ` (ran \<pi>) = {t |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). t + d) ` (ran \<pi>)  = {t + d |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite htps" unfolding htps_def by auto
qed

lemma finite_htps: 
  assumes fp: "finite_plan"
    shows "finite htps"
  using finite_acts_imp_finite_htps fp finite_ran finite_plan_def by blast

lemma finite_htps_is_set_htpl:
  assumes "finite htps"
  shows "htps = set htpl" unfolding htpl_def 
  using set_sorted_list_of_set assms by blast

lemma set_htpl_eq_htps: 
  assumes fp: "finite_plan"
  shows "htps = set htpl" 
  using finite_htps assms finite_htps_is_set_htpl
  by blast

lemma time_index_bij_betw_set:
  assumes fp: "finite_plan "
  shows "bij_betw time_index {n. n < card htps} htps"
proof -
  have 3: "distinct htpl" unfolding htpl_def by simp
  show "bij_betw time_index {n. n < card htps} htps"
    apply (subst card_htps_len_htpl)
    apply (subst set_htpl_eq_htps[OF fp])
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

lemmas time_index_strict_sorted_set = time_index_strict_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set = time_index_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_strict_sorted_set' = time_index_strict_sorted_list'[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set' = time_index_sorted_list'[simplified card_htps_len_htpl[symmetric]]

lemmas time_index_sorted = time_index_sorted_list time_index_sorted_set time_index_strict_sorted_list time_index_strict_sorted_set
  time_index_sorted_list' time_index_sorted_set' time_index_strict_sorted_list' time_index_strict_sorted_set'


lemma time_indexI_htps:
  assumes finite_plan
      and "t \<in> htps"
    shows "\<exists>i < card htps. time_index i = t"
  using time_index_img_set assms by force

lemma time_indexI_htpl:    
  assumes "t \<in> set (htpl)"
    shows "\<exists>i < length htpl. time_index i = t"
  using time_index_img_list assms by force

lemma no_actions_between_indexed_timepoints: 
  assumes "finite_plan"
    "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'>time_index l. t' < time_index (Suc l) \<and> a \<in> happ_at plan_happ_seq t')"
  using no_non_indexed_time_points[OF assms(2)] 
    a_in_B_iff_t_in_htps finite_htps[OF assms(1)] 
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
    moreover
    have fhtps: "finite htps" using fr finite_acts_imp_finite_htps by blast
    ultimately
    have "\<exists>x. x \<in> set htpl" using finite_htps_is_set_htpl by blast 
    with len
    have False by simp
  }
  thus "card (ran \<pi>) = 0" by blast
qed

subsection \<open>Fluents and Constants in a Plan\<close>

text \<open>Actions only refer to fluent propositions. The entire problem is fluent.\<close>
abbreviation snap_ref_fluents where
"snap_ref_fluents s \<equiv> pre s \<union> adds s \<union> dels s \<subseteq> fluents"

definition act_ref_fluents where
"act_ref_fluents a \<equiv>
    snap_ref_fluents (at_start a) 
  \<and> snap_ref_fluents (at_end a)
  \<and> over_all a \<subseteq> fluents"

definition fluent_plan where
"fluent_plan \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. act_ref_fluents a)"

definition fluent_happ_seq where
"fluent_happ_seq \<equiv> \<forall>t. (\<forall>h \<in> happ_at plan_happ_seq t. snap_ref_fluents h)"

definition fluent_domain where
"fluent_domain actions \<equiv> \<forall>a \<in> actions. act_ref_fluents a"

text \<open>Actions only modify fluent propositions. The problem can have constants.\<close>
abbreviation snap_mod_fluents where
"snap_mod_fluents s \<equiv> adds s \<union> dels s \<subseteq> fluents"

definition act_mod_fluents where
"act_mod_fluents a \<equiv>
    snap_mod_fluents (at_start a)
  \<and> snap_mod_fluents (at_end a)"

definition const_valid_plan where
"const_valid_plan \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. act_mod_fluents a)"

definition const_valid_happ_seq where
"const_valid_happ_seq \<equiv> \<forall>t. (\<forall>h \<in> happ_at plan_happ_seq t. snap_mod_fluents h)"

lemma cv_plan_imp_cv_hs: "const_valid_plan \<Longrightarrow> const_valid_happ_seq"
  unfolding const_valid_plan_def act_mod_fluents_def  plan_happ_seq_def const_valid_happ_seq_def
  by blast

definition const_valid_domain where
"const_valid_domain actions \<equiv> \<forall>a \<in> actions. act_mod_fluents a"

text \<open>The restriction of a state to its fluents\<close>
definition fluent_state::"'proposition set \<Rightarrow> 'proposition set" where
"fluent_state S \<equiv> S \<inter> fluents"

definition fluent_state_seq::"'proposition state_sequence \<Rightarrow> bool" where
"fluent_state_seq M \<equiv> \<forall>i \<le> length htpl. (M i \<subseteq> fluents)"

lemma app_valid_snap_to_fluent_state:
  assumes "M \<subseteq> fluents"
      and "\<forall>s \<in> H. snap_mod_fluents s"
    shows "apply_effects M H \<subseteq> fluents"
proof -
  have "M - \<Union> (dels ` H) \<subseteq> fluents" using assms by blast
  moreover
  have "\<And>M. M \<subseteq> fluents \<Longrightarrow> M \<union> \<Union> (adds ` H) \<subseteq> fluents" using assms by blast
  ultimately
  show ?thesis unfolding apply_effects_def by simp
qed

lemma app_fluent_valid_snaps:
  assumes "\<forall>s \<in> H. adds s \<union> dels s \<subseteq> fluents"
      and "apply_effects M H = M'"
    shows "apply_effects (M \<inter> fluents) H = (M' \<inter> fluents)" 
  using assms unfolding apply_effects_def by blast

lemma fluent_plan_is_const_valid: "fluent_plan \<Longrightarrow> const_valid_plan" 
  unfolding fluent_plan_def act_ref_fluents_def  
    const_valid_plan_def act_mod_fluents_def  
  by blast

abbreviation snap_consts where
"snap_consts s \<equiv> pre s \<union> adds s \<union> dels s - fluents"

abbreviation act_consts where
"act_consts a \<equiv> snap_consts (at_start a) \<union> snap_consts (at_end a) \<union> (over_all a - fluents)"

definition plan_consts where
"plan_consts \<equiv> \<Union>(act_consts ` {a|a t d. (a, t, d) \<in> ran \<pi>})"

definition happ_seq_consts where
"happ_seq_consts \<equiv> \<Union>(snap_consts ` {s|t s. (t, s) \<in> plan_happ_seq})"

lemma happ_seq_consts_const: "happ_seq_consts \<inter> fluents = {}" unfolding happ_seq_consts_def by auto

definition domain_consts where
"domain_consts \<equiv> plan_consts \<union> (goal - fluents) \<union> (init - fluents)"

lemma fluent_plan_consts:
  assumes "fluent_plan"
  shows "plan_consts = {}"
  using assms unfolding fluent_plan_def plan_consts_def act_ref_fluents_def 
  by (auto simp: Let_def)

lemma cv_plan_consts:
  assumes "const_valid_plan"
  shows "plan_consts = \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - fluents"
  using assms unfolding const_valid_plan_def plan_consts_def act_mod_fluents_def by fast

lemma cv_domain_consts:
  assumes "const_valid_plan"
  shows "domain_consts = \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - fluents \<union> (goal - fluents) \<union> (init - fluents)"
  using cv_plan_consts[OF assms] domain_consts_def by simp

lemma plan_and_happ_seq_consts:
  "plan_consts = (happ_seq_consts \<union> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})) - fluents"
  unfolding plan_consts_def happ_seq_consts_def 
  apply (rule equalityI; rule subsetI)
  subgoal for x
    unfolding plan_happ_seq_def by fast
  subgoal for x
    using in_happ_seqE_act by fast
  done

lemma cv_plan_cv_happ_seq:
  "const_valid_plan = const_valid_happ_seq" unfolding const_valid_plan_def const_valid_happ_seq_def 
  plan_happ_seq_def act_mod_fluents_def by fast

lemma cv_happ_seq_consts:
  assumes "const_valid_happ_seq"
  shows "happ_seq_consts = \<Union>(pre ` {s|t s. (t, s) \<in> plan_happ_seq}) - fluents"
  using assms unfolding const_valid_happ_seq_def  happ_seq_consts_def 
  by blast

lemma plan_consts_not_fluent:
  "fluents \<inter> plan_consts = {}" unfolding plan_consts_def by blast

lemma domain_consts_not_fluent:
  "fluents \<inter> domain_consts = {}" unfolding domain_consts_def using plan_consts_not_fluent by blast

lemma plan_consts_empty:
  assumes "length htpl = 0"
      and "finite_plan" 
    shows "plan_consts = {}"
proof -
  from set_htpl_eq_htps assms
  have "htps = {}" by simp
  thus ?thesis unfolding plan_consts_def htps_def by simp
qed

lemma invs_elim:
  assumes "x \<in> \<Union>(over_all ` {a| a. (a, t, d) \<in> ran \<pi>})"
      and dp: durations_positive
  shows "x \<in> invs_at plan_inv_seq (t + d)"
proof -
  from assms 
  obtain a where
    "x \<in> over_all a"
    "(a, t, d) \<in> ran \<pi>" by blast
  hence "x \<in> invs_at plan_inv_seq (t + d)" unfolding invs_at_def plan_inv_seq_def using dp unfolding durations_positive_def by fastforce
  thus ?thesis by blast
qed

lemma state_seq_consts_ind:
  assumes vss: "valid_state_sequence MS"
      and cvp: const_valid_plan
      and len: "0 < length htpl"
      and x_not_fluent: "x \<notin> fluents"
      and i_ran: "i < length htpl"
      and x_in_MS: "x \<in> MS (Suc i)"
    shows "x \<in> MS i"
proof -
  from x_in_MS
  have "x \<in> apply_effects (MS i) (happ_at plan_happ_seq (time_index i))" using vss i_ran unfolding valid_state_sequence_def Let_def by blast
  moreover
  from cvp[THEN cv_plan_imp_cv_hs]
  have "\<Union>(adds ` (happ_at plan_happ_seq (time_index i))) \<subseteq> fluents" 
       "\<Union>(dels ` (happ_at plan_happ_seq (time_index i))) \<subseteq> fluents" unfolding const_valid_happ_seq_def by blast+
  hence "x \<notin> \<Union>(adds ` (happ_at plan_happ_seq (time_index i))) \<union> \<Union>(dels ` (happ_at plan_happ_seq (time_index i)))" using \<open>x \<notin> fluents\<close> by blast
  ultimately
  show "x \<in> MS i" unfolding apply_effects_def by blast
qed

lemma in_state_seq_consts_in_init:
  assumes vss: "valid_state_sequence MS"
      and cvp: const_valid_plan
      and len: "0 < length htpl"
      and x_not_fluent: "x \<notin> fluents"
      and i_ran: "i < length htpl"
      and x_in_MS: "x \<in> MS i"
    shows "x \<in> MS 0"
  using i_ran x_in_MS
proof (induction i)
  case 0
  then show ?case by blast
next
  case (Suc i)
  with state_seq_consts_ind x_not_fluent vss cvp
  have "x \<in> MS i" by fastforce
  with Suc
  show ?case by auto
qed

lemma in_happ_seq_pre_consts_in_init:
  assumes fp: finite_plan
      and vss: "valid_state_sequence MS"
      and cvp: const_valid_plan
      and dp: durations_positive
      and x_in_pre: "x \<in> \<Union>(pre ` happ_at plan_happ_seq (time_index i)) \<union> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})"
      and i_ran: "i < length htpl"
      and x_not_fluent: "x \<notin> fluents"
    shows "x \<in> MS 0"
  using assms
proof (cases "length htpl")
  case 0
  have htps: "htps = {}" using set_htpl_eq_htps fp 0 by auto
  hence "happ_at plan_happ_seq (time_index i) = {}" using a_in_B_iff_t_in_htps by simp
  hence "x \<notin> \<Union>(pre ` happ_at plan_happ_seq (time_index i))" by blast
  moreover
  have "ran \<pi> = {}" using htps unfolding htps_def by auto
  ultimately
  show ?thesis using x_in_pre by blast
next
  case (Suc nat)
  consider "x \<in> \<Union>(pre ` happ_at plan_happ_seq (time_index i))" | "x \<in> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})" using x_in_pre by blast
  hence "\<exists>i < length htpl. x \<in> MS i"
  proof cases
    case 1
    then show ?thesis using vss unfolding valid_state_sequence_def Let_def using i_ran by blast
  next
    case 2
    with invs_elim[OF _ dp]  
    obtain t where
      t: "t \<in> htps"
      "x \<in> invs_at plan_inv_seq t" unfolding htps_def by blast
    then obtain i where
      i: "t = time_index i"
         "i < length htpl" using time_index_img_list fp set_htpl_eq_htps by blast
    show ?thesis using i t vss unfolding valid_state_sequence_def Let_def by blast
  qed
  thus ?thesis using x_not_fluent in_state_seq_consts_in_init[OF vss cvp] by fastforce
qed


lemma valid_plan_happ_seq_consts_const:
  assumes fp: finite_plan
      and vp: valid_plan
      and cvp: const_valid_plan
      and dp: durations_positive
      and x: "x \<in> happ_seq_consts"
    shows "x \<in> init - fluents"
proof -
  from vp[simplified valid_plan_def]
  obtain MS where
    vss: "valid_state_sequence MS"
    and init: "MS 0 = init" 
    and goal: "goal \<subseteq> MS (length htpl)"
    by blast
  from x 
  have "x \<in> \<Union>(snap_consts ` {h|t h. (t, h) \<in> plan_happ_seq})" unfolding happ_seq_consts_def by simp
  with cvp 
  have x: "x \<in> \<Union>(pre ` {h|t h. (t, h) \<in> plan_happ_seq}) - fluents" using cv_plan_imp_cv_hs act_mod_fluents_def const_valid_happ_seq_def  by fast
  then obtain t where
    t: "x \<in>  \<Union>(pre ` happ_at plan_happ_seq t)" by auto
  then obtain i where
    i: "i < length htpl"
       "time_index i = t" using a_in_B_iff_t_in_htps finite_htps_is_set_htpl[OF finite_htps[OF fp]] time_indexI_htpl by blast
  hence "\<exists>i < length htpl. x \<in> \<Union>(pre ` happ_at plan_happ_seq (time_index i))" using t by blast
  hence "x \<in> MS 0" using in_happ_seq_pre_consts_in_init[OF fp vss cvp] x dp by blast
  with x init
  show ?thesis by blast
qed

lemma valid_plan_const_invs_const:
  assumes fp: finite_plan
      and vp: valid_plan
      and cvp: const_valid_plan
      and dp: durations_positive
      and x: "x \<in> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>}) - fluents"
    shows "x \<in> init - fluents"
proof -
  from vp[simplified valid_plan_def]
  obtain MS where
    vss: "valid_state_sequence MS"
    and init: "MS 0 = init" 
    and goal: "goal \<subseteq> MS (length htpl)"
    by blast
  from x 
  have x: "x \<in> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})"
       "x \<notin> fluents" by blast+
  hence "\<exists>t. t \<in> htps" unfolding htps_def by blast
  hence "0 < length htpl" using finite_htps_is_set_htpl finite_htps fp by auto
  hence "x \<in> MS 0" using in_happ_seq_pre_consts_in_init[OF fp vss cvp dp, where x = x] x by auto
  thus "x \<in> init - fluents" using x init by blast
qed


text \<open>The constants in a valid plan are constant\<close>
lemma valid_plan_consts:
  assumes fp: finite_plan
      and vp: valid_plan
      and cvp: const_valid_plan
      and dp: durations_positive
    shows "plan_consts \<subseteq> init - fluents"
proof -
  from vp[simplified valid_plan_def]
  obtain MS where
    vss: "valid_state_sequence MS"
    and init: "MS 0 = init" 
    and goal: "goal \<subseteq> MS (length htpl)"
    by blast
  have "plan_consts = (happ_seq_consts \<union> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})) - fluents" using plan_and_happ_seq_consts by blast
  hence "plan_consts = happ_seq_consts \<union> (\<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>}) - fluents)" using happ_seq_consts_const by auto
  thus ?thesis using valid_plan_happ_seq_consts_const valid_plan_const_invs_const assms by blast
qed

text \<open>The constants in the goal of a valid plan must be present in the initial state.\<close>
lemma valid_plan_goal:
  assumes fp: finite_plan
      and vp: valid_plan
      and cvp: const_valid_plan
      and dp: durations_positive
  shows "goal - fluents \<subseteq> init - fluents"
proof -
  from vp[simplified valid_plan_def]
  obtain MS where
    vss: "local.valid_state_sequence MS" 
    and init: "MS 0 = init" 
    and goal: "goal \<subseteq> MS (length htpl)" 
    by blast
  show ?thesis 
  proof (cases "length htpl")
    case 0
    then show ?thesis using init goal by auto
  next
    case (Suc nat)
    hence "MS (length htpl - 1) - fluents \<subseteq> init - fluents" using in_state_seq_consts_in_init[OF vss cvp] init by auto
    moreover
    have "MS (length htpl) - fluents \<subseteq> MS (length htpl - 1) - fluents" using state_seq_consts_ind vss cvp Suc by auto
    ultimately
    show ?thesis using goal by blast
  qed
qed
end

text \<open>
The idea behind this abstraction is to maintain the shape of the plan, the time points, and the 
happening sequence, while changing which propositions exist in the states and are modified by the
happenings.

A plan that is "const_valid" (does not modify some constants, if they exist) can be used when
equality is a proposition. The same plan must be valid, if we restrict the preconditions to the set of fluents. 

Equalities in PDDL can simply be compiled away to constants.
\<close>

context
  fixes over_all::"'act \<Rightarrow> 'prop set" 
    and over_all'
    and pre::"'snap \<Rightarrow> 'prop set"
    and pre' 
    and fluents::"'prop set"
    and at_start::"'act \<Rightarrow> 'snap"
    and at_end adds dels 
    and \<pi>::"('i, 'act, 'time::time) temp_plan"
  assumes cvp: "const_valid_plan \<pi> fluents at_start at_end adds dels"
      and over_all'_def: "over_all' = (\<lambda>a. over_all a \<inter> fluents)"
      and pre'_def: "pre' = (\<lambda>s. pre s \<inter> fluents)"
begin

lemma cvp_state_seq:
  assumes MS'_p: "\<forall>i \<le> length (htpl \<pi>). MS' i = MS i \<inter> fluents"
      and vss: "(valid_state_sequence \<pi> at_start at_end over_all pre adds dels MS)"
    shows "(valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS' 
    \<and> fluent_plan \<pi> fluents at_start at_end over_all' pre' adds dels
    \<and> fluent_state_seq \<pi> fluents MS')"
proof -

  let ?B = "plan_happ_seq \<pi> at_start at_end"
  let ?t = "time_index \<pi>"

  let ?Inv = "plan_inv_seq \<pi> over_all"
  let ?Inv' = "plan_inv_seq \<pi> over_all'"
  
  from cvp cv_plan_imp_cv_hs
  have cv_hs: "\<forall>t. (\<forall>h \<in> happ_at ?B t. snap_mod_fluents fluents adds dels h)" unfolding const_valid_happ_seq_def by blast

  have app_eff: "apply_effects adds dels (MS i) (happ_at ?B (?t i)) = MS (Suc i)"
       and invs: "invs_at ?Inv (?t i) \<subseteq> MS i"
       and pres: "\<Union> (pre ` happ_at ?B (?t i)) \<subseteq> MS i"
       if "i < length (htpl \<pi>)" for i using that vss unfolding valid_state_sequence_def by (auto simp: Let_def)

    have "fluent_plan \<pi> fluents at_start at_end over_all' pre' adds dels" 
      unfolding fluent_plan_def act_ref_fluents_def 
    using cvp over_all'_def pre'_def unfolding const_valid_plan_def act_mod_fluents_def by fast
  moreover
  have "valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS'"
       "fluent_state_seq \<pi> fluents MS'" 
  proof -
    show "fluent_state_seq \<pi> fluents MS'" using MS'_p unfolding fluent_state_seq_def by simp
    have "apply_effects adds dels (MS' i) (happ_at ?B (?t i)) = MS' (Suc i)" (is "apply_effects adds dels (MS' i) ?S = MS' (Suc i)")
       and "invs_at ?Inv' (?t i) \<subseteq> MS' i"
       and "\<Union> (pre' ` happ_at ?B (?t i)) \<subseteq> MS' i"
       if i_ran: "i < length (htpl \<pi>)" for i
    proof -
      show "apply_effects adds dels (MS' i) ?S = MS' (Suc i)" 
      proof -
        have "\<Union>(adds ` ?S) \<subseteq> fluents" 
             "\<Union>(dels ` ?S) \<subseteq> fluents" using i_ran cv_hs unfolding fluent_state_seq_def by auto
        hence "\<forall>s\<in>happ_at (plan_happ_seq \<pi> at_start at_end) (time_index \<pi> i). snap_mod_fluents fluents adds dels s" by blast
        thus "apply_effects adds dels (MS' i) ?S = MS' (Suc i)" using app_fluent_valid_snaps[OF _ app_eff[OF that]] using MS'_p that by simp
      qed
      show "invs_at ?Inv' (?t i) \<subseteq> MS' i" 
      proof -
        have "invs_at (plan_inv_seq \<pi> over_all') (time_index \<pi> i) = invs_at (plan_inv_seq \<pi> over_all) (time_index \<pi> i) \<inter> fluents" 
          unfolding invs_at_def plan_inv_seq_def over_all'_def by auto
        thus "invs_at ?Inv' (?t i) \<subseteq> MS' i" using invs MS'_p i_ran by auto
      qed
      show "\<Union> (pre' ` ?S) \<subseteq> MS' i" 
      proof -
        have "\<Union> (pre ` ?S) \<inter> fluents =  \<Union> (pre' ` ?S)" unfolding  plan_happ_seq_def pre'_def by auto
        thus "\<Union> (pre' ` ?S) \<subseteq> MS' i" using pres MS'_p i_ran by auto
      qed
    qed
    thus "valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS'" unfolding valid_state_sequence_def by (auto simp: Let_def)
  qed
  ultimately
  show "valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS' \<and>
  fluent_plan \<pi> fluents at_start at_end over_all' pre' adds dels \<and> fluent_state_seq \<pi> fluents MS'" by (auto intro: exI[where x = "\<lambda>i. (MS i \<inter> fluents)"])
qed

lemma cvp_state_seq':
  assumes MS'_p: "\<forall>i \<le> length (htpl \<pi>). MS' i \<inter> fluents = MS i \<inter> fluents" 
                 "\<forall>i \<le> length (htpl \<pi>). (MS i - fluents) = (MS' i - fluents) \<union> domain_consts \<pi> fluents init goal at_start at_end over_all pre adds dels" 
    and vss: "valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS'"
  shows "valid_state_sequence \<pi> at_start at_end over_all pre adds dels MS"
proof -

  let ?B = "plan_happ_seq \<pi> at_start at_end"
  let ?t = "time_index \<pi>"

  let ?Inv = "plan_inv_seq \<pi> over_all"
  let ?Inv' = "plan_inv_seq \<pi> over_all'"

  let ?dc = "domain_consts \<pi> fluents init goal at_start at_end over_all pre adds dels"

  from MS'_p
  have MS'_p': "\<forall>i \<le> length (htpl \<pi>). MS' i \<union> ?dc = MS i" by auto

  from cvp cv_plan_imp_cv_hs
  have cv_hs: "\<forall>t. (\<forall>h \<in> happ_at ?B t. snap_mod_fluents fluents adds dels h)" unfolding const_valid_happ_seq_def by blast

  from vss[simplified valid_state_sequence_def]
  have app_eff: "apply_effects adds dels (MS' i) (happ_at ?B (?t i)) = MS' (Suc i)"
       and invs: "invs_at ?Inv' (?t i) \<subseteq> MS' i"
       and pres: "\<Union> (pre' ` happ_at ?B (?t i)) \<subseteq> MS' i"
       if "i < length (htpl \<pi>)" for i using that by (auto simp: Let_def)

  have dc: "?dc = 
    \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - fluents \<union> (goal - fluents) \<union> (init - fluents)" (is "?dc = ?dc'")
    using cv_domain_consts cvp by fastforce
  have "apply_effects adds dels (MS i) (happ_at ?B (?t i)) = MS (Suc i)" (is "apply_effects adds dels (MS i) ?S = MS (Suc i)")
     and "invs_at ?Inv (?t i) \<subseteq> MS i"
     and "\<Union> (pre ` happ_at ?B (?t i)) \<subseteq> MS i"
     if i_ran: "i < length (htpl \<pi>)" for i
  proof -
    show "apply_effects adds dels (MS i) ?S = MS (Suc i)" 
    proof -
      have "\<Union>(adds ` ?S) \<subseteq> fluents" (is "?as \<subseteq> fluents")
           "\<Union>(dels ` ?S) \<subseteq> fluents" (is "?ds \<subseteq> fluents") using i_ran cv_hs unfolding fluent_state_seq_def by auto
      hence "?as \<inter> ?dc = {}"
            "?ds \<inter> ?dc = {}" using dc by auto
      moreover
      from app_eff i_ran
      have "(MS' i - ?ds) \<union> ?as = MS' (Suc i)" unfolding apply_effects_def by simp
      ultimately
      have "(MS' i \<union> ?dc) - ?ds \<union> ?as = MS' (Suc i) \<union> ?dc" by auto
      thus "apply_effects adds dels (MS i) ?S = MS (Suc i)" unfolding apply_effects_def using MS'_p' i_ran by simp
    qed
    show "invs_at ?Inv (?t i) \<subseteq> MS i" 
    proof -
      have "invs_at ?Inv (?t i) \<subseteq> invs_at ?Inv' (?t i) \<union> ?dc" 
        unfolding invs_at_def plan_inv_seq_def dc over_all'_def by auto
      hence "invs_at ?Inv (?t i) \<subseteq> MS' i \<union> ?dc" using invs i_ran by auto
      thus "invs_at ?Inv (?t i) \<subseteq> MS i" 
        apply -
        apply (erule subset_trans)
        using MS'_p' i_ran by auto
    qed
    show "\<Union> (pre ` ?S) \<subseteq> MS i" 
    proof -
      from pres i_ran
      have "\<Union> (pre' ` ?S) \<subseteq> MS' i" by simp
      hence "\<Union> (pre ` ?S) \<inter> fluents \<subseteq> MS' i" unfolding pre'_def by simp
      moreover
      from cvp[simplified cv_plan_cv_happ_seq, THEN cv_happ_seq_consts]
      have "\<Union> (pre ` ?S) - fluents \<subseteq> happ_seq_consts \<pi> fluents at_start at_end pre adds dels - fluents" by auto
      hence "\<Union> (pre ` ?S) - fluents \<subseteq> ?dc" using plan_and_happ_seq_consts unfolding domain_consts_def by fast
      ultimately
      have "\<Union> (pre ` ?S) \<subseteq> MS' i \<union> ?dc" by blast
      thus "\<Union> (pre ` ?S) \<subseteq> MS i" using MS'_p' i_ran by simp
    qed
  qed
  thus "valid_state_sequence \<pi> at_start at_end over_all pre adds dels MS" unfolding valid_state_sequence_def by (auto simp: Let_def)
qed

text \<open>Not necessary, probably.\<close>
lemma cvp_nm_happ_seq_equiv: "nm_happ_seq pre adds dels \<epsilon> (plan_happ_seq \<pi> at_start at_end) \<longleftrightarrow> nm_happ_seq pre' adds dels \<epsilon> (plan_happ_seq \<pi> at_start at_end)"
proof -
  from cvp
  have "const_valid_happ_seq \<pi> fluents at_start at_end adds dels" using cv_plan_cv_happ_seq by blast
  from this[simplified const_valid_happ_seq_def]
  have "\<forall>s t a b. a \<in> happ_at (plan_happ_seq \<pi> at_start at_end) s \<and> b \<in> happ_at (plan_happ_seq \<pi> at_start at_end) t
    \<longrightarrow> (mutex_snap_action pre adds dels a b \<longleftrightarrow> mutex_snap_action pre' adds dels a b)" unfolding mutex_snap_action_def 
    apply -
    apply (intro allI; rule impI; rule iffI; erule conjE)
     apply (elim disjE)
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre'_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre'_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre'_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre'_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre'_def by auto
    done
  thus ?thesis unfolding nm_happ_seq_def by blast
qed


text \<open>An attempt was made to remove these assumptions by proving that constants in a plan are
      indeed constant. However, this only works for the direction of the proof that does not 
      need it.\<close>

lemma cvp_mutex_plan_equiv:
  "mutex_valid_plan \<pi> at_start at_end pre adds dels \<epsilon> \<longleftrightarrow> mutex_valid_plan \<pi> at_start at_end pre' adds dels \<epsilon>"
proof -
  have mutex_equiv: "mutex_snap_action pre adds dels a b \<longleftrightarrow> mutex_snap_action pre' adds dels a b"
    if "adds a \<subseteq> fluents" "dels a \<subseteq> fluents" "adds b \<subseteq> fluents" "dels b \<subseteq> fluents" for a b
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

    show "mutex_snap_action pre adds dels a b \<longleftrightarrow> mutex_snap_action pre' adds dels a b"
      unfolding mutex_snap_action_def pre'_def
      apply (rule iffI; elim disjE)
      subgoal by (drule j[of _ _ fluents], rule i; simp add: that)
      subgoal by simp
      subgoal by (drule j[of _ _ fluents], rule i; simp add: that)
      subgoal by simp
      subgoal by (drule k, rule i, simp_all add: that)
      subgoal by simp
      subgoal by (drule k, rule i, simp_all add: that)
      by simp
  qed

  have mutex_equiv': "mutex_snap_action pre adds dels (f a) (g b)
    \<longleftrightarrow> mutex_snap_action pre' adds dels (f a) (g b)" 
    if "\<exists>t d. (a, t, d)\<in>ran \<pi>" "\<exists>t d. (b, t, d)\<in>ran \<pi>" "f = at_start \<or> f = at_end" "g = at_start \<or> g = at_end" for a b f g
    using that
    apply -
    apply (elim disjE; rule mutex_equiv)
    using cvp unfolding const_valid_plan_def act_mod_fluents_def
    by blast+

  have mutex_self: "mutex_snap_action pre adds dels (at_start a) (at_end a) \<longleftrightarrow> mutex_snap_action pre' adds dels (at_start a) (at_end a)" 
    if "\<exists>t d. (a, t, d)\<in>ran \<pi>" for a
    using that mutex_equiv'[of a a at_start at_end] by simp
  hence "(\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action pre adds dels (at_start a) (at_end a))
    \<longleftrightarrow> (\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action pre' adds dels (at_start a) (at_end a))"
    by fast
  moreover
  
  have mutex_sched: "mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db \<longleftrightarrow> mutex_sched at_start at_end pre' adds dels \<epsilon> a ta da b tb db" if 
    "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)" for i j a ta da b tb db
  proof -
    have ab_ran: "\<exists>t d. (a, t, d) \<in> ran \<pi>" "\<exists>t d. (b, t, d) \<in> ran \<pi>" using that ranI by fast+
    show ?thesis
    proof 
      assume as: "mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db"
      have "\<not> mutex_snap_action pre' adds dels sa sb" 
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
          apply (cases)
          subgoal apply (simp add: mutex_equiv'[OF ab_ran, symmetric])
            using t as[simplified mutex_sched_def] by blast
          subgoal apply (simp add: mutex_equiv'[OF ab_ran, symmetric])
            using t as[simplified mutex_sched_def] by blast
          subgoal apply (simp add: mutex_equiv'[OF ab_ran, symmetric])
            using t as[simplified mutex_sched_def] by blast
          subgoal apply (simp add: mutex_equiv'[OF ab_ran, symmetric])
            using t as[simplified mutex_sched_def] by blast
          done 
      qed
      thus "mutex_sched at_start at_end pre' adds dels \<epsilon> a ta da b tb db" 
        unfolding mutex_sched_def by blast
  
    next
      assume as: "mutex_sched at_start at_end pre' adds dels \<epsilon> a ta da b tb db"
      have "\<not> mutex_snap_action pre adds dels sa sb" 
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
          apply (cases)
          subgoal apply (simp add: mutex_equiv'[OF ab_ran])
            using t as[simplified mutex_sched_def] by blast
          subgoal apply (simp add: mutex_equiv'[OF ab_ran])
            using t as[simplified mutex_sched_def] by blast
          subgoal apply (simp add: mutex_equiv'[OF ab_ran])
            using t as[simplified mutex_sched_def] by blast
          subgoal apply (simp add: mutex_equiv'[OF ab_ran])
            using t as[simplified mutex_sched_def] by blast
          done 
      qed
      thus "mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db" 
        unfolding mutex_sched_def by blast
    qed
  qed
  hence "(\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db) \<longleftrightarrow>
     (\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched at_start at_end pre' adds dels \<epsilon> a ta da b tb db)"
    by blast
  ultimately
  show ?thesis
    unfolding mutex_valid_plan_eq mutex_valid_plan_alt_def
    by argo
qed


lemma const_plan_equiv: 
  assumes "goal - fluents \<subseteq> init - fluents"
      and "plan_consts \<pi> fluents at_start at_end over_all pre adds dels \<subseteq> init - fluents"
    shows "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon> \<longleftrightarrow>
       valid_plan \<pi> (fluent_state fluents init) (fluent_state fluents goal) at_start at_end over_all' lower upper pre' adds dels \<epsilon>" 
  unfolding valid_plan_def
proof
  assume "\<exists>M. valid_state_sequence \<pi> at_start at_end over_all pre adds dels M \<and>
        M 0 = init \<and>
        goal \<subseteq> M (length (htpl \<pi>)) \<and>
        durations_ge_0 \<pi> \<and> durations_valid \<pi> lower upper \<and> 
        mutex_valid_plan \<pi> at_start at_end pre adds dels \<epsilon> \<and> 
        finite_plan \<pi>"
  then obtain MS where
    vss: "valid_state_sequence \<pi> at_start at_end over_all pre adds dels MS"
    and init: "MS 0 = init"
    and goal: "goal \<subseteq> MS (length (htpl \<pi>))"
    and dur: "durations_ge_0 \<pi> \<and> durations_valid \<pi> lower upper"
    and mutex: "mutex_valid_plan \<pi> at_start at_end pre adds dels \<epsilon>"
    and finite: "finite_plan \<pi>" by blast

  define MS' where "MS' = (\<lambda>i. if (i \<le> length (htpl \<pi>)) then MS i \<inter> fluents else undefined)"  
  hence "\<forall>i \<le> length (htpl \<pi>). MS' i = MS i \<inter> fluents" by auto
  with vss 
  have vss': "valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS'" 
    and fss': "fluent_state_seq \<pi> fluents MS'" 
    and fp: "fluent_plan \<pi> fluents at_start at_end over_all' pre' adds dels"
    using cvp_state_seq by auto

  from MS'_def goal
  have goal': "goal \<inter> fluents \<subseteq> MS' (length (htpl \<pi>))" by auto

  from MS'_def init
  have init': "init \<inter> fluents = MS' 0" by simp

  show "\<exists>M. valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels M \<and>
      M 0 = fluent_state fluents init \<and>
      fluent_state fluents goal \<subseteq> M (length (htpl \<pi>)) \<and>
      durations_ge_0 \<pi> \<and> durations_valid \<pi> lower upper \<and>
      mutex_valid_plan \<pi> at_start at_end pre' adds dels \<epsilon> \<and>
      finite_plan \<pi>"
    using vss' cvp_mutex_plan_equiv dur init' goal' mutex finite 
    unfolding fluent_state_def by blast
next
  assume "\<exists>M. valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels M \<and>
        M 0 = fluent_state fluents init \<and>
        fluent_state fluents goal \<subseteq> M (length (htpl \<pi>)) \<and>
        durations_ge_0 \<pi> \<and> durations_valid \<pi> lower upper \<and>
        mutex_valid_plan \<pi> at_start at_end pre' adds dels \<epsilon> \<and>
        finite_plan \<pi>"
  then obtain MS' where
    vss': "valid_state_sequence \<pi> at_start at_end over_all' pre' adds dels MS'"
    and init': "MS' 0 = init \<inter> fluents"
    and goal': "goal \<inter> fluents \<subseteq> MS' (length (htpl \<pi>))"
    and dur: "durations_ge_0 \<pi> \<and> durations_valid \<pi> lower upper"
    and mutex: "mutex_valid_plan \<pi> at_start at_end pre' adds dels \<epsilon>"
    and finite: "finite_plan \<pi>" unfolding fluent_state_def by auto

  let ?dc = "domain_consts \<pi> fluents init goal at_start at_end over_all pre adds dels"

  define MS where "MS \<equiv> \<lambda>i. if (i \<le> length (htpl \<pi>)) then MS' i \<union> ?dc else undefined"
  have "\<forall>i\<le>length (htpl \<pi>). MS i - fluents = (MS' i - fluents) \<union> ?dc"
  proof (rule allI; rule impI)
    fix i
    assume "i \<le> length (htpl \<pi>)"
    hence "MS i = MS' i \<union> ?dc" using MS_def by simp
    hence "MS i - fluents = MS' i \<union> ?dc - fluents" by simp
    hence "MS i - fluents = (MS' i - fluents) \<union> (?dc - fluents)" by auto
    thus "MS i - fluents = (MS' i - fluents) \<union> ?dc" using domain_consts_not_fluent by fast
  qed
  hence vss: "valid_state_sequence \<pi> at_start at_end over_all pre adds dels MS" 
    using vss' MS_def cvp_state_seq'[where MS = MS and MS' = MS'] by fastforce
  
  show "\<exists>M. valid_state_sequence \<pi> at_start at_end over_all pre adds dels M \<and>
        M 0 = init \<and> goal \<subseteq> M (length (htpl \<pi>)) \<and> durations_ge_0 \<pi> \<and> 
        durations_valid \<pi> lower upper \<and>
        mutex_valid_plan \<pi> at_start at_end pre adds dels \<epsilon> \<and>
        finite_plan \<pi>"
  proof (cases "length (htpl \<pi>)")
    case 0
    define MS where "MS \<equiv> (\<lambda>x. init)" 
    
    have "goal \<inter> fluents \<subseteq> init \<inter> fluents" using init' goal' 0  by simp
    hence init_goal: "goal \<subseteq> init" using assms by blast
    have any: "\<forall>M. valid_state_sequence \<pi> at_start at_end over_all pre adds dels M"
      unfolding valid_state_sequence_def using 0 by (auto simp: Let_def)
    show ?thesis using init_goal MS_def any dur mutex cvp_mutex_plan_equiv finite by auto
  next
    case (Suc nat)
    have init: "init = MS 0" unfolding MS_def domain_consts_def using assms Suc using init' by auto
    moreover
    have goal: "goal \<subseteq> MS (length (htpl \<pi>))" unfolding MS_def using goal' unfolding domain_consts_def by auto
    ultimately
    show ?thesis using dur mutex cvp_mutex_plan_equiv finite vss by auto
  qed
qed 
end

text \<open>Another thing we need to prove is the relationship between at_start, at_end, 
  pre, adds, and dels.\<close>

context 
  fixes \<pi>::"('i, 'action, 'time::time) temp_plan"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and at_start'::"'action \<Rightarrow> 'snap_action_1"
    and at_end'::  "'action  \<Rightarrow> 'snap_action_1"
    and pre'::     "'snap_action_1 \<Rightarrow> 'proposition set"
    and adds'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and dels'::    "'snap_action_1 \<Rightarrow> 'proposition set"
  assumes start_snap_replacement: 
    "\<forall>(a, t, d) \<in> ran \<pi>. pre (at_start a) = pre' (at_start' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. adds (at_start a) = adds' (at_start' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. dels (at_start a) = dels' (at_start' a)"
    and end_snap_replacement:
    "\<forall>(a, t, d) \<in> ran \<pi>. pre (at_end a) = pre' (at_end' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. adds (at_end a) = adds' (at_end' a)"
    "\<forall>(a, t, d) \<in> ran \<pi>. dels (at_end a) = dels' (at_end' a)"
begin


lemma f_transfer_1: 
  assumes "\<forall>(a, t, d) \<in> ran \<pi>. f (at_start a) = f' (at_start' a)"
      and "\<forall>(a, t, d) \<in> ran \<pi>. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f ` (happ_at (plan_happ_seq \<pi> at_start at_end) t)) \<subseteq> \<Union>(f' ` (happ_at (plan_happ_seq \<pi> at_start' at_end') t))"
proof (rule subsetI)
  fix x
  assume "x \<in> \<Union> (f ` happ_at (plan_happ_seq \<pi> at_start at_end) t)"
  then obtain h where
    x: "x \<in> f h"
    and x_happ: "(t, h) \<in> plan_happ_seq \<pi> at_start at_end" by blast
  have "\<exists>h. x \<in> f' h \<and> h \<in> happ_at (plan_happ_seq \<pi> at_start' at_end') t" 
    apply (cases rule: in_happ_seqE[OF x_happ])
    using assms x unfolding  plan_happ_seq_def by blast+
  thus "x \<in> \<Union> (f' ` happ_at (plan_happ_seq \<pi> at_start' at_end') t)" by blast
qed

lemma f_transfer_2:
  assumes "\<forall>(a, t, d) \<in> ran \<pi>. f (at_start a) = f' (at_start' a)"
      and "\<forall>(a, t, d) \<in> ran \<pi>. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f' ` (happ_at (plan_happ_seq \<pi> at_start' at_end') t)) \<subseteq> \<Union>(f ` (happ_at (plan_happ_seq \<pi> at_start at_end) t))"
proof (rule subsetI)
  fix x
  assume "x \<in> \<Union> (f' ` happ_at (plan_happ_seq \<pi> at_start' at_end') t)"
  then obtain h where
    x: "x \<in> f' h"
    and x_happ: "(t, h) \<in> plan_happ_seq \<pi> at_start' at_end'" by blast
  have "\<exists>h. x \<in> f h \<and> h \<in> happ_at (plan_happ_seq \<pi> at_start at_end) t" 
    apply (cases rule: in_happ_seqE[OF x_happ])
    using assms x unfolding  plan_happ_seq_def by blast+
  thus "x \<in> \<Union> (f ` happ_at (plan_happ_seq \<pi> at_start at_end) t)" by blast
qed

lemma f_transfer:
  assumes "\<forall>(a, t, d) \<in> ran \<pi>. f (at_start a) = f' (at_start' a)"
      and "\<forall>(a, t, d) \<in> ran \<pi>. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f ` (happ_at (plan_happ_seq \<pi> at_start at_end) t)) = \<Union>(f' ` (happ_at (plan_happ_seq \<pi> at_start' at_end') t))"
  apply (rule equalityI) using f_transfer_1[OF assms] f_transfer_2[OF assms] by auto

lemmas pre_transfer = f_transfer[OF start_snap_replacement(1) end_snap_replacement(1)]
lemmas adds_transfer = f_transfer[OF start_snap_replacement(2) end_snap_replacement(2)]
lemmas dels_transfer = f_transfer[OF start_snap_replacement(3) end_snap_replacement(3)]

lemma vss_equiv_if_snaps_functionally_equiv:
  "valid_state_sequence \<pi> at_start at_end over_all pre adds dels MS \<longleftrightarrow> valid_state_sequence \<pi> at_start' at_end' over_all pre' adds' dels' MS"
  unfolding valid_state_sequence_def  using adds_transfer dels_transfer pre_transfer unfolding Let_def apply_effects_def by simp

lemma in_happ_seq_trans_1:  
  assumes "h \<in> happ_at (plan_happ_seq \<pi> at_start at_end) time" 
    shows "\<exists>h' \<in> happ_at (plan_happ_seq \<pi> at_start' at_end') time. pre h = pre' h' \<and> adds h = adds' h' \<and> dels h = dels' h'"
  apply (cases rule: in_happ_seqE[OF assms[simplified]])
  unfolding plan_happ_seq_def using start_snap_replacement apply blast
  using end_snap_replacement by fastforce

lemma in_happ_seqE1:
  assumes "h \<in> happ_at (plan_happ_seq \<pi> at_start at_end) time" 
      and "\<And>h'. h' \<in> happ_at (plan_happ_seq \<pi> at_start' at_end') time \<Longrightarrow> pre h = pre' h' \<Longrightarrow> adds h = adds' h' \<Longrightarrow> dels h = dels' h' \<Longrightarrow> thesis"
    shows thesis
  using in_happ_seq_trans_1 assms by blast

lemma in_happ_seq_trans_2:  
  assumes "h \<in> happ_at (plan_happ_seq \<pi> at_start' at_end') time" 
    shows "\<exists>h' \<in> happ_at (plan_happ_seq \<pi> at_start at_end) time. pre h' = pre' h \<and> adds h' = adds' h \<and> dels h' = dels' h"
  apply (rule in_happ_seqE[OF assms[simplified]])
  unfolding plan_happ_seq_def using start_snap_replacement apply blast
  using end_snap_replacement by fastforce

lemma in_happ_seqE2:  
  assumes "h \<in> happ_at (plan_happ_seq \<pi> at_start' at_end') time" 
      and "\<And>h'. h' \<in> happ_at (plan_happ_seq \<pi> at_start at_end) time \<Longrightarrow> pre h' = pre' h \<Longrightarrow> adds h' = adds' h \<Longrightarrow> dels h' = dels' h \<Longrightarrow> thesis"
    shows thesis
  using assms in_happ_seq_trans_2 by blast

lemma mutex_snap_action_equiv:
  assumes a: "\<exists>t d. (a, t, d) \<in> ran \<pi>"
      and b: "\<exists>t d. (b, t, d) \<in> ran \<pi>"
      and h: "h = at_start a \<and> h' = at_start' a \<or> h = at_end a \<and> h' = at_end' a"
      and i: "i = at_start b \<and> i' = at_start' b \<or> i = at_end b \<and> i' = at_end' b"
    shows "mutex_snap_action pre adds dels h i
    \<longleftrightarrow> mutex_snap_action pre' adds' dels' h' i'"
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
  show ?thesis unfolding mutex_snap_action_def by simp
qed

lemma mutex_valid_plan_equiv_if_snaps_functionally_equiv:
  "mutex_valid_plan \<pi> at_start at_end pre adds dels \<epsilon> 
\<longleftrightarrow> mutex_valid_plan \<pi> at_start' at_end' pre' adds' dels' \<epsilon>"
proof -
  have "(\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action pre adds dels (at_start a) (at_end a))
    \<longleftrightarrow> (\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action pre' adds' dels' (at_start' a) (at_end' a))"
    using mutex_snap_action_equiv by fast
  moreover
  have "mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db \<longleftrightarrow> mutex_sched at_start' at_end' pre' adds' dels' \<epsilon> a ta da b tb db" if 
    "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" 
    "\<pi> i = Some (a, ta, da)" 
    "\<pi> j = Some (b, tb, db)" for i j a ta da b tb db
   proof -
     have ab_ran: "\<exists>t d. (a, t, d) \<in> ran \<pi>" "\<exists>t d. (b, t, d) \<in> ran \<pi>" 
       using that ranI by fast+
    show ?thesis 
         proof 
      assume as: "mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db"
      have "\<not> mutex_snap_action pre' adds' dels' sa sb" 
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
          have "\<not>mutex_snap_action pre adds dels (at_start a) (at_start b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 1 by auto
        next
          case 2
          with t as
          have "\<not>mutex_snap_action pre adds dels (at_start a) (at_end b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 2 by auto
        next
          case 3
          with t as
          have "\<not>mutex_snap_action pre adds dels (at_end a) (at_start b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 3 by auto
        next
          case 4
          with t as
          have "\<not>mutex_snap_action pre adds dels (at_end a) (at_end b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 4 by auto
        qed
      qed
      thus "mutex_sched at_start' at_end' pre' adds' dels' \<epsilon> a ta da b tb db" 
        unfolding mutex_sched_def by blast
    next
      assume as: "mutex_sched at_start' at_end' pre' adds' dels' \<epsilon> a ta da b tb db"
      have "\<not> mutex_snap_action pre adds dels sa sb" 
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
          have "\<not>mutex_snap_action pre' adds' dels' (at_start' a) (at_start' b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 1 by auto
        next
          case 2
          with t as
          have "\<not>mutex_snap_action pre' adds' dels' (at_start' a) (at_end' b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 2 by auto
        next
          case 3
          with t as
          have "\<not>mutex_snap_action pre' adds' dels' (at_end' a) (at_start' b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 3 by auto
        next
          case 4
          with t as
          have "\<not>mutex_snap_action pre' adds' dels' (at_end' a) (at_end' b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv[OF ab_ran] 4 by auto
        qed
      qed
      thus "mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db" 
        unfolding mutex_sched_def by blast
    qed
  qed
  hence "(\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched at_start at_end pre adds dels \<epsilon> a ta da b tb db) 
  \<longleftrightarrow> (\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched at_start' at_end' pre' adds' dels' \<epsilon> a ta da b tb db)" by blast
  ultimately
  show ?thesis unfolding mutex_valid_plan_eq mutex_valid_plan_alt_def by argo
qed

lemma valid_plan_equiv_if_snaps_functionally_equiv:
  "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon>
  \<longleftrightarrow> valid_plan \<pi> init goal at_start' at_end' over_all lower upper pre' adds' dels' \<epsilon>"
  unfolding valid_plan_def
  using vss_equiv_if_snaps_functionally_equiv mutex_valid_plan_equiv_if_snaps_functionally_equiv
  by simp
end

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

locale finite_props_temp_planning_problem = 
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
    and props:: "'proposition set"
    and actions:: "'action set"
  + assumes fluent_domain: "fluent_domain props at_start at_end over_all pre adds dels actions"
        and init_props: "init \<subseteq> props"
        and goal_props: "goal \<subseteq> props"

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
begin

abbreviation "over_all' \<equiv> (\<lambda>a. over_all a \<inter> fluents)"
abbreviation "pre' \<equiv> (\<lambda>s. pre s \<inter> fluents)"
abbreviation "init' \<equiv> init \<inter> fluents"
abbreviation "goal' \<equiv> goal \<inter> fluents"

sublocale finite_props_temp_planning_problem init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon> fluents actions 
  apply standard using finite_fluent_domain 
  unfolding const_valid_domain_def fluent_domain_def act_mod_fluents_def act_ref_fluents_def
  by blast+

context 
  fixes \<pi>::"('i, 'action, 'time) temp_plan"
  assumes plan_actions_in_problem: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
      and actions_wf: "\<forall>a \<in> actions. act_consts fluents at_start at_end over_all pre adds dels a \<subseteq> init - fluents"
      and dom_wf: "goal - fluents \<subseteq> init - fluents" (* This is necessary, so we don't admit invalid plans *)
begin
  lemma valid_plan_in_finite_props:
    "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon> 
  \<longleftrightarrow> valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>"
  proof (rule const_plan_equiv[simplified fluent_state_def])
    show "const_valid_plan \<pi> fluents at_start at_end adds dels" using plan_actions_in_problem finite_fluent_domain const_valid_plan_def const_valid_domain_def by fast
    show "plan_consts \<pi> fluents at_start at_end over_all pre adds dels \<subseteq> init - fluents" 
      using plan_actions_in_problem actions_wf unfolding plan_consts_def by blast
  qed (auto simp: dom_wf)
end
end

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
  sublocale unique_snaps_temp_planning_problem 
    init goal AtStart AtEnd over_all lower upper 
    "pre_imp at_start at_end pre" "add_imp at_start at_end adds" "del_imp at_start at_end dels" \<epsilon> props actions 
  proof
    show "inj_on AtStart actions" "inj_on AtEnd actions" unfolding inj_on_def by blast+
    show "AtStart ` actions \<inter> AtEnd ` actions = {}" by blast
  qed
end

locale finite_fluent_temp_planning_problem' = 
  finite_fluent_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> fluents actions
+ finite_temp_planning_problem' init goal at_start at_end over_all lower upper pre adds dels \<epsilon> fluents actions
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
  abbreviation pre_imp'::"'action snap_action \<Rightarrow> 'proposition set" where
  "pre_imp' \<equiv> \<lambda>x. (pre_imp at_start at_end pre x \<inter> fluents)"
  
  sublocale unique_snaps_temp_planning_problem 
    init' goal' AtStart AtEnd over_all' lower upper 
    pre_imp' "add_imp at_start at_end adds" "del_imp at_start at_end dels" \<epsilon> fluents actions 
    ..
  
  sublocale finite_props_temp_planning_problem 
    init' goal' AtStart AtEnd over_all' lower upper 
    pre_imp' "add_imp at_start at_end adds" "del_imp at_start at_end dels" \<epsilon> fluents actions
    apply standard
    using finite_fluent_domain
    unfolding add_imp_def del_imp_def fluent_domain_def act_ref_fluents_def pre_imp_def const_valid_domain_def act_mod_fluents_def
    by auto

  context
    fixes \<pi>::"('i, 'action, 'time) temp_plan"
    assumes plan_actions_in_problem: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
        and actions_wf: "\<forall>a \<in> actions. act_consts fluents at_start at_end over_all pre adds dels a \<subseteq> init - fluents"
        and dom_wf: "goal - fluents \<subseteq> init - fluents" (* This is necessary, so we don't admit invalid plans *)
  begin
  lemma valid_plan_alt:
    "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon>
      \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd over_all' lower upper pre_imp' (add_imp at_start at_end adds) (del_imp at_start at_end dels) \<epsilon>"
  proof -
    have "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon> 
    \<longleftrightarrow> valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>"
      using valid_plan_in_finite_props plan_actions_in_problem actions_wf dom_wf by blast
    moreover
    have "valid_plan \<pi> init' goal' at_start at_end over_all' lower upper pre' adds dels \<epsilon>
    \<longleftrightarrow> valid_plan \<pi> init' goal' AtStart AtEnd over_all' lower upper pre_imp' (add_imp at_start at_end adds) (del_imp at_start at_end dels) \<epsilon>"
      apply (rule valid_plan_equiv_if_snaps_functionally_equiv)
      unfolding pre_imp_def add_imp_def del_imp_def by simp+
    ultimately
    show ?thesis by simp
  qed
  end
end

locale ta_temp_planning = 
  finite_props_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions  +
  unique_snaps_temp_planning_problem init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions 
    for props::   "('proposition::linorder) set"
    and actions:: "('action::linorder) set"
    and init::    "'proposition set"
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
end
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

text \<open>Temporal plans could be multi-sets, lists or just the range of a partial function. 
It is only necessary that the entries do not have to be unique, because unique entries are a 
consequence of prohibiting self-overlap. I chose a partial function.\<close>
type_synonym ('i, 'a, 't) temp_plan = "'i \<rightharpoonup> ('a \<times> 't \<times> 't)"
context
  fixes \<pi>::"('i, 'action, 'time::time) temp_plan"
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
text \<open>We want to define a plan in an abstract manner. This needs to be more abstract.\<close>
definition mutex_snap_action::"'snap_action \<Rightarrow> 'snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  (pre a) \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  ((adds a) \<inter> (dels b)) \<noteq> {} \<or>
  (pre b) \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b) \<inter> (dels a) \<noteq> {}
)"

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

definition happ_at::"('time \<times> 'snap_action) set \<Rightarrow> 'time \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s. (t, s) \<in> B}"

lemma a_in_B_iff_t_in_htps: "(\<exists>a. a \<in> happ_at plan_happ_seq t) \<longleftrightarrow> (t \<in> htps)"
proof
  assume "\<exists>a. a \<in> happ_at plan_happ_seq t"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" unfolding happ_at_def plan_happ_seq_def by fast
  thus "t \<in> htps" unfolding plan_happ_seq_def htps_def by blast
next
  assume "t \<in> htps"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" unfolding plan_happ_seq_def htps_def by force
  thus "\<exists>a. a \<in> happ_at plan_happ_seq t" unfolding happ_at_def by blast
qed

text \<open>If something is in the happening sequence, then there must be an action in the plan.\<close>
lemma in_happ_seqE:
  assumes in_happ_seq: "(t, snap) \<in> plan_happ_seq"
  shows "\<exists>t d a. (a, t, d) \<in> ran \<pi> \<and> (at_start a = snap \<or> at_end a = snap)"
  using assms unfolding plan_happ_seq_def by blast

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
  (\<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> ((a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b) 
    \<and> (a = b \<longrightarrow> t = u)))
  \<and> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"

lemma eps_zero_imp_zero_sep: 
  assumes "\<epsilon> = 0"
  shows "nm_happ_seq B = (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)" 
  using assms unfolding nm_happ_seq_def by fastforce

lemma eps_gt_zero_imp_eps_sep:
  assumes "0 < \<epsilon>"
  shows "nm_happ_seq B = (\<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> ((a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b) \<and> (a = b \<longrightarrow> t = u)))"
proof -
  from assms
  have "(\<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> (a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)) \<Longrightarrow> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"
    by force
  thus ?thesis unfolding nm_happ_seq_def using assms by blast
qed

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

definition valid_plan::"bool" where
"valid_plan \<equiv> \<exists>M. 
    valid_state_sequence M
    \<and> M 0 = init
    \<and> goal \<subseteq> M (length htpl)
    \<and> durations_ge_0
    \<and> durations_valid
    \<and> nm_happ_seq plan_happ_seq"

definition finite_plan::bool where
"finite_plan \<equiv> finite (dom \<pi>)"

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
lemma finite_htps: 
  assumes fp: "finite_plan"
    shows "finite htps"
proof -
  have 1: "finite ((\<lambda>(a, t, d). t) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). t + d) ` (ran \<pi>))"
    using fp[simplified finite_plan_def]
    by (simp add: finite_ran)+
  moreover
  have "(\<lambda>(a, t, d). t) ` (ran \<pi>) = {t |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). t + d) ` (ran \<pi>)  = {t + d |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite htps" unfolding htps_def by auto
qed

lemma set_htpl_eq_htps: 
  assumes fp: "finite_plan"
  shows "htps  = set htpl" 
  unfolding htpl_def set_sorted_list_of_set[OF finite_htps[OF assms(1)]]
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


lemma no_actions_between_indexed_timepoints: 
  assumes "finite_plan"
    "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'>time_index l. t' < time_index (Suc l) \<and> a \<in> happ_at plan_happ_seq t')"
  using no_non_indexed_time_points[OF assms(2)] 
    a_in_B_iff_t_in_htps finite_htps[OF assms(1)] 
  unfolding htpl_def by auto


lemma "i < length htpl 
  \<Longrightarrow> snap \<in> happ_at plan_happ_seq (time_index i) 
  \<Longrightarrow> \<exists>t d a. (a, t, d) \<in> ran \<pi> \<and> (at_start a = snap \<or> at_end a = snap)"
  apply (rule in_happ_seqE)
  unfolding happ_at_def by blast

end

locale basic_temp_planning_problem =
  fixes props::   "('proposition::linorder) set"
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
  assumes some_props:       "card props > 0"
      and some_actions:     "card actions > 0"
      and finite_props:     "finite props"
      and finite_actions:   "finite actions"
      and eps_range:        "0 \<le> \<epsilon>"
begin


text \<open>This is a property of plan actions\<close>
definition wf_act where
"wf_act a \<equiv> let snap_props = \<lambda>s. pre s \<union> adds s \<union> dels s
  in (
    snap_props (at_start a) \<subseteq> props
  \<and> snap_props (at_end a) \<subseteq> props
  \<and> over_all a \<subseteq> props)" 


(* For the compilation, all plan actions need to be in the problem. Moreover, all actions in the 
  problem need to only refer to propositions. Therefore, plan-actions in problem, implies wf-acts *)

(* If a plan exists where all actions only refer to the propositions, then a plan exists, where
  all actions only modify the propositions. Also the initial state  *)


(* 
  context 
    fixes \<pi>::"('i, 'action, 'time) temp_plan"
  begin
    
definition wf_acts where
"wf_acts \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. wf_act a)"

    (* PDDL plans must not modify equalities, but can use them in preconditions. *)
    definition act_mod_props where
      "act_mod_props a \<equiv> (
        let snap_effs = (\<lambda>s. adds s \<union> dels s)
        in snap_effs (at_start a) \<subseteq> props \<and> snap_effs (at_end a) \<subseteq> props
       )"
  
    definition plan_acts_mod_props where
      "plan_acts_mod_props = (\<forall>(a, t, d) \<in> ran \<pi>. act_mod_props a)"

    definition act_prec_ran where
      "act_prec_ran a \<equiv> (
        over_all a \<subseteq> props \<union> init
      \<and> pre (at_start a) \<subseteq> props \<union> init
      \<and> pre (at_end a) \<subseteq> props \<union> init
      )"

    definition plan_acts_prec_ranges where
      "plan_acts_prec_ranges \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. act_prec_ran a)"

    definition restr_props_in_state_seq::"'proposition state_sequence \<Rightarrow> 'proposition state_sequence" where
      "restr_props_in_state_seq M i \<equiv> (M i \<inter> props)"
    
    context 
      assumes prec_rans: plan_acts_prec_ranges
          and prop_upds: plan_acts_mod_props
    begin
      lemma over_all_imp_eq: "(\<lambda>t. invs_at (plan_inv_seq \<pi> over_all) t \<inter> props) = invs_at (plan_inv_seq \<pi> over_all_imp)"
        by (rule ext; auto simp: plan_inv_seq_def over_all_imp_def invs_at_def)

      lemma happ_seq_imp_eq_adds: "adds ` (happ_at (plan_happ_seq \<pi> at_start at_end) t) = add_imp ` (happ_at (plan_happ_seq \<pi> AtStart AtEnd) t)"
      proof (rule equalityI; rule subsetI)
        fix x
        assume "x \<in> adds ` happ_at (plan_happ_seq \<pi> at_start at_end) t"
        then 
        consider "x \<in> adds ` {at_start a |a d. (a, t, d) \<in> ran \<pi>}" | 
                 "x \<in> adds ` {at_end a |a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" unfolding happ_at_def plan_happ_seq_def by fast
        thus "x \<in> add_imp ` happ_at (plan_happ_seq \<pi> AtStart AtEnd) t"
        proof cases
          assume "x \<in> adds ` {at_start a |a d. (a, t, d) \<in> ran \<pi>}"
          hence "x \<in> add_imp ` {AtStart a|a d. (a, t, d) \<in> ran \<pi>}" unfolding add_imp_def by force
          thus ?thesis unfolding happ_at_def plan_happ_seq_def by blast
        next
          assume "x \<in> adds ` {at_end a|a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" 
          hence "x \<in> add_imp ` {AtEnd a|a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" unfolding add_imp_def by force
          thus ?thesis unfolding happ_at_def plan_happ_seq_def by blast
        qed
      next
        fix x
        assume "x \<in> add_imp ` happ_at (plan_happ_seq \<pi> AtStart AtEnd) t"
        thus "x \<in> adds ` happ_at (plan_happ_seq \<pi> at_start at_end) t" unfolding add_imp_def happ_at_def plan_happ_seq_def by force
      qed

    lemma happ_seq_imp_eq_dels: "dels ` (happ_at (plan_happ_seq \<pi> at_start at_end) t) = 
      del_imp ` (happ_at (plan_happ_seq \<pi> AtStart AtEnd) t)"
      proof (rule equalityI; rule subsetI)
        fix x
        assume "x \<in> dels ` happ_at (plan_happ_seq \<pi> at_start at_end) t"
        then 
        consider "x \<in> dels ` {at_start a |a d. (a, t, d) \<in> ran \<pi>}" | 
                 "x \<in> dels ` {at_end a |a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" 
          unfolding happ_at_def plan_happ_seq_def by fast
        thus "x \<in> del_imp ` happ_at (plan_happ_seq \<pi> AtStart AtEnd) t"
        proof cases
          assume "x \<in> dels ` {at_start a |a d. (a, t, d) \<in> ran \<pi>}"
          hence "x \<in> del_imp ` {AtStart a|a d. (a, t, d) \<in> ran \<pi>}" unfolding del_imp_def by force
          thus ?thesis unfolding happ_at_def plan_happ_seq_def by blast
        next
          assume "x \<in> dels ` {at_end a|a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" 
          hence "x \<in> del_imp ` {AtEnd a|a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" unfolding del_imp_def by force
          thus ?thesis unfolding happ_at_def plan_happ_seq_def by blast
        qed
      next
        fix x
        assume "x \<in> del_imp ` happ_at (plan_happ_seq \<pi> AtStart AtEnd) t"
        thus "x \<in> dels ` happ_at (plan_happ_seq \<pi> at_start at_end) t" unfolding del_imp_def happ_at_def plan_happ_seq_def by force
      qed

      lemma happ_seq_imp_eq_pres: "(\<lambda>x. pre x \<inter> props) ` (happ_at (plan_happ_seq \<pi> at_start at_end) t)
        = pre_imp ` (happ_at (plan_happ_seq \<pi> AtStart AtEnd) t)"
      proof (rule equalityI; rule subsetI)
        fix x
        assume "x \<in> (\<lambda>x. pre x \<inter> props) ` happ_at (plan_happ_seq \<pi> at_start at_end) t"
        then 
        consider "x \<in> (\<lambda>x. pre x \<inter> props) ` {at_start a |a d. (a, t, d) \<in> ran \<pi>}" | 
                 "x \<in> (\<lambda>x. pre x \<inter> props) ` {at_end a |a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" unfolding happ_at_def plan_happ_seq_def by fast
        thus "x \<in> pre_imp ` happ_at (plan_happ_seq \<pi> AtStart AtEnd) t"
        proof cases
          assume "x \<in> (\<lambda>x. pre x \<inter> props) ` {at_start a |a d. (a, t, d) \<in> ran \<pi>}"
          hence "x \<in> pre_imp ` {AtStart a|a d. (a, t, d) \<in> ran \<pi>}" unfolding pre_imp_def by force
          thus ?thesis unfolding happ_at_def plan_happ_seq_def by blast
        next
          assume "x \<in> (\<lambda>x. pre x \<inter> props) ` {at_end a|a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" 
          hence "x \<in> pre_imp ` {AtEnd a|a t' d. t' + d = t \<and> (a, t', d) \<in> ran \<pi>}" unfolding pre_imp_def by force
          thus ?thesis unfolding happ_at_def plan_happ_seq_def by blast
        qed
      next
        fix x
        assume "x \<in> pre_imp ` happ_at (plan_happ_seq \<pi> AtStart AtEnd) t"
        thus "x \<in> (\<lambda>x. pre x \<inter> props) ` happ_at (plan_happ_seq \<pi> at_start at_end) t" 
          unfolding pre_imp_def happ_at_def plan_happ_seq_def by force
      qed

      lemma happ_seq_imp_inv_eqs: "invs_at (plan_inv_seq \<pi> over_all) t \<inter> props
        = invs_at (plan_inv_seq \<pi> over_all_imp) t"
         unfolding invs_at_def plan_inv_seq_def over_all_imp_def 
         by (rule equalityI; rule subsetI) auto
    
      (* First prove that a valid plan where the actions are restricted to modify the propositions
         in the set,  *)
  
      lemma valid_state_seq_eq: "valid_state_sequence \<pi> at_start at_end over_all pre adds dels M =
        valid_state_sequence \<pi> AtStart AtEnd over_all_imp pre_imp add_imp del_imp (restr_props_in_state_seq M)"
        unfolding valid_state_sequence_def
      proof -
        define B where "B = happ_at (plan_happ_seq \<pi> at_start at_end)"
        define B' where "B' = happ_at (plan_happ_seq \<pi> AtStart AtEnd)"
        define ti where "ti = time_index \<pi>"

        have "\<forall>t i. apply_effects adds dels (M i) (B t) = M (Suc i) \<longleftrightarrow> 
          apply_effects add_imp del_imp (restr_props_in_state_seq M i) (B' t) = restr_props_in_state_seq M (Suc i)"
        proof (intro allI; rule iffI)
          fix t i
          assume a: "apply_effects adds dels (M i) (B t) = M (Suc i)"
          from prop_upds[simplified plan_acts_mod_props_def, simplified act_mod_props_def] in_happ_seqE
          have "\<forall>s \<in> happ_at (plan_happ_seq \<pi> at_start at_end) t. adds s \<subseteq> props \<and> dels s \<subseteq> props" 
            unfolding happ_at_def by fastforce
          hence "apply_effects adds dels (restr_props_in_state_seq M i) (B t) = restr_props_in_state_seq M (Suc i)"
            using a unfolding apply_effects_def B_def restr_props_in_state_seq_def by auto
          thus "apply_effects add_imp del_imp (restr_props_in_state_seq M i) (B' t) = restr_props_in_state_seq M (Suc i)"
            sorry
        qed
      qed

      lemma plan_with_eq_is_plan_without_eq: "valid_plan \<pi> init goal at_start at_end over_all lower upper pre adds dels \<epsilon>
              \<equiv> valid_plan \<pi> init_imp goal_imp AtStart AtEnd over_all_imp lower upper pre_imp add_imp del_imp \<epsilon>"
        sorry
end
  end *)
end

text \<open>By making the planning domain finite, it becomes possible to reduce it to a timed automaton
with a finite number of states.\<close>
locale temp_planning_problem = basic_temp_planning_problem props actions init goal at_start at_end over_all lower upper pre adds dels \<epsilon>
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
    and \<epsilon>::       "'time" +
  assumes wf_init:  "init \<subseteq> props" 
      and wf_goal:  "goal \<subseteq> props"
      and wf_acts:  "\<forall>a \<in> actions. wf_act a"
      and at_start_inj_on: "inj_on at_start actions"
      and at_end_inj_on:   "inj_on at_end actions"
      and snaps_disj:      "(at_start ` actions) \<inter> (at_end ` actions) = {}"
      and eps_range:       "0 \<le> \<epsilon>"
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

subsection \<open>Temporal plans\<close>
context
fixes \<pi>:: "('i, 'action, 'time) temp_plan"
begin

definition plan_actions_in_problem where
"plan_actions_in_problem \<equiv> \<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"

lemma at_start_in_happ_seqE: 
  assumes in_happ_seq: "(t, at_start a) \<in> plan_happ_seq \<pi> at_start at_end"
      and a_in_actions: "a \<in> actions"
      and nso: "no_self_overlap \<pi>"
      and dp: "durations_positive \<pi>"
      and pap: "plan_actions_in_problem"
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
      with pap[simplified plan_actions_in_problem_def]
      have "\<exists>a' d. at_start a = at_start a'\<and> (a', t, d) \<in> ran \<pi> \<and> a' \<in> actions" by auto
      with 1 a_in_actions at_start_inj_on[simplified inj_on_def]
      show ?thesis by blast
    next
      case 2
      with pap[simplified plan_actions_in_problem_def]
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
      from dp[simplified durations_positive_def] d_in_ran e(1)
      consider "t \<le> t + d" | "t \<le> t + e" by fastforce
      hence False 
        apply cases
        using False nso[simplified no_self_overlap_def] ij 
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
  assumes in_happ_seq: "(s, at_end a) \<in> plan_happ_seq \<pi> at_start at_end"
      and a_in_actions: "a \<in> actions"
      and nso: "no_self_overlap \<pi>" (* Can be removed if uniqueness quantification \<exists>! is replaced with \<exists> *)
      and dp: "durations_positive \<pi>"
      and pap: "plan_actions_in_problem"
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
    with pap[simplified plan_actions_in_problem_def] 
    have "\<exists>a' d. (s, at_end a) = (s, at_start a') \<and> (a', s, d) \<in> ran \<pi> \<and> a' \<in> actions" by blast
    with snaps_disj 1 a_in_actions
    show ?thesis by blast
  next
    case 2
    with pap[simplified plan_actions_in_problem_def]
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
end
end

datatype (act: 'a) snap_action = 
  AtStart 'a |
  AtEnd 'a

(* Locale a: Planning without the injectivity of at_start and at_end 
     Locale b = a: Planning with the injectivity
   Locale c = a: Sublocale b. 
  This is necessary for the arguments about active actions
  *)

(*
  The timed automaton construction needs a set of propositions and actions, which are both
  finite. The plan actions need to be subsets of the actions in the locale. The locale actions need
  to only refer to propositions in the set.
*)

(*
  - Finite vs infinite plans. Assumptions on plans are irrelevant
  - Equality and inequality: Encodable as non-fluent propositions.
  - Non-fluent propositions: 
    - If actions in a plan do not modify these, then it is possible to remove them from the initial
      state, goal state and the actions' preconditions, thereby obtaining the actions which only refer
      to a certain set of propositions.
    - The goal state must include a subset of the non-fluents of the initial state.
    - 

  - Technically, if the set of fluent propositions is finite, the set of actions must be finite. Ignore this.
  - The set of actions is better restricted to a finite set.
  - Assume we have two locales which restrict plan actions to A and A' where A' is the set of actions with
      preconditions only in P.
  - Plan actions in problem. 

  - It is better to leave the equivalence proofs for the existence of plans inside the locales.
*)

(* This is what we will instantiate PDDL with. A valid plan here is a valid plan, in the basic domain,
which is a valid plan in the domain used for the compilation *)
locale finite_domain_planning = 
  basic_temp_planning_problem props actions init goal at_start at_end over_all lower upper pre adds dels \<epsilon>
    for props::   "('proposition::linorder) set"
    and actions::    "('action::linorder) set"
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

  definition "init_imp = init \<inter> props"
  definition "goal_imp = goal \<inter> props"
  
  fun app_snap::"('snap_action \<Rightarrow> 'proposition set) \<Rightarrow> 'action snap_action \<Rightarrow> 'proposition set" where
  "app_snap f (AtStart a) = f (at_start a)" |
  "app_snap f (AtEnd a) = f (at_end a)"
  
  definition pre_imp::"'action snap_action \<Rightarrow> 'proposition set" where
  "pre_imp = (\<inter>) props o app_snap pre"
  
  definition add_imp::"'action snap_action \<Rightarrow> 'proposition set" where
  "add_imp = app_snap adds"
  
  definition del_imp::"'action snap_action \<Rightarrow> 'proposition set" where
  "del_imp = app_snap dels"

  definition over_all_imp::"'action \<Rightarrow> 'proposition set" where
  "over_all_imp = (\<inter>) props o over_all"

  sublocale temp_planning_problem props actions init_imp goal_imp AtStart AtEnd over_all_imp lower upper pre_imp add_imp del_imp \<epsilon>
  proof
    show "init_imp \<subseteq> props" "goal_imp \<subseteq> props" unfolding init_imp_def goal_imp_def by simp+
    show "inj_on AtStart actions" "inj_on AtEnd actions" unfolding inj_on_def by blast+
    show "AtStart ` actions \<inter> AtEnd ` actions = {}" by blast
    show "0 \<le> \<epsilon>" by (rule eps_range)
  qed 
end
end
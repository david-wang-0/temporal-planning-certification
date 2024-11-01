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
          snap_props (at_start_a) \<subseteq> props
        \<and> snap_props (at_end a) \<subseteq> props
        \<and> over_all a \<subseteq> props)"
      and at_start_inj: "inj_on at_start actions"
      and at_end_inj:   "inj_on at_end actions"
      and snaps_disj:   "(at_start ` actions) \<inter> (at_end ` actions) = {}"
      and prop_numbering:   "bij_betw p {n. n < card props} props"
      and action_numbering: "bij_betw act {n. n < card actions} actions"
      and some_props:       "card props > 0"
      and some_actions:     "card actions > 0"
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

definition snap_actions::"'snap_action set" where
"snap_actions \<equiv> (at_start ` actions) \<union> (at_end ` actions)"

text \<open>Useful lemmas about the numberings\<close>

lemma act_inj_on: "inj_on act {n. n < card actions}"
  using action_numbering bij_betw_def by blast

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

lemma time_index_bij_betw_list: "bij_betw time_index {n. n < length htpl} (set htpl)"
  using bij_betw_nth distinct_sorted_list_of_set htpl_def[symmetric] lessThan_def
  by metis

text \<open>Happening Sequences\<close>

definition plan_happ_seq::"('time \<times> 'snap_action) set" where
"plan_happ_seq \<equiv> 
    {(t, at_start a) | a t d. (a, t, d) \<in> ran \<pi>} 
  \<union> {(t + d, at_end a) | a t d. (a, t, d) \<in> ran \<pi>}"

definition happ_at::"('time \<times> 'snap_action) set \<Rightarrow> 'time \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s |s. (t, s) \<in> B}"

text \<open>Invariants\<close>
definition plan_inv_seq::"('proposition, 'time) invariant_sequence" where
"plan_inv_seq \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('proposition, 'time) invariant_sequence \<Rightarrow> 'time \<Rightarrow> 'proposition set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"


subsubsection \<open>Non-mutex snap-action sequence\<close>

text \<open>This will not work as such. Equality for snap-actions must first take the original action
into account, but this is something to worry about later. (in a locale?)\<close>

text \<open>From the locale assumptions, we know that if a is not b then \<close>
definition nm_sa_seq::"('time \<times> 'snap_action) set \<Rightarrow> bool" where
"nm_sa_seq B \<equiv> \<not>(\<exists>t u. t - u \<le> \<epsilon> \<and> u - t \<le> \<epsilon> \<and> (\<exists>a b. a \<noteq> b \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u \<longrightarrow> \<not>(mutex_snap_action a b)))"

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
\<Rightarrow> ('time \<times> 'snap_action) set
\<Rightarrow> ('proposition, 'time) invariant_sequence 
\<Rightarrow> bool" where
"valid_state_sequence M B Inv \<equiv> (
  let 
    T = fst ` B 
  in
    \<exists>t. unique_increasing_sequence T t
    \<and> (\<forall>i. Suc i < card T \<longrightarrow> (
      let 
        S = happ_at B (t i);
        pres = \<Union>(pre ` S);
        invs = invs_at Inv (t i)
      in
        apply_effects (M i) S = (M (Suc i))
        \<and> invs \<subseteq> (M i)
        \<and> pres \<subseteq> (M i)
        \<and> nm_sa_seq B
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


definition plan_actions_in_problem::bool where
"plan_actions_in_problem \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> a \<in> actions"

definition finite_plan::bool where
"finite_plan \<equiv> finite (dom \<pi>)"

definition durations_non_zero::bool where
"durations_non_zero \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> 0 \<le> d"

definition valid_plan::"bool" where
"valid_plan \<equiv> \<exists>M. (
  let 
    B = plan_happ_seq;
    Inv = plan_inv_seq
  in
    valid_state_sequence M B Inv
    \<and> no_self_overlap
    \<and> (M 0) = init
    \<and> (M (card B - 1)) = goal
    \<and> plan_actions_in_problem
    \<and> finite_plan
    \<and> durations_non_zero
)"
end

context temporal_plan
begin

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

lemma time_index_bij_betw_set:
  assumes "finite_plan"
  shows "bij_betw time_index {n. n < card htps} htps"
proof -
  have 1: "card htps = length htpl" using htpl_def by simp
  have 3: "distinct htpl" unfolding htpl_def by simp
  show "bij_betw time_index {n. n < card htps} htps"
    apply (subst 1)
    apply (subst set_htpl_eq_htps[OF assms])
    using time_index_bij_betw_list
    by blast
qed

lemmas time_index_ord = strict_sorted_list_of_set[of htps, simplified htpl_def[symmetric], THEN sorted_wrt_nth_less]

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
    by (metis not_less_iff_gr_or_eq time_index_ord)
  moreover
  have "l < l'" using l'
    by (metis Suc_lessD linorder_neqE_nat order_less_asym' a time_index_ord)
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
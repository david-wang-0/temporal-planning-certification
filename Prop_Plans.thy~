theory Prop_Plans
  imports Base
begin


type_synonym 'p snap_action = "'p set \<times> 'p set \<times> 'p set"
definition "pre \<equiv> fst"
definition adds ("eff\<^sup>+ _" [65])  where
 "adds \<equiv> fst o snd" 
definition dels ("eff\<^sup>- _" [65])  where
 "dels \<equiv> snd o snd"

datatype ('t :: time) lower_bound =
  GT 't |
  GE 't

datatype ('t :: time) upper_bound =
  LT 't |
  LE 't

type_synonym ('p, 't) durative_action = "'p snap_action \<times> 'p snap_action \<times> 'p set \<times> 't lower_bound \<times> 't upper_bound"

definition snap_at_start ("_\<^sub>\<turnstile>" [66]) where
  "snap_at_start \<equiv> fst"

definition snap_at_end ("_\<^sub>\<stileturn>" [66]) where
  "snap_at_end \<equiv> fst o snd"

definition over_all ("pre\<^sup>\<longleftrightarrow>(_)" [66]) where
  "over_all \<equiv> fst o snd o snd"

definition min_dur ("L(_)" [65]) where
  "min_dur \<equiv> fst o snd o snd o snd"

definition max_dur ("U(_)" [65]) where
  "max_dur \<equiv> fst o snd o snd o snd"

type_synonym ('p, 't) scheduled_action = "('p, 't) durative_action \<times> 't \<times> 't"

type_synonym ('p, 't) plan = "nat \<rightharpoonup> ('p, 't) scheduled_action"

type_synonym ('p, 't) tpp = "'p set \<times> ('p, 't) durative_action set \<times> 'p set \<times> 'p set"

definition props where
  "props \<equiv> fst"

definition actions where
  "actions \<equiv> fst o snd"

definition init where
  "init \<equiv> fst o snd o snd"

definition goal where
  "goal \<equiv> snd o snd o snd"

section \<open>State sequences and happening sequences\<close>

type_synonym 'p state = "'p set"

type_synonym ('p) state_sequence = "nat \<Rightarrow> ('p state)"

text \<open>Happening Time Points\<close>
definition htps::"('p, 't::time) plan \<Rightarrow> 't set" where
"htps \<pi> \<equiv> {t |a t d. (a, t, d) \<in> ran \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> ran \<pi>}"

text \<open>Happening Sequences\<close>
type_synonym ('p, 't) happening_sequence = "('t \<times> 'p snap_action) set"

definition plan_happ_seq::"('p, 't::time) plan \<Rightarrow> ('p, 't) happening_sequence" where
"plan_happ_seq \<pi> \<equiv> 
    {(t, snap_at_start a) | a t d. (a, t, d) \<in> ran \<pi>} 
  \<union> {(t + d, snap_at_end a) | a t d. (a, t, d) \<in> ran \<pi>}"

definition happ_at::"('p, 't) happening_sequence \<Rightarrow> 't \<Rightarrow> 'p snap_action set" where
"happ_at B t \<equiv> {s |s. (t, s) \<in> B}"

text \<open>Invariants\<close>
type_synonym ('p, 't) invariant_sequence = "('t \<times> 'p set) set"

definition plan_inv_seq::"('p, 't::time) plan \<Rightarrow> ('p, 't) invariant_sequence" where
"plan_inv_seq \<pi> \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('p, 't) invariant_sequence \<Rightarrow> 't \<Rightarrow> 'p set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"

text \<open>An indexed sequence/array (or something)\<close>
type_synonym ('v) indexing = "nat \<Rightarrow> 'v"

definition complete_sequence::"'t set \<Rightarrow> 't indexing \<Rightarrow> bool" where
"complete_sequence T t \<equiv> (\<forall>i. (i < card T) \<longrightarrow> (t i) \<in> T) 
  \<and> (\<forall>s \<in> T. \<exists>i. i < card T \<and> s = t i)"

definition unique_increasing_sequence::"('t :: linorder) set \<Rightarrow> 't indexing \<Rightarrow> bool" where
"unique_increasing_sequence T t \<equiv>
    complete_sequence T t
  \<and> (\<forall>i j. i < j \<and> j < card T \<longrightarrow> (t i) < (t j))"

text \<open>Effect application\<close>
definition apply_effects::"'p state \<Rightarrow> 'p snap_action set \<Rightarrow> 'p state" where
"apply_effects M S \<equiv> (M - \<Union>(dels ` S)) \<union> \<Union>(adds ` S)"


text \<open>Non-interfering snap-actions\<close>

definition mutex_snap_action::"'p snap_action \<Rightarrow> 'p snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  a = b \<or>
  pre a \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  (adds a \<inter> dels b) \<noteq> {} \<or>
  pre b \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b \<inter> dels a) \<noteq> {}
)"

subsubsection \<open>Non-mutex snap-action sequence\<close>

text \<open>This will not work as such. Equality for snap-actions must first take the original action
into account, but this is something to worry about later.\<close>
definition nm_sa_seq::"('p, 't) happening_sequence \<Rightarrow> 't \<Rightarrow> bool" where
"nm_sa_seq B \<epsilon> \<equiv> \<not>(\<exists>t u. \<exists>a b. a \<noteq> b \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u)"


subsubsection \<open>Valid state sequence\<close>

definition valid_state_sequence::"
  'p state_sequence 
\<Rightarrow> ('p, 't :: time) happening_sequence 
\<Rightarrow> ('p, 't) invariant_sequence 
\<Rightarrow> 't
\<Rightarrow> bool" where
"valid_state_sequence M B Inv \<epsilon> \<equiv> (
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
        \<and> nm_sa_seq B \<epsilon>
    ))
)"

text \<open>For the definition of a valid plan\<close>

definition no_self_overlap::"('p, 't::time) plan \<Rightarrow> bool" where
"no_self_overlap \<pi> \<equiv> \<not>(\<exists>i j a t d u e. i \<noteq> j
  \<and> i \<in> dom \<pi>
  \<and> j \<in> dom \<pi>
  \<and> Some (a, t, d) = \<pi> i
  \<and> Some (a, u, e) = \<pi> j
  \<and> t \<le> u \<and> u \<le> t + d)"


text \<open>
This is not correct
\<close>

definition valid_plan::"('p, 't::time) tpp \<Rightarrow> ('p, 't) plan \<Rightarrow> 't \<Rightarrow> bool" where
"valid_plan P \<pi> \<epsilon> \<equiv> \<exists>M. (
  let 
    B = plan_happ_seq \<pi>;
    Inv = plan_inv_seq \<pi>
  in
    valid_state_sequence M B Inv \<epsilon>
    \<and> no_self_overlap \<pi>
    \<and> (M 0) = init P
    \<and> (M (card B - 1)) = goal P
)"


locale temp_planning_problem = 
  fixes props::   "'proposition set"
    and actions:: "'action set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<Rightarrow> ('t::time) lower_bound"
    and upper::   "'action  \<Rightarrow> 't upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and p::       "'proposition indexing"
    and act::     "'action indexing"
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
      and prop_numbering:   "bij_betw p {j. j < card props} props"
      and action_numbering: "bij_betw act {j. j < card actions} actions"
begin 
definition apply_effects::"'proposition set \<Rightarrow> 'snap_action set \<Rightarrow> 'proposition set" where
"apply_effects M S \<equiv> (M - \<Union>(dels ` S)) \<union> \<Union>(adds ` S)"

definition mutex_snap_action::"'snap_action \<Rightarrow> 'snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  pre a \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  (adds a \<inter> dels b) \<noteq> {} \<or>
  pre b \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b \<inter> dels a) \<noteq> {}
)"

lemma act_inj_on: "inj_on act {j. j < card actions}"
  using action_numbering bij_betw_def by blast

lemma act_img_action: "act ` {n. n < card actions} = actions"
  using action_numbering[simplified bij_betw_def] by simp

end

find_theorems name: "disj*on"

locale temporal_plan = temp_planning_problem _ _ _ _ _ _ _ _ upper pre
  for upper::   "'action  \<Rightarrow> ('t::time) upper_bound"
  and pre::     "'snap_action \<Rightarrow> 'proposition set" +
fixes \<pi>::"nat \<rightharpoonup> ('action \<times> 't \<times> 't)"
begin
  
text \<open>Happening Time Points\<close>
definition htps::"'t set" where
"htps \<equiv> {t |a t d. (a, t, d) \<in> ran \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> ran \<pi>}"

text \<open>Happening Sequences\<close>

definition plan_happ_seq::"('t \<times> 'snap_action) set" where
"plan_happ_seq \<equiv> 
    {(t, at_start a) | a t d. (a, t, d) \<in> ran \<pi>} 
  \<union> {(t + d, at_end a) | a t d. (a, t, d) \<in> ran \<pi>}"

definition happ_at::"('t \<times> 'snap_action) set \<Rightarrow> 't \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s |s. (t, s) \<in> B}"

text \<open>Invariants\<close>
definition plan_inv_seq::"('proposition, 't) invariant_sequence" where
"plan_inv_seq \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('proposition, 't) invariant_sequence \<Rightarrow> 't \<Rightarrow> 'proposition set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"


subsubsection \<open>Non-mutex snap-action sequence\<close>

text \<open>This will not work as such. Equality for snap-actions must first take the original action
into account, but this is something to worry about later. (in a locale?)\<close>

text \<open>From the locale assumptions, we know that if a is not b then \<close>
definition nm_sa_seq::"('t \<times> 'snap_action) set \<Rightarrow> 't \<Rightarrow> bool" where
"nm_sa_seq B \<epsilon> \<equiv> \<not>(\<exists>t u. \<exists>a b. a \<noteq> b \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u)"

subsubsection \<open>Valid state sequence\<close>

definition valid_state_sequence::"
  'proposition state_sequence 
\<Rightarrow> ('t \<times> 'snap_action) set
\<Rightarrow> ('proposition, 't) invariant_sequence 
\<Rightarrow> 't
\<Rightarrow> bool" where
"valid_state_sequence M B Inv \<epsilon> \<equiv> (
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
        \<and> nm_sa_seq B \<epsilon>
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


definition valid_plan::"'t \<Rightarrow> bool" where
"valid_plan \<epsilon> \<equiv> \<exists>M. (
  let 
    B = plan_happ_seq;
    Inv = plan_inv_seq
  in
    valid_state_sequence M B Inv \<epsilon>
    \<and> no_self_overlap
    \<and> (M 0) = init
    \<and> (M (card B - 1)) = goal
)"
end
end
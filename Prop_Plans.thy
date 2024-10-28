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

type_synonym ('p, 't) plan = "('p, 't) scheduled_action set"

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
"htps \<pi> \<equiv> {t |a t d. (a, t, d) \<in> \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> \<pi>}"

text \<open>Happening Sequences\<close>
type_synonym ('p, 't) happening_sequence = "('t \<times> 'p snap_action) set"

definition plan_happ_seq::"('p, 't::time) plan \<Rightarrow> ('p, 't) happening_sequence" where
"plan_happ_seq \<pi> \<equiv> 
    {(t, snap_at_start a) | a t d. (a, t, d) \<in> \<pi>} 
  \<union> {(t + d, snap_at_end a) | a t d. (a, t, d) \<in> \<pi>}"

definition happ_at::"('p, 't) happening_sequence \<Rightarrow> 't \<Rightarrow> 'p snap_action set" where
"happ_at B t \<equiv> {s |s. (t, s) \<in> B}"

text \<open>Invariants\<close>
type_synonym ('p, 't) invariant_sequence = "('t \<times> 'p set) set"

definition plan_inv_seq::"('p, 't::time) plan \<Rightarrow> ('p, 't) invariant_sequence" where
"plan_inv_seq \<pi> \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('p, 't) invariant_sequence \<Rightarrow> 't \<Rightarrow> 'p set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"

text \<open>An indexed sequence/array (or something)\<close>
type_synonym ('v) indexing = "nat \<Rightarrow> 'v"

definition unique_increasing_sequence::"('t :: linorder) set \<Rightarrow> 't indexing \<Rightarrow> bool" where
"unique_increasing_sequence T t \<equiv>
    (\<forall>i. (i < card T) \<longrightarrow> (t i) \<in> T) 
  \<and> (\<forall>s \<in> T. \<exists>i. i < card T \<and> s = t i)
  \<and> (\<forall>i j. i < j \<and> j < card T \<longrightarrow> (t i) < (t j))
"

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
into account, but this is something to worry about later. (in a locale?)\<close>

text \<open>Again, this needs an index to distinguish between actions and therefore snap-actions, but this 
is to worry about later.\<close>
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

text \<open>This is necessary to distinguish double entries in the plan\<close>
definition weakly_increasing_sequence::"('t :: linorder) list \<Rightarrow> 't indexing \<Rightarrow> bool" where
"weakly_increasing_sequence T t \<equiv>
    (\<forall>i. (i < length T) \<longrightarrow> (t i) \<in> set T) 
  \<and> (\<forall>s \<in> set T. \<exists>i. i < length T \<and> s = t i)
  \<and> (\<forall>i j. i < j \<and> j < length T \<longrightarrow> (t i) \<le> (t j))"

text \<open>Again, this is insufficient. It is necessary to distinguish different entries by the indexes, 
because a plan is a set\<close>
definition no_self_overlap::"('p, 't::time) plan \<Rightarrow> bool" where
"no_self_overlap \<pi> \<equiv> \<not>(\<exists>t u d e a. 
  (a, t, d) \<in> \<pi> 
  \<and> (a, u, e) \<in> \<pi> 
  \<and> (u \<noteq> t \<or> d \<noteq> e) 
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


subsection \<open>Compilation\<close>
text \<open>Collecting all propositions of the problem\<close>
definition "snap_props S \<equiv> pre S \<union> adds S \<union> dels S"
definition "da_props DA \<equiv> snap_props (snap_at_start DA) \<union> snap_props (snap_at_end DA) \<union> over_all DA"

definition props_correct::"('p, 't) tpp \<Rightarrow> bool" where
  "props_correct problem \<equiv> (\<Union> (da_props ` actions problem)) \<union> init problem \<union> goal problem \<subseteq> props problem"


end
theory Prop_Plans
  imports Base
begin

type_synonym 'p state = "'p set"

type_synonym 'p snap_action = "'p set \<times> 'p set \<times> 'p set"
definition "pre \<equiv> fst"
definition adds ("eff\<^sup>+ _" [65])  where
 "adds \<equiv> fst o snd" 
definition dels ("eff\<^sup>+ _" [65])  where
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

type_synonym ('p, 't) plan = "('p, 't) scheduled_action list"

type_synonym ('p, 't) tpp = "'p set \<times> ('p, 't) durative_action set \<times> 'p set \<times> 'p set"

definition props where
  "props \<equiv> fst"

definition actions where
  "actions \<equiv> fst o snd"

definition init where
  "init \<equiv> fst o snd o snd"

definition goal where
  "goal \<equiv> snd o snd o snd"
 
(* definition acts_non_intrf :: "ground_action \<Rightarrow> ground_action \<Rightarrow> bool" where
    "acts_non_intrf a b \<longleftrightarrow> (
      let 
        add\<^sub>a = set(adds(effect a)); del\<^sub>a = set(dels(effect a)); pre\<^sub>a = Atom ` atoms (precondition a);
        add\<^sub>b = set(adds(effect b)); del\<^sub>b = set(dels(effect b)); pre\<^sub>b = Atom ` atoms (precondition b) 
      in
      pre\<^sub>a \<inter> (add\<^sub>b \<union> del\<^sub>b) = {} \<and>
      pre\<^sub>b \<inter> (add\<^sub>a \<union> del\<^sub>a) = {} \<and>
      add\<^sub>a \<inter> del\<^sub>b = {} \<and>
      add\<^sub>b \<inter> del\<^sub>a = {})" *)

definition mutex_snap_action::"'p snap_action \<Rightarrow> 'p snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  a = b \<or>
  pre a \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  (adds a \<inter> dels b) \<noteq> {} \<or>
  pre b \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b \<inter> dels a) \<noteq> {}
)"

definition valid_plan::"('p, 't) tpp \<Rightarrow> ('p, 't) plan \<Rightarrow> bool" where
  "valid_plan \<equiv> undefined"

subsection \<open>Compilation\<close>
text \<open>Collecting all propositions of the problem\<close>
definition "snap_props S \<equiv> pre S \<union> adds S \<union> dels S"
definition "da_props DA \<equiv> snap_props (snap_at_start DA) \<union> snap_props (snap_at_end DA) \<union> over_all DA"

definition props_correct::"('p, 't) tpp \<Rightarrow> bool" where
  "props_correct problem \<equiv> (\<Union> (da_props ` actions problem)) \<union> init problem \<union> goal problem \<subseteq> props problem"


end
theory Diagonal_Timed_Automata
  imports Main
begin

chapter \<open>Basic Definitions and Semantics\<close>

section \<open>Time\<close>

class time = linordered_ab_group_add +
  assumes dense: "x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
  assumes non_trivial: "\<exists> x. x \<noteq> 0"

begin

lemma non_trivial_neg: "\<exists> x. x < 0"
proof -
  from non_trivial obtain x where "x \<noteq> 0" by auto
  then show ?thesis
  proof (cases "x < 0", auto, goal_cases)
    case 1
    then have "x > 0" by auto
    then have "(-x) < 0" by auto
    then show ?case by blast
  qed
qed

end


text \<open>
clock \<open>'c\<close> \<open>\<le>\<close> clock \<open>'c\<close> + time \<open>'t\<close>
\<close>
datatype ('c, 't :: time) dconstraint =
  AND "('c, 't) dconstraint" "('c, 't) dconstraint" |
  LT 'c 't |
  LE 'c 't |
  EQ 'c 't |
  GT 'c 't |
  GE 'c 't |
  CLT 'c 'c 't |
  CLE 'c 'c 't |
  CEQ 'c 'c 't |
  CGT 'c 'c 't |
  CGE 'c 'c 't

section \<open>Syntactic Definition\<close>

text \<open>
  For an informal description of timed automata we refer to Bengtsson and Yi \<^cite>\<open>"BengtssonY03"\<close>.
  We define a timed automaton \<open>A\<close>
\<close>

type_synonym
  ('c, 'time, 's) invassn = "'s \<Rightarrow> ('c, 'time) dconstraint"

type_synonym
  ('c, 'time) clkassn = "'c \<times> 'time"

type_synonym
  ('a, 'c, 'time, 's) transition = "'s * ('c, 'time) dconstraint * 'a * ('c, 'time) clkassn list * 's"

type_synonym
  ('a, 'c, 'time, 's) ta = "('a, 'c, 'time, 's) transition set * ('c, 'time, 's) invassn"

definition trans_of :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('a, 'c, 'time, 's) transition set" where
  "trans_of \<equiv> fst"
definition inv_of  :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('c, 'time, 's) invassn" where
  "inv_of \<equiv> snd"

abbreviation transition ::
  "('a, 'c, 'time, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 'time) dconstraint \<Rightarrow> 'a \<Rightarrow> ('c, 'time) clkassn list \<Rightarrow> 's \<Rightarrow> bool"
("_ \<turnstile> _ \<longrightarrow>\<^bsup>_,_,_\<^esup> _" [61,61,61,61,61,61] 61) where
  "(A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l') \<equiv> (l,g,a,r,l') \<in> trans_of A"

subsection \<open>Collecting Information About Clocks\<close>

fun collect_clks :: "('c, 't :: time) dconstraint \<Rightarrow> 'c set"
where
  "collect_clks (AND cc1 cc2) = collect_clks cc1 \<union> collect_clks cc2" |
  "collect_clks (LT c _) = {c}" |
  "collect_clks (LE c _) = {c}" |
  "collect_clks (EQ c _) = {c}" |
  "collect_clks (GE c _) = {c}" |
  "collect_clks (GT c _) = {c}" |
  "collect_clks (CLT c d _) = {c, d}" |
  "collect_clks (CLE c d _) = {c, d}" |
  "collect_clks (CEQ c d _) = {c, d}" |
  "collect_clks (CGE c d _) = {c, d}" |
  "collect_clks (CGT c d _) = {c, d}"

(* Clocks which are assigned in transitions *)
definition collect_clkvt :: "('a, 'c, 't::time, 's) transition set \<Rightarrow> 'c set"
where
  "collect_clkvt S = \<Union> {set ((map fst o fst o snd o snd o snd) t) | t . t \<in> S}"

section \<open>Operational Semantics\<close>

type_synonym ('c, 't) cval = "'c \<Rightarrow> 't"

definition cval_add :: "('c,'t) cval \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval" (infixr "\<oplus>" 64)
where
  "u \<oplus> d = (\<lambda> x. u x + d)"

inductive clock_val :: "('c, 't) cval \<Rightarrow> ('c, 't::time) dconstraint \<Rightarrow> bool" ("_ \<turnstile> _" [62, 62] 62)
where
  "\<lbrakk>u \<turnstile> cc1; u \<turnstile> cc2\<rbrakk> \<Longrightarrow> u \<turnstile> AND cc1 cc2" |
  "\<lbrakk>u c < d\<rbrakk> \<Longrightarrow> u \<turnstile> LT c d" |
  "\<lbrakk>u c \<le> d\<rbrakk> \<Longrightarrow> u \<turnstile> LE c d" |
  "\<lbrakk>u c = d\<rbrakk> \<Longrightarrow> u \<turnstile> EQ c d" |
  "\<lbrakk>u c \<ge> d\<rbrakk> \<Longrightarrow> u \<turnstile> GE c d" |
  "\<lbrakk>u c > d\<rbrakk> \<Longrightarrow> u \<turnstile> GT c d" |
  "\<lbrakk>u c1 < u c2 + d\<rbrakk> \<Longrightarrow> u \<turnstile> CLT c1 c2 d" |
  "\<lbrakk>u c1 \<le> u c2 + d\<rbrakk> \<Longrightarrow> u \<turnstile> CLE c1 c2 d" |
  "\<lbrakk>u c1 = u c2 + d\<rbrakk> \<Longrightarrow> u \<turnstile> CEQ c1 c2 d" |
  "\<lbrakk>u c1 \<ge> u c2 + d\<rbrakk> \<Longrightarrow> u \<turnstile> CGE c1 c2 d" |
  "\<lbrakk>u c1 > u c2 + d\<rbrakk> \<Longrightarrow> u \<turnstile> CGT c1 c2 d" 

declare clock_val.intros[intro]

inductive_cases[elim!]: "u \<turnstile> AND cc1 cc2"
inductive_cases[elim!]: "u \<turnstile> LT c d"
inductive_cases[elim!]: "u \<turnstile> LE c d"
inductive_cases[elim!]: "u \<turnstile> EQ c d"
inductive_cases[elim!]: "u \<turnstile> GE c d"
inductive_cases[elim!]: "u \<turnstile> GT c d"
inductive_cases[elim!]: "u \<turnstile> CLT c1 c2 d"
inductive_cases[elim!]: "u \<turnstile> CLE c1 c2 d"
inductive_cases[elim!]: "u \<turnstile> CEQ c1 c2 d"
inductive_cases[elim!]: "u \<turnstile> CGE c1 c2 d"
inductive_cases[elim!]: "u \<turnstile> CGT c1 c2 d"

fun clock_set :: "('c \<times> 't :: time) list \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
where
  "clock_set [] u = u" |
  "clock_set ((c, v)#cs) u = (clock_set cs u)(c:=v)"

abbreviation clock_set_abbrv :: "('c \<times> 't :: time) list  \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
("[_]_" [65,65] 65)
where
  "[s]u \<equiv> clock_set s u"

inductive step_t ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> ('t::time) \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61] 61)                      
where
  "\<lbrakk>u \<turnstile> inv_of A l; u \<oplus> d \<turnstile> inv_of A l; d \<ge> 0\<rbrakk> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u \<oplus> d\<rangle>"

declare step_t.intros[intro!]

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"

lemma step_t_determinacy1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow>  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'',u''\<rangle> \<Longrightarrow> l' = l''"
by auto

lemma step_t_determinacy2:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow>  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'',u''\<rangle> \<Longrightarrow> u' = u''"
by auto

lemma step_t_cont1:
  "d \<ge> 0 \<Longrightarrow> e \<ge> 0 \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>e\<^esup> \<langle>l'',u''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d+e\<^esup> \<langle>l'',u''\<rangle>"
proof -
  assume A: "d \<ge> 0" "e \<ge> 0" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>" "A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>e\<^esup> \<langle>l'',u''\<rangle>"
  hence "u' = (u \<oplus> d)" "u'' = (u' \<oplus> e)" by auto
  hence "u'' = (u \<oplus> (d + e))" unfolding cval_add_def by auto
  with A show ?thesis by auto
qed

inductive step_a ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<lbrakk>A \<turnstile> l \<longrightarrow>\<^bsup>g,a,s\<^esup> l'; u \<turnstile> g; u' \<turnstile> inv_of A l'; u' = [s]u\<rbrakk> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>)"

inductive step ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow> \<langle>_,_\<rangle>" [61,61,61] 61)
where
  step_a: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)" |
  step_t: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"

declare step.intros[intro]

inductive
  steps :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l, u\<rangle>" |
  step: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"

declare steps.intros[intro]

end

theory Diagonal_Timed_Automata
  imports Base
begin

chapter \<open>Basic Definitions and Semantics\<close>

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
  This is a copy of \<^cite>\<open>Wimmer2016\<close>
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

definition cval_add :: "('c,'t::time) cval \<Rightarrow> 't \<Rightarrow> ('c,'t) cval" (infixr "\<oplus>" 64)
where
  "u \<oplus> d = (\<lambda> x. u x + d)"

inductive clock_val :: "('c, 't::time) cval \<Rightarrow> ('c, 't) dconstraint \<Rightarrow> bool" ("_ \<turnstile> _" [62, 62] 62)
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


definition AND_ALL::"('c, 't::time) dconstraint list \<Rightarrow> ('c, 't) dconstraint" where
"AND_ALL xs \<equiv> foldr AND xs (let c = SOME c. True in CEQ c c 0)"

lemma AND_ALL_iff: "(W \<turnstile> (AND_ALL xs)) \<longleftrightarrow> list_all (\<lambda>x. W \<turnstile> x) xs"
proof (induction xs)
  case Nil
  have "list_all (clock_val W) [] = True" by auto
  moreover
  have "W \<turnstile> AND_ALL [] = True" unfolding AND_ALL_def by (auto simp: Let_def)
  ultimately
  show ?case by simp
next
  case (Cons x xs)
  have "(list_all (\<lambda>x. W \<turnstile> x) (x#xs)) = ((W \<turnstile> x) \<and> list_all (\<lambda>x. W \<turnstile> x) xs)" using list_all_simps by simp
  hence "(list_all (\<lambda>x. W \<turnstile> x) (x#xs)) = (W \<turnstile> x \<and> W \<turnstile> AND_ALL xs)" using Cons.IH by simp
  moreover
  have "(W \<turnstile> x \<and> W \<turnstile> AND_ALL xs) = (W \<turnstile> AND x (AND_ALL xs))"
    by (rule iffI; blast; cases rule: clock_val.cases, auto)
  hence "(W \<turnstile> x \<and> W \<turnstile> AND_ALL xs) = W \<turnstile> AND_ALL (x # xs)" apply (subst AND_ALL_def) apply (subst AND_ALL_def)
    using foldr_Cons by auto
  ultimately
  show ?case by simp
qed

lemma AND_ALL_dist: "W \<turnstile> AND_ALL xs \<and> W \<turnstile> AND_ALL ys \<longleftrightarrow> W \<turnstile> AND_ALL (xs @ ys)"
  using AND_ALL_iff list_all_append by blast

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

lemma steps_trans: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"
  by (induction rule: steps.induct) auto

lemma steps_twist: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow> \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"
  by (induction rule: steps.induct) auto


lemma clock_set_all_cases:
  assumes "\<forall>v'. (c, v') \<in> set xs \<longrightarrow> v = v'"
  shows "(clock_set xs W) c = v \<or> (clock_set xs W) c = W c"
  using assms
  apply (induction xs) by auto


lemma clock_set_certain:
  assumes "\<forall>v'. (c, v') \<in> set xs \<longrightarrow> v = v'"
      and "(c, v) \<in> set xs"
  shows "(clock_set xs W) c = v"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then
  consider "(c, v) \<in> set xs" | "(c, v) = x" by fastforce
  then show ?case 
  proof cases
    case 1
    obtain a b where 
      x: "x = (a, b)"
      by (cases x) auto
    moreover 
    consider "(c, v) = x" | "a \<noteq> c" using x Cons by fastforce
    moreover
    have "([xs]W) c = v"  
      apply (rule Cons.IH)
      using Cons.prems apply simp by (rule 1)
    ultimately
    show ?thesis by auto
  next
    case 2
    then show ?thesis by auto
  qed
qed

lemma clock_set_none: 
  assumes "\<not>(\<exists>v. (c, v) \<in> set xs)"
  shows "(clock_set xs W) c = W c"
  using assms
  by (induction xs, auto)

lemma clock_set_append_other:
  assumes "x \<noteq> y"
  shows "(clock_set ((y, a)#xs) W)x = (clock_set xs W) x"
  using fun_upd_other assms by simp
      

definition le_ta::"('a, 'c, 't::time, 's) ta \<Rightarrow> ('a, 'c, 't, 's) ta \<Rightarrow> bool" where
"le_ta A B \<equiv> (\<forall>t \<in> trans_of A. t \<in> trans_of B) 
  \<and> (\<forall>v s. v \<turnstile> inv_of A s \<longrightarrow> v \<turnstile> inv_of B s)"


lemma ta_superset: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> le_ta A B  \<Longrightarrow> B \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
proof (induction rule: steps.induct)
  case (refl A l u)
  then show ?case by blast
next
  case (step A l u l' u' l'' u'')
  hence \<open>B \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>\<close> 
  proof (induction rule: step.induct)
    case (step_a A l u a l' u')
    then obtain g s where
      facts: "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,s\<^esup> l'" 
      "u \<turnstile> g" 
      "u' \<turnstile> inv_of A l'" 
      "u' = [s]u" by (cases rule: step_a.cases) simp
    
    with \<open>le_ta A B\<close>
    have "B \<turnstile> l \<longrightarrow>\<^bsup>g,a,s\<^esup> l'"  unfolding le_ta_def by blast
    moreover
    from facts \<open>le_ta A B\<close>
    have "u' \<turnstile> inv_of B l'" unfolding le_ta_def by auto
    ultimately
    show ?case
      apply -
      apply (rule step.step_a, rule step_a.intros)
      using facts by auto
  next
    case (step_t A l u d l' u')
    then obtain d where
      d: "0 \<le> d"
      and u': "u' = u \<oplus> d"
      and l': "l' = l"
      and u_inv: "u \<turnstile> inv_of A l"
      and u'_inv: "u \<oplus> d \<turnstile> inv_of A l"
      by blast

    
    have invs: "u \<turnstile> inv_of B l" "u \<oplus> d \<turnstile> inv_of B l" 
      using u_inv u'_inv \<open>le_ta A B\<close>
      unfolding le_ta_def by simp+
    
    show ?case
      apply (rule step.step_t)
      apply (subst l')
      apply (subst u')
      apply (rule step_t.intros)
        apply (rule invs(1))
       apply (rule invs(2))
      by (rule d)
  qed
  moreover
  have "B \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'',u''\<rangle>" using step by blast
  ultimately
  show ?case by (rule steps.step)
qed
end

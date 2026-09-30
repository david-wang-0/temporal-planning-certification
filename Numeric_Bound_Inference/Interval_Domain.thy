theory Interval_Domain
  imports Main "HOL-Library.Extended" "HOL-Library.While_Combinator"
begin

section \<open>Vendored interval abstract domain (from HOL-IMP)\<close>

text \<open>
  This theory is a verbatim, IMP-free copy of the interval abstract domain of the Isabelle
  distribution's \<open>HOL-IMP\<close> session (\<open>Abs_Int2_ivl.thy\<close>, the generic parts of \<open>Abs_Int0.thy\<close>
  and \<open>Abs_Int3.thy\<close>), by Tobias Nipkow, distributed under the BSD licence
  (\<open>COPYRIGHT\<close> in the Isabelle distribution). Only the domain itself is kept: the
  @{text ivl} quotient type and its lattice / arithmetic instances, the backward
  ("inverse") operators, the widening/narrowing classes with the @{text ivl} instance and the
  generic pre-fixpoint iterators. Everything tied to IMP (\<open>com\<close>/\<open>acom\<close>/\<open>st\<close>, the
  \<open>Abs_Int_*\<close> locales and their interpretations) is dropped; the interpretation-generated facts
  the bound inference relies on (@{text gamma_num'}, @{text gamma_plus'}, @{text inv_plus'},
  @{text inv_less'}) are restated as plain lemmas with the interpretation's own proofs.

  Why vendor: \<open>HOL-IMP.Abs_Int0\<close> instantiates @{text "option :: (order) order"}, which clashes
  (duplicate definitional instance) with \<open>HOL-Library.Option_ord\<close> pulled in by Munta's
  Automatic_Refinement, so the original cannot be co-imported with the reduction tower.
\<close>


text \<open>The lattice notation @{text "\<sqinter>"} / @{text "\<squnion>"} / @{text "\<bottom>"} / @{text "\<top>"} is not on
  by default in @{theory Main}; HOL-IMP enables it through its own imports, so we activate the bundle
  here (it then reaches every theory importing this one).\<close>

unbundle lattice_syntax


subsection \<open>Generic lattice class and function concretisation (Abs_Int0)\<close>

class semilattice_sup_top = semilattice_sup + order_top

instance "fun" :: (type, semilattice_sup_top) semilattice_sup_top ..

definition \<gamma>_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)set" where
"\<gamma>_fun \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(F x)}"


subsection \<open>Interval domain (Abs_Int2_ivl)\<close>

type_synonym eint = "int extended"
type_synonym eint2 = "eint * eint"

definition \<gamma>_rep :: "eint2 \<Rightarrow> int set" where
"\<gamma>_rep p = (let (l,h) = p in {i. l \<le> Fin i \<and> Fin i \<le> h})"

definition eq_ivl :: "eint2 \<Rightarrow> eint2 \<Rightarrow> bool" where
"eq_ivl p1 p2 = (\<gamma>_rep p1 = \<gamma>_rep p2)"

lemma refl_eq_ivl[simp]: "eq_ivl p p"
by(auto simp: eq_ivl_def)

quotient_type ivl = eint2 / eq_ivl
by(rule equivpI)(auto simp: reflp_def symp_def transp_def eq_ivl_def)

abbreviation ivl_abbr :: "eint \<Rightarrow> eint \<Rightarrow> ivl" (\<open>[_, _]\<close>) where
"[l,h] == abs_ivl(l,h)"

lift_definition \<gamma>_ivl :: "ivl \<Rightarrow> int set" is \<gamma>_rep
by(simp add: eq_ivl_def)

lemma \<gamma>_ivl_nice: "\<gamma>_ivl[l,h] = {i. l \<le> Fin i \<and> Fin i \<le> h}"
by transfer (simp add: \<gamma>_rep_def)

lift_definition num_ivl :: "int \<Rightarrow> ivl" is "\<lambda>i. (Fin i, Fin i)" .

lift_definition in_ivl :: "int \<Rightarrow> ivl \<Rightarrow> bool"
  is "\<lambda>i (l,h). l \<le> Fin i \<and> Fin i \<le> h"
by(auto simp: eq_ivl_def \<gamma>_rep_def)

lemma in_ivl_nice: "in_ivl i [l,h] = (l \<le> Fin i \<and> Fin i \<le> h)"
by transfer simp

definition is_empty_rep :: "eint2 \<Rightarrow> bool" where
"is_empty_rep p = (let (l,h) = p in l>h | l=Pinf & h=Pinf | l=Minf & h=Minf)"

lemma \<gamma>_rep_cases: "\<gamma>_rep p = (case p of (Fin i,Fin j) => {i..j} | (Fin i,Pinf) => {i..} |
  (Minf,Fin i) \<Rightarrow> {..i} | (Minf,Pinf) \<Rightarrow> UNIV | _ \<Rightarrow> {})"
by(auto simp add: \<gamma>_rep_def split: prod.splits extended.splits)

lift_definition  is_empty_ivl :: "ivl \<Rightarrow> bool" is is_empty_rep
apply(auto simp: eq_ivl_def \<gamma>_rep_cases is_empty_rep_def)
apply(auto simp: not_less less_eq_extended_case split: extended.splits)
done

lemma eq_ivl_iff: "eq_ivl p1 p2 = (is_empty_rep p1 & is_empty_rep p2 | p1 = p2)"
by(auto simp: eq_ivl_def is_empty_rep_def \<gamma>_rep_cases Icc_eq_Icc split: prod.splits extended.splits)

definition empty_rep :: eint2 where "empty_rep = (Pinf,Minf)"

lift_definition empty_ivl :: ivl is empty_rep .

lemma is_empty_empty_rep[simp]: "is_empty_rep empty_rep"
by(auto simp add: is_empty_rep_def empty_rep_def)

lemma is_empty_rep_iff: "is_empty_rep p = (\<gamma>_rep p = {})"
by(auto simp add: \<gamma>_rep_cases is_empty_rep_def split: prod.splits extended.splits)

declare is_empty_rep_iff[THEN iffD1, simp]


instantiation ivl :: semilattice_sup_top
begin

definition le_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> bool" where
"le_rep p1 p2 = (let (l1,h1) = p1; (l2,h2) = p2 in
  if is_empty_rep(l1,h1) then True else
  if is_empty_rep(l2,h2) then False else l1 \<ge> l2 & h1 \<le> h2)"

lemma le_iff_subset: "le_rep p1 p2 \<longleftrightarrow> \<gamma>_rep p1 \<subseteq> \<gamma>_rep p2"
apply rule
apply(auto simp: is_empty_rep_def le_rep_def \<gamma>_rep_def split: if_splits prod.splits)[1]
apply(auto simp: is_empty_rep_def \<gamma>_rep_cases le_rep_def)
apply(auto simp: not_less split: extended.splits)
done

lift_definition less_eq_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> bool" is le_rep
by(auto simp: eq_ivl_def le_iff_subset)

definition less_ivl where "i1 < i2 = (i1 \<le> i2 \<and> \<not> i2 \<le> (i1::ivl))"

lemma le_ivl_iff_subset: "iv1 \<le> iv2 \<longleftrightarrow> \<gamma>_ivl iv1 \<subseteq> \<gamma>_ivl iv2"
by transfer (rule le_iff_subset)

definition sup_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"sup_rep p1 p2 = (if is_empty_rep p1 then p2 else if is_empty_rep p2 then p1
  else let (l1,h1) = p1; (l2,h2) = p2 in  (min l1 l2, max h1 h2))"

lift_definition sup_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is sup_rep
by(auto simp: eq_ivl_iff sup_rep_def)

lift_definition top_ivl :: ivl is "(Minf,Pinf)" .

lemma is_empty_min_max:
  "\<not> is_empty_rep (l1,h1) \<Longrightarrow> \<not> is_empty_rep (l2, h2) \<Longrightarrow> \<not> is_empty_rep (min l1 l2, max h1 h2)"
by(auto simp add: is_empty_rep_def max_def min_def split: if_splits)

instance
proof (standard, goal_cases)
  case 1 show ?case by (rule less_ivl_def)
next
  case 2 show ?case by transfer (simp add: le_rep_def split: prod.splits)
next
  case 3 thus ?case by transfer (auto simp: le_rep_def split: if_splits)
next
  case 4 thus ?case by transfer (auto simp: le_rep_def eq_ivl_iff split: if_splits)
next
  case 5 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def is_empty_min_max)
next
  case 6 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def is_empty_min_max)
next
  case 7 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def)
next
  case 8 show ?case by transfer (simp add: le_rep_def is_empty_rep_def)
qed

end

text\<open>Implement (naive) executable equality:\<close>
instantiation ivl :: equal
begin

definition equal_ivl where
"equal_ivl i1 (i2::ivl) = (i1\<le>i2 \<and> i2 \<le> i1)"

instance
proof (standard, goal_cases)
  case 1 show ?case by(simp add: equal_ivl_def eq_iff)
qed

end

lemma [simp]: fixes x :: "'a::linorder extended" shows "(\<not> x < Pinf) = (x = Pinf)"
by(simp add: not_less)
lemma [simp]: fixes x :: "'a::linorder extended" shows "(\<not> Minf < x) = (x = Minf)"
by(simp add: not_less)

instantiation ivl :: bounded_lattice
begin

definition inf_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"inf_rep p1 p2 = (let (l1,h1) = p1; (l2,h2) = p2 in (max l1 l2, min h1 h2))"

lemma \<gamma>_inf_rep: "\<gamma>_rep(inf_rep p1 p2) = \<gamma>_rep p1 \<inter> \<gamma>_rep p2"
by(auto simp:inf_rep_def \<gamma>_rep_cases split: prod.splits extended.splits)

lift_definition inf_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is inf_rep
by(auto simp: \<gamma>_inf_rep eq_ivl_def)

lemma \<gamma>_inf: "\<gamma>_ivl (iv1 \<sqinter> iv2) = \<gamma>_ivl iv1 \<inter> \<gamma>_ivl iv2"
by transfer (rule \<gamma>_inf_rep)

definition "\<bottom> = empty_ivl"

instance
proof (standard, goal_cases)
  case 1 thus ?case by (simp add: \<gamma>_inf le_ivl_iff_subset)
next
  case 2 thus ?case by (simp add: \<gamma>_inf le_ivl_iff_subset)
next
  case 3 thus ?case by (simp add: \<gamma>_inf le_ivl_iff_subset)
next
  case 4 show ?case
    unfolding bot_ivl_def by transfer (auto simp: le_iff_subset)
qed

end


lemma eq_ivl_empty: "eq_ivl p empty_rep = is_empty_rep p"
by (metis eq_ivl_iff is_empty_empty_rep)

lemma le_ivl_nice: "[l1,h1] \<le> [l2,h2] \<longleftrightarrow>
  (if [l1,h1] = \<bottom> then True else
   if [l2,h2] = \<bottom> then False else l1 \<ge> l2 & h1 \<le> h2)"
unfolding bot_ivl_def by transfer (simp add: le_rep_def eq_ivl_empty)

lemma sup_ivl_nice: "[l1,h1] \<squnion> [l2,h2] =
  (if [l1,h1] = \<bottom> then [l2,h2] else
   if [l2,h2] = \<bottom> then [l1,h1] else [min l1 l2,max h1 h2])"
unfolding bot_ivl_def by transfer (simp add: sup_rep_def eq_ivl_empty)

lemma inf_ivl_nice: "[l1,h1] \<sqinter> [l2,h2] = [max l1 l2,min h1 h2]"
by transfer (simp add: inf_rep_def)

lemma top_ivl_nice: "\<top> = [-\<infinity>,\<infinity>]"
by (simp add: top_ivl_def)


instantiation ivl :: plus
begin

definition plus_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"plus_rep p1 p2 =
  (if is_empty_rep p1 \<or> is_empty_rep p2 then empty_rep else
   let (l1,h1) = p1; (l2,h2) = p2 in (l1+l2, h1+h2))"

lift_definition plus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is plus_rep
by(auto simp: plus_rep_def eq_ivl_iff)

instance ..
end

lemma plus_ivl_nice: "[l1,h1] + [l2,h2] =
  (if [l1,h1] = \<bottom> \<or> [l2,h2] = \<bottom> then \<bottom> else [l1+l2 , h1+h2])"
unfolding bot_ivl_def by transfer (auto simp: plus_rep_def eq_ivl_empty)

lemma uminus_eq_Minf[simp]: "-x = Minf \<longleftrightarrow> x = Pinf"
by(cases x) auto
lemma uminus_eq_Pinf[simp]: "-x = Pinf \<longleftrightarrow> x = Minf"
by(cases x) auto

lemma uminus_le_Fin_iff: "- x \<le> Fin(-y) \<longleftrightarrow> Fin y \<le> (x::'a::ordered_ab_group_add extended)"
by(cases x) auto
lemma Fin_uminus_le_iff: "Fin(-y) \<le> -x \<longleftrightarrow> x \<le> ((Fin y)::'a::ordered_ab_group_add extended)"
by(cases x) auto

instantiation ivl :: uminus
begin

definition uminus_rep :: "eint2 \<Rightarrow> eint2" where
"uminus_rep p = (let (l,h) = p in (-h, -l))"

lemma \<gamma>_uminus_rep: "i \<in> \<gamma>_rep p \<Longrightarrow> -i \<in> \<gamma>_rep(uminus_rep p)"
by(auto simp: uminus_rep_def \<gamma>_rep_def image_def uminus_le_Fin_iff Fin_uminus_le_iff
        split: prod.split)

lift_definition uminus_ivl :: "ivl \<Rightarrow> ivl" is uminus_rep
by (auto simp: uminus_rep_def eq_ivl_def \<gamma>_rep_cases)
   (auto simp: Icc_eq_Icc split: extended.splits)

instance ..
end

lemma \<gamma>_uminus: "i \<in> \<gamma>_ivl iv \<Longrightarrow> -i \<in> \<gamma>_ivl(- iv)"
by transfer (rule \<gamma>_uminus_rep)

lemma uminus_nice: "-[l,h] = [-h,-l]"
by transfer (simp add: uminus_rep_def)

instantiation ivl :: minus
begin

definition minus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
"(iv1::ivl) - iv2 = iv1 + -iv2"

instance ..
end


definition inv_plus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl*ivl" where
"inv_plus_ivl iv iv1 iv2 = (iv1 \<sqinter> (iv - iv2), iv2 \<sqinter> (iv - iv1))"

definition above_rep :: "eint2 \<Rightarrow> eint2" where
"above_rep p = (if is_empty_rep p then empty_rep else let (l,h) = p in (l,\<infinity>))"

definition below_rep :: "eint2 \<Rightarrow> eint2" where
"below_rep p = (if is_empty_rep p then empty_rep else let (l,h) = p in (-\<infinity>,h))"

lift_definition above :: "ivl \<Rightarrow> ivl" is above_rep
by(auto simp: above_rep_def eq_ivl_iff)

lift_definition below :: "ivl \<Rightarrow> ivl" is below_rep
by(auto simp: below_rep_def eq_ivl_iff)

lemma \<gamma>_aboveI: "i \<in> \<gamma>_ivl iv \<Longrightarrow> i \<le> j \<Longrightarrow> j \<in> \<gamma>_ivl(above iv)"
by transfer 
   (auto simp add: above_rep_def \<gamma>_rep_cases is_empty_rep_def
         split: extended.splits)

lemma \<gamma>_belowI: "i \<in> \<gamma>_ivl iv \<Longrightarrow> j \<le> i \<Longrightarrow> j \<in> \<gamma>_ivl(below iv)"
by transfer 
   (auto simp add: below_rep_def \<gamma>_rep_cases is_empty_rep_def
         split: extended.splits)

definition inv_less_ivl :: "bool \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl * ivl" where
"inv_less_ivl res iv1 iv2 =
  (if res
   then (iv1 \<sqinter> (below iv2 - [1,1]),
         iv2 \<sqinter> (above iv1 + [1,1]))
   else (iv1 \<sqinter> above iv2, iv2 \<sqinter> below iv1))"

lemma above_nice: "above[l,h] = (if [l,h] = \<bottom> then \<bottom> else [l,\<infinity>])"
unfolding bot_ivl_def by transfer (simp add: above_rep_def eq_ivl_empty)

lemma below_nice: "below[l,h] = (if [l,h] = \<bottom> then \<bottom> else [-\<infinity>,h])"
unfolding bot_ivl_def by transfer (simp add: below_rep_def eq_ivl_empty)

lemma add_mono_le_Fin:
  "\<lbrakk>x1 \<le> Fin y1; x2 \<le> Fin y2\<rbrakk> \<Longrightarrow> x1 + x2 \<le> Fin (y1 + (y2::'a::ordered_ab_group_add))"
by(drule (1) add_mono) simp

lemma add_mono_Fin_le:
  "\<lbrakk>Fin y1 \<le> x1; Fin y2 \<le> x2\<rbrakk> \<Longrightarrow> Fin(y1 + y2::'a::ordered_ab_group_add) \<le> x1 + x2"
by(drule (1) add_mono) simp

text \<open>The facts the \<open>HOL-IMP\<close> \<open>global_interpretation\<close>s of \<open>Val_semilattice\<close> /
  \<open>Val_lattice_gamma\<close> / \<open>Val_inv\<close> generate, restated as plain lemmas (same proofs).\<close>

lemma mono_gamma_ivl: "a \<le> b \<Longrightarrow> \<gamma>_ivl a \<le> \<gamma>_ivl b"
by transfer (simp add: le_iff_subset)

lemma gamma_Top_ivl[simp]: "\<gamma>_ivl \<top> = UNIV"
by transfer (simp add: \<gamma>_rep_def)

lemma gamma_num': "i \<in> \<gamma>_ivl (num_ivl i)"
by transfer (simp add: \<gamma>_rep_def)

lemma gamma_plus': "i1 \<in> \<gamma>_ivl a1 \<Longrightarrow> i2 \<in> \<gamma>_ivl a2 \<Longrightarrow> i1+i2 \<in> \<gamma>_ivl (a1 + a2)"
apply transfer
apply(auto simp: \<gamma>_rep_def plus_rep_def add_mono_le_Fin add_mono_Fin_le)
by(auto simp: empty_rep_def is_empty_rep_def)

lemma gamma_bot_ivl[simp]: "\<gamma>_ivl \<bottom> = {}"
unfolding bot_ivl_def by transfer simp

lemma test_num': "in_ivl i a = (i \<in> \<gamma>_ivl a)"
by transfer (auto simp: \<gamma>_rep_def)

lemma inv_plus': "inv_plus_ivl a a1 a2 = (a\<^sub>1',a\<^sub>2') \<Longrightarrow>
  i1 \<in> \<gamma>_ivl a1 \<Longrightarrow> i2 \<in> \<gamma>_ivl a2 \<Longrightarrow> i1+i2 \<in> \<gamma>_ivl a \<Longrightarrow> i1 \<in> \<gamma>_ivl a\<^sub>1' \<and> i2 \<in> \<gamma>_ivl a\<^sub>2'"
unfolding inv_plus_ivl_def minus_ivl_def
apply(clarsimp simp add: \<gamma>_inf)
using gamma_plus'[of "i1+i2" _ "-i1"] gamma_plus'[of "i1+i2" _ "-i2"]
by(simp add:  \<gamma>_uminus)

lemma inv_less': "inv_less_ivl (i1<i2) a1 a2 = (a\<^sub>1',a\<^sub>2') \<Longrightarrow>
  i1 \<in> \<gamma>_ivl a1 \<Longrightarrow> i2 \<in> \<gamma>_ivl a2 \<Longrightarrow> i1 \<in> \<gamma>_ivl a\<^sub>1' \<and> i2 \<in> \<gamma>_ivl a\<^sub>2'"
unfolding inv_less_ivl_def minus_ivl_def one_extended_def
apply(clarsimp simp add: \<gamma>_inf split: if_splits)
using gamma_plus'[of "i1+1" _ "-1"] gamma_plus'[of "i2 - 1" _ "1"]
apply(simp add: \<gamma>_belowI[of i2] \<gamma>_aboveI[of i1]
  uminus_ivl.abs_eq uminus_rep_def \<gamma>_ivl_nice)
apply(simp add: \<gamma>_aboveI[of i2] \<gamma>_belowI[of i1])
done

text\<open>Monotonicity:\<close>

lemma mono_plus_ivl: "iv1 \<le> iv2 \<Longrightarrow> iv3 \<le> iv4 \<Longrightarrow> iv1+iv3 \<le> iv2+(iv4::ivl)"
apply transfer
apply(auto simp: plus_rep_def le_iff_subset split: if_splits)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)

lemma mono_minus_ivl: "iv1 \<le> iv2 \<Longrightarrow> -iv1 \<le> -(iv2::ivl)"
apply transfer
apply(auto simp: uminus_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: \<gamma>_rep_cases split: extended.splits)

lemma mono_above: "iv1 \<le> iv2 \<Longrightarrow> above iv1 \<le> above iv2"
apply transfer
apply(auto simp: above_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)

lemma mono_below: "iv1 \<le> iv2 \<Longrightarrow> below iv1 \<le> below iv2"
apply transfer
apply(auto simp: below_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)


subsection \<open>Widening and narrowing (Abs_Int3)\<close>

class widen =
fixes widen :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix \<open>\<nabla>\<close> 65)

class narrow =
fixes narrow :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix \<open>\<triangle>\<close> 65)

class wn = widen + narrow + order +
assumes widen1: "x \<le> x \<nabla> y"
assumes widen2: "y \<le> x \<nabla> y"
assumes narrow1: "y \<le> x \<Longrightarrow> y \<le> x \<triangle> y"
assumes narrow2: "y \<le> x \<Longrightarrow> x \<triangle> y \<le> x"
begin

lemma narrowid[simp]: "x \<triangle> x = x"
by (rule order.antisym) (simp_all add: narrow1 narrow2)

end

lemma top_widen_top[simp]: "\<top> \<nabla> \<top> = (\<top>::_::{wn,order_top})"
by (metis eq_iff top_greatest widen2)

instantiation ivl :: wn
begin

definition "widen_rep p1 p2 =
  (if is_empty_rep p1 then p2 else if is_empty_rep p2 then p1 else
   let (l1,h1) = p1; (l2,h2) = p2
   in (if l2 < l1 then Minf else l1, if h1 < h2 then Pinf else h1))"

lift_definition widen_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is widen_rep
by(auto simp: widen_rep_def eq_ivl_iff)

definition "narrow_rep p1 p2 =
  (if is_empty_rep p1 \<or> is_empty_rep p2 then empty_rep else
   let (l1,h1) = p1; (l2,h2) = p2
   in (if l1 = Minf then l2 else l1, if h1 = Pinf then h2 else h1))"

lift_definition narrow_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is narrow_rep
by(auto simp: narrow_rep_def eq_ivl_iff)

instance
proof
qed (transfer, auto simp: widen_rep_def narrow_rep_def le_iff_subset \<gamma>_rep_def subset_eq is_empty_rep_def empty_rep_def eq_ivl_def split: if_splits extended.splits)+

end


subsubsection "Pre-fixpoint computation"

definition iter_widen :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('a::{order,widen})option"
where "iter_widen f = while_option (\<lambda>x. \<not> f x \<le> x) (\<lambda>x. x \<nabla> f x)"

definition iter_narrow :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('a::{order,narrow})option"
where "iter_narrow f = while_option (\<lambda>x. x \<triangle> f x < x) (\<lambda>x. x \<triangle> f x)"

definition pfp_wn :: "('a::{order,widen,narrow} \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"
where "pfp_wn f x =
  (case iter_widen f x of None \<Rightarrow> None | Some p \<Rightarrow> iter_narrow f p)"


lemma iter_widen_pfp: "iter_widen f x = Some p \<Longrightarrow> f p \<le> p"
by(auto simp add: iter_widen_def dest: while_option_stop)

lemma iter_widen_inv:
assumes "!!x. P x \<Longrightarrow> P(f x)" "!!x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P(x1 \<nabla> x2)" and "P x"
and "iter_widen f x = Some y" shows "P y"
using while_option_rule[where P = "P", OF _ assms(4)[unfolded iter_widen_def]]
by (blast intro: assms(1-3))

end

theory Numeric_Bound_Inference_Guards
  imports Numeric_Bound_Inference_Threshold
begin

section \<open>Guard refinement: recovering bounds that numeric guards enforce\<close>

text \<open>
  The base and threshold theories \<^emph>\<open>drop\<close> numeric preconditions (guards). That is sound --
  dropping a guard only \<^emph>\<open>adds\<close> transitions -- but it loses the upper bound a guard enforces.
  The counter domain is the canonical case: \<open>increase counter 1\<close> guarded by \<open>counter < n\<close> keeps
  the counter in \<open>[0, n]\<close>, yet guard-free it runs to infinity, so the analysis returns
  @{term "[Fin 0, \<infinity>]::ivl"}.

  This theory adds guards to the concrete transition system and \<^bold>\<open>refines\<close> the abstract box by
  the guard before applying an action's effects: for each comparison, interval-evaluate both
  sides (@{const daeval}) and meet each bare-fluent side with what the comparison and the OTHER
  side's interval permit -- the two-sided backward refinement of HOL-IMP's
  @{const inv_less_ivl} (plus a plain meet for equality). Refinement is sound and can only
  shrink the box, so soundness still reduces to a bound-invariant check (@{text gbound_inv_sound},
  the guarded mirror of @{thm [source] bound_inv_sound}). With guards the counter's \<open>[0, n]\<close>
  becomes a provable invariant, and guarded threshold widening \<^emph>\<open>computes\<close> it.

  Fragment: general comparisons \<open>e\<^sub>1 \<lesseqgtr> e\<^sub>2\<close> over the full expression language, all five
  operators (\<open>=\<close>, \<open>\<le>\<close>, \<open>\<ge>\<close>, \<open><\<close>, \<open>>\<close>). Fluent-vs-fluent guards (painter's \<open>item_id = counter\<close>,
  majsp's \<open>battery \<ge> distance\<close>) refine BOTH sides; a side that is not a bare fluent read still
  contributes its interval to the refinement of the other side.
\<close>


subsection \<open>Guarded concrete semantics\<close>

datatype cmpop = CEq | CLe | CGe | CLt | CGt

fun cmp_sem :: "cmpop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "cmp_sem CEq x y = (x = y)"
| "cmp_sem CLe x y = (x \<le> y)"
| "cmp_sem CGe x y = (y \<le> x)"
| "cmp_sem CLt x y = (x < y)"
| "cmp_sem CGt x y = (y < x)"

datatype 'n gcomp = GCmp cmpop "'n dexp" "'n dexp"

fun sat_gcomp :: "'n dval \<Rightarrow> 'n gcomp \<Rightarrow> bool" where
  "sat_gcomp v (GCmp p a b) = cmp_sem p (deval v a) (deval v b)"

definition sat_guard :: "'n dval \<Rightarrow> 'n gcomp list \<Rightarrow> bool" where
  "sat_guard v g = (\<forall>c \<in> set g. sat_gcomp v c)"

text \<open>A guarded action is a guard (conjunction of comparisons) together with its parallel updates.\<close>

type_synonym 'n gaction = "'n gcomp list \<times> 'n dact"

text \<open>Concrete collecting semantics: an action fires only from a state satisfying its guard.\<close>

inductive_set dgreach :: "'n dval \<Rightarrow> 'n gaction set \<Rightarrow> 'n dval set"
  for v0 :: "'n dval" and A :: "'n gaction set"
where
  dgreach_init: "v0 \<in> dgreach v0 A"
| dgreach_step: "\<lbrakk> v \<in> dgreach v0 A; (g, us) \<in> A; sat_guard v g \<rbrakk>
                \<Longrightarrow> dapply_upds us v \<in> dgreach v0 A"


subsection \<open>Abstract guard refinement\<close>

lemma gamma_env_update:
  assumes "v \<in> \<gamma>_env E" and "v f \<in> \<gamma>_ivl iv"
  shows "v \<in> \<gamma>_env (E(f := iv))"
  using assms by (simp add: \<gamma>_fun_def)

text \<open>Refine the interval pair of one comparison: the two-sided backward step. For the four order
  operators this is @{const inv_less_ivl} in the right orientation (strictness included); for
  equality both sides meet.\<close>

fun refine_pair :: "cmpop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl \<times> ivl" where
  "refine_pair CEq i1 i2 = (i1 \<sqinter> i2, i2 \<sqinter> i1)"
| "refine_pair CLe i1 i2 = (case inv_less_ivl False i2 i1 of (j2, j1) \<Rightarrow> (j1, j2))"
| "refine_pair CGe i1 i2 = inv_less_ivl False i1 i2"
| "refine_pair CLt i1 i2 = inv_less_ivl True i1 i2"
| "refine_pair CGt i1 i2 = (case inv_less_ivl True i2 i1 of (j2, j1) \<Rightarrow> (j1, j2))"

lemma refine_pair_sound:
  assumes rp: "refine_pair p i1 i2 = (i1', i2')"
      and m1: "x \<in> \<gamma>_ivl i1"
      and m2: "y \<in> \<gamma>_ivl i2"
      and sat: "cmp_sem p x y"
    shows "x \<in> \<gamma>_ivl i1' \<and> y \<in> \<gamma>_ivl i2'"
proof (cases p)
  case CEq
  have "x = y" using sat CEq by simp
  thus ?thesis using rp m1 m2 CEq by (auto simp: \<gamma>_inf)
next
  case CLe
  obtain j2 j1 where jj: "inv_less_ivl False i2 i1 = (j2, j1)" by fastforce
  have "(y < x) = False" using sat CLe by simp
  hence "inv_less_ivl (y < x) i2 i1 = (j2, j1)" using jj by simp
  hence "y \<in> \<gamma>_ivl j2 \<and> x \<in> \<gamma>_ivl j1" using inv_less' m2 m1 by blast
  moreover
  have "(i1', i2') = (j1, j2)" using rp jj CLe by simp
  ultimately show ?thesis by simp
next
  case CGe
  have "(x < y) = False" using sat CGe by simp
  hence "inv_less_ivl (x < y) i1 i2 = (i1', i2')" using rp CGe by simp
  thus ?thesis using inv_less' m1 m2 by blast
next
  case CLt
  have "(x < y) = True" using sat CLt by simp
  hence "inv_less_ivl (x < y) i1 i2 = (i1', i2')" using rp CLt by simp
  thus ?thesis using inv_less' m1 m2 by blast
next
  case CGt
  obtain j2 j1 where jj: "inv_less_ivl True i2 i1 = (j2, j1)" by fastforce
  have "(y < x) = True" using sat CGt by simp
  hence "inv_less_ivl (y < x) i2 i1 = (j2, j1)" using jj by simp
  hence "y \<in> \<gamma>_ivl j2 \<and> x \<in> \<gamma>_ivl j1" using inv_less' m2 m1 by blast
  moreover
  have "(i1', i2') = (j1, j2)" using rp jj CGt by simp
  ultimately show ?thesis by simp
qed

text \<open>Write a refined interval back into the box -- only a bare fluent read can be written back;
  any other expression shape leaves the box unchanged (sound: refinement information on a
  compound expression has no single home fluent).\<close>

definition refine_var :: "'n dexp \<Rightarrow> ivl \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "refine_var a iv E = (case a of DVar f \<Rightarrow> E(f := E f \<sqinter> iv) | _ \<Rightarrow> E)"

lemma refine_var_sound:
  assumes env: "v \<in> \<gamma>_env E" and mem: "deval v a \<in> \<gamma>_ivl iv"
  shows "v \<in> \<gamma>_env (refine_var a iv E)"
proof (cases a)
  case (DVar f)
  have "v f \<in> \<gamma>_ivl (E f)" using env by (simp add: \<gamma>_fun_def)
  moreover have "v f \<in> \<gamma>_ivl iv" using mem DVar by simp
  ultimately have "v f \<in> \<gamma>_ivl (E f \<sqinter> iv)" by (simp add: \<gamma>_inf)
  thus ?thesis using env DVar by (simp add: refine_var_def gamma_env_update)
qed (auto simp: refine_var_def env)

text \<open>Refine the box by one comparison: interval-evaluate both sides, backward-refine the pair,
  and write each side's refined interval back (bare fluent reads only).\<close>

fun refine_gcomp :: "'n gcomp \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "refine_gcomp (GCmp p a b) E =
     (case refine_pair p (daeval E a) (daeval E b) of
        (ia, ib) \<Rightarrow> refine_var b ib (refine_var a ia E))"

definition refine_guard :: "'n gcomp list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "refine_guard g E = fold refine_gcomp g E"

lemma refine_gcomp_sound:
  assumes env: "v \<in> \<gamma>_env E" and sat: "sat_gcomp v c"
  shows "v \<in> \<gamma>_env (refine_gcomp c E)"
proof -
  obtain p a b where c: "c = GCmp p a b" by (cases c)
  obtain ia ib where rp: "refine_pair p (daeval E a) (daeval E b) = (ia, ib)" by fastforce
  have ma: "deval v a \<in> \<gamma>_ivl (daeval E a)" using env by (rule daeval_sound)
  have mb: "deval v b \<in> \<gamma>_ivl (daeval E b)" using env by (rule daeval_sound)
  have satc: "cmp_sem p (deval v a) (deval v b)" using sat unfolding c by simp
  have mem: "deval v a \<in> \<gamma>_ivl ia \<and> deval v b \<in> \<gamma>_ivl ib"
    using refine_pair_sound[OF rp ma mb satc] by blast
  have "v \<in> \<gamma>_env (refine_var a ia E)"
    using env mem by (simp add: refine_var_sound)
  hence "v \<in> \<gamma>_env (refine_var b ib (refine_var a ia E))"
    using mem by (simp add: refine_var_sound)
  thus ?thesis unfolding c using rp by simp
qed

lemma fold_refine_gcomp_sound:
  "\<lbrakk> v \<in> \<gamma>_env E; \<forall>c\<in>set g. sat_gcomp v c \<rbrakk> \<Longrightarrow> v \<in> \<gamma>_env (fold refine_gcomp g E)"
proof (induction g arbitrary: E)
  case Nil
  thus ?case by simp
next
  case (Cons c g)
  have sc: "sat_gcomp v c" using Cons.prems(2) by simp
  have "v \<in> \<gamma>_env (refine_gcomp c E)" using Cons.prems(1) sc by (rule refine_gcomp_sound)
  moreover have "\<forall>c'\<in>set g. sat_gcomp v c'" using Cons.prems(2) by simp
  ultimately have "v \<in> \<gamma>_env (fold refine_gcomp g (refine_gcomp c E))" by (rule Cons.IH)
  thus ?case by simp
qed

lemma refine_guard_sound:
  assumes "v \<in> \<gamma>_env E" and "sat_guard v g"
  shows "v \<in> \<gamma>_env (refine_guard g E)"
  using assms by (simp add: refine_guard_def sat_guard_def fold_refine_gcomp_sound)


subsection \<open>Guarded abstract transfer and soundness\<close>

text \<open>Checking that the new environment can possibly satisfy the guard.\<close>
fun aenv_inter_gcomp::"'n aenv \<Rightarrow> 'n gcomp \<Rightarrow> bool" where
  "aenv_inter_gcomp E (GCmp p a b) =
     (case refine_pair p (daeval E a) (daeval E b) of
       (ia, ib) \<Rightarrow> if (ia = \<bottom> \<or> ib = \<bottom>) then False else True)"

definition aenv_inter_guard :: "'n aenv \<Rightarrow> 'n gcomp list \<Rightarrow> bool" where
  "aenv_inter_guard E G = (\<forall>g \<in> set G. aenv_inter_gcomp E g)"

text \<open>Apply an action's effects to the guard-refined box.\<close>

definition gastep_upds :: "'n gaction \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "gastep_upds ga E = (
    if aenv_inter_guard E (fst ga)
    then astep_upds (snd ga) (refine_guard (fst ga) E)
    else E)"

lemma aenv_inter_gcomp_sound:
  assumes env: "v \<in> \<gamma>_env E " and sat: "sat_gcomp v c"
  shows "aenv_inter_gcomp E c"
proof -
  obtain p a b where c: "c = GCmp p a b" by (cases c)
  obtain ia ib where rp: "refine_pair p (daeval E a) (daeval E b) = (ia, ib)" by fastforce
  have ma: "deval v a \<in> \<gamma>_ivl (daeval E a)" using env by (blast intro: daeval_sound)
  have mb: "deval v b \<in> \<gamma>_ivl (daeval E b)" using env by (blast intro: daeval_sound)
  have satc: "cmp_sem p (deval v a) (deval v b)" using sat unfolding c by simp
  have mem: "deval v a \<in> \<gamma>_ivl ia \<and> deval v b \<in> \<gamma>_ivl ib"
    using refine_pair_sound[OF rp ma mb satc] by blast
  hence "ia \<noteq> \<bottom>" "ib \<noteq> \<bottom>" by auto
  thus ?thesis using c rp by auto
qed

lemma aenv_inter_guard_sound:
  assumes "v \<in> \<gamma>_env E" and "sat_guard v G"
  shows "aenv_inter_guard E G"
  using assms aenv_inter_gcomp_sound aenv_inter_guard_def sat_guard_def by blast

lemma gastep_upds_sound:
  assumes "v \<in> \<gamma>_env E" and "sat_guard v (fst ga)"
  shows "dapply_upds (snd ga) v \<in> \<gamma>_env (gastep_upds ga E)"
proof -
  have "v \<in> \<gamma>_env (refine_guard (fst ga) E)" using assms by (simp add: refine_guard_sound)
  moreover
  have "aenv_inter_guard E (fst ga)" using assms aenv_inter_guard_sound by blast
  ultimately
  show ?thesis using astep_upds_sound unfolding gastep_upds_def by auto
qed

definition gastep :: "'n gaction list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "gastep acts E = fold (\<lambda>a acc. acc \<squnion> gastep_upds a E) acts E"

lemma gastep_extensive: "E \<le> gastep acts E"
  unfolding gastep_def by (rule fold_sup_init)

lemma gastep_ge_action: "a \<in> set acts \<Longrightarrow> gastep_upds a E \<le> gastep acts E"
  unfolding gastep_def by (rule fold_sup_elem)

definition is_gbound_inv :: "'n dval \<Rightarrow> 'n gaction list \<Rightarrow> 'n aenv \<Rightarrow> bool" where
  "is_gbound_inv v0 acts E \<longleftrightarrow> v0 \<in> \<gamma>_env E \<and> gastep acts E \<le> E"

theorem gbound_inv_sound:
  assumes inv: "is_gbound_inv v0 acts E"
  shows "dgreach v0 (set acts) \<subseteq> \<gamma>_env E"
proof
  fix v assume "v \<in> dgreach v0 (set acts)"
  thus "v \<in> \<gamma>_env E"
  proof (induction rule: dgreach.induct)
    case dgreach_init
    show ?case using inv by (simp add: is_gbound_inv_def)
  next
    case (dgreach_step v g us)
    have "dapply_upds us v \<in> \<gamma>_env (gastep_upds (g, us) E)"
      using dgreach_step.IH dgreach_step.hyps(3) gastep_upds_sound[of v E "(g, us)"] by simp
    moreover have "gastep_upds (g, us) E \<le> E"
    proof -
      have "gastep_upds (g, us) E \<le> gastep acts E"
        using dgreach_step.hyps(2) by (rule gastep_ge_action)
      also have "\<dots> \<le> E" using inv by (simp add: is_gbound_inv_def)
      finally show ?thesis .
    qed
    ultimately show ?case using mono_gamma_env by blast
  qed
qed


subsection \<open>Guarded inference (plain and threshold widening)\<close>

definition ginfer :: "'n gaction list \<Rightarrow> 'n dval \<Rightarrow> 'n aenv option" where
  "ginfer acts v0 =
     while_option (\<lambda>E. \<not> gastep acts E \<le> E) (\<lambda>E. widen_env E (gastep acts E)) (init_env v0)"

lemma ginfer_ge_init:
  assumes "ginfer acts v0 = Some E" shows "init_env v0 \<le> E"
proof (rule while_option_rule[where P = "\<lambda>x. init_env v0 \<le> x", OF _ assms[unfolded ginfer_def]])
  fix s assume s: "init_env v0 \<le> s" and "\<not> gastep acts s \<le> s"
  show "init_env v0 \<le> widen_env s (gastep acts s)"
    using s widen_env_ge1 order_trans by blast
next
  show "init_env v0 \<le> init_env v0" by simp
qed

theorem ginfer_sound:
  assumes "ginfer acts v0 = Some E"
  shows "dgreach v0 (set acts) \<subseteq> \<gamma>_env E"
proof (rule gbound_inv_sound)
  have post: "gastep acts E \<le> E"
    using while_option_stop[OF assms[unfolded ginfer_def]] by simp
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound ginfer_ge_init[OF assms] mono_gamma_env by blast
  thus "is_gbound_inv v0 acts E" using post by (simp add: is_gbound_inv_def)
qed

definition ginfer_thr :: "int list \<Rightarrow> 'n gaction list \<Rightarrow> 'n dval \<Rightarrow> 'n aenv option" where
  "ginfer_thr T acts v0 =
     while_option (\<lambda>E. \<not> gastep acts E \<le> E) (\<lambda>E. widen_env_thr T E (gastep acts E)) (init_env v0)"

lemma ginfer_thr_ge_init:
  assumes "ginfer_thr T acts v0 = Some E" shows "init_env v0 \<le> E"
proof (rule while_option_rule[where P = "\<lambda>x. init_env v0 \<le> x", OF _ assms[unfolded ginfer_thr_def]])
  fix s assume s: "init_env v0 \<le> s" and "\<not> gastep acts s \<le> s"
  show "init_env v0 \<le> widen_env_thr T s (gastep acts s)"
    using s widen_env_thr_ge1 order_trans by blast
next
  show "init_env v0 \<le> init_env v0" by simp
qed

theorem ginfer_thr_sound:
  assumes "ginfer_thr T acts v0 = Some E"
  shows "dgreach v0 (set acts) \<subseteq> \<gamma>_env E"
proof (rule gbound_inv_sound)
  have post: "gastep acts E \<le> E"
    using while_option_stop[OF assms[unfolded ginfer_thr_def]] by simp
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound ginfer_thr_ge_init[OF assms] mono_gamma_env by blast
  thus "is_gbound_inv v0 acts E" using post by (simp add: is_gbound_inv_def)
qed


subsection \<open>Fluent-list-relative inference (no @{class enum} on the fluent type)\<close>

text \<open>@{const ginfer_thr} exits on @{term "gastep acts E \<le> E"}, a comparison of two functions
  @{typ "'n aenv"} -- executable only when @{typ 'n} is enumerable. The reduction's fluent type is
  not, so this variant tests the exit condition on an explicit fluent list @{term fs} only. That is
  sound whenever every fluent an action writes (@{text targets}) is in @{term fs}: off @{term fs}
  the step is the identity (@{text gastep_untouched}), so the list-relative post-fixpoint is a
  genuine one, and @{thm [source] gbound_inv_sound} applies unchanged.\<close>

definition le_on :: "'n list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv \<Rightarrow> bool" where
  "le_on fs E1 E2 \<longleftrightarrow> (\<forall>f \<in> set fs. E1 f \<le> E2 f)"

definition targets :: "'n gaction list \<Rightarrow> 'n set" where
  "targets acts = (\<Union>(g, us) \<in> set acts. fst ` set us)"

definition ginfer_thr_on :: "'n list \<Rightarrow> int list \<Rightarrow> 'n gaction list \<Rightarrow> 'n dval \<Rightarrow> 'n aenv option" where
  "ginfer_thr_on fs T acts v0 =
     while_option (\<lambda>E. \<not> le_on fs (gastep acts E) E) (\<lambda>E. widen_env_thr T E (gastep acts E)) (init_env v0)"

text \<open>Guard refinement only meets, so it never grows the box.\<close>

lemma refine_var_le: "refine_var a iv E \<le> E"
  by (auto simp: refine_var_def le_fun_def split: dexp.split)

lemma refine_gcomp_le: "refine_gcomp c E \<le> E"
proof (cases c)
  case (GCmp p a b)
  obtain ia ib where rp: "refine_pair p (daeval E a) (daeval E b) = (ia, ib)" by fastforce
  have "refine_var b ib (refine_var a ia E) \<le> refine_var a ia E" by (rule refine_var_le)
  also have "\<dots> \<le> E" by (rule refine_var_le)
  finally show ?thesis using GCmp rp by simp
qed

lemma fold_refine_gcomp_le: "fold refine_gcomp g E \<le> E"
proof (induction g arbitrary: E)
  case Nil
  show ?case by simp
next
  case (Cons c g)
  have "fold refine_gcomp g (refine_gcomp c E) \<le> refine_gcomp c E" by (rule Cons.IH)
  also have "\<dots> \<le> E" by (rule refine_gcomp_le)
  finally show ?case by simp
qed

lemma refine_guard_le: "refine_guard g E \<le> E"
  by (simp add: refine_guard_def fold_refine_gcomp_le)

text \<open>A fluent no update of the action writes is not grown by the guarded step.\<close>

lemma gastep_upds_untouched:
  assumes "f \<notin> fst ` set (snd ga)"
  shows "gastep_upds ga E f \<le> E f"
proof -
  have none: "map_of (snd ga) f = None" using assms by (simp add: map_of_eq_None_iff)
  have "refine_guard (fst ga) E f \<le> E f" using refine_guard_le by (rule le_funD)
  thus ?thesis using none by (simp add: gastep_upds_def astep_upds_def)
qed

lemma fold_sup_apply:
  "fold (\<lambda>a acc. acc \<squnion> g a) xs z f = fold (\<lambda>a acc. acc \<squnion> g a f) xs (z f)"
proof (induction xs arbitrary: z)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  have "fold (\<lambda>a acc. acc \<squnion> g a) (a # xs) z f = fold (\<lambda>a acc. acc \<squnion> g a) xs (z \<squnion> g a) f"
    by (simp only: fold_simps)
  also have "\<dots> = fold (\<lambda>a acc. acc \<squnion> g a f) xs ((z \<squnion> g a) f)" by (rule Cons.IH)
  also have "\<dots> = fold (\<lambda>a acc. acc \<squnion> g a f) xs (z f \<squnion> g a f)" by (simp only: sup_apply)
  finally show ?case by (simp only: fold_simps)qed

lemma gastep_untouched:
  assumes "f \<notin> targets acts"
  shows "gastep acts E f = E f"
proof (rule order.antisym)
  have "gastep_upds a E f \<le> E f" if "a \<in> set acts" for a
  proof -
    have "f \<notin> fst ` set (snd a)" using assms that by (cases a) (auto simp: targets_def)
    thus ?thesis by (rule gastep_upds_untouched)
  qed
  thus "gastep acts E f \<le> E f" unfolding gastep_def fold_sup_apply by (subst fold_sup_le_iff) simp
  show "E f \<le> gastep acts E f" using gastep_extensive by (rule le_funD)
qed

lemma ginfer_thr_on_ge_init:
  assumes "ginfer_thr_on fs T acts v0 = Some E" shows "init_env v0 \<le> E"
proof (rule while_option_rule[where P = "\<lambda>x. init_env v0 \<le> x", OF _ assms[unfolded ginfer_thr_on_def]])
  fix s assume s: "init_env v0 \<le> s" and "\<not> le_on fs (gastep acts s) s"
  show "init_env v0 \<le> widen_env_thr T s (gastep acts s)"
    using s widen_env_thr_ge1 order_trans by blast
next
  show "init_env v0 \<le> init_env v0" by simp
qed

lemma ginfer_thr_on_post:
  assumes sub: "targets acts \<subseteq> set fs"
      and res: "ginfer_thr_on fs T acts v0 = Some E"
  shows "gastep acts E \<le> E"
proof (rule le_funI)
  fix f
  have on: "le_on fs (gastep acts E) E"
    using while_option_stop[OF res[unfolded ginfer_thr_on_def]] by simp
  show "gastep acts E f \<le> E f"
  proof (cases "f \<in> set fs")
    case True
    thus ?thesis using on by (simp add: le_on_def)
  next
    case False
    hence "f \<notin> targets acts" using sub by blast
    thus ?thesis by (simp add: gastep_untouched)
  qed
qed

lemma ginfer_thr_on_inv:
  assumes sub: "targets acts \<subseteq> set fs"
      and res: "ginfer_thr_on fs T acts v0 = Some E"
  shows "is_gbound_inv v0 acts E"
proof -
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound ginfer_thr_on_ge_init[OF res] mono_gamma_env by blast
  thus ?thesis using ginfer_thr_on_post[OF sub res] by (simp add: is_gbound_inv_def)
qed

theorem ginfer_thr_on_sound:
  assumes sub: "targets acts \<subseteq> set fs"
      and res: "ginfer_thr_on fs T acts v0 = Some E"
  shows "dgreach v0 (set acts) \<subseteq> \<gamma>_env E"
  using ginfer_thr_on_inv[OF sub res] by (rule gbound_inv_sound)


subsection \<open>Tight threshold extraction (guard caps + signed landings)\<close>

text \<open>Precision-only (soundness is threshold-independent, @{thm [source] ginfer_thr_sound}):
  harvest the tight threshold set from the guarded action system -- guard-expression constants,
  the signed landing values of guarded self-offsets, and effect-RHS constants with
  @{text DMul}/@{text DDiv} coefficient noise dropped -- so the widening lands on problem
  constants instead of jumping to @{term "\<infinity>"}. Guard caps against ANOTHER fluent (a var-vs-var
  guard) are estimated by evaluating the other side at the INITIAL valuation @{term v0} -- exact
  for a never-assigned static fluent (painter's \<open>item_id\<close>, majsp's \<open>distance\<close>), a harmless extra
  threshold otherwise. Likewise a self-offset by a non-constant expression (majsp's
  \<open>battery := battery - distance\<close>) is @{term v0}-estimated. No soundness obligation:
  @{const ginfer_thr}/@{thm [source] ginfer_thr_sound} never inspect the threshold list.\<close>

text \<open>Effect-RHS constants, dropping @{text DMul}/@{text DDiv} coefficients (threshold noise).\<close>
fun dexp_thr_consts :: "'n dexp \<Rightarrow> int list" where
  "dexp_thr_consts (DConst c) = [c]"
| "dexp_thr_consts (DVar _)   = []"
| "dexp_thr_consts (DAdd a b) = dexp_thr_consts a @ dexp_thr_consts b"
| "dexp_thr_consts (DSub a b) = dexp_thr_consts a @ dexp_thr_consts b"
| "dexp_thr_consts (DMul _ _) = []"
| "dexp_thr_consts (DDiv _ _) = []"

text \<open>All guard-expression constants (both sides of every comparison).\<close>
definition guard_consts :: "'n gcomp list \<Rightarrow> int list" where
  "guard_consts g = concat (map (\<lambda>c. case c of GCmp p a b \<Rightarrow>
       dexp_thr_consts a @ dexp_thr_consts b) g)"

text \<open>Cap candidates a guard imposes on fluent @{term f}: for every comparison with @{term f}
  bare on one side, the @{term v0}-evaluation of the other side plus that side's constants.\<close>
definition caps_on :: "'n dval \<Rightarrow> 'n \<Rightarrow> 'n gcomp list \<Rightarrow> int list" where
  "caps_on v0 f g = concat (map (\<lambda>c. case c of GCmp p a b \<Rightarrow>
       (if a = DVar f then deval v0 b # dexp_thr_consts b else [])
     @ (if b = DVar f then deval v0 a # dexp_thr_consts a else [])) g)"

text \<open>Signed self-offset, @{term v0}-evaluated: @{text \<open>f := f + e\<close>} \<mapsto> @{term "Some (deval v0 e)"},
  @{text \<open>f := f - e\<close>} \<mapsto> @{term "Some (- deval v0 e)"}, anything else \<mapsto> @{term None}.\<close>
fun upd_offset :: "'n dval \<Rightarrow> 'n \<Rightarrow> 'n dexp \<Rightarrow> int option" where
  "upd_offset v0 f (DAdd a b) =
     (if a = DVar f then Some (deval v0 b)
      else if b = DVar f then Some (deval v0 a) else None)"
| "upd_offset v0 f (DSub a b) = (if a = DVar f then Some (- deval v0 b) else None)"
| "upd_offset v0 f _ = None"

text \<open>A guarded self-offset lands on @{term "k + d"} for each cap @{term k} on the offset fluent.\<close>
definition landing_cs :: "'n dval \<Rightarrow> 'n gcomp list \<Rightarrow> ('n \<times> 'n dexp) \<Rightarrow> int list" where
  "landing_cs v0 g u = (case upd_offset v0 (fst u) (snd u) of
       None \<Rightarrow> [] | Some d \<Rightarrow> map (\<lambda>k. k + d) (caps_on v0 (fst u) g))"

definition gaction_thr :: "'n dval \<Rightarrow> 'n gaction \<Rightarrow> int list" where
  "gaction_thr v0 ga = guard_consts (fst ga)
                  @ concat (map (landing_cs v0 (fst ga)) (snd ga))
                  @ concat (map (dexp_thr_consts \<circ> snd) (snd ga))"

text \<open>The tight threshold set: initial fluent values (the caller supplies the fluent list, since
  @{typ 'n} is not enumerable in general) plus every action's harvest.\<close>
definition thr_set :: "'n list \<Rightarrow> 'n dval \<Rightarrow> 'n gaction list \<Rightarrow> int list" where
  "thr_set fs v0 acts = remdups (map v0 fs @ concat (map (gaction_thr v0) acts))"
                                                                 


section \<open>Worked example: the counter's upper bound recovered from its guard\<close>

text \<open>
  One fluent (type @{typ unit}) starting at \<open>0\<close>; one action \<open>counter := counter + 1\<close> guarded by
  \<open>counter \<le> 0\<close> (the smallest counter instance \<open>n = 1\<close>). Guard-free (base/threshold theories) the
  reachable set is all of \<open>\<nat>\<close> and the inferred bound is @{term "[Fin 0, \<infinity>]::ivl"}. \<^bold>\<open>With the
  guard\<close>, firing is blocked once \<open>counter > 0\<close>, so the reachable set is \<open>{0, 1}\<close> and @{term "[Fin 0, Fin 1]::ivl"}
  is a genuine bound invariant -- which @{thm [source] gbound_inv_sound} turns into the reachability
  bound. The step check is decided by evaluation (@{text "by eval"}); the executable guarded
  threshold analysis @{const ginfer_thr} computes the same box (see the closing @{command value}).
\<close>

definition ctr_act :: "unit gaction" where
  "ctr_act = ([GCmp CLe (DVar ()) (DConst 0)], [((), DAdd (DVar ()) (DConst 1))])"

definition ctr_init :: "unit dval" where
  "ctr_init = (\<lambda>_. 0)"

definition ctr_bound :: "unit aenv" where
  "ctr_bound = (\<lambda>_. [Fin 0, Fin 1])"

lemma ctr_init_in: "ctr_init \<in> \<gamma>_env ctr_bound"
  by (auto simp: \<gamma>_fun_def ctr_init_def ctr_bound_def \<gamma>_ivl_nice)

lemma ctr_step_le: "gastep [ctr_act] ctr_bound \<le> ctr_bound"
  by eval

lemma ctr_is_gbound_inv: "is_gbound_inv ctr_init [ctr_act] ctr_bound"
  unfolding is_gbound_inv_def using ctr_init_in ctr_step_le by blast

theorem ctr_reachable_bounded:
  "dgreach ctr_init (set [ctr_act]) \<subseteq> {v. 0 \<le> v () \<and> v () \<le> 1}"
proof -
  have "dgreach ctr_init (set [ctr_act]) \<subseteq> \<gamma>_env ctr_bound"
    using ctr_is_gbound_inv by (rule gbound_inv_sound)
  also have "\<gamma>_env ctr_bound \<subseteq> {v. 0 \<le> v () \<and> v () \<le> 1}"
    by (auto simp: \<gamma>_fun_def ctr_bound_def \<gamma>_ivl_nice)
  finally show ?thesis .
qed

text \<open>The guarded threshold analysis is executable and computes the recovered box \<open>[0,1]\<close>.\<close>

value "map_option (\<lambda>E. E ()) (ginfer_thr [0, 1::int] [ctr_act] ctr_init)"


text \<open>The tight threshold set is AUTO-extracted (no hand-supplied list): @{const thr_set}
  harvests \<open>{0, 1}\<close> for the guarded self-increment (init \<open>0\<close>, guard constant \<open>0\<close>, landing
  \<open>0 + 1\<close>), and feeding it to @{const ginfer_thr} recomputes the same tight box \<open>[0,1]\<close>.\<close>

value "thr_set [()] ctr_init [ctr_act]"
  \<comment> \<open>\<open>[0, 1]\<close>: init \<open>0\<close>, guard constant/cap \<open>0\<close>, landing \<open>0 + 1\<close> (self-increment \<open>+1\<close>)\<close>

value "map_option (\<lambda>E. E ()) (ginfer_thr (thr_set [()] ctr_init [ctr_act]) [ctr_act] ctr_init)"
  \<comment> \<open>\<open>Some [Fin 0, Fin 1]\<close> -- the tight box, threshold set AUTO-extracted\<close>

text \<open>And the unguarded constant-assign counter of the threshold theory (\<open>cnt := 5\<close>, starting \<open>0\<close>):
  the harvest is \<open>{0, 5}\<close> (init \<open>0\<close> + the assigned constant \<open>5\<close>; no guard \<Rightarrow> no landing) -- exactly
  the list @{const cnt_thr} previously supplied by hand.\<close>

value "thr_set [()] cnt_init [([], cnt_act)]"
  \<comment> \<open>\<open>[0, 5]\<close>: init \<open>0\<close>, assign-constant \<open>5\<close> (no guard \<Rightarrow> no landing)\<close>

text \<open>A var-vs-var demo: two fluents (@{typ bool} names), \<open>item\<close> (@{term True}) static at \<open>1\<close>,
  \<open>counter\<close> (@{term False}) incremented under the guard \<open>item = counter\<close> -- the painter shape.
  The static fluent keeps its point interval \<open>[1,1]\<close>, the relational refinement transfers it onto
  the counter before the \<open>+1\<close>, and the harvested thresholds (init values \<open>0\<close>, \<open>1\<close>; landing
  \<open>1 + 1\<close>) let the widening settle at the tight \<open>[0, 2]\<close>.\<close>

definition vv_acts :: "bool gaction list" where
  "vv_acts = [([GCmp CEq (DVar True) (DVar False)],
               [(False, DAdd (DVar False) (DConst 1))])]"

definition vv_init :: "bool dval" where
  "vv_init = (\<lambda>f. if f then 1 else 0)"

value "thr_set [True, False] vv_init vv_acts"
  \<comment> \<open>\<open>[1, 0, 2]\<close>: inits \<open>1\<close>/\<open>0\<close>, landing \<open>1 + 1 = 2\<close> (cap = the static side's init)\<close>

value "map_option (\<lambda>E. (E True, E False))
         (ginfer_thr (thr_set [True, False] vv_init vv_acts) vv_acts vv_init)"
  \<comment> \<open>\<open>Some ([Fin 1, Fin 1], [Fin 0, Fin 2])\<close> -- the static point survives, the counter is capped\<close>
end

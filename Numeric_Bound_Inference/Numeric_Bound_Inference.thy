theory Numeric_Bound_Inference
  imports Interval_Domain
begin

section \<open>Numeric-fluent bound inference by interval abstract interpretation\<close>

text \<open>
  This is an abstract interpreter that infers sound numeric bounds
  \<open>[lo, hi]\<close> for every numeric fluent of a grounded temporal-planning problem.

  \<^bold>\<open>Why.\<close> The NTA reduction encodes numeric fluents as \<^emph>\<open>bounded\<close> \<open>int\<close> network
  variables, so the Munta certificate check only makes sense against a fixed range
  per fluent (\<open>num_net_bounds\<close> / \<open>fluent_in_bounds\<close> / \<open>num_seq_in_bounds\<close> in the
  reduction locales, where it enters as a reachability \<^emph>\<open>assumption\<close> on the plan
  trace). This theory computes such a range statically, so the
  bound assumptions become a \<^emph>\<open>discharged\<close> fact rather than a raw hypothesis.

  \<^bold>\<open>How (HOL-IMP, vendored).\<close> We reuse the interval domain of HOL-IMP's \<open>Abs_Int2_ivl\<close> /
  \<open>Abs_Int3\<close>, vendored IMP-free as @{theory \<open>Numeric_Bound_Inference.Interval_Domain\<close>} (HOL-IMP
  itself cannot be co-imported with the Munta-based reduction tower, see there): the type @{typ ivl}, its lattice
  (@{term "(\<squnion>)"} / @{term "(\<sqinter>)"} / @{term "\<top>"} / @{term "\<bottom>"}), interval
  @{term "(+)"} / @{term "(-)"}, the concretisation @{const \<gamma>_ivl}, the constant
  abstraction @{const num_ivl}, the soundness facts @{thm [source] gamma_num'} /
  @{thm [source] gamma_plus'}, and the widening @{term "(\<nabla>)"} (@{class wn}) with the
  iterator @{const iter_widen}. We do \<^emph>\<open>not\<close> reuse the IMP \<open>com\<close>/collecting-semantics
  framework: a planning problem is a \<^emph>\<open>flat\<close> nondeterministic transition system (any
  applicable action fires at any step), so the natural abstract object is a fixpoint
  over a map @{typ \<open>'n \<Rightarrow> ivl\<close>} rather than an annotated command.

  \<^bold>\<open>Fragment.\<close> The concrete syntax @{text \<open>'n dexp\<close>} mirrors the project's
  @{text nexp} (\<open>Temporal_Planning_Semantics/Temporal_Plans.thy\<close>): constants,
  fluents, \<open>+\<close>, \<open>-\<close>, \<open>*\<close>, \<open>/\<close>. We work over the \<^emph>\<open>discrete integer\<close> fragment (the one
  the Munta reduction targets: \<open>fluent_in_bounds\<close> already carries \<open>r \<in> \<int>\<close>), so a
  valuation is @{typ \<open>'n \<Rightarrow> int\<close>}. In the numeric benchmark domains the effect
  right-hand sides that
  actually move fluents are \<open>increase\<close>/\<open>decrease\<close>/\<open>assign\<close> over constants and fluents
  (i.e. @{text DConst}/@{text DVar}/@{text DAdd}/@{text DSub}); \<open>*\<close> and \<open>/\<close> occur only
  in \<^emph>\<open>duration\<close> expressions. Accordingly @{text DMul}/@{text DDiv} are abstracted to
  @{term \<top>} here (sound but imprecise).

  \<^bold>\<open>Guards.\<close> Numeric preconditions only ever \<^emph>\<open>prune\<close> transitions, so ignoring them is
  a sound over-approximation. This theory models an action as its numeric update list only;
  guard-based interval refinement (via @{const inv_less_ivl} / @{const inv_plus_ivl}) is added
  on top in theory \<open>Numeric_Bound_Inference_Guards\<close>.
\<close>


subsection \<open>Concrete numeric syntax and semantics\<close>

text \<open>@{text \<open>'n dexp\<close>} mirrors the project's @{text nexp} fragment; @{text 'n} is the
  (ground) fluent name.\<close>

datatype 'n dexp =
    DConst int
  | DVar 'n
  | DAdd "'n dexp" "'n dexp"
  | DSub "'n dexp" "'n dexp"
  | DMul "'n dexp" "'n dexp"
  | DDiv "'n dexp" "'n dexp"

type_synonym 'n dval = "'n \<Rightarrow> int"

fun deval :: "'n dval \<Rightarrow> 'n dexp \<Rightarrow> int" where
  "deval v (DConst c) = c"
| "deval v (DVar f)   = v f"
| "deval v (DAdd a b) = deval v a + deval v b"
| "deval v (DSub a b) = deval v a - deval v b"
| "deval v (DMul a b) = deval v a * deval v b"
| "deval v (DDiv a b) = deval v a div deval v b"

text \<open>A numeric update assigns an expression to a fluent; an action is a list of
  \<^emph>\<open>parallel\<close> updates whose right-hand sides all read the pre-state, mirroring the
  project's @{text apply_upds} (RHS collapsed to functional form per snap).\<close>

type_synonym 'n dupd    = "'n \<times> 'n dexp"
type_synonym 'n dact = "'n dupd list"

definition dapply_upds :: "'n dact \<Rightarrow> 'n dval \<Rightarrow> 'n dval" where
  "dapply_upds U v = (\<lambda>f. case map_of U f of None \<Rightarrow> v f | Some e \<Rightarrow> deval v e)"

text \<open>Concrete collecting semantics: the reachable valuations from an initial state
  @{term v0} under an action set @{term A} \<^emph>\<open>(the flat planning transition system)\<close>.\<close>

inductive_set dreach :: "'n dval \<Rightarrow> 'n dact set \<Rightarrow> 'n dval set"
  for v0 :: "'n dval" and A :: "'n dact set"
where
  dreach_init: "v0 \<in> dreach v0 A"
| dreach_step: "\<lbrakk> v \<in> dreach v0 A; a \<in> A \<rbrakk> \<Longrightarrow> dapply_upds a v \<in> dreach v0 A"


subsection \<open>Abstract domain: environments of intervals\<close>

text \<open>An abstract state maps each fluent to an interval; its concretisation is the
  HOL-IMP function concretisation @{const \<gamma>_fun} of @{const \<gamma>_ivl}.\<close>

type_synonym 'n aenv = "'n \<Rightarrow> ivl"

abbreviation \<gamma>_env :: "'n aenv \<Rightarrow> 'n dval set" where
  "\<gamma>_env \<equiv> \<gamma>_fun \<gamma>_ivl"

lemma mono_gamma_env:
  assumes "E1 \<le> E2" shows "\<gamma>_env E1 \<subseteq> \<gamma>_env E2"
proof
  fix v assume "v \<in> \<gamma>_env E1"
  hence *: "v f \<in> \<gamma>_ivl (E1 f)" for f by (simp add: \<gamma>_fun_def)
  have "v f \<in> \<gamma>_ivl (E2 f)" for f
  proof -
    have "E1 f \<le> E2 f" using assms by (rule le_funD)
    hence "\<gamma>_ivl (E1 f) \<subseteq> \<gamma>_ivl (E2 f)" by (simp add: le_ivl_iff_subset)
    thus ?thesis using * by blast
  qed
  thus "v \<in> \<gamma>_env E2" by (simp add: \<gamma>_fun_def)
qed


subsection \<open>Abstract evaluation of numeric expressions\<close>

fun daeval :: "'n aenv \<Rightarrow> 'n dexp \<Rightarrow> ivl" where
  "daeval E (DConst c) = num_ivl c"
| "daeval E (DVar f)   = E f"
| "daeval E (DAdd a b) = daeval E a + daeval E b"
| "daeval E (DSub a b) = daeval E a - daeval E b"
| "daeval E (DMul a b) = \<top>"
| "daeval E (DDiv a b) = \<top>"

text \<open>Interval subtraction is sound (the vendored domain proves @{thm [source] gamma_plus'} and
  @{thm [source] \<gamma>_uminus}; @{text minus_ivl} is @{term "\<lambda>a b. a + - b"}).\<close>

lemma gamma_minus':
  assumes "i1 \<in> \<gamma>_ivl a1" and "i2 \<in> \<gamma>_ivl a2"
  shows "i1 - i2 \<in> \<gamma>_ivl (a1 - a2)"
proof -
  have "- i2 \<in> \<gamma>_ivl (- a2)" using assms(2) by (rule \<gamma>_uminus)
  hence "i1 + (- i2) \<in> \<gamma>_ivl (a1 + (- a2))" using assms(1) gamma_plus' by blast
  thus ?thesis unfolding minus_ivl_def by (simp only: diff_conv_add_uminus)
qed

text \<open>Soundness of abstract evaluation: @{const daeval} over-approximates @{const deval}.\<close>

lemma daeval_sound:
  assumes v: "v \<in> \<gamma>_env E"
  shows "deval v e \<in> \<gamma>_ivl (daeval E e)"
proof (induction e)
  case (DConst c)
  show ?case by (simp add: gamma_num')
next
  case (DVar f)
  show ?case using v by (simp add: \<gamma>_fun_def)
next
  case (DAdd a b)
  have "deval v a + deval v b \<in> \<gamma>_ivl (daeval E a + daeval E b)"
    using DAdd.IH by (rule gamma_plus')
  thus ?case by simp
next
  case (DSub a b)
  have "deval v a - deval v b \<in> \<gamma>_ivl (daeval E a - daeval E b)"
    using DSub.IH by (rule gamma_minus')
  thus ?case by simp
next
  case (DMul a b)
  show ?case by (simp add: top_ivl_nice \<gamma>_ivl_nice)
next
  case (DDiv a b)
  show ?case by (simp add: top_ivl_nice \<gamma>_ivl_nice)
qed


subsection \<open>Abstract transfer functions\<close>

text \<open>Abstract counterpart of @{const dapply_upds}: assign each written fluent the
  abstract value of its RHS, keep the rest.\<close>

definition astep_upds :: "'n dact \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "astep_upds U E = (\<lambda>f. case map_of U f of None \<Rightarrow> E f | Some e \<Rightarrow> daeval E e)"

lemma astep_upds_sound:
  assumes "v \<in> \<gamma>_env E"
  shows "dapply_upds U v \<in> \<gamma>_env (astep_upds U E)"
proof -
  have "dapply_upds U v f \<in> \<gamma>_ivl (astep_upds U E f)" for f
  proof (cases "map_of U f")
    case None
    thus ?thesis using assms by (simp add: dapply_upds_def astep_upds_def \<gamma>_fun_def)
  next
    case (Some e)
    have "deval v e \<in> \<gamma>_ivl (daeval E e)" using assms by (rule daeval_sound)
    thus ?thesis using Some by (simp add: dapply_upds_def astep_upds_def)
  qed
  thus ?thesis by (simp add: \<gamma>_fun_def)
qed

text \<open>One collecting step over the whole action list: join the current environment
  with the transfer of \<^emph>\<open>every\<close> action (all evaluated in the same @{term E}).\<close>

definition astep :: "'n dact list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "astep acts E = fold (\<lambda>a acc. acc \<squnion> astep_upds a E) acts E"

lemma fold_sup_init: "(z::'a::semilattice_sup) \<le> fold (\<lambda>a acc. acc \<squnion> g a) xs z"
proof (induction xs arbitrary: z)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  have "z \<le> z \<squnion> g a" by simp
  also have "z \<squnion> g a \<le> fold (\<lambda>a acc. acc \<squnion> g a) xs (z \<squnion> g a)" by (rule Cons.IH)
  finally show ?case by simp
qed

lemma fold_sup_elem:
  "x \<in> set xs \<Longrightarrow> g x \<le> fold (\<lambda>a acc. acc \<squnion> g a) xs (z::'a::semilattice_sup)"
proof (induction xs arbitrary: z)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "x = a")
    case True
    have "g a \<le> z \<squnion> g a" by simp
    also have "\<dots> \<le> fold (\<lambda>a acc. acc \<squnion> g a) xs (z \<squnion> g a)" by (rule fold_sup_init)
    finally show ?thesis using True by simp
  next
    case False
    hence "x \<in> set xs" using Cons.prems by simp
    hence "g x \<le> fold (\<lambda>a acc. acc \<squnion> g a) xs (z \<squnion> g a)" by (rule Cons.IH)
    thus ?thesis by simp
  qed
qed

lemma astep_extensive: "E \<le> astep acts E"
  unfolding astep_def by (rule fold_sup_init)

lemma astep_ge_action:
  "a \<in> set acts \<Longrightarrow> astep_upds a E \<le> astep acts E"
  unfolding astep_def by (rule fold_sup_elem)


subsection \<open>Monotonicity of the abstract step\<close>

text \<open>@{const daeval} is monotone in the environment: interval @{term "(+)"} / @{term "(-)"} are
  monotone in the refinement (subset) order (HOL-IMP @{thm [source] mono_plus_ivl} /
  @{thm [source] mono_minus_ivl}). Note subtraction is monotone here because a \<^emph>\<open>wider\<close> subtrahend
  yields a wider result -- the lattice order is \<open>\<subseteq>\<close>, not the numeric order.\<close>

lemma mono_minus_ivl2:
  assumes "iv1 \<le> iv2" and "iv3 \<le> iv4" shows "iv1 - iv3 \<le> iv2 - (iv4::ivl)"
proof -
  have "- iv3 \<le> - iv4" using assms(2) by (rule mono_minus_ivl)
  hence "iv1 + (- iv3) \<le> iv2 + (- iv4)" using assms(1) mono_plus_ivl by blast
  thus ?thesis by (simp only: minus_ivl_def)
qed

lemma daeval_mono:
  assumes "E1 \<le> E2" shows "daeval E1 e \<le> daeval E2 e"
proof (induction e)
  case (DConst c)
  show ?case by simp
next
  case (DVar f)
  show ?case using assms by (simp add: le_fun_def)
next
  case (DAdd a b)
  have "daeval E1 a + daeval E1 b \<le> daeval E2 a + daeval E2 b"
    using DAdd.IH by (blast intro: mono_plus_ivl)
  thus ?case by simp
next
  case (DSub a b)
  thus ?case by (simp add: mono_minus_ivl2)
next
  case (DMul a b)
  show ?case by simp
next
  case (DDiv a b)
  show ?case by simp
qed

lemma astep_upds_mono:
  assumes "E1 \<le> E2" shows "astep_upds U E1 \<le> astep_upds U E2"
proof (rule le_funI)
  fix f
  show "astep_upds U E1 f \<le> astep_upds U E2 f"
  proof (cases "map_of U f")
    case None
    thus ?thesis using assms by (simp add: astep_upds_def le_fun_def)
  next
    case (Some e)
    have "daeval E1 e \<le> daeval E2 e" using assms by (rule daeval_mono)
    thus ?thesis using Some by (simp add: astep_upds_def)
  qed
qed

lemma fold_sup_mono:
  assumes "z1 \<le> (z2::'a::semilattice_sup)"
    and "\<And>a. a \<in> set xs \<Longrightarrow> g1 a \<le> g2 a"
  shows "fold (\<lambda>a acc. acc \<squnion> g1 a) xs z1 \<le> fold (\<lambda>a acc. acc \<squnion> g2 a) xs z2"
  using assms
proof (induction xs arbitrary: z1 z2)
  case Nil
  thus ?case by simp
next
  case (Cons a xs)
  have ga: "g1 a \<le> g2 a" using Cons.prems(2)[of a] by simp
  have "z1 \<squnion> g1 a \<le> z2 \<squnion> g2 a" using Cons.prems(1) ga by (rule sup_mono)
  moreover have "\<And>b. b \<in> set xs \<Longrightarrow> g1 b \<le> g2 b" using Cons.prems(2) by simp
  ultimately have "fold (\<lambda>a acc. acc \<squnion> g1 a) xs (z1 \<squnion> g1 a)
                 \<le> fold (\<lambda>a acc. acc \<squnion> g2 a) xs (z2 \<squnion> g2 a)"
    by (rule Cons.IH)
  thus ?case by simp
qed

lemma astep_mono:
  assumes "E1 \<le> E2" shows "astep acts E1 \<le> astep acts E2"
  unfolding astep_def
  by (rule fold_sup_mono[OF assms]) (rule astep_upds_mono[OF assms])


subsection \<open>Soundness of a bound invariant\<close>

text \<open>A \<^emph>\<open>bound invariant\<close> is an abstract environment that contains the initial state
  and is closed under one abstract step (a post-fixpoint of @{const astep}). This is the
  soundness certificate: any such @{term E} over-approximates \<^emph>\<open>all\<close> reachable states.\<close>

definition is_bound_inv :: "'n dval \<Rightarrow> 'n dact list \<Rightarrow> 'n aenv \<Rightarrow> bool" where
  "is_bound_inv v0 acts E \<longleftrightarrow> v0 \<in> \<gamma>_env E \<and> astep acts E \<le> E"

theorem bound_inv_sound:
  assumes inv: "is_bound_inv v0 acts E"
  shows "dreach v0 (set acts) \<subseteq> \<gamma>_env E"
proof
  fix v assume "v \<in> dreach v0 (set acts)"
  thus "v \<in> \<gamma>_env E"
  proof (induction rule: dreach.induct)
    case dreach_init
    show ?case using inv by (simp add: is_bound_inv_def)
  next
    case (dreach_step v a)
    have "dapply_upds a v \<in> \<gamma>_env (astep_upds a E)"
      using dreach_step.IH by (rule astep_upds_sound)
    moreover have "astep_upds a E \<le> E"
    proof -
      have "astep_upds a E \<le> astep acts E"
        using dreach_step.hyps(2) by (rule astep_ge_action)
      also have "\<dots> \<le> E" using inv by (simp add: is_bound_inv_def)
      finally show ?thesis .
    qed
    ultimately show ?case using mono_gamma_env by blast
  qed
qed


subsection \<open>Computing a bound invariant by widening\<close>

text \<open>The inference: start from point intervals at the initial values and iterate the
  abstract step, \<^emph>\<open>widening\<close> (@{term "(\<nabla>)"}, pointwise) to force termination. On
  success the result is a post-fixpoint, hence sound by @{thm [source] bound_inv_sound}.
  Soundness is independent of the widening operator (it only uses the exit condition),
  so it needs no termination argument.\<close>

definition init_env :: "'n dval \<Rightarrow> 'n aenv" where
  "init_env v0 = (\<lambda>f. num_ivl (v0 f))"

definition widen_env :: "'n aenv \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "widen_env E1 E2 = (\<lambda>f. E1 f \<nabla> E2 f)"

definition infer :: "'n dact list \<Rightarrow> 'n dval \<Rightarrow> 'n aenv option" where
  "infer acts v0 =
     while_option (\<lambda>E. \<not> astep acts E \<le> E) (\<lambda>E. widen_env E (astep acts E)) (init_env v0)"

lemma init_env_sound: "v0 \<in> \<gamma>_env (init_env v0)"
  by (simp add: \<gamma>_fun_def init_env_def gamma_num')

lemma widen_env_ge1: "E1 \<le> widen_env E1 E2"
  by (simp add: widen_env_def le_fun_def widen1)

lemma infer_ge_init:
  assumes "infer acts v0 = Some E" shows "init_env v0 \<le> E"
proof (rule while_option_rule[where P = "\<lambda>x. init_env v0 \<le> x", OF _ assms[unfolded infer_def]])
  fix s assume s: "init_env v0 \<le> s" and "\<not> astep acts s \<le> s"
  show "init_env v0 \<le> widen_env s (astep acts s)"
    using s widen_env_ge1 order_trans by blast
next
  show "init_env v0 \<le> init_env v0" by simp
qed

theorem infer_sound:
  assumes "infer acts v0 = Some E"
  shows "dreach v0 (set acts) \<subseteq> \<gamma>_env E"
proof (rule bound_inv_sound)
  have post: "astep acts E \<le> E"
    using while_option_stop[OF assms[unfolded infer_def]] by simp
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound infer_ge_init[OF assms] mono_gamma_env by blast
  thus "is_bound_inv v0 acts E" using post by (simp add: is_bound_inv_def)
qed


subsection \<open>Narrowing: recovering precision after widening\<close>

text \<open>Widening over-shoots (it jumps unstable bounds straight to @{term "\<infinity>"}); a \<^emph>\<open>narrowing\<close>
  pass then tightens them back while staying sound. Soundness is maintained through the loop
  invariant @{term "dreach v0 (set acts) \<subseteq> \<gamma>_env x \<and> astep acts x \<le> x"}: each narrowing step keeps
  both the over-approximation and the post-fixpoint property (the latter needs
  @{thm [source] astep_mono}). Termination of narrowing is not proved here.\<close>

lemma infer_post:
  assumes "infer acts v0 = Some E" shows "astep acts E \<le> E"
  using while_option_stop[OF assms[unfolded infer_def]] by simp

definition narrow_env :: "'n aenv \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "narrow_env E1 E2 = (\<lambda>f. E1 f \<triangle> E2 f)"

lemma narrow_env1:
  assumes "E2 \<le> E1" shows "E2 \<le> narrow_env E1 E2"
proof (rule le_funI)
  fix f
  have "E2 f \<le> E1 f" using assms by (rule le_funD)
  thus "E2 f \<le> narrow_env E1 E2 f" by (simp add: narrow_env_def narrow1)
qed

lemma narrow_env2:
  assumes "E2 \<le> E1" shows "narrow_env E1 E2 \<le> E1"
proof (rule le_funI)
  fix f
  have "E2 f \<le> E1 f" using assms by (rule le_funD)
  thus "narrow_env E1 E2 f \<le> E1 f" by (simp add: narrow_env_def narrow2)
qed

text \<open>A narrowing step preserves the post-fixpoint property (monotonicity is the crux).\<close>

lemma narrow_post_fixpoint:
  assumes "astep acts x \<le> x"
  shows "astep acts (narrow_env x (astep acts x)) \<le> narrow_env x (astep acts x)"
proof -
  have "narrow_env x (astep acts x) \<le> x" using assms by (rule narrow_env2)
  hence "astep acts (narrow_env x (astep acts x)) \<le> astep acts x" by (rule astep_mono)
  also have "astep acts x \<le> narrow_env x (astep acts x)" using assms by (rule narrow_env1)
  finally show ?thesis .
qed

text \<open>A narrowing step preserves the over-approximation.\<close>

lemma narrow_sound:
  assumes "dreach v0 (set acts) \<subseteq> \<gamma>_env x" and "astep acts x \<le> x"
  shows "dreach v0 (set acts) \<subseteq> \<gamma>_env (narrow_env x (astep acts x))"
proof -
  have "dreach v0 (set acts) \<subseteq> \<gamma>_env (astep acts x)"
    using assms(1) astep_extensive mono_gamma_env by (metis subset_trans)
  moreover have "\<gamma>_env (astep acts x) \<subseteq> \<gamma>_env (narrow_env x (astep acts x))"
    using assms(2) narrow_env1 mono_gamma_env by metis
  ultimately show ?thesis by blast
qed

text \<open>Widen to a post-fixpoint, then narrow. The result still over-approximates every reachable
  state (soundness is independent of how far narrowing runs).\<close>

definition infer_narrow :: "'n dact list \<Rightarrow> 'n dval \<Rightarrow> 'n aenv option" where
  "infer_narrow acts v0 =
     (case infer acts v0 of None \<Rightarrow> None
      | Some E \<Rightarrow>
          while_option (\<lambda>x. narrow_env x (astep acts x) < x)
                       (\<lambda>x. narrow_env x (astep acts x)) E)"

theorem infer_narrow_sound:
  assumes "infer_narrow acts v0 = Some E"
  shows "dreach v0 (set acts) \<subseteq> \<gamma>_env E"
proof -
  obtain Ew where w: "infer acts v0 = Some Ew"
    and nar: "while_option (\<lambda>x. narrow_env x (astep acts x) < x)
                           (\<lambda>x. narrow_env x (astep acts x)) Ew = Some E"
    using assms unfolding infer_narrow_def by (auto split: option.splits)
  have "dreach v0 (set acts) \<subseteq> \<gamma>_env E \<and> astep acts E \<le> E"
  proof (rule while_option_rule[where P = "\<lambda>x. dreach v0 (set acts) \<subseteq> \<gamma>_env x \<and> astep acts x \<le> x"
          and b = "\<lambda>x. narrow_env x (astep acts x) < x"
          and c = "\<lambda>x. narrow_env x (astep acts x)" and s = Ew])
    fix x assume J: "dreach v0 (set acts) \<subseteq> \<gamma>_env x \<and> astep acts x \<le> x"
      and "narrow_env x (astep acts x) < x"
    have "dreach v0 (set acts) \<subseteq> \<gamma>_env (narrow_env x (astep acts x))"
      using J using narrow_sound by auto
    moreover have "astep acts (narrow_env x (astep acts x)) \<le> narrow_env x (astep acts x)"
      using J by (blast intro: narrow_post_fixpoint)
    ultimately show "dreach v0 (set acts) \<subseteq> \<gamma>_env (narrow_env x (astep acts x))
                   \<and> astep acts (narrow_env x (astep acts x)) \<le> narrow_env x (astep acts x)" ..
  next
    show "while_option (\<lambda>x. narrow_env x (astep acts x) < x)
                       (\<lambda>x. narrow_env x (astep acts x)) Ew = Some E" by (rule nar)
  next
    show "dreach v0 (set acts) \<subseteq> \<gamma>_env Ew \<and> astep acts Ew \<le> Ew"
      using infer_sound[OF w] infer_post[OF w] by blast
  qed
  thus ?thesis by blast
qed


subsection \<open>Worked example: a fluent assigned a constant\<close>

text \<open>A single fluent (type @{typ unit}) starts at \<open>0\<close>; one action assigns it \<open>5\<close>.
  The interval @{term "[Fin 0, Fin 5]::ivl"} is a bound invariant, so every reachable
  valuation keeps the fluent in \<open>{0..5}\<close>. (The proof uses only
  @{thm [source] le_ivl_iff_subset} and @{thm [source] \<gamma>_ivl_nice}, avoiding the
  fragile empty-interval side conditions of the \<open>_nice\<close> arithmetic lemmas.)\<close>

definition cnt_act :: "unit dact" where
  "cnt_act = [((), DConst 5)]"

definition cnt_init :: "unit dval" where
  "cnt_init = (\<lambda>_. 0)"

definition cnt_bound :: "unit aenv" where
  "cnt_bound = (\<lambda>_. ([Fin 0, Fin 5]::ivl))"

lemma num_ivl_nice: "num_ivl i = [Fin i, Fin i]"
  by transfer simp

lemma astep_upds_cnt: "astep_upds cnt_act cnt_bound f = num_ivl 5"
  by (cases f) (simp add: astep_upds_def cnt_act_def)

lemma cnt_astep_upds_le: "astep_upds cnt_act cnt_bound \<le> cnt_bound"
proof (rule le_funI)
  fix f :: unit
  have "\<gamma>_ivl (num_ivl 5) \<subseteq> \<gamma>_ivl (cnt_bound f)"
    by (auto simp: num_ivl_nice cnt_bound_def \<gamma>_ivl_nice)
  thus "astep_upds cnt_act cnt_bound f \<le> cnt_bound f"
    by (simp add: astep_upds_cnt le_ivl_iff_subset)
qed

lemma cnt_is_bound_inv: "is_bound_inv cnt_init [cnt_act] cnt_bound"
  unfolding is_bound_inv_def
proof
  show "cnt_init \<in> \<gamma>_env cnt_bound"
    by (auto simp: \<gamma>_fun_def cnt_init_def cnt_bound_def \<gamma>_ivl_nice)
next
  have "astep [cnt_act] cnt_bound = cnt_bound \<squnion> astep_upds cnt_act cnt_bound"
    by (simp add: astep_def)
  also have "\<dots> \<le> cnt_bound"
    using cnt_astep_upds_le by (simp add: le_sup_iff)
  finally show "astep [cnt_act] cnt_bound \<le> cnt_bound" .
qed

theorem cnt_reachable_bounded:
  "dreach cnt_init (set [cnt_act]) \<subseteq> {v. 0 \<le> v () \<and> v () \<le> 5}"
proof -
  have "dreach cnt_init (set [cnt_act]) \<subseteq> \<gamma>_env cnt_bound"
    using cnt_is_bound_inv by (rule bound_inv_sound)
  also have "\<gamma>_env cnt_bound \<subseteq> {v. 0 \<le> v () \<and> v () \<le> 5}"
    by (auto simp: \<gamma>_fun_def cnt_bound_def \<gamma>_ivl_nice)
  finally show ?thesis .
qed


subsection \<open>Worked example: a monotone counter (an \<open>increase\<close> effect)\<close>

text \<open>The representative numeric-effect case from the benchmark survey: one action
  \<open>increase x by 1\<close>. The fluent grows without bound above but stays \<open>\<ge> 0\<close>; the inferred
  interval @{term "[Fin 0, \<infinity>]::ivl"} witnesses exactly that. A \<^emph>\<open>global\<close> closure would be
  false here (monotone growth), yet the lower bound is a sound invariant, and widening would
  discover the \<open>\<infinity>\<close> upper bound automatically.\<close>

definition inc_act :: "unit dact" where
  "inc_act = [((), DAdd (DVar ()) (DConst 1))]"

definition inc_init :: "unit dval" where
  "inc_init = (\<lambda>_. 0)"

definition inc_bound :: "unit aenv" where
  "inc_bound = (\<lambda>_. [Fin 0, \<infinity>]::ivl)"

lemma gamma_ivl_bot: "\<gamma>_ivl \<bottom> = {}"
  unfolding bot_ivl_def by transfer (auto simp: \<gamma>_rep_def empty_rep_def)

lemma ivl_Fin_Pinf_neq_bot: "([Fin a, \<infinity>]::ivl) \<noteq> \<bottom>"
proof -
  have "a \<in> \<gamma>_ivl ([Fin a, \<infinity>]::ivl)" by (simp add: \<gamma>_ivl_nice)
  thus ?thesis using gamma_ivl_bot by fastforce
qed

lemma ivl_Fin_Fin_neq_bot:
  assumes "a \<le> b" shows "([Fin a, Fin b]::ivl) \<noteq> \<bottom>"
proof -
  have "a \<in> \<gamma>_ivl ([Fin a, Fin b]::ivl)" using assms by (simp add: \<gamma>_ivl_nice)
  thus ?thesis using gamma_ivl_bot by fastforce
qed

lemma inc_sum: "[Fin 0, \<infinity>] + num_ivl 1 = ([Fin 1, \<infinity>]::ivl)"
  by (simp add: num_ivl_nice plus_ivl_nice ivl_Fin_Pinf_neq_bot ivl_Fin_Fin_neq_bot)

lemma astep_upds_inc: "astep_upds inc_act inc_bound f = ([Fin 1, \<infinity>]::ivl)"
  by (cases f) (simp add: astep_upds_def inc_act_def inc_bound_def inc_sum)

lemma inc_astep_upds_le: "astep_upds inc_act inc_bound \<le> inc_bound"
proof (rule le_funI)
  fix f :: unit
  have "\<gamma>_ivl ([Fin 1, \<infinity>]::ivl) \<subseteq> \<gamma>_ivl (inc_bound f)"
    by (auto simp: inc_bound_def \<gamma>_ivl_nice)
  thus "astep_upds inc_act inc_bound f \<le> inc_bound f"
    by (simp add: astep_upds_inc le_ivl_iff_subset)
qed

lemma inc_is_bound_inv: "is_bound_inv inc_init [inc_act] inc_bound"
  unfolding is_bound_inv_def
proof
  show "inc_init \<in> \<gamma>_env inc_bound"
    by (auto simp: \<gamma>_fun_def inc_init_def inc_bound_def \<gamma>_ivl_nice)
next
  have "astep [inc_act] inc_bound = inc_bound \<squnion> astep_upds inc_act inc_bound"
    by (simp add: astep_def)
  also have "\<dots> \<le> inc_bound" using inc_astep_upds_le by (simp add: le_sup_iff)
  finally show "astep [inc_act] inc_bound \<le> inc_bound" .
qed

theorem inc_reachable_nonneg:
  "dreach inc_init (set [inc_act]) \<subseteq> {v. 0 \<le> v ()}"
proof -
  have "dreach inc_init (set [inc_act]) \<subseteq> \<gamma>_env inc_bound"
    using inc_is_bound_inv by (rule bound_inv_sound)
  also have "\<gamma>_env inc_bound \<subseteq> {v. 0 \<le> v ()}"
    by (auto simp: \<gamma>_fun_def inc_bound_def \<gamma>_ivl_nice)
  finally show ?thesis .
qed

end

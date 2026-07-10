theory Numeric_Bound_Inference_Threshold
  imports Numeric_Bound_Inference
begin

section \<open>Threshold widening for numeric bound inference\<close>

text \<open>
  The base theory @{theory \<open>Numeric_Bound_Inference.Numeric_Bound_Inference\<close>} infers bounds with
  HOL-IMP's \<^emph>\<open>plain\<close> widening @{term "(\<nabla>)"}, which throws a growing bound straight to
  @{term "\<infinity>"} in one step. That guarantees fast termination but loses precision: the
  \<open>cnt\<close> example (\<open>f := 5\<close>) widens to @{term "[Fin 0, \<infinity>]::ivl"} instead of
  @{term "[Fin 0, Fin 5]::ivl"}.

  This theory adds \<^bold>\<open>threshold widening\<close> (BOUND_INFERENCE_pseudocode.md \<open>\<section>\<close>4): a growing bound
  advances only to the next \<^emph>\<open>threshold\<close> (an integer constant drawn from the problem) rather
  than to @{term "\<infinity>"}; only when it must pass every threshold does it reach @{term "\<infinity>"}. With
  the constant \<open>5\<close> in the threshold set, \<open>cnt\<close> now converges at @{term "[Fin 0, Fin 5]::ivl"}.

  Soundness reuses the base development unchanged: the exit test still yields a post-fixpoint of
  @{const astep}, and @{thm [source] bound_inv_sound} does the rest. Threshold widening only needs
  to be \<^emph>\<open>extensive\<close> (@{text widen1}); it is a genuine widening for termination purposes, but as in
  the base theory termination itself is not proved here.
\<close>


subsection \<open>Threshold rounding on @{typ eint}\<close>

text \<open>@{term "thr_below T x"} is the greatest threshold @{text "\<le> x"} (else @{term Minf});
  @{term "thr_above T x"} the least threshold @{text "\<ge> x"} (else @{term Pinf}).\<close>

definition thr_below :: "int list \<Rightarrow> eint \<Rightarrow> eint" where
  "thr_below T x = (let cs = filter (\<lambda>t. Fin t \<le> x) T in if cs = [] then Minf else Fin (Max (set cs)))"

definition thr_above :: "int list \<Rightarrow> eint \<Rightarrow> eint" where
  "thr_above T x = (let cs = filter (\<lambda>t. x \<le> Fin t) T in if cs = [] then Pinf else Fin (Min (set cs)))"

lemma thr_below_le: "thr_below T x \<le> x"
proof (cases "filter (\<lambda>t. Fin t \<le> x) T = []")
  case True
  thus ?thesis by (simp add: thr_below_def)
next
  case False
  let ?cs = "filter (\<lambda>t. Fin t \<le> x) T"
  have ne: "set ?cs \<noteq> {}" using False by (cases ?cs) auto
  have mem: "Max (set ?cs) \<in> set ?cs" using ne by (rule Max_in[OF finite_set])
  have "\<forall>t \<in> set ?cs. Fin t \<le> x" by auto
  hence "Fin (Max (set ?cs)) \<le> x" using mem by blast
  thus ?thesis using False by (simp add: thr_below_def)
qed

lemma thr_above_ge: "x \<le> thr_above T x"
proof (cases "filter (\<lambda>t. x \<le> Fin t) T = []")
  case True
  thus ?thesis by (simp add: thr_above_def)
next
  case False
  let ?cs = "filter (\<lambda>t. x \<le> Fin t) T"
  have ne: "set ?cs \<noteq> {}" using False by (cases ?cs) auto
  have mem: "Min (set ?cs) \<in> set ?cs" using ne by (rule Min_in[OF finite_set])
  have "\<forall>t \<in> set ?cs. x \<le> Fin t" by auto
  hence "x \<le> Fin (Min (set ?cs))" using mem by blast
  thus ?thesis using False by (simp add: thr_above_def)
qed


subsection \<open>Threshold widening on intervals\<close>

text \<open>Same shape as HOL-IMP's @{text widen_rep} (Abs_Int3), but landing on the next threshold
  rather than jumping to @{term Minf}/@{term Pinf}.\<close>

definition widen_thr_rep :: "int list \<Rightarrow> eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
  "widen_thr_rep T p1 p2 =
     (if is_empty_rep p1 then p2 else if is_empty_rep p2 then p1
      else let (l1,h1) = p1; (l2,h2) = p2
           in (if l2 < l1 then thr_below T l2 else l1, if h1 < h2 then thr_above T h2 else h1))"

lift_definition widen_thr_ivl :: "int list \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" is widen_thr_rep
  by (auto simp: widen_thr_rep_def eq_ivl_iff)

text \<open>Threshold widening is extensive in its first argument (@{text widen1}); that is all the
  soundness argument needs. We prove the subset fact on representatives, then transfer.\<close>

lemma widen_thr_rep_ge1: "\<gamma>_rep p \<subseteq> \<gamma>_rep (widen_thr_rep T p q)"
proof (cases "is_empty_rep p")
  case True
  thus ?thesis by (simp add: is_empty_rep_iff)
next
  case notp: False
  show ?thesis
  proof (cases "is_empty_rep q")
    case True
    thus ?thesis using notp by (simp add: widen_thr_rep_def)
  next
    case notq: False
    obtain l1 h1 where p: "p = (l1, h1)" by (cases p)
    obtain l2 h2 where q: "q = (l2, h2)" by (cases q)
    have lo: "(if l2 < l1 then thr_below T l2 else l1) \<le> l1"
    proof (cases "l2 < l1")
      case True
      have "thr_below T l2 \<le> l2" by (rule thr_below_le)
      also have "l2 \<le> l1" using True by simp
      finally show ?thesis using True by simp
    next
      case False
      thus ?thesis by simp
    qed
    have hi: "h1 \<le> (if h1 < h2 then thr_above T h2 else h1)"
    proof (cases "h1 < h2")
      case True
      have "h1 \<le> h2" using True by simp
      also have "h2 \<le> thr_above T h2" by (rule thr_above_ge)
      finally show ?thesis using True by simp
    next
      case False
      thus ?thesis by simp
    qed
    show ?thesis
      using notp notq p q lo hi
      by (auto simp: widen_thr_rep_def \<gamma>_rep_def split: prod.splits elim: order_trans)
  qed
qed

lemma widen_thr_ge1: "iv \<le> widen_thr_ivl T iv iv'"
  unfolding le_ivl_iff_subset
  by transfer (rule widen_thr_rep_ge1)


subsection \<open>Threshold-widening inference\<close>

definition widen_env_thr :: "int list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "widen_env_thr T E1 E2 = (\<lambda>f. widen_thr_ivl T (E1 f) (E2 f))"

lemma widen_env_thr_ge1: "E1 \<le> widen_env_thr T E1 E2"
  by (simp add: widen_env_thr_def le_fun_def widen_thr_ge1)

definition infer_thr :: "int list \<Rightarrow> 'n action list \<Rightarrow> 'n valuation \<Rightarrow> 'n aenv option" where
  "infer_thr T acts v0 =
     while_option (\<lambda>E. \<not> astep acts E \<le> E) (\<lambda>E. widen_env_thr T E (astep acts E)) (init_env v0)"

lemma infer_thr_ge_init:
  assumes "infer_thr T acts v0 = Some E" shows "init_env v0 \<le> E"
proof (rule while_option_rule[where P = "\<lambda>x. init_env v0 \<le> x", OF _ assms[unfolded infer_thr_def]])
  fix s assume s: "init_env v0 \<le> s" and "\<not> astep acts s \<le> s"
  show "init_env v0 \<le> widen_env_thr T s (astep acts s)"
    using s widen_env_thr_ge1 order_trans by blast
next
  show "init_env v0 \<le> init_env v0" by simp
qed

theorem infer_thr_sound:
  assumes "infer_thr T acts v0 = Some E"
  shows "reach v0 (set acts) \<subseteq> \<gamma>_env E"
proof (rule bound_inv_sound)
  have post: "astep acts E \<le> E"
    using while_option_stop[OF assms[unfolded infer_thr_def]] by simp
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound infer_thr_ge_init[OF assms] mono_gamma_env by blast
  thus "is_bound_inv v0 acts E" using post by (simp add: is_bound_inv_def)
qed


subsection \<open>Threshold-set extraction (a convenient default)\<close>

text \<open>Soundness is independent of the threshold list; precision is not. A reasonable default
  gathers every integer constant occurring in the action right-hand sides. The caller can
  prepend the initial fluent values (\<open>\<section>\<close>4 of the pseudocode).\<close>

fun nexp_consts :: "'n nexp \<Rightarrow> int list" where
  "nexp_consts (NConst c) = [c]"
| "nexp_consts (NVar f)   = []"
| "nexp_consts (NAdd a b) = nexp_consts a @ nexp_consts b"
| "nexp_consts (NSub a b) = nexp_consts a @ nexp_consts b"
| "nexp_consts (NMul a b) = nexp_consts a @ nexp_consts b"
| "nexp_consts (NDiv a b) = nexp_consts a @ nexp_consts b"

definition action_consts :: "'n action list \<Rightarrow> int list" where
  "action_consts acts = concat (map (\<lambda>a. concat (map (\<lambda>u. nexp_consts (snd u)) a)) acts)"


section \<open>Narrowing with a non-extensive step (recovers precision)\<close>

text \<open>
  The base @{const infer_narrow} is inert: @{const astep} is \<^emph>\<open>extensive\<close>
  (@{thm [source] astep_extensive}), so @{term "astep acts x \<le> x"} forces
  @{term "astep acts x = x"} and a narrowing step @{term "narrow_env x (astep acts x)"}
  collapses to @{term x}. We split the step into the initial contribution and a
  \<^bold>\<open>pure\<close> action step \<open>pstep\<close> (the join of the action images \<^emph>\<open>without\<close> the
  accumulator @{term E}), and narrow against
  \<open>sstep acts v0 E = init_env v0 \<squnion> pstep acts E\<close>. This step is \<^emph>\<open>not\<close> extensive over
  @{term E} (so narrowing can tighten a bound widening overshot) yet always
  @{text "\<ge> init_env v0"} (so the initial state stays inside the box). Its post-fixpoints are
  exactly the bound invariants, so soundness reuses @{thm [source] bound_inv_sound} unchanged.
\<close>

lemma gamma_num_ivl: "\<gamma>_ivl (num_ivl a) = {a}"
  by (auto simp: num_ivl_nice \<gamma>_ivl_nice)

lemma init_env_le_iff: "init_env v0 \<le> E \<longleftrightarrow> v0 \<in> \<gamma>_env E"
  by (auto simp: init_env_def le_fun_def le_ivl_iff_subset gamma_num_ivl \<gamma>_fun_def)

lemma fold_sup_le_iff:
  fixes z E :: "'a::semilattice_sup"
  shows "fold (\<lambda>a acc. acc \<squnion> g a) xs z \<le> E \<longleftrightarrow> z \<le> E \<and> (\<forall>a\<in>set xs. g a \<le> E)"
proof (induction xs arbitrary: z)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  have "fold (\<lambda>a acc. acc \<squnion> g a) (a # xs) z \<le> E
        \<longleftrightarrow> fold (\<lambda>a acc. acc \<squnion> g a) xs (z \<squnion> g a) \<le> E" by simp
  also have "\<dots> \<longleftrightarrow> (z \<squnion> g a \<le> E) \<and> (\<forall>b\<in>set xs. g b \<le> E)" by (rule Cons.IH)
  also have "\<dots> \<longleftrightarrow> z \<le> E \<and> (\<forall>b\<in>set (a # xs). g b \<le> E)" by (auto simp: le_sup_iff)
  finally show ?case .
qed

lemma astep_le_iff: "astep acts E \<le> E \<longleftrightarrow> (\<forall>a\<in>set acts. astep_upds a E \<le> E)"
  unfolding astep_def by (subst fold_sup_le_iff) simp

definition pstep :: "'n action list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "pstep acts E = fold (\<lambda>a acc. acc \<squnion> astep_upds a E) acts \<bottom>"

lemma pstep_le_iff: "pstep acts E \<le> E \<longleftrightarrow> (\<forall>a\<in>set acts. astep_upds a E \<le> E)"
  unfolding pstep_def by (subst fold_sup_le_iff) simp

lemma pstep_mono:
  assumes "E1 \<le> E2" shows "pstep acts E1 \<le> pstep acts E2"
  unfolding pstep_def
  by (rule fold_sup_mono[OF order_refl]) (rule astep_upds_mono[OF assms])

definition sstep :: "'n action list \<Rightarrow> 'n valuation \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "sstep acts v0 E = init_env v0 \<squnion> pstep acts E"

lemma init_le_sstep: "init_env v0 \<le> sstep acts v0 E"
  by (simp add: sstep_def)

lemma sstep_mono:
  assumes "E1 \<le> E2" shows "sstep acts v0 E1 \<le> sstep acts v0 E2"
  unfolding sstep_def by (rule sup_mono[OF order_refl pstep_mono[OF assms]])

lemma sstep_le_iff_bound_inv: "sstep acts v0 E \<le> E \<longleftrightarrow> is_bound_inv v0 acts E"
proof -
  have "sstep acts v0 E \<le> E \<longleftrightarrow> init_env v0 \<le> E \<and> pstep acts E \<le> E"
    by (simp add: sstep_def le_sup_iff)
  also have "\<dots> \<longleftrightarrow> v0 \<in> \<gamma>_env E \<and> astep acts E \<le> E"
    by (simp add: init_env_le_iff pstep_le_iff astep_le_iff)
  finally show ?thesis by (simp add: is_bound_inv_def)
qed

lemma infer_thr_bound_inv:
  assumes "infer_thr T acts v0 = Some E" shows "is_bound_inv v0 acts E"
proof -
  have "astep acts E \<le> E" using while_option_stop[OF assms[unfolded infer_thr_def]] by simp
  moreover have "v0 \<in> \<gamma>_env E"
    using init_env_sound infer_thr_ge_init[OF assms] mono_gamma_env by blast
  ultimately show ?thesis by (simp add: is_bound_inv_def)
qed

text \<open>A narrowing step preserves the bound-invariant property (the crux is
  @{thm [source] sstep_mono} plus non-extensivity, so the step can strictly tighten).\<close>

lemma narrow_bound_inv_step:
  assumes "is_bound_inv v0 acts x"
  shows "is_bound_inv v0 acts (narrow_env x (sstep acts v0 x))"
proof -
  have le: "sstep acts v0 x \<le> x" using assms by (simp add: sstep_le_iff_bound_inv)
  have y_le_x: "narrow_env x (sstep acts v0 x) \<le> x" using le by (rule narrow_env2)
  have s_le_y: "sstep acts v0 x \<le> narrow_env x (sstep acts v0 x)" using le by (rule narrow_env1)
  have "sstep acts v0 (narrow_env x (sstep acts v0 x)) \<le> sstep acts v0 x"
    using y_le_x by (rule sstep_mono)
  hence "sstep acts v0 (narrow_env x (sstep acts v0 x)) \<le> narrow_env x (sstep acts v0 x)"
    using s_le_y by (rule order_trans)
  thus ?thesis by (simp add: sstep_le_iff_bound_inv)
qed

definition infer_narrow_thr :: "int list \<Rightarrow> 'n action list \<Rightarrow> 'n valuation \<Rightarrow> 'n aenv option" where
  "infer_narrow_thr T acts v0 =
     (case infer_thr T acts v0 of None \<Rightarrow> None
      | Some E \<Rightarrow> while_option (\<lambda>x. narrow_env x (sstep acts v0 x) < x)
                              (\<lambda>x. narrow_env x (sstep acts v0 x)) E)"

theorem infer_narrow_thr_sound:
  assumes "infer_narrow_thr T acts v0 = Some E"
  shows "reach v0 (set acts) \<subseteq> \<gamma>_env E"
proof -
  obtain Ew where w: "infer_thr T acts v0 = Some Ew"
    and nar: "while_option (\<lambda>x. narrow_env x (sstep acts v0 x) < x)
                           (\<lambda>x. narrow_env x (sstep acts v0 x)) Ew = Some E"
    using assms unfolding infer_narrow_thr_def by (auto split: option.splits)
  have "is_bound_inv v0 acts E"
  proof (rule while_option_rule[where P = "is_bound_inv v0 acts"
          and b = "\<lambda>x. narrow_env x (sstep acts v0 x) < x"
          and c = "\<lambda>x. narrow_env x (sstep acts v0 x)" and s = Ew])
    fix x assume inv: "is_bound_inv v0 acts x"
      and "narrow_env x (sstep acts v0 x) < x"
    show "is_bound_inv v0 acts (narrow_env x (sstep acts v0 x))"
      by (rule narrow_bound_inv_step[OF inv])
  next
    show "while_option (\<lambda>x. narrow_env x (sstep acts v0 x) < x)
                       (\<lambda>x. narrow_env x (sstep acts v0 x)) Ew = Some E" by (rule nar)
  next
    show "is_bound_inv v0 acts Ew" by (rule infer_thr_bound_inv[OF w])
  qed
  thus ?thesis by (rule bound_inv_sound)
qed


section \<open>Worked example: threshold widening computes the tight bound [0,5]\<close>

text \<open>
  The base theory's \<open>cnt\<close> fluent (@{const cnt_act}: \<open>f := 5\<close> from @{const cnt_init}: \<open>f = 0\<close>)
  widens to @{term "[Fin 0, \<infinity>]::ivl"} under plain widening. Here we run @{const infer_thr}
  with the threshold set \<open>{0,5}\<close> and prove it returns exactly the base theory's
  @{const cnt_bound} (that is, \<open>\<lambda>_. [Fin 0, Fin 5]\<close>) -- the tight bound.
\<close>

lemma widen_thr_ivl_nice:
  "widen_thr_ivl T [l1,h1] [l2,h2] =
   (if [l1,h1] = \<bottom> then [l2,h2] else if [l2,h2] = \<bottom> then [l1,h1]
    else [if l2 < l1 then thr_below T l2 else l1, if h1 < h2 then thr_above T h2 else h1])"
  unfolding bot_ivl_def by transfer (auto simp: widen_thr_rep_def eq_ivl_empty)

definition cnt_thr :: "int list" where "cnt_thr = [0, 5]"

lemma astep_upds_cnt_const: "astep_upds cnt_act E = (\<lambda>_. num_ivl 5)"
proof (rule ext)
  fix f :: unit
  show "astep_upds cnt_act E f = num_ivl 5" by (cases f) (simp add: astep_upds_def cnt_act_def)
qed

lemma astep_cnt: "astep [cnt_act] E = (\<lambda>f. E f \<squnion> num_ivl 5)"
  by (simp add: astep_def astep_upds_cnt_const sup_fun_def)

lemma num_ivl_sup_0_5: "num_ivl 0 \<squnion> num_ivl 5 = ([Fin 0, Fin 5]::ivl)"
  by (simp add: num_ivl_nice sup_ivl_nice ivl_Fin_Fin_neq_bot min_def max_def)

lemma astep_cnt_init: "astep [cnt_act] (init_env cnt_init) = (\<lambda>_. [Fin 0, Fin 5])"
  by (simp add: astep_cnt init_env_def cnt_init_def num_ivl_sup_0_5)

lemma widen_cnt: "widen_thr_ivl cnt_thr (num_ivl 0) [Fin 0, Fin 5] = ([Fin 0, Fin 5]::ivl)"
proof -
  have "thr_above cnt_thr (Fin 5) = Fin 5" by (simp add: thr_above_def cnt_thr_def)
  moreover have "([Fin 0, Fin 0]::ivl) \<noteq> \<bottom>" using ivl_Fin_Fin_neq_bot[of 0 0] by simp
  moreover have "([Fin 0, Fin 5]::ivl) \<noteq> \<bottom>" using ivl_Fin_Fin_neq_bot[of 0 5] by simp
  ultimately show ?thesis by (simp add: num_ivl_nice widen_thr_ivl_nice)
qed

lemma test_init_false: "\<not> astep [cnt_act] (init_env cnt_init) \<le> init_env cnt_init"
proof -
  have "\<not> num_ivl (5::int) \<le> num_ivl 0" by (simp add: le_ivl_iff_subset gamma_num_ivl)
  hence "\<not> astep_upds cnt_act (init_env cnt_init) \<le> init_env cnt_init"
    by (simp add: astep_upds_cnt_const le_fun_def init_env_def cnt_init_def)
  thus ?thesis by (simp add: astep_le_iff)
qed

lemma test_bound_true: "astep [cnt_act] cnt_bound \<le> cnt_bound"
  using cnt_is_bound_inv by (simp add: is_bound_inv_def)

theorem infer_thr_cnt: "infer_thr cnt_thr [cnt_act] cnt_init = Some cnt_bound"
proof -
  let ?b = "\<lambda>E::unit aenv. \<not> astep [cnt_act] E \<le> E"
  let ?c = "\<lambda>E::unit aenv. widen_env_thr cnt_thr E (astep [cnt_act] E)"
  have c_init: "?c (init_env cnt_init) = cnt_bound"
    by (simp add: widen_env_thr_def astep_cnt init_env_def cnt_init_def num_ivl_sup_0_5 widen_cnt cnt_bound_def)
  have "while_option ?b ?c (init_env cnt_init) = while_option ?b ?c cnt_bound"
    using test_init_false c_init by (subst while_option_unfold) simp
  also have "\<dots> = Some cnt_bound"
    using test_bound_true by (subst while_option_unfold) simp
  finally show ?thesis by (simp add: infer_thr_def)
qed


section \<open>Worked example: the counter domain (smallest instance)\<close>

text \<open>
  The design spec (BOUND_INFERENCE_pseudocode.md \<open>\<section>\<close>5) infers \<open>[0, n]\<close> for a counter capped by a
  guard \<open>counter = item_id\<close>. Its \<^bold>\<open>smallest instance\<close> (\<open>n = 1\<close>, one item with id \<open>0\<close>) is
  \<^item> \<open>inc\<close>:   guard \<open>counter = 0\<close>,   effect \<open>counter += 1\<close>
  \<^item> \<open>reset\<close>: effect \<open>counter := 0\<close>
  with \<open>counter = 0\<close> initially. \<^emph>\<open>With\<close> the guard the reachable set is \<open>{0, 1}\<close>: from \<open>0\<close>, \<open>inc\<close>
  fires (guard \<open>0 = 0\<close>) giving \<open>1\<close>; at \<open>1\<close> the guard \<open>1 = 0\<close> fails, so \<open>inc\<close> is blocked; \<open>reset\<close>
  returns to \<open>0\<close>. Hence the tight bound is \<open>[0, 1]\<close>.

  \<^bold>\<open>Why this fragment gets \<open>[0, \<infinity>]\<close> instead.\<close> An action here is its update list \<^emph>\<open>only\<close> --
  numeric guards are dropped (a sound over-approximation: dropping a guard only \<^emph>\<open>adds\<close>
  transitions, \<open>\<section>\<close>4). So \<open>inc\<close> becomes an \<^bold>\<open>unconditional\<close> \<open>counter += 1\<close>, whose reachable set
  from \<open>0\<close> is all of \<open>\<nat>\<close>. The inferred bound is therefore \<open>[0, \<infinity>]\<close> -- sound, and in fact
  \<^emph>\<open>tight for the guard-free system\<close>, but not the \<open>[0, 1]\<close> the guard would give. Threshold
  widening cannot rescue it: no finite threshold caps a genuinely unbounded fluent, so the upper
  bound correctly reaches \<open>\<infinity>\<close> (the "cannot finitize" verdict). Recovering \<open>[0, 1]\<close> needs the
  guard-refinement pass (intersect with \<open>counter = 0\<close> via @{const inv_less_ivl} / equality),
  which is future work. We reuse the base theory's @{const inc_act} / @{const inc_init} /
  @{const inc_bound} (\<open>= [0, \<infinity>]\<close>) for the increment and add @{term ctr_reset}.
\<close>

definition ctr_reset :: "unit action" where "ctr_reset = [((), NConst 0)]"

lemma astep_upds_ctr_reset: "astep_upds ctr_reset E = (\<lambda>_. num_ivl 0)"
proof (rule ext)
  fix f :: unit
  show "astep_upds ctr_reset E f = num_ivl 0" by (cases f) (simp add: astep_upds_def ctr_reset_def)
qed

lemma ctr_reset_le: "astep_upds ctr_reset inc_bound \<le> inc_bound"
  by (simp add: astep_upds_ctr_reset le_fun_def inc_bound_def le_ivl_iff_subset gamma_num_ivl \<gamma>_ivl_nice)

text \<open>The guard-free counter (increment + reset) has \<open>[0, \<infinity>]\<close> as a bound invariant.\<close>

lemma ctr_is_bound_inv: "is_bound_inv inc_init [inc_act, ctr_reset] inc_bound"
  unfolding is_bound_inv_def
proof
  show "inc_init \<in> \<gamma>_env inc_bound"
    by (auto simp: \<gamma>_fun_def inc_init_def inc_bound_def \<gamma>_ivl_nice)
next
  show "astep [inc_act, ctr_reset] inc_bound \<le> inc_bound"
    by (simp add: astep_le_iff inc_astep_upds_le ctr_reset_le)
qed

text \<open>So every reachable valuation keeps the counter \<open>\<ge> 0\<close> (the sound lower bound is real; the
  upper bound is \<open>\<infinity>\<close>, i.e. genuinely unbounded once the capping guard is dropped).\<close>

theorem ctr_reachable_nonneg:
  "reach inc_init (set [inc_act, ctr_reset]) \<subseteq> {v. 0 \<le> v ()}"
proof -
  have "reach inc_init (set [inc_act, ctr_reset]) \<subseteq> \<gamma>_env inc_bound"
    using ctr_is_bound_inv by (rule bound_inv_sound)
  also have "\<gamma>_env inc_bound \<subseteq> {v. 0 \<le> v ()}"
    by (auto simp: \<gamma>_fun_def inc_bound_def \<gamma>_ivl_nice)
  finally show ?thesis .
qed

end

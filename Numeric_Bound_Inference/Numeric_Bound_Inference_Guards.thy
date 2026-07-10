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
  the guard before applying an action's effects: intersect each fluent's interval with what the
  guard permits (HOL-IMP @{term "(\<sqinter>)"} / @{thm [source] \<gamma>_inf}). Refinement is sound and can only
  shrink the box, so soundness still reduces to a bound-invariant check (@{text gbound_inv_sound},
  the guarded mirror of @{thm [source] bound_inv_sound}). With guards the counter's \<open>[0, n]\<close>
  becomes a provable invariant, and guarded threshold widening \<^emph>\<open>computes\<close> it.

  Fragment: positive fluent-vs-constant comparisons (\<open>\<le>\<close>, \<open>\<ge>\<close>, \<open>=\<close>), matching the Gigante survey's
  numeric guards. Fluent-to-fluent comparisons are a straightforward extension (refine both sides).
\<close>


subsection \<open>Guarded concrete semantics\<close>

datatype 'n gcomp = GLe 'n int | GGe 'n int | GEq 'n int

fun sat_gcomp :: "'n valuation \<Rightarrow> 'n gcomp \<Rightarrow> bool" where
  "sat_gcomp v (GLe f k) = (v f \<le> k)"
| "sat_gcomp v (GGe f k) = (k \<le> v f)"
| "sat_gcomp v (GEq f k) = (v f = k)"

definition sat_guard :: "'n valuation \<Rightarrow> 'n gcomp list \<Rightarrow> bool" where
  "sat_guard v g = (\<forall>c \<in> set g. sat_gcomp v c)"

text \<open>A guarded action is a guard (conjunction of comparisons) together with its parallel updates.\<close>

type_synonym 'n gaction = "'n gcomp list \<times> 'n action"

text \<open>Concrete collecting semantics: an action fires only from a state satisfying its guard.\<close>

inductive_set greach :: "'n valuation \<Rightarrow> 'n gaction set \<Rightarrow> 'n valuation set"
  for v0 :: "'n valuation" and A :: "'n gaction set"
where
  greach_init: "v0 \<in> greach v0 A"
| greach_step: "\<lbrakk> v \<in> greach v0 A; (g, us) \<in> A; sat_guard v g \<rbrakk>
                \<Longrightarrow> apply_upds us v \<in> greach v0 A"


subsection \<open>Abstract guard refinement\<close>

text \<open>The half-bounded intervals a single comparison permits.\<close>

definition ivl_le :: "int \<Rightarrow> ivl" where "ivl_le k = [Minf, Fin k]"
definition ivl_ge :: "int \<Rightarrow> ivl" where "ivl_ge k = [Fin k, Pinf]"

lemma gamma_ivl_le: "\<gamma>_ivl (ivl_le k) = {i. i \<le> k}"
  by (auto simp: ivl_le_def \<gamma>_ivl_nice)

lemma gamma_ivl_ge: "\<gamma>_ivl (ivl_ge k) = {i. k \<le> i}"
  by (auto simp: ivl_ge_def \<gamma>_ivl_nice)

lemma gamma_env_update:
  assumes "v \<in> \<gamma>_env E" and "v f \<in> \<gamma>_ivl iv"
  shows "v \<in> \<gamma>_env (E(f := iv))"
  using assms by (simp add: \<gamma>_fun_def)

text \<open>Refine the box of one fluent by one comparison (intersect with the permitted half-interval).\<close>

fun refine_gcomp :: "'n gcomp \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "refine_gcomp (GLe f k) E = E(f := E f \<sqinter> ivl_le k)"
| "refine_gcomp (GGe f k) E = E(f := E f \<sqinter> ivl_ge k)"
| "refine_gcomp (GEq f k) E = E(f := E f \<sqinter> num_ivl k)"

definition refine_guard :: "'n gcomp list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "refine_guard g E = fold refine_gcomp g E"

lemma refine_gcomp_sound:
  assumes "v \<in> \<gamma>_env E" and "sat_gcomp v c"
  shows "v \<in> \<gamma>_env (refine_gcomp c E)"
proof (cases c)
  case (GLe f k)
  have "v f \<in> \<gamma>_ivl (E f)" using assms(1) by (simp add: \<gamma>_fun_def)
  moreover have "v f \<in> \<gamma>_ivl (ivl_le k)" using assms(2) GLe by (simp add: gamma_ivl_le)
  ultimately have "v f \<in> \<gamma>_ivl (E f \<sqinter> ivl_le k)" by (simp add: \<gamma>_inf)
  thus ?thesis using assms(1) GLe by (simp add: gamma_env_update)
next
  case (GGe f k)
  have "v f \<in> \<gamma>_ivl (E f)" using assms(1) by (simp add: \<gamma>_fun_def)
  moreover have "v f \<in> \<gamma>_ivl (ivl_ge k)" using assms(2) GGe by (simp add: gamma_ivl_ge)
  ultimately have "v f \<in> \<gamma>_ivl (E f \<sqinter> ivl_ge k)" by (simp add: \<gamma>_inf)
  thus ?thesis using assms(1) GGe by (simp add: gamma_env_update)
next
  case (GEq f k)
  have "v f \<in> \<gamma>_ivl (E f)" using assms(1) by (simp add: \<gamma>_fun_def)
  moreover have "v f \<in> \<gamma>_ivl (num_ivl k)" using assms(2) GEq by (simp add: gamma_num_ivl)
  ultimately have "v f \<in> \<gamma>_ivl (E f \<sqinter> num_ivl k)" by (simp add: \<gamma>_inf)
  thus ?thesis using assms(1) GEq by (simp add: gamma_env_update)
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

text \<open>Apply an action's effects to the guard-refined box.\<close>

definition gastep_upds :: "'n gaction \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "gastep_upds ga E = astep_upds (snd ga) (refine_guard (fst ga) E)"

lemma gastep_upds_sound:
  assumes "v \<in> \<gamma>_env E" and "sat_guard v (fst ga)"
  shows "apply_upds (snd ga) v \<in> \<gamma>_env (gastep_upds ga E)"
proof -
  have "v \<in> \<gamma>_env (refine_guard (fst ga) E)" using assms by (simp add: refine_guard_sound)
  thus ?thesis unfolding gastep_upds_def by (rule astep_upds_sound)
qed

definition gastep :: "'n gaction list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "gastep acts E = fold (\<lambda>a acc. acc \<squnion> gastep_upds a E) acts E"

lemma gastep_extensive: "E \<le> gastep acts E"
  unfolding gastep_def by (rule fold_sup_init)

lemma gastep_ge_action: "a \<in> set acts \<Longrightarrow> gastep_upds a E \<le> gastep acts E"
  unfolding gastep_def by (rule fold_sup_elem)

definition is_gbound_inv :: "'n valuation \<Rightarrow> 'n gaction list \<Rightarrow> 'n aenv \<Rightarrow> bool" where
  "is_gbound_inv v0 acts E \<longleftrightarrow> v0 \<in> \<gamma>_env E \<and> gastep acts E \<le> E"

theorem gbound_inv_sound:
  assumes inv: "is_gbound_inv v0 acts E"
  shows "greach v0 (set acts) \<subseteq> \<gamma>_env E"
proof
  fix v assume "v \<in> greach v0 (set acts)"
  thus "v \<in> \<gamma>_env E"
  proof (induction rule: greach.induct)
    case greach_init
    show ?case using inv by (simp add: is_gbound_inv_def)
  next
    case (greach_step v g us)
    have "apply_upds us v \<in> \<gamma>_env (gastep_upds (g, us) E)"
      using greach_step.IH greach_step.hyps(3) gastep_upds_sound[of v E "(g, us)"] by simp
    moreover have "gastep_upds (g, us) E \<le> E"
    proof -
      have "gastep_upds (g, us) E \<le> gastep acts E"
        using greach_step.hyps(2) by (rule gastep_ge_action)
      also have "\<dots> \<le> E" using inv by (simp add: is_gbound_inv_def)
      finally show ?thesis .
    qed
    ultimately show ?case using mono_gamma_env by blast
  qed
qed


subsection \<open>Guarded inference (plain and threshold widening)\<close>

definition ginfer :: "'n gaction list \<Rightarrow> 'n valuation \<Rightarrow> 'n aenv option" where
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
  shows "greach v0 (set acts) \<subseteq> \<gamma>_env E"
proof (rule gbound_inv_sound)
  have post: "gastep acts E \<le> E"
    using while_option_stop[OF assms[unfolded ginfer_def]] by simp
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound ginfer_ge_init[OF assms] mono_gamma_env by blast
  thus "is_gbound_inv v0 acts E" using post by (simp add: is_gbound_inv_def)
qed

definition ginfer_thr :: "int list \<Rightarrow> 'n gaction list \<Rightarrow> 'n valuation \<Rightarrow> 'n aenv option" where
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
  shows "greach v0 (set acts) \<subseteq> \<gamma>_env E"
proof (rule gbound_inv_sound)
  have post: "gastep acts E \<le> E"
    using while_option_stop[OF assms[unfolded ginfer_thr_def]] by simp
  have "v0 \<in> \<gamma>_env E"
    using init_env_sound ginfer_thr_ge_init[OF assms] mono_gamma_env by blast
  thus "is_gbound_inv v0 acts E" using post by (simp add: is_gbound_inv_def)
qed


subsection \<open>Tight threshold extraction (guard caps + signed landings)\<close>

text \<open>Precision-only (soundness is threshold-independent, @{thm [source] ginfer_thr_sound}):
  harvest the tight threshold set from the guarded action system -- guard caps, the signed
  landing values of guarded self-offsets, and effect-RHS constants with @{text NMul}/@{text NDiv}
  coefficient noise dropped -- so the widening lands on problem constants instead of jumping to
  @{term "\<infinity>"}. No soundness obligation: @{const ginfer_thr}/@{thm [source] ginfer_thr_sound} never
  inspect the threshold list.\<close>

fun gcomp_fluent :: "'n gcomp \<Rightarrow> 'n" where
  "gcomp_fluent (GLe f _) = f" | "gcomp_fluent (GGe f _) = f" | "gcomp_fluent (GEq f _) = f"

fun gcomp_const :: "'n gcomp \<Rightarrow> int" where
  "gcomp_const (GLe _ k) = k" | "gcomp_const (GGe _ k) = k" | "gcomp_const (GEq _ k) = k"

definition guard_consts :: "'n gcomp list \<Rightarrow> int list" where
  "guard_consts g = map gcomp_const g"

definition guard_consts_on :: "'n \<Rightarrow> 'n gcomp list \<Rightarrow> int list" where
  "guard_consts_on f g = map gcomp_const (filter (\<lambda>c. gcomp_fluent c = f) g)"

text \<open>Signed self-offset: @{text \<open>f := f + c\<close>} \<mapsto> @{term "Some c"},
  @{text \<open>f := f - c\<close>} \<mapsto> @{term "Some (- c)"}, anything else \<mapsto> @{term None}.\<close>
fun signed_offset :: "'n \<Rightarrow> 'n nexp \<Rightarrow> int option" where
  "signed_offset f (NAdd (NVar g) (NConst c)) = (if g = f then Some c else None)"
| "signed_offset f (NAdd (NConst c) (NVar g)) = (if g = f then Some c else None)"
| "signed_offset f (NSub (NVar g) (NConst c)) = (if g = f then Some (- c) else None)"
| "signed_offset f _ = None"

text \<open>A guarded self-offset lands on @{term "k + d"} for each cap @{term k} on the offset fluent.\<close>
definition landing_cs :: "'n gcomp list \<Rightarrow> ('n \<times> 'n nexp) \<Rightarrow> int list" where
  "landing_cs g u = (case signed_offset (fst u) (snd u) of
       None \<Rightarrow> [] | Some d \<Rightarrow> map (\<lambda>k. k + d) (guard_consts_on (fst u) g))"

text \<open>Effect-RHS constants, dropping @{text NMul}/@{text NDiv} coefficients (threshold noise).\<close>
fun nexp_thr_consts :: "'n nexp \<Rightarrow> int list" where
  "nexp_thr_consts (NConst c) = [c]"
| "nexp_thr_consts (NVar _)   = []"
| "nexp_thr_consts (NAdd a b) = nexp_thr_consts a @ nexp_thr_consts b"
| "nexp_thr_consts (NSub a b) = nexp_thr_consts a @ nexp_thr_consts b"
| "nexp_thr_consts (NMul _ _) = []"
| "nexp_thr_consts (NDiv _ _) = []"

definition gaction_thr :: "'n gaction \<Rightarrow> int list" where
  "gaction_thr ga = guard_consts (fst ga)
                  @ concat (map (landing_cs (fst ga)) (snd ga))
                  @ concat (map (nexp_thr_consts \<circ> snd) (snd ga))"

text \<open>The tight threshold set: initial fluent values (the caller supplies the fluent list, since
  @{typ 'n} is not enumerable in general) plus every action's harvest.\<close>
definition thr_set :: "'n list \<Rightarrow> 'n valuation \<Rightarrow> 'n gaction list \<Rightarrow> int list" where
  "thr_set fs v0 acts = remdups (map v0 fs @ concat (map gaction_thr acts))"



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
  "ctr_act = ([GLe () 0], [((), NAdd (NVar ()) (NConst 1))])"

definition ctr_init :: "unit valuation" where
  "ctr_init = (\<lambda>_. 0)"

definition ctr_bound :: "unit aenv" where
  "ctr_bound = (\<lambda>_. [Fin 0, Fin 1])"

lemma ctr_init_in: "ctr_init \<in> \<gamma>_env ctr_bound"
  by (auto simp: \<gamma>_fun_def ctr_init_def ctr_bound_def \<gamma>_ivl_nice)

lemma ctr_step_le: "gastep [ctr_act] ctr_bound \<le> ctr_bound"
  by (simp add: gastep_def gastep_upds_def refine_guard_def ctr_act_def ctr_bound_def
                astep_upds_def ivl_le_def num_ivl_nice inf_ivl_nice plus_ivl_nice
                sup_ivl_nice le_ivl_nice le_fun_def ivl_Fin_Fin_neq_bot)

lemma ctr_is_gbound_inv: "is_gbound_inv ctr_init [ctr_act] ctr_bound"
  unfolding is_gbound_inv_def using ctr_init_in ctr_step_le by blast

theorem ctr_reachable_bounded:
  "greach ctr_init (set [ctr_act]) \<subseteq> {v. 0 \<le> v () \<and> v () \<le> 1}"
proof -
  have "greach ctr_init (set [ctr_act]) \<subseteq> \<gamma>_env ctr_bound"
    using ctr_is_gbound_inv by (rule gbound_inv_sound)
  also have "\<gamma>_env ctr_bound \<subseteq> {v. 0 \<le> v () \<and> v () \<le> 1}"
    by (auto simp: \<gamma>_fun_def ctr_bound_def \<gamma>_ivl_nice)
  finally show ?thesis .
qed

text \<open>The guarded threshold analysis is executable and computes the recovered box \<open>[0,1]\<close>.\<close>

value "map_option (\<lambda>E. E ()) (ginfer_thr [0, 1::int] [ctr_act] ctr_init)"


text \<open>The tight threshold set is now AUTO-extracted (no hand-supplied list): @{const thr_set}
  harvests \<open>{0, 1}\<close> for the guarded self-increment (init \<open>0\<close>, guard cap \<open>0\<close>, landing \<open>0 + 1\<close>), and
  feeding it to @{const ginfer_thr} recomputes the same tight box \<open>[0,1]\<close>.\<close>

value "thr_set [()] ctr_init [ctr_act]"
  \<comment> \<open>\<open>[0, 1]\<close>: init \<open>0\<close>, guard cap \<open>0\<close> (\<open>GLe () 0\<close>), landing \<open>0 + 1\<close> (self-increment \<open>+1\<close>)\<close>

value "map_option (\<lambda>E. E ()) (ginfer_thr (thr_set [()] ctr_init [ctr_act]) [ctr_act] ctr_init)"
  \<comment> \<open>\<open>Some [Fin 0, Fin 1]\<close> -- the tight box, threshold set AUTO-extracted\<close>

text \<open>And the unguarded constant-assign counter of the threshold theory (\<open>cnt := 5\<close>, starting \<open>0\<close>):
  the harvest is \<open>{0, 5}\<close> (init \<open>0\<close> + the assigned constant \<open>5\<close>; no guard \<Rightarrow> no landing) -- exactly
  the list @{const cnt_thr} previously supplied by hand.\<close>

value "thr_set [()] cnt_init [([], cnt_act)]"
  \<comment> \<open>\<open>[0, 5]\<close>: init \<open>0\<close>, assign-constant \<open>5\<close> (no guard \<Rightarrow> no landing)\<close>
end

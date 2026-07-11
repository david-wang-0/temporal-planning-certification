theory Numeric_Bound_Inference_Extract
  imports Numeric_Bound_Inference_Guards
begin

section \<open>Finite-box extraction: the \<open>\<infinity> \<Rightarrow> reject\<close> bridge to the executable pipeline\<close>

text \<open>
  The threshold interval analysis (@{const ginfer_thr}) produces a per-fluent box of
  @{typ ivl}s whose endpoints are @{typ eint} (@{const Fin} / @{term \<infinity>} / @{term "-\<infinity>"});
  a genuinely-unbounded fluent comes out with an infinite endpoint. The NTA reduction, in
  contrast, encodes each numeric fluent as a \<^emph>\<open>bounded\<close> @{typ int} network variable
  (its \<open>fluent_lo\<close> / \<open>fluent_hi\<close> are finite @{typ int}). The executable pipeline must therefore
  either extract a \<^bold>\<open>finite\<close> @{typ int} box \<open>[lo, hi]\<close> for every tracked fluent, or \<^bold>\<open>reject\<close>
  the problem (``bound-inference failed'').

  This theory builds that extraction (@{text ivl_bounds} / @{text extract_box} /
  @{text infer_fluent_bounds}) and proves its soundness: whenever extraction succeeds, the
  extracted finite box bounds every reachable valuation on the tracked fluents.
\<close>


subsection \<open>Extracting the finite endpoints of a single interval\<close>

text \<open>The representation-level extractor: a rep \<open>(l, h)\<close> yields \<open>Some (i, j)\<close>
  exactly when it is a non-empty \<^emph>\<open>finite\<close> interval \<open>(Fin i, Fin j)\<close> with \<open>i \<le> j\<close>;
  every other rep -- empty, or with an infinite endpoint -- yields @{term None}.\<close>

definition bounds_rep :: "eint2 \<Rightarrow> (int \<times> int) option" where
  "bounds_rep p = (case p of (Fin i, Fin j) \<Rightarrow> (if i \<le> j then Some (i, j) else None)
                          | _ \<Rightarrow> None)"

lemma bounds_rep_respect:
  "eq_ivl p1 p2 \<Longrightarrow> bounds_rep p1 = bounds_rep p2"
  by (auto simp: eq_ivl_def bounds_rep_def \<gamma>_rep_cases Icc_eq_Icc
           split: extended.splits prod.splits if_splits)

lift_definition ivl_bounds :: "ivl \<Rightarrow> (int \<times> int) option" is bounds_rep
  by (rule bounds_rep_respect)

definition finite_ivl :: "ivl \<Rightarrow> bool" where
  "finite_ivl iv \<longleftrightarrow> ivl_bounds iv \<noteq> None"

lemma bounds_rep_gamma:
  assumes "bounds_rep p = Some (lo, hi)"
  shows "\<gamma>_rep p = {lo..hi}"
  using assms
  by (auto simp: bounds_rep_def \<gamma>_rep_cases split: extended.splits prod.splits if_splits)

lemma ivl_bounds_gamma:
  assumes "ivl_bounds iv = Some (lo, hi)"
  shows "\<gamma>_ivl iv = {lo..hi}"
  using assms
  by (transfer) (rule bounds_rep_gamma)


subsection \<open>Extracting a finite box for a list of fluents\<close>

definition extract_box :: "'n list \<Rightarrow> 'n aenv \<Rightarrow> ('n \<Rightarrow> int \<times> int) option" where
  "extract_box fs E =
     (if \<forall>f\<in>set fs. finite_ivl (E f) then Some (\<lambda>f. the (ivl_bounds (E f))) else None)"

definition infer_fluent_bounds ::
    "int list \<Rightarrow> 'n list \<Rightarrow> 'n gaction list \<Rightarrow> 'n valuation \<Rightarrow> ('n \<Rightarrow> int \<times> int) option" where
  "infer_fluent_bounds T fs acts v0 =
     (case ginfer_thr T acts v0 of None \<Rightarrow> None | Some E \<Rightarrow> extract_box fs E)"


subsection \<open>Soundness of the extracted finite box\<close>

theorem infer_fluent_bounds_sound:
  assumes b: "infer_fluent_bounds T fs acts v0 = Some b"
    and v: "v \<in> greach v0 (set acts)"
    and f: "f \<in> set fs"
  shows "fst (b f) \<le> v f \<and> v f \<le> snd (b f)"
proof -
  obtain E where E: "ginfer_thr T acts v0 = Some E"
    and box: "extract_box fs E = Some b"
    using b by (auto simp: infer_fluent_bounds_def split: option.splits)
  have fin: "\<forall>g\<in>set fs. finite_ivl (E g)"
    and bdef: "b = (\<lambda>g. the (ivl_bounds (E g)))"
    using box by (auto simp: extract_box_def split: if_splits)
  have "ivl_bounds (E f) \<noteq> None" using fin f by (simp add: finite_ivl_def)
  then obtain lo hi where lohi: "ivl_bounds (E f) = Some (lo, hi)" by auto
  hence bf: "b f = (lo, hi)" using bdef by simp
  have "\<gamma>_ivl (E f) = {lo..hi}" using lohi by (rule ivl_bounds_gamma)
  moreover have "v \<in> \<gamma>_env E" using ginfer_thr_sound[OF E] v by blast
  hence "v f \<in> \<gamma>_ivl (E f)" by (simp add: \<gamma>_fun_def)
  ultimately have "v f \<in> {lo..hi}" by simp
  thus ?thesis using bf by simp
qed

text \<open>A @{const \<gamma>_env}-level restatement: the extracted box contains the whole reachable set,
  restricted to the tracked fluents.\<close>

corollary infer_fluent_bounds_greach_subset:
  assumes "infer_fluent_bounds T fs acts v0 = Some b"
  shows "greach v0 (set acts)
           \<subseteq> {v. \<forall>f\<in>set fs. fst (b f) \<le> v f \<and> v f \<le> snd (b f)}"
  using infer_fluent_bounds_sound[OF assms] by blast


subsection \<open>Sanity: a point interval is finite, @{term \<top>} is not\<close>

lemma ivl_bounds_num_ivl: "ivl_bounds (num_ivl k) = Some (k, k)"
  by (transfer) (simp add: bounds_rep_def)

lemma finite_ivl_num_ivl: "finite_ivl (num_ivl k)"
  by (simp add: finite_ivl_def ivl_bounds_num_ivl)

lemma ivl_bounds_top: "ivl_bounds \<top> = None"
  by (transfer) (simp add: bounds_rep_def top_ivl_def)

lemma not_finite_ivl_top: "\<not> finite_ivl \<top>"
  by (simp add: finite_ivl_def ivl_bounds_top)


subsection \<open>Demo: finite box extracted, \<open>\<infinity>\<close> box rejected\<close>

text \<open>\<^bold>\<open>Success.\<close> The guarded counter (\<open>counter := counter + 1\<close> guarded by \<open>counter \<le> 0\<close>) of
  @{theory \<open>Numeric_Bound_Inference.Numeric_Bound_Inference_Guards\<close>}: threshold widening lands
  on the recovered box \<open>[0, 1]\<close>, so extraction succeeds with the finite box \<open>(0, 1)\<close>.\<close>

value "map_option (\<lambda>b. b ())
         (infer_fluent_bounds (thr_set [()] ctr_init [ctr_act]) [()] [ctr_act] ctr_init)"
  \<comment> \<open>\<open>Some (0, 1)\<close> -- a finite box\<close>

text \<open>\<^bold>\<open>Rejection.\<close> The \<^emph>\<open>unguarded\<close> monotone counter (\<open>counter := counter + 1\<close>, no guard) grows
  without bound; threshold widening returns \<open>[Fin 0, \<infinity>]\<close>, whose upper endpoint is infinite, so
  extraction rejects the problem (``bound-inference failed'', @{term None}).\<close>

definition unguarded_inc :: "unit gaction" where
  "unguarded_inc = ([], [((), NAdd (NVar ()) (NConst 1))])"

value "map_option (\<lambda>E. E ())
         (ginfer_thr (thr_set [()] ctr_init [unguarded_inc]) [unguarded_inc] ctr_init)"
  \<comment> \<open>\<open>Some [Fin 0, \<infinity>]\<close> -- the \<open>\<infinity>\<close> upper bound the guard-free run discovers\<close>

value "infer_fluent_bounds (thr_set [()] ctr_init [unguarded_inc]) [()] [unguarded_inc] ctr_init"
  \<comment> \<open>\<open>None\<close> -- rejected: the \<open>\<infinity>\<close> endpoint is not extractable to a finite \<open>int\<close> box\<close>

end

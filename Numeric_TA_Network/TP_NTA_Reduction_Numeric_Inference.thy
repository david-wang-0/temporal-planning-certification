theory TP_NTA_Reduction_Numeric_Inference
  imports
    TP_NTA_Reduction_Numeric_Bounds
    Numeric_Bound_Inference.Numeric_Bound_Inference_Extract
begin

section \<open>Discharging the bound certificate from the interval bound inference\<close>

text \<open>The reduction side of the bound-inference bridge: the reduction's numeric fragment (@{typ \<open>('n, 'r) nexp\<close>}
  over a partial field valuation) is translated into the inference's integer draft world
  (@{typ \<open>'n dexp\<close>} over a total @{typ int} valuation), the relaxed snaps become guarded draft actions,
  and a box returned by @{const infer_fluent_bounds_on} on that translation discharges
  @{text num_bound_inv} whenever the declared @{text fluent_lo}/@{text fluent_hi} agree with it.
  The translation is faithful on the @{text nexp_ok} fragment (integer-valued reads, exact divisions),
  which is exactly what the grounder-match contract guarantees on integer-ok valuations.\<close>

fun cmp_op_to_cmpop :: "cmp_op \<Rightarrow> cmpop" where
  "cmp_op_to_cmpop Ceq = CEq"
| "cmp_op_to_cmpop Cle = CLe"
| "cmp_op_to_cmpop Cge = CGe"
| "cmp_op_to_cmpop Clt = CLt"
| "cmp_op_to_cmpop Cgt = CGt"

context numeric_tp_nta_reduction_defs
begin

text \<open>Syntactic translation of the numeric fragment into the draft world: constants go through
  @{term const_to_int}, everything else is structural.\<close>
primrec nexp_to_dexp :: "('n, 'r) nexp \<Rightarrow> 'n dexp" where
  "nexp_to_dexp (NConst c) = DConst (const_to_int c)"
| "nexp_to_dexp (NVar f)   = DVar f"
| "nexp_to_dexp (NAdd a b) = DAdd (nexp_to_dexp a) (nexp_to_dexp b)"
| "nexp_to_dexp (NSub a b) = DSub (nexp_to_dexp a) (nexp_to_dexp b)"
| "nexp_to_dexp (NMul a b) = DMul (nexp_to_dexp a) (nexp_to_dexp b)"
| "nexp_to_dexp (NDiv a b) = DDiv (nexp_to_dexp a) (nexp_to_dexp b)"

fun comp_to_gcomp :: "('n, 'r) comp \<Rightarrow> 'n gcomp" where
  "comp_to_gcomp (Comp p a b) = GCmp (cmp_op_to_cmpop p) (nexp_to_dexp a) (nexp_to_dexp b)"

text \<open>A relaxed snap as a guarded draft action: its numeric guard and its numeric updates.\<close>
definition snap_gaction :: "'snap_action \<Rightarrow> 'n gaction" where
  "snap_gaction s = (map comp_to_gcomp (n_pre s), map (\<lambda>(f, e). (f, nexp_to_dexp e)) (upds s))"

text \<open>The draft action list (both snaps of every action), the draft initial valuation, and the
  inferred box: the inference run over the declared fluents with its own threshold set.\<close>
definition draft_acts :: "'n gaction list" where
  "draft_acts = concat (map (\<lambda>a. snap_gaction (at_start a) # [snap_gaction (at_end a)]) actions)"

definition draft_init :: "'n dval" where
  "draft_init = (\<lambda>f. const_to_int (num_init f))"

definition inferred_box :: "('n \<Rightarrow> int \<times> int) option" where
  "inferred_box =
     infer_fluent_bounds_on nfluents (thr_set nfluents draft_init draft_acts) draft_acts draft_init"

text \<open>The draft valuation of a partial field valuation: the integer encoding on the declared fluents,
  the draft initial value elsewhere (so undeclared fluents stay inside every inferred environment).\<close>
definition dval_of :: "('n \<rightharpoonup> 'r) \<Rightarrow> 'n dval" where
  "dval_of w = (\<lambda>f. if f \<in> set nfluents then const_to_int (the (w f)) else draft_init f)"

end


context numeric_tp_nta_reduction
begin

subsection \<open>The integer encoding on integers: strict order and injectivity, exact division\<close>

lemma const_to_int_less:
  assumes "x \<in> \<int>" and "y \<in> \<int>" and "x < y"
  shows "const_to_int x < const_to_int y"
proof -
  have "of_int (const_to_int x) < (of_int (const_to_int y) :: 'r)"
    using assms by (simp add: const_to_int_round_trip)
  thus ?thesis by simp
qed

lemma const_to_int_inj:
  assumes "x \<in> \<int>" and "y \<in> \<int>" and "const_to_int x = const_to_int y"
  shows "x = y"
proof -
  have "x = of_int (const_to_int x)" using assms(1) by (simp add: const_to_int_round_trip)
  also have "\<dots> = of_int (const_to_int y)" using assms(3) by simp
  also have "\<dots> = y" using assms(2) by (rule const_to_int_round_trip)
  finally show ?thesis .
qed

lemma const_to_int_div_exact:
  assumes "a \<in> \<int>" and "b \<in> \<int>" and "b \<noteq> 0" and "const_to_int b dvd const_to_int a"
  shows "const_to_int (a / b) = const_to_int a div const_to_int b"
proof -
  obtain ma where a: "a = Int.of_int ma" using assms(1) by (auto elim: Ints_cases)
  obtain mb where b: "b = Int.of_int mb" using assms(2) by (auto elim: Ints_cases)
  have mb0: "mb \<noteq> 0" using assms(3) b by auto
  have "mb dvd ma" using assms(4) a b const_to_int_of_int by simp
  then obtain q where q: "ma = mb * q" by blast
  hence "a / b = Int.of_int q" using a b mb0 by simp
  hence ab: "const_to_int (a / b) = q" by (simp add: const_to_int_of_int)
  have ca: "const_to_int a = mb * q" using a q by (simp only: const_to_int_of_int)
  have cb: "const_to_int b = mb" using b by (simp only: const_to_int_of_int)
  show ?thesis using ab ca cb mb0 by simp
qed

subsection \<open>Faithfulness of the translation on the @{const nexp_ok} fragment\<close>

lemma deval_nexp_to_dexp:
  assumes "nexp_ok w e" and "eval_nexp w e = Some r"
  shows "deval (dval_of w) (nexp_to_dexp e) = const_to_int r"
  using assms
proof (induction e arbitrary: r)
  case (NConst c)
  thus ?case by simp
next
  case (NVar f)
  thus ?case by (simp add: dval_of_def)
next
  case (NAdd a b)
  obtain ra where ra: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    using nexp_ok_eval_bnd NAdd.prems(1) by auto
  obtain rb where rb: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    using nexp_ok_eval_bnd NAdd.prems(1) by auto
  have r: "r = ra + rb" using NAdd.prems(2) ra(1) rb(1) by simp
  have da: "deval (dval_of w) (nexp_to_dexp a) = const_to_int ra"
    using NAdd.IH(1) NAdd.prems(1) ra(1) by simp
  have db: "deval (dval_of w) (nexp_to_dexp b) = const_to_int rb"
    using NAdd.IH(2) NAdd.prems(1) rb(1) by simp
  show ?case using da db ra(2) rb(2) r by (simp add: const_to_int_add)
next
  case (NSub a b)
  obtain ra where ra: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    using nexp_ok_eval_bnd NSub.prems(1) by auto
  obtain rb where rb: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    using nexp_ok_eval_bnd NSub.prems(1) by auto
  have r: "r = ra - rb" using NSub.prems(2) ra(1) rb(1) by simp
  have da: "deval (dval_of w) (nexp_to_dexp a) = const_to_int ra"
    using NSub.IH(1) NSub.prems(1) ra(1) by simp
  have db: "deval (dval_of w) (nexp_to_dexp b) = const_to_int rb"
    using NSub.IH(2) NSub.prems(1) rb(1) by simp
  show ?case using da db ra(2) rb(2) r by (simp add: const_to_int_diff)
next
  case (NMul a b)
  obtain ra where ra: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    using nexp_ok_eval_bnd NMul.prems(1) by auto
  obtain rb where rb: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    using nexp_ok_eval_bnd NMul.prems(1) by auto
  have r: "r = ra * rb" using NMul.prems(2) ra(1) rb(1) by simp
  have da: "deval (dval_of w) (nexp_to_dexp a) = const_to_int ra"
    using NMul.IH(1) NMul.prems(1) ra(1) by simp
  have db: "deval (dval_of w) (nexp_to_dexp b) = const_to_int rb"
    using NMul.IH(2) NMul.prems(1) rb(1) by simp
  show ?case using da db ra(2) rb(2) r by (simp add: const_to_int_mult)
next
  case (NDiv a b)
  obtain ra where ra: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    using nexp_ok_eval_bnd NDiv.prems(1) by auto
  obtain rb where rb: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    using nexp_ok_eval_bnd NDiv.prems(1) by auto
  have nz: "rb \<noteq> 0" and dvd: "const_to_int rb dvd const_to_int ra"
    using NDiv.prems(1) ra(1) rb(1) by auto
  have r: "r = ra / rb" using NDiv.prems(2) ra(1) rb(1) nz by simp
  have da: "deval (dval_of w) (nexp_to_dexp a) = const_to_int ra"
    using NDiv.IH(1) NDiv.prems(1) ra(1) by simp
  have db: "deval (dval_of w) (nexp_to_dexp b) = const_to_int rb"
    using NDiv.IH(2) NDiv.prems(1) rb(1) by simp
  show ?case using da db r const_to_int_div_exact[OF ra(2) rb(2) nz dvd] by simp
qed

lemma sat_comp_to_gcomp:
  assumes "comp_ok w c" and "sat_comp w c"
  shows "sat_gcomp (dval_of w) (comp_to_gcomp c)"
proof (cases c)
  case (Comp p a b)
  have oka: "nexp_ok w a" and okb: "nexp_ok w b" using assms(1) Comp by simp_all
  obtain ra where ra: "eval_nexp w a = Some ra" "ra \<in> \<int>" using nexp_ok_eval_bnd[OF oka] by blast
  obtain rb where rb: "eval_nexp w b = Some rb" "rb \<in> \<int>" using nexp_ok_eval_bnd[OF okb] by blast
  have rel: "cmp_op_rel p ra rb" using assms(2) Comp ra(1) rb(1) by simp
  have da: "deval (dval_of w) (nexp_to_dexp a) = const_to_int ra"
    by (rule deval_nexp_to_dexp[OF oka ra(1)])
  have db: "deval (dval_of w) (nexp_to_dexp b) = const_to_int rb"
    by (rule deval_nexp_to_dexp[OF okb rb(1)])
  have "cmp_sem (cmp_op_to_cmpop p) (const_to_int ra) (const_to_int rb)"
  proof (cases p)
    case Ceq
    thus ?thesis using rel by simp
  next
    case Cle
    thus ?thesis using rel const_to_int_mono[OF ra(2) rb(2)] by simp
  next
    case Cge
    thus ?thesis using rel const_to_int_mono[OF rb(2) ra(2)] by simp
  next
    case Clt
    thus ?thesis using rel const_to_int_less[OF ra(2) rb(2)] by simp
  next
    case Cgt
    thus ?thesis using rel const_to_int_less[OF rb(2) ra(2)] by simp
  qed
  thus ?thesis using Comp da db by simp
qed

subsection \<open>The draft action list: shape facts\<close>

lemma snap_gaction_writes: "fst ` set (snd (snap_gaction s)) = fst ` set (upds s)"
  unfolding snap_gaction_def by (force simp: image_iff)

lemma upds_writes_nfluents:
  assumes "s \<in> all_snaps" and "(f, e) \<in> set (upds s)"
  shows "f \<in> set nfluents"
  using assms snap_writes_nfluents_start snap_writes_nfluents_end
  unfolding all_snaps_def by force

lemma draft_acts_elem:
  assumes "ga \<in> set draft_acts"
  obtains s where "s \<in> all_snaps" and "ga = snap_gaction s"
  using assms unfolding draft_acts_def all_snaps_def by auto

lemma snap_gaction_in_draft_acts:
  assumes "s \<in> all_snaps"
  shows "snap_gaction s \<in> set draft_acts"
  using assms unfolding all_snaps_def draft_acts_def by auto

lemma targets_draft_acts: "targets draft_acts \<subseteq> set nfluents"
proof
  fix f assume "f \<in> targets draft_acts"
  then obtain ga where ga: "ga \<in> set draft_acts" and f: "f \<in> fst ` set (snd ga)"
    unfolding targets_def by force
  obtain s where
      s: "s \<in> all_snaps"
    and gs: "ga = snap_gaction s"
    using draft_acts_elem[OF ga] .
  have "f \<in> fst ` set (upds s)" using f gs snap_gaction_writes by simp
  thus "f \<in> set nfluents" using upds_writes_nfluents[OF s] by fastforce
qed

lemma upds_functional_all_snaps:
  assumes "s \<in> all_snaps"
  shows "distinct (map fst (upds s))"
  using assms upds_functional_start upds_functional_end
  unfolding all_snaps_def upds_functional_list_def by auto

lemma map_of_snap_gaction:
  assumes "s \<in> all_snaps" and "(f, e) \<in> set (upds s)"
  shows "map_of (snd (snap_gaction s)) f = Some (nexp_to_dexp e)"
proof -
  have "map_of (upds s) f = Some e"
    using map_of_is_SomeI[OF upds_functional_all_snaps[OF assms(1)] assms(2)] .
  thus ?thesis by (simp add: snap_gaction_def map_of_map)
qed

subsection \<open>In-bounds valuations inhabit the inferred environment\<close>

lemma dval_of_in_gamma:
  assumes "fluent_in_bounds w"
      and "init_env draft_init \<le> E"
      and "\<And>f. f \<in> set nfluents \<Longrightarrow> \<gamma>_ivl (E f) = {fluent_lo f..fluent_hi f}"
  shows "dval_of w \<in> \<gamma>_env E"
proof -
  have "dval_of w f \<in> \<gamma>_ivl (E f)" for f
  proof (cases "f \<in> set nfluents")
    case True
    obtain r where
        r: "w f = Some r"
      and rlo: "fluent_lo f \<le> const_to_int r"
      and rhi: "const_to_int r \<le> fluent_hi f"
      using assms(1) True unfolding fluent_in_bounds_def by blast
    have "dval_of w f = const_to_int r" using True r by (simp add: dval_of_def)
    thus ?thesis using assms(3)[OF True] rlo rhi by simp
  next
    case False
    have eq: "dval_of w f = draft_init f" using False by (simp add: dval_of_def)
    have mem: "draft_init f \<in> \<gamma>_ivl (init_env draft_init f)" by (simp add: init_env_def gamma_num')
    have sub: "\<gamma>_ivl (init_env draft_init f) \<subseteq> \<gamma>_ivl (E f)"
      using le_funD[OF assms(2), of f] by (simp add: le_ivl_iff_subset)
    show ?thesis using subsetD[OF sub mem] by (simp add: eq)
  qed
  thus ?thesis by (simp add: \<gamma>_fun_def)
qed

subsection \<open>Transfer lemmas for the main theorem\<close>

text \<open>The grounder-match contract, lifted from the per-action @{text at_start}/@{text at_end} form of the
  locale assumptions to a member of @{const all_snaps}.\<close>
lemma all_snaps_upds_nexp_ok:
  assumes "s \<in> all_snaps" and "num_val_ok w" and "(f, e) \<in> set (upds s)"
  shows "nexp_ok w e"
  using assms snap_upds_nexp_ok_start snap_upds_nexp_ok_end
  unfolding all_snaps_def by fastforce

lemma all_snaps_pre_comp_ok:
  assumes "s \<in> all_snaps" and "num_val_ok w" and "c \<in> set (n_pre s)"
  shows "comp_ok w c"
  using assms snap_pre_comp_ok_start snap_pre_comp_ok_end
  unfolding all_snaps_def by fastforce

text \<open>Guard transfer: a snap's numeric guard, satisfied by an integer-ok valuation, is satisfied by
  its draft translation (@{thm [source] sat_comp_to_gcomp}, comparison by comparison).\<close>
lemma sat_guard_snap_gaction:
  assumes "s \<in> all_snaps" and "num_val_ok w" and "sat_comps w (set (n_pre s))"
  shows "sat_guard (dval_of w) (fst (snap_gaction s))"
proof -
  have "sat_gcomp (dval_of w) (comp_to_gcomp c)" if "c \<in> set (n_pre s)" for c
    using sat_comp_to_gcomp[OF all_snaps_pre_comp_ok[OF assms(1,2) that] sat_compsD[OF assms(3) that]] .
  thus ?thesis unfolding sat_guard_def snap_gaction_def by simp
qed

text \<open>Update transfer: the draft action's update of @{term f} is the integer encoding of the concrete
  update result (@{thm [source] map_of_snap_gaction} + @{thm [source] deval_nexp_to_dexp}).\<close>
lemma dapply_upds_snap_gaction:
  assumes "s \<in> all_snaps" and "(f, e) \<in> set (upds s)"
      and "nexp_ok w e" and "eval_nexp w e = Some r"
  shows "dapply_upds (snd (snap_gaction s)) (dval_of w) f = const_to_int r"
  using map_of_snap_gaction[OF assms(1,2)] deval_nexp_to_dexp[OF assms(3,4)]
  by (simp add: dapply_upds_def)

text \<open>Two generic facts about the inference's environments: a value of the initial valuation lies in
  every environment above @{const init_env}, and a guarded step from inside a guarded post-fixpoint stays
  inside it.\<close>
lemma init_env_le_gammaD:
  assumes "init_env v0 \<le> E"
  shows "v0 f \<in> \<gamma>_ivl (E f)"
proof -
  have "v0 f \<in> \<gamma>_ivl (init_env v0 f)" by (simp add: init_env_def gamma_num')
  thus ?thesis using le_funD[OF assms, of f] by (simp add: le_ivl_iff_subset subset_iff)
qed

lemma gbound_inv_stepD:
  assumes "is_gbound_inv v0 acts E" and "ga \<in> set acts"
      and "v \<in> \<gamma>_env E" and "sat_guard v (fst ga)"
  shows "dapply_upds (snd ga) v \<in> \<gamma>_env E"
proof -
  have "gastep_upds ga E \<le> E"
    using order_trans[OF gastep_ge_action[OF assms(2)]] assms(1) unfolding is_gbound_inv_def by blast
  thus ?thesis using gastep_upds_sound[OF assms(3,4)] mono_gamma_env by blast
qed

subsection \<open>Main: an inferred box matching the declared bounds discharges the certificate\<close>

text \<open>Via @{thm [source] num_bound_invI}: the init clause is @{text \<open>init_env draft_init \<le> E\<close>} read at
  @{term f} (@{thm [source] init_env_le_gammaD}); the step clause moves the in-bounds valuation @{term w}
  into the draft world (@{thm [source] dval_of_in_gamma}), where the snap's guard holds by faithfulness of
  the translation (@{thm [source] sat_guard_snap_gaction}), so the guarded abstract step stays inside the
  post-fixpoint @{term E} (@{thm [source] gbound_inv_stepD}), and the draft update of @{term f} is exactly
  @{text \<open>const_to_int r\<close>} of the concrete result (@{thm [source] dapply_upds_snap_gaction}).\<close>
theorem inferred_box_imp_num_bound_inv:
  assumes box: "inferred_box = Some b"
      and lo: "\<And>f. f \<in> set nfluents \<Longrightarrow> fluent_lo f = fst (b f)"
      and hi: "\<And>f. f \<in> set nfluents \<Longrightarrow> fluent_hi f = snd (b f)"
  shows "num_bound_inv"
proof -
  obtain E where
      inv: "is_gbound_inv draft_init draft_acts E"
    and ge: "init_env draft_init \<le> E"
    and gam0: "\<And>f. f \<in> set nfluents \<Longrightarrow> \<gamma>_ivl (E f) = {fst (b f)..snd (b f)}"
    using infer_fluent_bounds_on_inv[OF targets_draft_acts box[unfolded inferred_box_def]] by blast
  have gam: "\<gamma>_ivl (E f) = {fluent_lo f..fluent_hi f}" if "f \<in> set nfluents" for f
    using gam0[OF that] lo[OF that] hi[OF that] by simp
  show ?thesis
  proof (rule num_bound_invI)
    \<comment> \<open>INIT: the draft initial valuation sits in @{term E}, and @{term E} is the declared box.\<close>
    fix f assume f: "f \<in> set nfluents"
    show "fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f"
      using init_env_le_gammaD[OF ge, of f] gam[OF f] by (simp add: draft_init_def)
  next
    \<comment> \<open>STEP: on any in-bounds valuation satisfying the snap guard, the update RHS lands in bounds.\<close>
    fix s f e w
    assume sAll: "s \<in> all_snaps"
       and fe: "(f, e) \<in> set (upds s)"
       and wfib: "fluent_in_bounds w"
       and wpre: "sat_comps w (set (n_pre s))"
    have wok: "num_val_ok w" using wfib by (rule fluent_in_bounds_imp_num_val_ok)
    have okE: "nexp_ok w e" using all_snaps_upds_nexp_ok[OF sAll wok fe] .
    obtain r where
        r: "eval_nexp w e = Some r"
      and rI: "r \<in> \<int>"
      using nexp_ok_eval_bnd[OF okE] by blast
    have "dapply_upds (snd (snap_gaction s)) (dval_of w) \<in> \<gamma>_env E"
      using gbound_inv_stepD[OF inv snap_gaction_in_draft_acts[OF sAll]
              dval_of_in_gamma[OF wfib ge gam] sat_guard_snap_gaction[OF sAll wok wpre]] .
    hence "dapply_upds (snd (snap_gaction s)) (dval_of w) f \<in> \<gamma>_ivl (E f)" by (simp add: \<gamma>_fun_def)
    hence "const_to_int r \<in> \<gamma>_ivl (E f)" using dapply_upds_snap_gaction[OF sAll fe okE r] by simp
    hence "fluent_lo f \<le> const_to_int r" and "const_to_int r \<le> fluent_hi f"
      using gam[OF upds_writes_nfluents[OF sAll fe]] by simp_all
    thus "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
             \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
      using r rI by blast
  qed
qed

end

end

theory TP_NTA_Reduction_Numeric_Bounds
  imports
    TP_NTA_Reduction_Correctness_Numeric
begin

text \<open>WP-E: discharge @{text num_seq_in_bounds} from a static bound certificate over the reduction's
  numeric semantics. NB @{text \<open>HOL-IMP.Abs_Int3\<close>} CANNOT be imported here: its @{text Abs_Int0}
  lattice makes @{text \<open>_ option\<close>} a @{text semilattice_sup_top} under a sort premise that CONFLICTS
  with the Munta/FPS tower's @{text \<open>_ option\<close>} arity (arity clash on @{text option}). So the interval
  domain is provided self-contained here (no HOL-IMP dependency).\<close>

context numeric_tp_nta_reduction
begin

text \<open>The \<^emph>\<open>relaxed\<close> snap set: every start/end snap of every action, stripped of its propositional
  pre/effects (only the numeric guard @{term n_pre} and numeric updates @{term upds} matter for the
  fluent trajectory). The actual happening at each step is a subset of the applicable members.\<close>
definition all_snaps :: "'snap_action set" where
  "all_snaps = at_start ` set actions \<union> at_end ` set actions"

text \<open>The static bound certificate (the reduction-native, finite-@{typ int} form of the interval
  post-fixpoint @{text is_gbound_inv}): for every relaxed snap and every update @{term \<open>(f, e)\<close>} it
  carries, on any in-bounds integer valuation @{term w} that satisfies the snap's numeric guard, the
  update RHS evaluates to an integer landing inside @{term f}'s declared bounds
  @{term \<open>[fluent_lo f, fluent_hi f]\<close>}. This is exactly the condition an interval analysis discharges;
  here it is the checkable hypothesis from which @{text num_seq_in_bounds} follows.\<close>
definition num_bound_inv :: bool where
  "num_bound_inv \<longleftrightarrow>
     \<comment> \<open>init in the box (the @{text \<open>v0 \<in> \<gamma>_env E\<close>} half): the initial valuation lands in bounds\<close>
     (\<forall>f \<in> set nfluents.
        fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f)
     \<comment> \<open>step preserves the box (the @{text \<open>gastep E \<le> E\<close>} half)\<close>
   \<and> (\<forall>s \<in> all_snaps. \<forall>(f, e) \<in> set (upds s).
        \<forall>w. fluent_in_bounds w \<longrightarrow> sat_comps w (set (n_pre s))
            \<longrightarrow> (\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
                    \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f))"


text \<open>Intro/dest rules for the bundled certificate, so consumers avoid @{text \<open>unfolding num_bound_inv_def\<close>}
  + @{text blast}: @{text num_bound_inv_initD} reaches the init-box facts, @{text num_bound_inv_stepD} the
  per-update landing witness, @{text num_bound_invI} builds the certificate from the two element-level goals
  (the interval layer discharges those).\<close>

lemma num_bound_inv_initD:
  assumes "num_bound_inv" and "f \<in> set nfluents"
  shows "fluent_lo f \<le> const_to_int (num_init f)"
    and "const_to_int (num_init f) \<le> fluent_hi f"
  using assms unfolding num_bound_inv_def by blast+

lemma num_bound_inv_stepD:
  assumes "num_bound_inv"
      and "s \<in> all_snaps" and "(f, e) \<in> set (upds s)"
      and "fluent_in_bounds w" and "sat_comps w (set (n_pre s))"
  obtains r where "eval_nexp w e = Some r" and "r \<in> \<int>"
    and "fluent_lo f \<le> const_to_int r" and "const_to_int r \<le> fluent_hi f"
  using assms unfolding num_bound_inv_def by blast

lemma num_bound_invI:
  assumes "\<And>f. f \<in> set nfluents
             \<Longrightarrow> fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f"
      and "\<And>s f e w. s \<in> all_snaps \<Longrightarrow> (f, e) \<in> set (upds s)
             \<Longrightarrow> fluent_in_bounds w \<Longrightarrow> sat_comps w (set (n_pre s))
             \<Longrightarrow> (\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
                     \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f)"
    shows "num_bound_inv"
  unfolding num_bound_inv_def using assms by blast
end


text \<open>The discharge locale: identical to @{locale numeric_tp_nta_reduction_correctness} but assuming
  the \<^emph>\<open>checkable\<close> certificate @{text num_bound_inv} in place of the reachability invariant
  @{text num_seq_in_bounds}. We prove @{text num_seq_in_bounds} here (the bridge), then re-obtain
  @{locale numeric_tp_nta_reduction_correctness} as a sublocale -- so every downstream numeric-net
  fact holds from the certificate, and WP-A's ground leaf discharges @{text num_bound_inv} instead.\<close>
locale numeric_tp_nta_reduction_bounds =
  tp_nta_reduction_correctness
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name +
  numeric_tp_nta_reduction
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
    n_pre n_inv upds num_init num_goal nfluents fluent_to_name fluent_lo fluent_hi const_to_int +
  num_plan: numeric_temp_plan_for_problem_list_impl_int
    at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>
    "set o n_pre" "set o n_inv" "set o upds"
    "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and \<pi> :: "('i, 'action, int) temp_plan"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
    and n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_name :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int" +
  assumes num_valid: "num_plan.num_rat_impl.num_valid_plan"
      \<comment> \<open>(@{text const_to_int_of_int} is now inherited from the base @{locale numeric_tp_nta_reduction}.)\<close>
      and bound_inv: "num_bound_inv"
      and num_goal_comp_ok: "\<And>w. num_val_ok w \<Longrightarrow> (\<forall>c \<in> set num_goal. comp_ok w c)"
begin

text \<open>S-property re-exports in the \<open>bounds\<close> locale (the same facts @{locale
  numeric_tp_nta_reduction_correctness} derives in @{theory TP_NTA_Reduction.TP_NTA_Reduction_Numeric_Edges},
  but proved here where only @{thm [source] num_valid} and the static well-formedness assumptions are in
  scope -- they do NOT depend on the reachability invariant, so they hold from the certificate side too).\<close>

lemma happ_at_index_decomp_bnd:
  "planning_sem.happ_at planning_sem.plan_happ_seq t
     = at_start ` { actions ! j | j. j < length actions \<and> (is_starting_index t j \<or> is_instant_index t j) }
       \<union> at_end ` { actions ! j | j. j < length actions \<and> (is_ending_index t j \<or> is_instant_index t j) }"
proof -
  have start_set: "planning_sem.instant_actions_at t \<union> planning_sem.starting_actions_at t
                     = { actions ! j | j. j < length actions \<and> (is_starting_index t j \<or> is_instant_index t j) }"
    unfolding planning_sem.instant_actions_at_def planning_sem.starting_actions_at_def
              is_starting_index_def is_instant_index_def
    by (simp only: set_conv_nth) blast
  have end_set: "planning_sem.instant_actions_at t \<union> planning_sem.ending_actions_at t
                   = { actions ! j | j. j < length actions \<and> (is_ending_index t j \<or> is_instant_index t j) }"
    unfolding planning_sem.instant_actions_at_def planning_sem.ending_actions_at_def
              is_ending_index_def is_instant_index_def
    by (simp only: set_conv_nth) blast
  have "planning_sem.happ_at planning_sem.plan_happ_seq t
          = planning_sem.instant_snaps_at t \<union> planning_sem.ending_snaps_at t \<union> planning_sem.starting_snaps_at t"
    by (rule planning_sem.happ_at_is_union_of_starting_ending_instant)
  also have "\<dots> = at_start ` (planning_sem.instant_actions_at t \<union> planning_sem.starting_actions_at t)
                    \<union> at_end ` (planning_sem.instant_actions_at t \<union> planning_sem.ending_actions_at t)"
    unfolding planning_sem.instant_snaps_at_def planning_sem.ending_snaps_at_def planning_sem.starting_snaps_at_def
    by (auto simp: image_Un)
  finally show ?thesis
    by (simp only: start_set end_set)
qed

text \<open>Every snap of a happening is a start/end snap of a plan action, so it lands in @{const all_snaps}.\<close>
lemma happening_subseteq_all_snaps:
  "planning_sem.happ_at planning_sem.plan_happ_seq t \<subseteq> all_snaps"
proof
  fix s assume "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq t"
  hence "s \<in> at_start ` { actions ! j | j. j < length actions \<and> (is_starting_index t j \<or> is_instant_index t j) }
          \<union> at_end ` { actions ! j | j. j < length actions \<and> (is_ending_index t j \<or> is_instant_index t j) }"
    by (simp only: happ_at_index_decomp_bnd)
  then consider
      (starting) j where "j < length actions" and "s = at_start (actions ! j)"
    | (ending) j where "j < length actions" and "s = at_end (actions ! j)"
    by blast
  thus "s \<in> all_snaps"
  proof cases
    case starting
    thus ?thesis unfolding all_snaps_def by auto
  next
    case ending
    thus ?thesis unfolding all_snaps_def by auto
  qed
qed

lemma happening_finite_bnd:
  "finite (planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i))"
proof -
  have "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)
          = snd ` {p \<in> planning_sem.plan_happ_seq. fst p = planning_sem.time_index i}"
    by (force simp: image_iff)
  thus ?thesis by (simp add: planning_sem.finite_happ_seq)
qed

lemma upds_functional_set_bnd:
  assumes "distinct (map fst us)"
  shows "upds_functional (set us)"
proof -
  have "e = e'" if "(f, e) \<in> set us" and "(f, e') \<in> set us" for f e e'
    using that assms by (metis map_of_is_SomeI option.inject)
  thus ?thesis unfolding upds_functional_def by auto
qed

lemma happening_upds_functional_bnd:
  assumes "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  shows "upds_functional ((set \<circ> upds) s)"
proof -
  have "s \<in> at_start ` { actions ! j | j. j < length actions
                            \<and> (is_starting_index (planning_sem.time_index i) j
                               \<or> is_instant_index (planning_sem.time_index i) j) }
          \<union> at_end ` { actions ! j | j. j < length actions
                          \<and> (is_ending_index (planning_sem.time_index i) j
                             \<or> is_instant_index (planning_sem.time_index i) j) }"
    using assms by (simp only: happ_at_index_decomp_bnd)
  then consider
      (starting) j where "j < length actions" and "s = at_start (actions ! j)"
    | (ending) j where "j < length actions" and "s = at_end (actions ! j)"
    by blast
  thus ?thesis
  proof cases
    case starting
    hence "actions ! j \<in> set actions" by simp
    hence "upds_functional_list (upds (at_start (actions ! j)))"
      using upds_functional_start by blast
    thus ?thesis
      using starting by (simp add: upds_functional_set_bnd upds_functional_list_def)
  next
    case ending
    hence "actions ! j \<in> set actions" by simp
    hence "upds_functional_list (upds (at_end (actions ! j)))"
      using upds_functional_end by blast
    thus ?thesis
      using ending by (simp add: upds_functional_set_bnd upds_functional_list_def)
  qed
qed

lemma num_mutex_valid_plan_bnd: "num_plan.num_rat_impl.num_mutex_valid_plan"
  using num_valid unfolding num_plan.num_rat_impl.num_valid_plan_def by blast

lemma happening_num_noninterfere_bnd:
  assumes "s1 \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and "s2 \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and "s1 \<noteq> s2"
    shows "\<not> num_plan.num_rat_impl.num_mutex_snap_action s1 s2"
proof -
  have h1: "(planning_sem.time_index i, s1) \<in> planning_sem.plan_happ_seq"
    using assms(1) by (rule planning_sem.in_happ_atD)
  have h2: "(planning_sem.time_index i, s2) \<in> planning_sem.plan_happ_seq"
    using assms(2) by (rule planning_sem.in_happ_atD)
  obtain a ta da where
    A: "(a, ta, da) \<in> ran \<pi>_sem"
    and as1: "at_start a = s1 \<and> planning_sem.time_index i = ta
                \<or> at_end a = s1 \<and> planning_sem.time_index i = ta + da"
    using planning_sem.in_happ_seq_exD[OF h1] by blast
  obtain b tb db where
    B: "(b, tb, db) \<in> ran \<pi>_sem"
    and bs2: "at_start b = s2 \<and> planning_sem.time_index i = tb
                \<or> at_end b = s2 \<and> planning_sem.time_index i = tb + db"
    using planning_sem.in_happ_seq_exD[OF h2] by blast
  obtain k where k: "\<pi>_sem k = Some (a, ta, da)" using A unfolding ran_def by blast
  obtain l where l: "\<pi>_sem l = Some (b, tb, db)" using B unfolding ran_def by blast
  have kdom: "k \<in> dom \<pi>_sem" using k by blast
  have ldom: "l \<in> dom \<pi>_sem" using l by blast
  note nmvp = num_mutex_valid_plan_bnd[unfolded num_plan.num_rat_impl.num_mutex_valid_plan_def, folded \<pi>_sem_def]
  have distinct_clause: "\<not> num_plan.num_rat_impl.num_mutex_snap_action sa sb"
    if "k' \<in> dom \<pi>_sem" and "l' \<in> dom \<pi>_sem" and "k' \<noteq> l'"
       and "\<pi>_sem k' = Some (a', ta', da')" and "\<pi>_sem l' = Some (b', tb', db')"
       and "sa = at_start a' \<and> tt = ta' \<or> sa = at_end a' \<and> tt = ta' + da'"
       and "sb = at_start b' \<and> u = tb' \<or> sb = at_end b' \<and> u = tb' + db'"
       and "tt - u < rat_of_int \<epsilon> \<and> u - tt < rat_of_int \<epsilon> \<or> tt = u"
     for k' l' a' ta' da' b' tb' db' sa sb tt u
    using nmvp that by blast
  have instant_clause: "\<not> num_plan.num_rat_impl.num_mutex_snap_action (at_start a') (at_end a')"
    if "(a', tt, d') \<in> ran \<pi>_sem" and "d' = 0 \<or> d' < rat_of_int \<epsilon>"
    for a' tt d'
    using nmvp that by blast
  consider (diff) "k \<noteq> l" | (same) "k = l" by blast
  thus ?thesis
  proof cases
    case diff
    show ?thesis
      by (rule distinct_clause[OF kdom ldom diff k l _ _ _])
         (use as1 bs2 in blast)+
  next
    case same
    hence eq: "a = b" "ta = tb" "da = db" using k l by auto
    have s12: "s1 = at_start a \<and> s2 = at_end a \<or> s1 = at_end a \<and> s2 = at_start a"
      using as1 bs2 assms(3) eq by auto
    have da0: "da = 0" using as1 bs2 assms(3) eq by auto
    have ni: "\<not> num_plan.num_rat_impl.num_mutex_snap_action (at_start a) (at_end a)"
      by (rule instant_clause[OF A]) (simp add: da0)
    thus ?thesis
      using s12 by (metis num_plan.num_rat_impl.num_mutex_snap_action_refl)
  qed
qed

text \<open>Guard persistence under a non-interfering write: if snap @{term a}'s writes are disjoint from
  snap @{term s}'s reads, then applying @{term a}'s numeric update leaves every comparison in @{term
  \<open>n_pre s\<close>} unchanged (each comparison reads only @{term s}-read fluents, none of which @{term a}
  touches).\<close>
lemma sat_comp_unchanged_by_write:
  assumes "num_plan.num_rat_impl.snap_writes a \<inter> num_plan.num_rat_impl.snap_reads s = {}"
      and "c \<in> set (n_pre s)"
    shows "sat_comp (num_plan.num_rat_impl.snap_num_update a w) c = sat_comp w c"
proof -
  obtain p e1 e2 where c: "c = Comp p e1 e2" by (cases c)
  have creads: "comp_fluents c \<subseteq> num_plan.num_rat_impl.snap_reads s"
    using assms(2) unfolding num_plan.num_rat_impl.snap_reads_def by (auto simp: o_def)
  have agree: "num_plan.num_rat_impl.snap_num_update a w g = w g" if "g \<in> comp_fluents c" for g
  proof -
    have "g \<in> num_plan.num_rat_impl.snap_reads s" using creads that by blast
    hence "g \<notin> num_plan.num_rat_impl.snap_writes a" using assms(1) by blast
    thus ?thesis by (rule num_plan.num_rat_impl.snap_num_update_unwritten)
  qed
  have e1: "eval_nexp (num_plan.num_rat_impl.snap_num_update a w) e1 = eval_nexp w e1"
    by (rule eval_nexp_cong) (use agree c in auto)
  have e2: "eval_nexp (num_plan.num_rat_impl.snap_num_update a w) e2 = eval_nexp w e2"
    by (rule eval_nexp_cong) (use agree c in auto)
  show ?thesis by (simp add: c e1 e2)
qed

text \<open>KERNEL: a single happening preserves in-bounds. Generalising the valuation @{term w} over the
  @{text finite_induct}, so the IH applies to the running (partially updated) valuation.\<close>
lemma happening_preserves_fib:
  assumes "num_bound_inv"
      and "finite S" and "S \<subseteq> all_snaps"
      and "\<forall>s\<in>S. upds_functional (set (upds s))"
      and "\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      and "fluent_in_bounds w"
      and "\<forall>s\<in>S. sat_comps w (set (n_pre s))"
    shows "fluent_in_bounds (num_plan.num_rat_impl.happening_num_update_set S w)"
  using assms(2-)
proof (induction S arbitrary: w rule: finite_induct)
  case empty
  have eqw: "num_plan.num_rat_impl.happening_num_update_set {} w = w"
    by (rule num_plan.num_rat_impl.happening_num_update_set_empty)
  show ?case unfolding eqw using empty.prems(4) by simp
next
  case (insert a F)
  \<comment> \<open>insert.prems: (1) insert a F \<subseteq> all_snaps, (2) functional, (3) non-interference,
     (4) fluent_in_bounds w, (5) guards.\<close>
  have aS: "a \<in> insert a F" by simp
  have funins: "\<And>x. x \<in> insert a F \<Longrightarrow> upds_functional ((set \<circ> upds) x)"
    using insert.prems(2) by (auto simp: o_def)
  have nmins: "\<And>x y. x \<in> insert a F \<Longrightarrow> y \<in> insert a F \<Longrightarrow> x \<noteq> y
                 \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
    using insert.prems(3) by blast
  have peel: "num_plan.num_rat_impl.happening_num_update_set (insert a F) w
                = num_plan.num_rat_impl.happening_num_update_set F (num_plan.num_rat_impl.snap_num_update a w)"
    by (rule num_plan.num_rat_impl.happening_num_update_set_insert[OF insert.hyps(1,2) funins nmins])
  let ?w' = "num_plan.num_rat_impl.snap_num_update a w"
  \<comment> \<open>(i) the running valuation stays in bounds\<close>
  have aAll: "a \<in> all_snaps" using insert.prems(1) by blast
  have aGuard: "sat_comps w (set (n_pre a))" using insert.prems(5) by blast
  have aFun: "upds_functional (set (upds a))" using funins[OF aS] by (simp add: o_def)
  have wFib: "fluent_in_bounds w" using insert.prems(4) .
  \<comment> \<open>the STEP clause of the certificate, specialised to snap @{term a} and valuation @{term w}\<close>
  have step: "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
                  \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
    if "(f, e) \<in> set (upds a)" for f e
  proof -
    have "\<forall>s \<in> all_snaps. \<forall>(f, e) \<in> set (upds s).
            \<forall>w. fluent_in_bounds w \<longrightarrow> sat_comps w (set (n_pre s))
                \<longrightarrow> (\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
                        \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f)"
      using assms(1) unfolding num_bound_inv_def by blast
    thus ?thesis using aAll that wFib aGuard by blast
  qed
  have fib': "fluent_in_bounds ?w'"
    unfolding fluent_in_bounds_def
  proof (intro ballI)
    fix f assume fN: "f \<in> set nfluents"
    show "\<exists>r. ?w' f = Some r \<and> r \<in> \<int> \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
    proof (cases "f \<in> fst ` set (upds a)")
      case True
      then obtain e where e: "(f, e) \<in> set (upds a)" by auto
      have "(f, e) \<in> (set \<circ> upds) a" using e by (simp add: o_def)
      hence wf: "?w' f = eval_nexp w e"
        by (rule num_plan.num_rat_impl.snap_num_update_writes[OF funins[OF aS]])
      obtain r where r: "eval_nexp w e = Some r" "r \<in> \<int>"
        "fluent_lo f \<le> const_to_int r" "const_to_int r \<le> fluent_hi f"
        using step[OF e] by blast
      show ?thesis using wf r by auto
    next
      case False
      hence "f \<notin> num_plan.num_rat_impl.snap_writes a"
        unfolding num_plan.num_rat_impl.snap_writes_def by (simp add: o_def)
      hence wf: "?w' f = w f"
        by (rule num_plan.num_rat_impl.snap_num_update_unwritten)
      show ?thesis using wf wFib fN unfolding fluent_in_bounds_def by auto
    qed
  qed
  \<comment> \<open>(ii) each remaining snap's guard persists\<close>
  have gpers: "sat_comps ?w' (set (n_pre s))" if sF: "s \<in> F" for s
  proof -
    have "a \<noteq> s" using insert.hyps(2) sF by blast
    hence "\<not> num_plan.num_rat_impl.num_mutex_snap_action a s"
      using nmins[of a s] sF by simp
    hence disj: "num_plan.num_rat_impl.snap_writes a \<inter> num_plan.num_rat_impl.snap_reads s = {}"
      unfolding num_plan.num_rat_impl.num_mutex_snap_action_def by blast
    have "sat_comps w (set (n_pre s))" using insert.prems(5) sF by blast
    thus ?thesis
      unfolding sat_comps_def
      using sat_comp_unchanged_by_write[OF disj] by simp
  qed
  \<comment> \<open>discharge the IH on the running valuation\<close>
  have "fluent_in_bounds (num_plan.num_rat_impl.happening_num_update_set F ?w')"
  proof (rule insert.IH)
    show "F \<subseteq> all_snaps" using insert.prems(1) by simp
    show "\<forall>s\<in>F. upds_functional (set (upds s))" using insert.prems(2) by simp
    show "\<forall>x\<in>F. \<forall>y\<in>F. x \<noteq> y \<longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      using nmins by auto
    show "fluent_in_bounds ?w'" by (rule fib')
    show "\<forall>s\<in>F. sat_comps ?w' (set (n_pre s))" using gpers by blast
  qed
  thus ?case unfolding peel .
qed

text \<open>Namespace bridges: the rat-refined @{text rat_impl} interpretation (which
  @{const num_plan.num_rat_impl.num_valid_state_sequence} unfolds into) and the propositional
  @{text planning_sem} interpretation are instantiated with the SAME plan @{const \<pi>_sem}, so all
  plan-derived constants coincide.\<close>
lemma rat_impl_plan_happ_seq_eq_bnd: "rat_impl.plan_happ_seq = planning_sem.plan_happ_seq"
  unfolding rat_impl.plan_happ_seq_def planning_sem.plan_happ_seq_def \<pi>_sem_def by simp

lemma rat_impl_htps_eq_bnd: "rat_impl.htps = planning_sem.htps"
  unfolding rat_impl.htps_def planning_sem.htps_def \<pi>_sem_def by simp

lemma rat_impl_htpl_eq_bnd: "rat_impl.htpl = planning_sem.htpl"
  by (simp add: rat_impl.htpl_def planning_sem.htpl_def rat_impl_htps_eq_bnd)

lemma rat_impl_time_index_eq_bnd: "rat_impl.time_index = planning_sem.time_index"
  by (simp add: rat_impl.time_index_def planning_sem.time_index_def rat_impl_htpl_eq_bnd)

lemma rat_impl_happ_at_eq_bnd:
  "planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)
     = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  by (simp add: rat_impl_plan_happ_seq_eq_bnd rat_impl_time_index_eq_bnd)

text \<open>The bridge: the certificate @{const num_bound_inv} implies the reachability invariant
  @{text num_seq_in_bounds} along every valid numeric state sequence (per-happening induction on
  @{term i}).\<close>
lemma num_seq_in_bounds_derived:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and "i \<le> length rat_impl.htpl"
    shows "fluent_in_bounds (snd (M i))"
  using \<open>i \<le> length rat_impl.htpl\<close>
proof (induction i)
  case 0
  \<comment> \<open>base: the initial valuation is @{term num_init} on the declared fluents (integer + in the box).\<close>
  have "\<exists>r. snd (M 0) f = Some r \<and> r \<in> \<int> \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
    if fN: "f \<in> set nfluents" for f
  proof -
    have val: "snd (M 0) f = Some (num_init f)" using m0 fN by simp
    have int: "num_init f \<in> \<int>" using num_init_val_ok fN by blast
    have "\<forall>f \<in> set nfluents.
            fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f"
      using bound_inv unfolding num_bound_inv_def by blast
    hence "fluent_lo f \<le> const_to_int (num_init f)" "const_to_int (num_init f) \<le> fluent_hi f"
      using fN by blast+
    thus ?thesis using val int by blast
  qed
  thus ?case unfolding fluent_in_bounds_def by blast
next
  case (Suc i)
  have i_lt': "i < length rat_impl.htpl" using Suc.prems by (rule Suc_le_lessD)
  have i_lt: "i < length planning_sem.htpl"
    using i_lt' unfolding rat_impl_htpl_eq_bnd .
  have IH: "fluent_in_bounds (snd (M i))" using Suc.IH Suc.prems by simp
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  \<comment> \<open>the two conjuncts of @{const num_plan.num_rat_impl.num_valid_state_sequence} at index @{term i}
     that we need: the numeric update and the numeric precondition.\<close>
  let ?Sr = "planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)"
  have vss_i:
      "num_plan.num_rat_impl.happening_num_update_set ?Sr (snd (M i)) = snd (M (Suc i))"
      "\<forall>s \<in> ?Sr. sat_comps (snd (M i)) ((set \<circ> n_pre) s)"
    using vss i_lt'
    unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def
    by (simp_all only:) blast+
  have SrS: "?Sr = ?S" by (rule rat_impl_happ_at_eq_bnd)
  have upd: "num_plan.num_rat_impl.happening_num_update_set ?S (snd (M i)) = snd (M (Suc i))"
    using vss_i(1) unfolding SrS .
  have pre: "\<forall>s \<in> ?S. sat_comps (snd (M i)) (set (n_pre s))"
    using vss_i(2) unfolding SrS by (simp add: o_def)
  \<comment> \<open>discharge the kernel on this happening\<close>
  have "fluent_in_bounds (num_plan.num_rat_impl.happening_num_update_set ?S (snd (M i)))"
  proof (rule happening_preserves_fib[OF bound_inv])
    show "finite ?S" by (rule happening_finite_bnd)
    show "?S \<subseteq> all_snaps" by (rule happening_subseteq_all_snaps)
    show "\<forall>s\<in>?S. upds_functional (set (upds s))"
      using happening_upds_functional_bnd by (auto simp: o_def)
    show "\<forall>x\<in>?S. \<forall>y\<in>?S. x \<noteq> y \<longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      using happening_num_noninterfere_bnd by blast
    show "fluent_in_bounds (snd (M i))" by (rule IH)
    show "\<forall>s\<in>?S. sat_comps (snd (M i)) (set (n_pre s))" by (rule pre)
  qed
  thus ?case by (simp add: upd)
qed

sublocale numeric_tp_nta_reduction_correctness
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name
    n_pre n_inv upds num_init num_goal nfluents fluent_to_name fluent_lo fluent_hi const_to_int
  apply unfold_locales
  using num_valid const_to_int_of_int num_goal_comp_ok num_seq_in_bounds_derived by blast+

end


section \<open>WP-E: the inline interval-arithmetic certificate check (\<open>is_gbound_inv'\<close>)\<close>

text \<open>The eval-decidable check that discharges @{text num_bound_inv} (and hence, through the bridge
  above, @{text num_seq_in_bounds}). It is the reduction-native, self-contained twin of the standalone
  @{text Numeric_Bound_Inference} interval analysis (which cannot be imported: HOL-IMP's @{text Abs_Int0}
  clashes with the Munta/FPS @{text \<open>_ option\<close>} arity). The standalone analysis \<^emph>\<open>computes\<close> a tight box
  @{term \<open>\<lambda>f. (fluent_lo f, fluent_hi f)\<close>} (threshold widening + guard refinement); THIS layer \<^emph>\<open>re-checks\<close>
  it by evaluation over the reduction's own @{typ \<open>('n, 'r) nexp\<close>}, so it also serves as WP-D's executable
  certificate check.

  \<^bold>\<open>Status: 3 sorries (the soundness lemmas). Definitions are concrete/executable.\<close> The interval eval works
  in the @{text const_to_int} encoding (code-generatable; reuses only @{text const_to_int_of_int} + the
  @{text nexp_ok} fragment). \<open>None\<close> = "cannot bound" (fail-closed; only via an \<open>NDiv\<close> whose
  divisor interval straddles 0).\<close>

context numeric_tp_nta_reduction
begin

definition map_ibnd2 ::
  "(int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int) \<Rightarrow> (int \<times> int) option \<Rightarrow> (int \<times> int) option \<Rightarrow> (int \<times> int) option"
  where "map_ibnd2 g x y = (case (x, y) of (Some a, Some b) \<Rightarrow> Some (g a b) | _ \<Rightarrow> None)"

fun aeval :: "('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> (int \<times> int) option" where
  "aeval B (NConst c) = Some (const_to_int c, const_to_int c)"
| "aeval B (NVar f)   = Some (B f)"
| "aeval B (NAdd a b) = map_ibnd2 (\<lambda>(al, ah) (bl, bh). (al + bl, ah + bh)) (aeval B a) (aeval B b)"
| "aeval B (NSub a b) = map_ibnd2 (\<lambda>(al, ah) (bl, bh). (al - bh, ah - bl)) (aeval B a) (aeval B b)"
| "aeval B (NMul a b) = map_ibnd2 (\<lambda>(al, ah) (bl, bh).
       let ps = [al * bl, al * bh, ah * bl, ah * bh] in (Min (set ps), Max (set ps)))
       (aeval B a) (aeval B b)"
| "aeval B (NDiv a b) = (case (aeval B a, aeval B b) of
       (Some (al, ah), Some (bl, bh)) \<Rightarrow>
         (if 0 < bl \<or> bh < 0
          then let ps = [al div bl, al div bh, ah div bl, ah div bh] in Some (Min (set ps), Max (set ps))
          else None)
     | _ \<Rightarrow> None)"

text \<open>Guard refinement: tighten the box by the var-vs-const numeric preconditions (where threshold caps
  land); all other comparison shapes are ignored -- sound, just a wider box.\<close>
fun refine_comp :: "('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_comp (Comp Cle (NVar f) (NConst c)) B = B(f := (fst (B f), min (snd (B f)) (const_to_int c)))"
| "refine_comp (Comp Cge (NVar f) (NConst c)) B = B(f := (max (fst (B f)) (const_to_int c), snd (B f)))"
| "refine_comp (Comp Ceq (NVar f) (NConst c)) B =
     B(f := (max (fst (B f)) (const_to_int c), min (snd (B f)) (const_to_int c)))"
| "refine_comp (Comp Clt (NVar f) (NConst c)) B = B(f := (fst (B f), min (snd (B f)) (const_to_int c - 1)))"
| "refine_comp (Comp Cgt (NVar f) (NConst c)) B = B(f := (max (fst (B f)) (const_to_int c + 1), snd (B f)))"
| "refine_comp _ B = B"

definition refine_box :: "('n, 'r) comp list \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_box cs B = fold refine_comp cs B"

definition box :: "'n \<Rightarrow> int \<times> int" where
  "box = (\<lambda>f. (fluent_lo f, fluent_hi f))"

text \<open>The eval-decidable certificate: init in the box, and every relaxed snap's update RHS,
  interval-evaluated over the guard-refined box, lands inside the target fluent's bounds.\<close>
definition is_gbound_inv' :: bool where
  "is_gbound_inv' \<longleftrightarrow>
     (\<forall>f \<in> set nfluents.
        fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f)
   \<and> (\<forall>s \<in> all_snaps. \<forall>(f, e) \<in> set (upds s).
        case aeval (refine_box (n_pre s) box) e of
          None \<Rightarrow> False
        | Some (al, ah) \<Rightarrow> fluent_lo f \<le> al \<and> ah \<le> fluent_hi f)"

text \<open>\<^bold>\<open>SORRY (WP-E).\<close> The interval eval over-approximates the concrete @{const eval_nexp} on the
  @{const nexp_ok} fragment: induction on @{term e}, using @{text const_to_int} commutation on integers
  (derivable from @{text const_to_int_of_int} + integrality) and interval-arithmetic monotonicity. Stated
  over an arbitrary box @{term B} that the read fluents of @{term w} inhabit (so it applies to the
  guard-refined box).\<close>
lemma aeval_sound:
  assumes "\<And>g. g \<in> nexp_fluents e \<Longrightarrow>
             (\<exists>r. w g = Some r \<and> r \<in> \<int> \<and> fst (B g) \<le> const_to_int r \<and> const_to_int r \<le> snd (B g))"
      and "nexp_ok w e"
      and "aeval B e = Some (al, ah)"
    shows "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int> \<and> al \<le> const_to_int r \<and> const_to_int r \<le> ah"
  sorry

text \<open>\<^bold>\<open>SORRY (WP-E).\<close> An in-box valuation satisfying the guards inhabits the guard-refined box (each
  @{const refine_comp} only shrinks a bound to a value the guard already forces).\<close>
lemma refine_box_sound:
  assumes "fluent_in_bounds w" and "sat_comps w (set cs)" and "g \<in> set nfluents"
    shows "\<exists>r. w g = Some r \<and> r \<in> \<int>
               \<and> fst (refine_box cs box g) \<le> const_to_int r \<and> const_to_int r \<le> snd (refine_box cs box g)"
  sorry

text \<open>\<^bold>\<open>SORRY (WP-E).\<close> The eval-decidable certificate implies the semantic certificate -- so a
  threshold-computed box, once @{const is_gbound_inv'} checks by evaluation, discharges @{const num_bound_inv}
  (hence @{text num_seq_in_bounds}). Via @{thm num_bound_invI}: init directly; step: @{thm refine_box_sound}
  puts @{term w} in the refined box, @{text snap_upds_nexp_ok_start}/@{text end} give @{const nexp_ok}
  (definedness + integrality), and @{thm aeval_sound} lands @{term \<open>const_to_int r\<close>} in @{term \<open>[al, ah]\<close>}
  \<open>\<subseteq>\<close> @{term \<open>[fluent_lo f, fluent_hi f]\<close>}.\<close>
theorem is_gbound_inv'_imp_num_bound_inv:
  assumes "is_gbound_inv'"
  shows "num_bound_inv"
  sorry

end

end

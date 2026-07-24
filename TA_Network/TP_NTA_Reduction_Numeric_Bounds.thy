theory TP_NTA_Reduction_Numeric_Bounds
  imports
    TP_NTA_Reduction_Correctness_Numeric
    TP_NTA_Reduction_Numeric_Model_Checking
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

  \<^bold>\<open>Status: all soundness lemmas proved (0 sorries). Definitions are concrete/executable.\<close> The interval
  eval works in the @{text const_to_int} encoding (code-generatable; reuses only @{text const_to_int_of_int}
  + the @{text nexp_ok} fragment). \<open>None\<close> = "cannot bound" (fail-closed; only via an \<open>NDiv\<close> whose
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
| "aeval B (NDiv a b) = None"
  \<comment> \<open>Fail-closed on division: @{term None} means \"cannot bound\", which forces the certificate check
     to reject any tracked-effect RHS containing an @{term NDiv} (sound; the benchmark fragment has
     none). Dropping the integer-division interval branch keeps @{text aeval_sound} vacuous on
     @{term NDiv} rather than requiring the truncating-division interval bound.\<close>

text \<open>Guard refinement now interval-evaluates the OTHER side of a comparison (@{const aeval}) and
  tightens a bare-\<open>NVar\<close> side by the op-appropriate endpoint(s) -- two-sided composition; subsumes the
  old var-vs-const arms (\<open>aeval\<close> of \<open>NConst c\<close> is the point \<open>[c, c]\<close>) and the point-box var-vs-var rule
  (\<open>aeval\<close> of \<open>NVar g\<close> is \<open>B g\<close>), and additionally exploits general operands like \<open>item_id + 1\<close>. \<open>None\<close>
  from \<open>aeval\<close> (an \<open>NDiv\<close>) refines nothing. Sound: only shrinks toward values the guard forces.\<close>
fun refine_left :: "('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_left (Comp p (NVar f) e) B =
     (case aeval B e of
        None \<Rightarrow> B
      | Some (l, h) \<Rightarrow>
          (case p of
             Cle \<Rightarrow> B(f := (fst (B f), min (snd (B f)) h))
           | Clt \<Rightarrow> B(f := (fst (B f), min (snd (B f)) (h - 1)))
           | Cge \<Rightarrow> B(f := (max (fst (B f)) l, snd (B f)))
           | Cgt \<Rightarrow> B(f := (max (fst (B f)) (l + 1), snd (B f)))
           | Ceq \<Rightarrow> B(f := (max (fst (B f)) l, min (snd (B f)) h))))"
| "refine_left _ B = B"

fun refine_right :: "('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_right (Comp p e (NVar g)) B =
     (case aeval B e of
        None \<Rightarrow> B
      | Some (l, h) \<Rightarrow>
          (case p of
             Cle \<Rightarrow> B(g := (max (fst (B g)) l, snd (B g)))
           | Clt \<Rightarrow> B(g := (max (fst (B g)) (l + 1), snd (B g)))
           | Cge \<Rightarrow> B(g := (fst (B g), min (snd (B g)) h))
           | Cgt \<Rightarrow> B(g := (fst (B g), min (snd (B g)) (h - 1)))
           | Ceq \<Rightarrow> B(g := (max (fst (B g)) l, min (snd (B g)) h))))"
| "refine_right _ B = B"

definition refine_comp :: "('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_comp c B = refine_right c (refine_left c B)"

definition refine_box :: "('n, 'r) comp list \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_box cs B = fold refine_comp cs B"

definition box :: "'n \<Rightarrow> int \<times> int" where
  "box = (\<lambda>f. (fluent_lo f, fluent_hi f))"

text \<open>The eval-decidable certificate: init in the box, and for every relaxed snap EITHER the
  guard-refined box is empty on some declared fluent -- then no in-bounds valuation satisfies the
  snap's numeric guard (by @{text refine_box_sound} such a valuation would inhabit every refined
  interval), so the snap can never fire and its updates are vacuously in bounds -- or every update
  RHS, interval-evaluated over the guard-refined box, lands inside the target fluent's bounds.
  The emptiness escape is what accepts a snap whose guard is statically unsatisfiable within the
  declared bounds (majsp-2: \<open>battery = [1,1]\<close> refined by \<open>battery \<ge> distance = [2,2]\<close> is empty --
  the move can never fire, which is exactly WHY the instance is unsolvable).\<close>
definition is_gbound_inv' :: bool where
  "is_gbound_inv' \<longleftrightarrow>
     (\<forall>f \<in> set nfluents.
        fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f)
   \<and> (\<forall>s \<in> all_snaps.
        (\<exists>g \<in> set nfluents.
           snd (refine_box (n_pre s) box g) < fst (refine_box (n_pre s) box g))
      \<or> (\<forall>(f, e) \<in> set (upds s).
           case aeval (refine_box (n_pre s) box) e of
             None \<Rightarrow> False
           | Some (al, ah) \<Rightarrow> fluent_lo f \<le> al \<and> ah \<le> fluent_hi f))"

text \<open>@{term const_to_int} round-trips on integers: it inverts @{term of_int} there.\<close>
lemma const_to_int_round_trip:
  assumes "x \<in> \<int>"
  shows "of_int (const_to_int x) = x"
proof -
  obtain k where "x = of_int k" using assms by (auto elim: Ints_cases)
  thus ?thesis by (simp add: const_to_int_of_int)
qed

text \<open>On integers @{term const_to_int} is additive / commutes with @{text \<open>-\<close>}, @{text \<open>*\<close>}.\<close>
lemma const_to_int_add:
  assumes "x \<in> \<int>" and "y \<in> \<int>"
  shows "const_to_int (x + y) = const_to_int x + const_to_int y"
proof -
  obtain a where a: "x = of_int a" using assms(1) by (auto elim: Ints_cases)
  obtain b where b: "y = of_int b" using assms(2) by (auto elim: Ints_cases)
  show ?thesis by (simp add: a b const_to_int_of_int flip: of_int_add)
qed

lemma const_to_int_diff:
  assumes "x \<in> \<int>" and "y \<in> \<int>"
  shows "const_to_int (x - y) = const_to_int x - const_to_int y"
proof -
  obtain a where a: "x = of_int a" using assms(1) by (auto elim: Ints_cases)
  obtain b where b: "y = of_int b" using assms(2) by (auto elim: Ints_cases)
  show ?thesis by (simp add: a b const_to_int_of_int flip: of_int_diff)
qed

lemma const_to_int_mult:
  assumes "x \<in> \<int>" and "y \<in> \<int>"
  shows "const_to_int (x * y) = const_to_int x * const_to_int y"
proof -
  obtain a where a: "x = of_int a" using assms(1) by (auto elim: Ints_cases)
  obtain b where b: "y = of_int b" using assms(2) by (auto elim: Ints_cases)
  show ?thesis by (simp add: a b const_to_int_of_int flip: of_int_mult)
qed

text \<open>@{term const_to_int} is monotone on integers.\<close>
lemma const_to_int_mono:
  assumes "x \<in> \<int>" and "y \<in> \<int>" and "x \<le> y"
  shows "const_to_int x \<le> const_to_int y"
proof -
  obtain a where a: "x = of_int a" using assms(1) by (auto elim: Ints_cases)
  obtain b where b: "y = of_int b" using assms(2) by (auto elim: Ints_cases)
  from assms(3) have "of_int a \<le> (of_int b :: 'r)" using a b by simp
  hence "a \<le> b" by simp
  thus ?thesis using a b by (simp add: const_to_int_of_int)
qed


text \<open>A one-sided monotone bound: multiplying an @{typ int} @{term x} in @{term \<open>[p, q]\<close>} by a fixed
  @{term c} keeps @{term \<open>c * x\<close>} between the two endpoints @{term \<open>c * p\<close>} and @{term \<open>c * q\<close>}
  (which end is the lower one depends on the sign of @{term c}, hence @{term min}/@{term max}).\<close>
lemma mult_between:
  fixes c p q x :: int
  assumes "p \<le> x" and "x \<le> q"
  shows "min (c * p) (c * q) \<le> c * x \<and> c * x \<le> max (c * p) (c * q)"
proof (cases "0 \<le> c")
  case True
  have "c * p \<le> c * x" using assms(1) True by (rule mult_left_mono)
  moreover have "c * x \<le> c * q" using assms(2) True by (rule mult_left_mono)
  ultimately show ?thesis by (simp add: min_def max_def)
next
  case False
  hence c: "c \<le> 0" by simp
  have "c * x \<le> c * p" using assms(1) c by (simp add: mult_left_mono_neg)
  moreover have "c * q \<le> c * x" using assms(2) c by (simp add: mult_left_mono_neg)
  ultimately show ?thesis by (simp add: min_def max_def)
qed

text \<open>Interval multiplication over @{typ int}: the product of two ranged values lands between the
  minimum and maximum of the four corner products.\<close>
lemma mult_in_corners:
  fixes xa xb la ha lb hb :: int
  assumes "la \<le> xa" and "xa \<le> ha" and "lb \<le> xb" and "xb \<le> hb"
  shows "min (min (la * lb) (la * hb)) (min (ha * lb) (ha * hb)) \<le> xa * xb"
    and "xa * xb \<le> max (max (la * lb) (la * hb)) (max (ha * lb) (ha * hb))"
proof -
  \<comment> \<open>bound @{term \<open>xa * xb\<close>} between @{term \<open>xa * lb\<close>} and @{term \<open>xa * hb\<close>} (fix @{term xa}, vary @{term xb})\<close>
  have b1: "min (xa * lb) (xa * hb) \<le> xa * xb"
    and b2: "xa * xb \<le> max (xa * lb) (xa * hb)"
    using mult_between[OF assms(3,4), of xa] by (simp_all add: mult.commute)
  \<comment> \<open>and each of @{term \<open>xa * lb\<close>}, @{term \<open>xa * hb\<close>} between its own two corners (fix the constant, vary @{term xa})\<close>
  have lbc: "min (la * lb) (ha * lb) \<le> xa * lb"
    and lbc': "xa * lb \<le> max (la * lb) (ha * lb)"
    using mult_between[OF assms(1,2), of lb] by (simp_all add: mult.commute)
  have hbc: "min (la * hb) (ha * hb) \<le> xa * hb"
    and hbc': "xa * hb \<le> max (la * hb) (ha * hb)"
    using mult_between[OF assms(1,2), of hb] by (simp_all add: mult.commute)
  show "min (min (la * lb) (la * hb)) (min (ha * lb) (ha * hb)) \<le> xa * xb"
    using b1 lbc hbc by (simp add: min_le_iff_disj) linarith
  show "xa * xb \<le> max (max (la * lb) (la * hb)) (max (ha * lb) (ha * hb))"
    using b2 lbc' hbc' by (simp add: le_max_iff_disj) linarith
qed


text \<open>Exact division on integers stays integer-valued (base-locale twin of the correctness-locale
  @{text Ints_div_exact}, which is only available above the tracking layer in the ancestor).\<close>
lemma Ints_div_exact_bnd:
  assumes "a \<in> \<int>" and "b \<in> \<int>" and "b \<noteq> 0"
      and "const_to_int b dvd const_to_int a"
    shows "a / b \<in> \<int>"
proof -
  obtain ma where a: "a = Int.of_int ma" using assms(1) by (auto elim: Ints_cases)
  obtain mb where b: "b = Int.of_int mb" using assms(2) by (auto elim: Ints_cases)
  have mb0: "mb \<noteq> 0" using assms(3) b by auto
  have "mb dvd ma" using assms(4) a b const_to_int_of_int by simp
  then obtain q where "ma = mb * q" by blast
  hence "a / b = Int.of_int q" using a b mb0 by simp
  thus ?thesis by simp
qed

text \<open>Base-locale twin of @{text nexp_ok_eval}: an @{const nexp_ok} expression evaluates to a defined,
  integer-valued result (needed here since @{text nexp_ok_eval} lives in the correctness locale).\<close>
lemma nexp_ok_eval_bnd:
  assumes "nexp_ok w e"
  shows "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>"
  using assms
proof (induction e)
  case (NConst c)
  thus ?case by auto
next
  case (NVar f)
  thus ?case by auto
next
  case (NAdd a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by auto
next
  case (NSub a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by auto
next
  case (NMul a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by auto
next
  case (NDiv a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  have nz: "rb \<noteq> 0" and dvd: "const_to_int rb dvd const_to_int ra"
    using NDiv.prems a(1) b(1) by auto
  have ev: "eval_nexp w (NDiv a b) = Some (ra / rb)" using a(1) b(1) nz by simp
  have iv: "ra / rb \<in> \<int>" by (rule Ints_div_exact_bnd[OF a(2) b(2) nz dvd])
  thus ?case using ev by blast
qed

text \<open>Base-locale twin of @{text nexp_ok_fluents}: an @{const nexp_ok} expression reads only declared
  fluents.\<close>
lemma nexp_ok_fluents_bnd:
  assumes "nexp_ok w e"
  shows "nexp_fluents e \<subseteq> set nfluents"
  using assms by (induction e) auto

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
  using assms
proof (induction e arbitrary: al ah)
  case (NConst c)
  have ci: "c \<in> \<int>" using NConst.prems(2) by simp
  have "al = const_to_int c" and "ah = const_to_int c" using NConst.prems(3) by simp_all
  thus ?case using ci by simp
next
  case (NVar f)
  have box: "\<exists>r. w f = Some r \<and> r \<in> \<int> \<and> fst (B f) \<le> const_to_int r \<and> const_to_int r \<le> snd (B f)"
    using NVar.prems(1) by simp
  have alah: "al = fst (B f)" "ah = snd (B f)" using NVar.prems(3) by (auto simp: prod_eq_iff)
  show ?case using box alah by auto
next
  case (NAdd a b)
  obtain al1 ah1 al2 ah2 where
      ea: "aeval B a = Some (al1, ah1)"
    and eb: "aeval B b = Some (al2, ah2)"
    and albd: "al = al1 + al2" and ahbd: "ah = ah1 + ah2"
    using NAdd.prems(3) by (auto simp: map_ibnd2_def split: option.splits)
  have oka: "nexp_ok w a" and okb: "nexp_ok w b" using NAdd.prems(2) by simp_all
  have ra: "\<exists>r. eval_nexp w a = Some r \<and> r \<in> \<int> \<and> al1 \<le> const_to_int r \<and> const_to_int r \<le> ah1"
    by (rule NAdd.IH(1)) (use NAdd.prems(1) oka ea in auto)
  have rb: "\<exists>r. eval_nexp w b = Some r \<and> r \<in> \<int> \<and> al2 \<le> const_to_int r \<and> const_to_int r \<le> ah2"
    by (rule NAdd.IH(2)) (use NAdd.prems(1) okb eb in auto)
  obtain ra' where a: "eval_nexp w a = Some ra'" "ra' \<in> \<int>" "al1 \<le> const_to_int ra'" "const_to_int ra' \<le> ah1"
    using ra by blast
  obtain rb' where b: "eval_nexp w b = Some rb'" "rb' \<in> \<int>" "al2 \<le> const_to_int rb'" "const_to_int rb' \<le> ah2"
    using rb by blast
  have ev: "eval_nexp w (NAdd a b) = Some (ra' + rb')" using a(1) b(1) by simp
  have int: "ra' + rb' \<in> \<int>" using a(2) b(2) by (rule Ints_add)
  have cti: "const_to_int (ra' + rb') = const_to_int ra' + const_to_int rb'"
    by (rule const_to_int_add[OF a(2) b(2)])
  show ?case using ev int cti a(3,4) b(3,4) albd ahbd by auto
next
  case (NSub a b)
  obtain al1 ah1 al2 ah2 where
      ea: "aeval B a = Some (al1, ah1)"
    and eb: "aeval B b = Some (al2, ah2)"
    and albd: "al = al1 - ah2" and ahbd: "ah = ah1 - al2"
    using NSub.prems(3) by (auto simp: map_ibnd2_def split: option.splits)
  have oka: "nexp_ok w a" and okb: "nexp_ok w b" using NSub.prems(2) by simp_all
  have ra: "\<exists>r. eval_nexp w a = Some r \<and> r \<in> \<int> \<and> al1 \<le> const_to_int r \<and> const_to_int r \<le> ah1"
    by (rule NSub.IH(1)) (use NSub.prems(1) oka ea in auto)
  have rb: "\<exists>r. eval_nexp w b = Some r \<and> r \<in> \<int> \<and> al2 \<le> const_to_int r \<and> const_to_int r \<le> ah2"
    by (rule NSub.IH(2)) (use NSub.prems(1) okb eb in auto)
  obtain ra' where a: "eval_nexp w a = Some ra'" "ra' \<in> \<int>" "al1 \<le> const_to_int ra'" "const_to_int ra' \<le> ah1"
    using ra by blast
  obtain rb' where b: "eval_nexp w b = Some rb'" "rb' \<in> \<int>" "al2 \<le> const_to_int rb'" "const_to_int rb' \<le> ah2"
    using rb by blast
  have ev: "eval_nexp w (NSub a b) = Some (ra' - rb')" using a(1) b(1) by simp
  have int: "ra' - rb' \<in> \<int>" using a(2) b(2) by (rule Ints_diff)
  have cti: "const_to_int (ra' - rb') = const_to_int ra' - const_to_int rb'"
    by (rule const_to_int_diff[OF a(2) b(2)])
  show ?case using ev int cti a(3,4) b(3,4) albd ahbd by auto
next
  case (NMul a b)
  obtain al1 ah1 al2 ah2 where
      ea: "aeval B a = Some (al1, ah1)"
    and eb: "aeval B b = Some (al2, ah2)"
    and albd: "al = Min (set [al1 * al2, al1 * ah2, ah1 * al2, ah1 * ah2])"
    and ahbd: "ah = Max (set [al1 * al2, al1 * ah2, ah1 * al2, ah1 * ah2])"
    using NMul.prems(3) by (auto simp: map_ibnd2_def Let_def split: option.splits)
  have oka: "nexp_ok w a" and okb: "nexp_ok w b" using NMul.prems(2) by simp_all
  have ra: "\<exists>r. eval_nexp w a = Some r \<and> r \<in> \<int> \<and> al1 \<le> const_to_int r \<and> const_to_int r \<le> ah1"
    by (rule NMul.IH(1)) (use NMul.prems(1) oka ea in auto)
  have rb: "\<exists>r. eval_nexp w b = Some r \<and> r \<in> \<int> \<and> al2 \<le> const_to_int r \<and> const_to_int r \<le> ah2"
    by (rule NMul.IH(2)) (use NMul.prems(1) okb eb in auto)
  obtain ra' where a: "eval_nexp w a = Some ra'" "ra' \<in> \<int>" "al1 \<le> const_to_int ra'" "const_to_int ra' \<le> ah1"
    using ra by blast
  obtain rb' where b: "eval_nexp w b = Some rb'" "rb' \<in> \<int>" "al2 \<le> const_to_int rb'" "const_to_int rb' \<le> ah2"
    using rb by blast
  have ev: "eval_nexp w (NMul a b) = Some (ra' * rb')" using a(1) b(1) by simp
  have int: "ra' * rb' \<in> \<int>" using a(2) b(2) by (rule Ints_mult)
  have cti: "const_to_int (ra' * rb') = const_to_int ra' * const_to_int rb'"
    by (rule const_to_int_mult[OF a(2) b(2)])
  \<comment> \<open>the product's encoding lands between the corner min and max\<close>
  have corners1:
      "min (min (al1 * al2) (al1 * ah2)) (min (ah1 * al2) (ah1 * ah2))
         \<le> const_to_int ra' * const_to_int rb'"
    and corners2:
      "const_to_int ra' * const_to_int rb'
         \<le> max (max (al1 * al2) (al1 * ah2)) (max (ah1 * al2) (ah1 * ah2))"
    using mult_in_corners[OF a(3) a(4) b(3) b(4)] by simp_all
  have lo: "al \<le> const_to_int (ra' * rb')" using corners1 cti albd by simp
  have hi: "const_to_int (ra' * rb') \<le> ah" using corners2 cti ahbd by simp
  show ?case using ev int lo hi by blast
next
  case (NDiv a b)
  \<comment> \<open>@{term aeval} on @{term NDiv} is @{term None} (fail-closed), so the premise is vacuous.\<close>
  have "aeval B (NDiv a b) = None" by simp
  thus ?case using NDiv.prems(3) by simp
qed


text \<open>Abbreviation for the fold invariant of @{const refine_box}: for a fixed valuation @{term w},
  every declared fluent's integer encoding lies inside the running box @{term B}.\<close>
definition in_refine_box :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> bool" where
  "in_refine_box w B \<longleftrightarrow> (\<forall>h \<in> set nfluents. \<exists>r. w h = Some r \<and> r \<in> \<int>
       \<and> fst (B h) \<le> const_to_int r \<and> const_to_int r \<le> snd (B h))"

text \<open>A single guard refinement preserves the fold invariant. @{const refine_comp} is the sequential
  composition @{term \<open>refine_right c (refine_left c B)\<close>}: @{const refine_left} tightens a bare-\<open>NVar\<close> LHS
  by the interval @{const aeval} computes for the RHS, and @{const refine_right} mirrors it for a bare-\<open>NVar\<close>
  RHS. Each only shrinks a bound toward a value @{term \<open>sat_comp w c\<close>} already forces -- @{term \<open>comp_ok w c\<close>}
  supplies the definedness and integrality of both sides (via @{text aeval_sound}) -- leaving every other
  fluent's box untouched.\<close>
lemma refine_left_pres:
  assumes "in_refine_box w B"
      and "sat_comp w c"
      and "comp_ok w c"
    shows "in_refine_box w (refine_left c B)"
proof -
  obtain p a e where c: "c = Comp p a e" by (cases c)
  show ?thesis
  proof (cases a)
    case (NConst k)
    have "refine_left c B = B" unfolding c NConst by simp
    thus ?thesis using assms(1) by simp
  next
    case (NVar f)
    show ?thesis
    proof (cases "aeval B e")
      case None
      have "refine_left c B = B" unfolding c NVar using None by simp
      thus ?thesis using assms(1) by simp
    next
      case (Some lh)
      obtain l h where lh: "aeval B e = Some (l, h)" using Some by (cases lh) simp
      have okf: "nexp_ok w (NVar f)" and oke: "nexp_ok w e"
        using assms(3) unfolding c NVar by simp_all
      have fin: "f \<in> set nfluents" using okf by simp
      obtain rf where rf: "w f = Some rf" "rf \<in> \<int>"
        and hlo: "fst (B f) \<le> const_to_int rf" and hhi: "const_to_int rf \<le> snd (B f)"
        using assms(1) fin unfolding in_refine_box_def by blast
      \<comment> \<open>every fluent read by the RHS has an in-box witness (needed by @{text aeval_sound})\<close>
      have wit: "\<exists>r. w g = Some r \<and> r \<in> \<int> \<and> fst (B g) \<le> const_to_int r \<and> const_to_int r \<le> snd (B g)"
        if "g \<in> nexp_fluents e" for g
      proof -
        have "g \<in> set nfluents" using nexp_ok_fluents_bnd[OF oke] that by blast
        thus ?thesis using assms(1) unfolding in_refine_box_def by blast
      qed
      obtain re where re: "eval_nexp w e = Some re" "re \<in> \<int>"
        and rlo: "l \<le> const_to_int re" and rhi: "const_to_int re \<le> h"
        using aeval_sound[OF wit oke lh] by blast
      have rel: "cmp_op_rel p rf re" using assms(2) rf(1) re(1) unfolding c NVar by simp
      \<comment> \<open>updating only @{term f}'s box entry preserves the invariant when @{term rf}'s image stays inside\<close>
      have box_upd: "in_refine_box w (B(f := nb))"
        if nb_lo: "fst nb \<le> const_to_int rf" and nb_hi: "const_to_int rf \<le> snd nb" for nb
      proof (unfold in_refine_box_def, rule ballI)
        fix h' assume h'in: "h' \<in> set nfluents"
        show "\<exists>r. w h' = Some r \<and> r \<in> \<int> \<and> fst ((B(f := nb)) h') \<le> const_to_int r \<and> const_to_int r \<le> snd ((B(f := nb)) h')"
        proof (cases "h' = f")
          case True
          thus ?thesis using rf nb_lo nb_hi by auto
        next
          case False
          thus ?thesis using assms(1) h'in unfolding in_refine_box_def by auto
        qed
      qed
      \<comment> \<open>strict monotonicity of the integer encoding (used by the strict comparison arms)\<close>
      have cti_lt: "const_to_int x < const_to_int y" if xi: "x \<in> \<int>" and yi: "y \<in> \<int>" and xy: "x < y" for x y
      proof -
        have le: "const_to_int x \<le> const_to_int y" using xi yi xy by (auto intro: const_to_int_mono)
        have "const_to_int x \<noteq> const_to_int y"
        proof
          assume "const_to_int x = const_to_int y"
          hence "of_int (const_to_int x) = (of_int (const_to_int y) :: 'r)" by simp
          hence "x = y" using const_to_int_round_trip[OF xi] const_to_int_round_trip[OF yi] by simp
          thus False using xy by simp
        qed
        thus ?thesis using le by simp
      qed
      show ?thesis
      proof (cases p)
        case Cle
        have eq: "refine_left c B = B(f := (fst (B f), min (snd (B f)) h))"
          unfolding c NVar using lh Cle by simp
        have "rf \<le> re" using rel Cle by simp
        hence "const_to_int rf \<le> const_to_int re" by (rule const_to_int_mono[OF rf(2) re(2)])
        hence "const_to_int rf \<le> min (snd (B f)) h" using hhi rhi by simp
        hence "in_refine_box w (B(f := (fst (B f), min (snd (B f)) h)))"
          using box_upd[of "(fst (B f), min (snd (B f)) h)"] hlo by simp
        thus ?thesis unfolding eq .
      next
        case Ceq
        have eq: "refine_left c B = B(f := (max (fst (B f)) l, min (snd (B f)) h))"
          unfolding c NVar using lh Ceq by simp
        have "rf = re" using rel Ceq by simp
        hence cti: "const_to_int rf = const_to_int re" by simp
        have a1: "max (fst (B f)) l \<le> const_to_int rf" using hlo rlo cti by simp
        have a2: "const_to_int rf \<le> min (snd (B f)) h" using hhi rhi cti by simp
        have "in_refine_box w (B(f := (max (fst (B f)) l, min (snd (B f)) h)))"
          using box_upd[of "(max (fst (B f)) l, min (snd (B f)) h)"] a1 a2 by simp
        thus ?thesis unfolding eq .
      next
        case Cge
        have eq: "refine_left c B = B(f := (max (fst (B f)) l, snd (B f)))"
          unfolding c NVar using lh Cge by simp
        have "re \<le> rf" using rel Cge by simp
        hence "const_to_int re \<le> const_to_int rf" by (rule const_to_int_mono[OF re(2) rf(2)])
        hence g1: "max (fst (B f)) l \<le> const_to_int rf" using hlo rlo by simp
        have "in_refine_box w (B(f := (max (fst (B f)) l, snd (B f))))"
          using box_upd[of "(max (fst (B f)) l, snd (B f))"] g1 hhi by simp
        thus ?thesis unfolding eq .
      next
        case Clt
        have eq: "refine_left c B = B(f := (fst (B f), min (snd (B f)) (h - 1)))"
          unfolding c NVar using lh Clt by simp
        have "rf < re" using rel Clt by simp
        hence "const_to_int rf < const_to_int re" by (rule cti_lt[OF rf(2) re(2)])
        hence "const_to_int rf \<le> h - 1" using rhi by linarith
        hence "const_to_int rf \<le> min (snd (B f)) (h - 1)" using hhi by simp
        hence "in_refine_box w (B(f := (fst (B f), min (snd (B f)) (h - 1))))"
          using box_upd[of "(fst (B f), min (snd (B f)) (h - 1))"] hlo by simp
        thus ?thesis unfolding eq .
      next
        case Cgt
        have eq: "refine_left c B = B(f := (max (fst (B f)) (l + 1), snd (B f)))"
          unfolding c NVar using lh Cgt by simp
        have "re < rf" using rel Cgt by simp
        hence "const_to_int re < const_to_int rf" by (rule cti_lt[OF re(2) rf(2)])
        hence "l + 1 \<le> const_to_int rf" using rlo by linarith
        hence "max (fst (B f)) (l + 1) \<le> const_to_int rf" using hlo by simp
        hence "in_refine_box w (B(f := (max (fst (B f)) (l + 1), snd (B f))))"
          using box_upd[of "(max (fst (B f)) (l + 1), snd (B f))"] hhi by simp
        thus ?thesis unfolding eq .
      qed
    qed
  next
    case (NAdd a1 a2)
    have "refine_left c B = B" unfolding c NAdd by simp
    thus ?thesis using assms(1) by simp
  next
    case (NSub a1 a2)
    have "refine_left c B = B" unfolding c NSub by simp
    thus ?thesis using assms(1) by simp
  next
    case (NMul a1 a2)
    have "refine_left c B = B" unfolding c NMul by simp
    thus ?thesis using assms(1) by simp
  next
    case (NDiv a1 a2)
    have "refine_left c B = B" unfolding c NDiv by simp
    thus ?thesis using assms(1) by simp
  qed
qed

text \<open>The mirror of @{thm [source] refine_left_pres} for @{const refine_right}: a bare-\<open>NVar\<close> RHS is
  tightened by the interval @{const aeval} computes for the LHS, with the comparison read the other way
  round.\<close>
lemma refine_right_pres:
  assumes "in_refine_box w B"
      and "sat_comp w c"
      and "comp_ok w c"
    shows "in_refine_box w (refine_right c B)"
proof -
  obtain p e a where c: "c = Comp p e a" by (cases c)
  show ?thesis
  proof (cases a)
    case (NConst k)
    have "refine_right c B = B" unfolding c NConst by simp
    thus ?thesis using assms(1) by simp
  next
    case (NAdd a1 a2)
    have "refine_right c B = B" unfolding c NAdd by simp
    thus ?thesis using assms(1) by simp
  next
    case (NSub a1 a2)
    have "refine_right c B = B" unfolding c NSub by simp
    thus ?thesis using assms(1) by simp
  next
    case (NMul a1 a2)
    have "refine_right c B = B" unfolding c NMul by simp
    thus ?thesis using assms(1) by simp
  next
    case (NDiv a1 a2)
    have "refine_right c B = B" unfolding c NDiv by simp
    thus ?thesis using assms(1) by simp
  next
    case (NVar g)
    show ?thesis
    proof (cases "aeval B e")
      case None
      have "refine_right c B = B" unfolding c NVar using None by simp
      thus ?thesis using assms(1) by simp
    next
      case (Some lh)
      obtain l h where lh: "aeval B e = Some (l, h)" using Some by (cases lh) simp
      have okg: "nexp_ok w (NVar g)" and oke: "nexp_ok w e"
        using assms(3) unfolding c NVar by simp_all
      have gin: "g \<in> set nfluents" using okg by simp
      obtain rg where rg: "w g = Some rg" "rg \<in> \<int>"
        and glo: "fst (B g) \<le> const_to_int rg" and ghi: "const_to_int rg \<le> snd (B g)"
        using assms(1) gin unfolding in_refine_box_def by blast
      have wit: "\<exists>r. w x = Some r \<and> r \<in> \<int> \<and> fst (B x) \<le> const_to_int r \<and> const_to_int r \<le> snd (B x)"
        if "x \<in> nexp_fluents e" for x
      proof -
        have "x \<in> set nfluents" using nexp_ok_fluents_bnd[OF oke] that by blast
        thus ?thesis using assms(1) unfolding in_refine_box_def by blast
      qed
      obtain re where re: "eval_nexp w e = Some re" "re \<in> \<int>"
        and rlo: "l \<le> const_to_int re" and rhi: "const_to_int re \<le> h"
        using aeval_sound[OF wit oke lh] by blast
      have rel: "cmp_op_rel p re rg" using assms(2) rg(1) re(1) unfolding c NVar by simp
      have box_upd: "in_refine_box w (B(g := nb))"
        if nb_lo: "fst nb \<le> const_to_int rg" and nb_hi: "const_to_int rg \<le> snd nb" for nb
      proof (unfold in_refine_box_def, rule ballI)
        fix h' assume h'in: "h' \<in> set nfluents"
        show "\<exists>r. w h' = Some r \<and> r \<in> \<int> \<and> fst ((B(g := nb)) h') \<le> const_to_int r \<and> const_to_int r \<le> snd ((B(g := nb)) h')"
        proof (cases "h' = g")
          case True
          thus ?thesis using rg nb_lo nb_hi by auto
        next
          case False
          thus ?thesis using assms(1) h'in unfolding in_refine_box_def by auto
        qed
      qed
      have cti_lt: "const_to_int x < const_to_int y" if xi: "x \<in> \<int>" and yi: "y \<in> \<int>" and xy: "x < y" for x y
      proof -
        have le: "const_to_int x \<le> const_to_int y" using xi yi xy by (auto intro: const_to_int_mono)
        have "const_to_int x \<noteq> const_to_int y"
        proof
          assume "const_to_int x = const_to_int y"
          hence "of_int (const_to_int x) = (of_int (const_to_int y) :: 'r)" by simp
          hence "x = y" using const_to_int_round_trip[OF xi] const_to_int_round_trip[OF yi] by simp
          thus False using xy by simp
        qed
        thus ?thesis using le by simp
      qed
      show ?thesis
      proof (cases p)
        case Cle
        have eq: "refine_right c B = B(g := (max (fst (B g)) l, snd (B g)))"
          unfolding c NVar using lh Cle by simp
        have "re \<le> rg" using rel Cle by simp
        hence "const_to_int re \<le> const_to_int rg" by (rule const_to_int_mono[OF re(2) rg(2)])
        hence g1: "max (fst (B g)) l \<le> const_to_int rg" using glo rlo by simp
        have "in_refine_box w (B(g := (max (fst (B g)) l, snd (B g))))"
          using box_upd[of "(max (fst (B g)) l, snd (B g))"] g1 ghi by simp
        thus ?thesis unfolding eq .
      next
        case Ceq
        have eq: "refine_right c B = B(g := (max (fst (B g)) l, min (snd (B g)) h))"
          unfolding c NVar using lh Ceq by simp
        have "re = rg" using rel Ceq by simp
        hence cti: "const_to_int rg = const_to_int re" by simp
        have a1: "max (fst (B g)) l \<le> const_to_int rg" using glo rlo cti by simp
        have a2: "const_to_int rg \<le> min (snd (B g)) h" using ghi rhi cti by simp
        have "in_refine_box w (B(g := (max (fst (B g)) l, min (snd (B g)) h)))"
          using box_upd[of "(max (fst (B g)) l, min (snd (B g)) h)"] a1 a2 by simp
        thus ?thesis unfolding eq .
      next
        case Cge
        have eq: "refine_right c B = B(g := (fst (B g), min (snd (B g)) h))"
          unfolding c NVar using lh Cge by simp
        have "rg \<le> re" using rel Cge by simp
        hence "const_to_int rg \<le> const_to_int re" by (rule const_to_int_mono[OF rg(2) re(2)])
        hence "const_to_int rg \<le> min (snd (B g)) h" using ghi rhi by simp
        hence "in_refine_box w (B(g := (fst (B g), min (snd (B g)) h)))"
          using box_upd[of "(fst (B g), min (snd (B g)) h)"] glo by simp
        thus ?thesis unfolding eq .
      next
        case Clt
        have eq: "refine_right c B = B(g := (max (fst (B g)) (l + 1), snd (B g)))"
          unfolding c NVar using lh Clt by simp
        have "re < rg" using rel Clt by simp
        hence "const_to_int re < const_to_int rg" by (rule cti_lt[OF re(2) rg(2)])
        hence "l + 1 \<le> const_to_int rg" using rlo by linarith
        hence "max (fst (B g)) (l + 1) \<le> const_to_int rg" using glo by simp
        hence "in_refine_box w (B(g := (max (fst (B g)) (l + 1), snd (B g))))"
          using box_upd[of "(max (fst (B g)) (l + 1), snd (B g))"] ghi by simp
        thus ?thesis unfolding eq .
      next
        case Cgt
        have eq: "refine_right c B = B(g := (fst (B g), min (snd (B g)) (h - 1)))"
          unfolding c NVar using lh Cgt by simp
        have "rg < re" using rel Cgt by simp
        hence "const_to_int rg < const_to_int re" by (rule cti_lt[OF rg(2) re(2)])
        hence "const_to_int rg \<le> h - 1" using rhi by linarith
        hence "const_to_int rg \<le> min (snd (B g)) (h - 1)" using ghi by simp
        hence "in_refine_box w (B(g := (fst (B g), min (snd (B g)) (h - 1))))"
          using box_upd[of "(fst (B g), min (snd (B g)) (h - 1))"] glo by simp
        thus ?thesis unfolding eq .
      qed
    qed
  qed
qed

text \<open>The two-sided composition preserves the invariant: fold @{const refine_left} then @{const refine_right}.\<close>
lemma refine_comp_pres:
  assumes "in_refine_box w B"
      and "sat_comp w c"
      and "comp_ok w c"
    shows "in_refine_box w (refine_comp c B)"
  unfolding refine_comp_def
  using refine_right_pres[OF refine_left_pres[OF assms] assms(2,3)] .

text \<open>Folding all guard refinements preserves the invariant.\<close>
lemma refine_box_fold_pres:
  assumes "in_refine_box w B"
      and "\<forall>c \<in> set cs. sat_comp w c"
      and "\<forall>c \<in> set cs. comp_ok w c"
    shows "in_refine_box w (fold refine_comp cs B)"
  using assms
proof (induction cs arbitrary: B)
  case Nil
  thus ?case by simp
next
  case (Cons c cs)
  have "in_refine_box w (refine_comp c B)"
    by (rule refine_comp_pres[OF Cons.prems(1)]) (use Cons.prems(2,3) in auto)
  hence "in_refine_box w (fold refine_comp cs (refine_comp c B))"
    by (rule Cons.IH) (use Cons.prems(2,3) in auto)
  thus ?case by simp
qed

text \<open>\<^bold>\<open>SORRY (WP-E).\<close> An in-box valuation satisfying the guards inhabits the guard-refined box (each
  @{const refine_comp} only shrinks a bound to a value the guard already forces).\<close>
lemma refine_box_sound:
  assumes "fluent_in_bounds w" and "sat_comps w (set cs)"
      and "\<forall>c \<in> set cs. comp_ok w c"
      and "g \<in> set nfluents"
    shows "\<exists>r. w g = Some r \<and> r \<in> \<int>
               \<and> fst (refine_box cs box g) \<le> const_to_int r \<and> const_to_int r \<le> snd (refine_box cs box g)"
proof -
  \<comment> \<open>the starting box @{const box} contains @{term w} (that is exactly @{const fluent_in_bounds})\<close>
  have "in_refine_box w box"
    unfolding in_refine_box_def box_def
    using assms(1) unfolding fluent_in_bounds_def by simp
  \<comment> \<open>folding all guards keeps @{term w} inside the box\<close>
  hence "in_refine_box w (fold refine_comp cs box)"
    by (rule refine_box_fold_pres)
       (use assms(2) assms(3) in \<open>auto simp: sat_comps_def\<close>)
  thus ?thesis
    unfolding refine_box_def in_refine_box_def using assms(4) by blast
qed

text \<open>\<^bold>\<open>SORRY (WP-E).\<close> The eval-decidable certificate implies the semantic certificate -- so a
  threshold-computed box, once @{const is_gbound_inv'} checks by evaluation, discharges @{const num_bound_inv}
  (hence @{text num_seq_in_bounds}). Via @{thm num_bound_invI}: init directly; step: @{thm refine_box_sound}
  puts @{term w} in the refined box, @{text snap_upds_nexp_ok_start}/@{text end} give @{const nexp_ok}
  (definedness + integrality), and @{thm aeval_sound} lands @{term \<open>const_to_int r\<close>} in @{term \<open>[al, ah]\<close>}
  \<open>\<subseteq>\<close> @{term \<open>[fluent_lo f, fluent_hi f]\<close>}.\<close>
theorem is_gbound_inv'_imp_num_bound_inv:
  assumes "is_gbound_inv'"
  shows "num_bound_inv"
proof (rule num_bound_invI)
  \<comment> \<open>INIT: the initial box-membership is the first conjunct of the eval-decidable certificate.\<close>
  fix f assume "f \<in> set nfluents"
  thus "fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f"
    using assms unfolding is_gbound_inv'_def by blast
next
  \<comment> \<open>STEP: on any in-bounds valuation satisfying the snap guard, the update RHS lands in bounds.\<close>
  fix s f e w
  assume sAll: "s \<in> all_snaps"
     and fe: "(f, e) \<in> set (upds s)"
     and wfib: "fluent_in_bounds w"
     and wpre: "sat_comps w (set (n_pre s))"
  have wok: "num_val_ok w" using wfib by (rule fluent_in_bounds_imp_num_val_ok)
  \<comment> \<open>@{const nexp_ok} of the RHS and @{const comp_ok} of the guards, from the grounder-match contract.\<close>
  have okE: "nexp_ok w e" and preOk: "\<forall>c \<in> set (n_pre s). comp_ok w c"
  proof -
    from sAll obtain a where a: "a \<in> set actions"
      and s: "s = at_start a \<or> s = at_end a"
      unfolding all_snaps_def by blast
    from s show "nexp_ok w e"
    proof
      assume "s = at_start a"
      thus ?thesis using snap_upds_nexp_ok_start a wok fe by fastforce
    next
      assume "s = at_end a"
      thus ?thesis using snap_upds_nexp_ok_end a wok fe by fastforce
    qed
    from s show "\<forall>c \<in> set (n_pre s). comp_ok w c"
    proof
      assume "s = at_start a"
      thus ?thesis using snap_pre_comp_ok_start a wok by fastforce
    next
      assume "s = at_end a"
      thus ?thesis using snap_pre_comp_ok_end a wok by fastforce
    qed
  qed
  \<comment> \<open>@{term w} inhabits every guard-refined interval (@{thm refine_box_sound}), so the refined
     box is nonempty on every declared fluent -- the certificate's emptiness escape is refuted.\<close>
  have nonempty: "\<not> (\<exists>g \<in> set nfluents.
       snd (refine_box (n_pre s) box g) < fst (refine_box (n_pre s) box g))"
  proof
    assume "\<exists>g \<in> set nfluents.
       snd (refine_box (n_pre s) box g) < fst (refine_box (n_pre s) box g)"
    then obtain g where g: "g \<in> set nfluents"
      and glt: "snd (refine_box (n_pre s) box g) < fst (refine_box (n_pre s) box g)"
      by blast
    obtain r where "fst (refine_box (n_pre s) box g) \<le> const_to_int r"
      and "const_to_int r \<le> snd (refine_box (n_pre s) box g)"
      using refine_box_sound[OF wfib wpre preOk g] by blast
    thus False using glt by linarith
  qed
  \<comment> \<open>the certificate's step conjunct, specialised to this snap and update, gives a bounding box.\<close>
  have "(\<exists>g \<in> set nfluents.
           snd (refine_box (n_pre s) box g) < fst (refine_box (n_pre s) box g))
      \<or> (\<forall>(f, e) \<in> set (upds s).
           case aeval (refine_box (n_pre s) box) e of
             None \<Rightarrow> False
           | Some (al, ah) \<Rightarrow> fluent_lo f \<le> al \<and> ah \<le> fluent_hi f)"
    using assms sAll unfolding is_gbound_inv'_def by blast
  hence "case aeval (refine_box (n_pre s) box) e of None \<Rightarrow> False
        | Some (al, ah) \<Rightarrow> fluent_lo f \<le> al \<and> ah \<le> fluent_hi f"
    using nonempty fe by fastforce
  then obtain al ah where
      aev: "aeval (refine_box (n_pre s) box) e = Some (al, ah)"
    and flo: "fluent_lo f \<le> al" and fhi: "ah \<le> fluent_hi f"
    by (cases "aeval (refine_box (n_pre s) box) e") auto
  \<comment> \<open>each read fluent of @{term e} sits inside the guard-refined box (via @{thm refine_box_sound}).\<close>
  have boxmem: "\<exists>r. w g = Some r \<and> r \<in> \<int>
                    \<and> fst (refine_box (n_pre s) box g) \<le> const_to_int r
                    \<and> const_to_int r \<le> snd (refine_box (n_pre s) box g)"
    if "g \<in> nexp_fluents e" for g
  proof -
    have "g \<in> set nfluents" using nexp_ok_fluents_bnd[OF okE] that by blast
    thus ?thesis using refine_box_sound[OF wfib wpre preOk] by blast
  qed
  \<comment> \<open>soundness of the interval eval lands @{term \<open>const_to_int r\<close>} in @{term \<open>[al, ah]\<close>}.\<close>
  obtain r where r: "eval_nexp w e = Some r" "r \<in> \<int>"
    and rlo: "al \<le> const_to_int r" and rhi: "const_to_int r \<le> ah"
    using aeval_sound[OF boxmem okE aev] by blast
  have "fluent_lo f \<le> const_to_int r" using flo rlo by simp
  moreover have "const_to_int r \<le> fluent_hi f" using fhi rhi by simp
  ultimately show "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
                       \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
    using r by blast
qed

end


text \<open>WP-E discharge locale over the PRIMED injective reduction (the @{const AtStart}/@{const AtEnd}
  relabeled snaps): the exact analog of @{locale numeric_tp_nta_reduction_correctness'} but assuming
  the \<^emph>\<open>checkable\<close> certificate @{text \<open>reduction_ref_impl.num_bound_inv\<close>} in place of the
  reachability invariant @{text num_seq_in_bounds}. Re-obtains @{locale numeric_tp_nta_reduction_bounds}
  at the injective snaps (which itself bridges to @{locale numeric_tp_nta_reduction_correctness}).\<close>
locale numeric_tp_nta_reduction_bounds' =
  tp_nta_reduction_correctness'
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name +
  numeric_tp_nta_reduction_defs'
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
    n_pre n_inv upds num_init num_goal nfluents fluent_to_name fluent_lo fluent_hi const_to_int +
  num_plan: numeric_temp_plan_for_problem_list_impl_int'
    at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>
    "set o n_pre" "set o n_inv" "set o upds"
    "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal" +
  fluent_names: unique_names fluent_to_name "set nfluents"
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
  assumes upds_functional_start:   "\<forall>a \<in> set actions. upds_functional_list (upds (at_start a))"
      and upds_functional_end:     "\<forall>a \<in> set actions. upds_functional_list (upds (at_end a))"
      and upds_no_cross_read_start: "\<forall>a \<in> set actions. upds_no_cross_read_list (upds (at_start a))"
      and upds_no_cross_read_end:   "\<forall>a \<in> set actions. upds_no_cross_read_list (upds (at_end a))"
      and fluent_bounds_valid:      "\<forall>f \<in> set nfluents. fluent_lo f \<le> fluent_hi f"
      and snap_upds_nexp_ok_start:
            "\<forall>a \<in> set actions. \<forall>w. reduction_ref_impl.num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_start a)). reduction_ref_impl.nexp_ok w e)"
      and snap_upds_nexp_ok_end:
            "\<forall>a \<in> set actions. \<forall>w. reduction_ref_impl.num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_end a)). reduction_ref_impl.nexp_ok w e)"
      and snap_pre_comp_ok_start:
            "\<forall>a \<in> set actions. \<forall>w. reduction_ref_impl.num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_start a)). reduction_ref_impl.comp_ok w c)"
      and snap_pre_comp_ok_end:
            "\<forall>a \<in> set actions. \<forall>w. reduction_ref_impl.num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_end a)). reduction_ref_impl.comp_ok w c)"
      and snap_inv_comp_ok:
            "\<forall>a \<in> set actions. \<forall>w. reduction_ref_impl.num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_inv a). reduction_ref_impl.comp_ok w c)"
      and num_init_val_ok: "\<forall>f \<in> set nfluents. num_init f \<in> \<int>"
      and const_to_int_of_int: "const_to_int (Int.of_int m) = m"
      and snap_writes_nfluents_start:
            "\<forall>a \<in> set actions. fst ` set (upds (at_start a)) \<subseteq> set nfluents"
      and snap_writes_nfluents_end:
            "\<forall>a \<in> set actions. fst ` set (upds (at_end a)) \<subseteq> set nfluents"
      and num_valid: "num_plan.num_rat_impl.num_valid_plan"
      \<comment> \<open>The checkable static certificate over the PRIMED injective reduction. @{text num_bound_inv} lives in
         the AXIOM locale @{locale numeric_tp_nta_reduction}, which has no interpretation at the injective
         snaps (only the defs locale is interpreted there, as @{text reduction_ref_impl}); so it is named
         here as the raw constant applied to the injective parameters -- exactly the @{text bound_inv}
         obligation the @{text ref_bounds} sublocale below produces.\<close>
      and bound_inv: "numeric_tp_nta_reduction.num_bound_inv AtStart AtEnd actions
            (rat_impl.set_impl.app_snap n_pre) (rat_impl.set_impl.app_snap upds)
            num_init nfluents fluent_lo fluent_hi const_to_int"
      and num_goal_comp_ok:
            "\<And>w. reduction_ref_impl.num_val_ok w \<Longrightarrow> (\<forall>c \<in> set num_goal. reduction_ref_impl.comp_ok w c)"
begin

text \<open>Instantiate the numeric snap-relabeling equivalence at the raw rat-refined numeric plan
@{text num_plan.num_rat_impl}: its update sets are functional on plan happenings (grounder
well-formedness) and it is numerically mutex-valid (a conjunct of @{text num_valid}).\<close>
sublocale nre: num_relabel_equiv at_start at_end "set o over_all"
  "map_option (map_lower_bound rat_of_int) o lower" "map_option (map_upper_bound rat_of_int) o upper"
  "set o pre" "set o adds" "set o dels" "set init" "set goal"
  "rat_of_int \<epsilon>" "map_option (map_prod id (map_prod rat_of_int rat_of_int)) o \<pi>"
  "set o n_pre" "set o n_inv" "set o upds"
  "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
  apply unfold_locales
  subgoal premises p for t s
  proof -
    have hts: "(t, s) \<in> rat_impl.plan_happ_seq" using p by (rule rat_impl.in_happ_atD)
    from rat_impl.in_happ_seq_exD_act[OF hts] obtain a tt d where
      a: "(a, tt, d) \<in> ran (map_option (map_prod id (map_prod rat_of_int rat_of_int)) o \<pi>)"
      and s: "at_start a = s \<or> at_end a = s" by blast
    have "a \<in> valid_plan_valid_2.plan2.plan_actions"
      using a unfolding valid_plan_valid_2.plan2.plan_actions_def by blast
    hence ain: "a \<in> set actions"
      using pap unfolding restr_to_props_valid.plan_actions_in_problem_def by blast
    show "upds_functional ((set o upds) s)"
    proof (cases "at_start a = s")
      case True
      hence "upds_functional_list (upds (at_start a))" using ain upds_functional_start by blast
      thus ?thesis using True by (simp add: upds_functional_set upds_functional_list_def)
    next
      case False
      hence "at_end a = s" using s by simp
      hence "upds_functional_list (upds (at_end a))" using ain upds_functional_end by blast
      thus ?thesis using \<open>at_end a = s\<close> by (simp add: upds_functional_set upds_functional_list_def)
    qed
  qed
  subgoal
    using num_valid unfolding num_plan.num_rat_impl.num_valid_plan_def by blast
  done

sublocale ref_bounds: numeric_tp_nta_reduction_bounds
  "rat_impl.list_inter props init" "rat_impl.list_inter props goal"
  AtStart AtEnd rat_impl.over_all_restr_list lower upper
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  \<epsilon> props actions \<pi> act_to_name prop_to_name
  "rat_impl.set_impl.app_snap n_pre" n_inv "rat_impl.set_impl.app_snap upds"
  num_init num_goal nfluents fluent_to_name fluent_lo fluent_hi const_to_int
  apply unfold_locales
                      apply (simp_all add: upds_functional_start upds_functional_end
        upds_no_cross_read_start upds_no_cross_read_end fluent_bounds_valid
        num_init_val_ok const_to_int_of_int
        snap_writes_nfluents_start snap_writes_nfluents_end
        snap_upds_nexp_ok_start snap_upds_nexp_ok_end
        snap_pre_comp_ok_start snap_pre_comp_ok_end snap_inv_comp_ok num_goal_comp_ok)
  \<comment> \<open>Remaining goals 1--2: the numeric plan-validity / state-sequence TRANSFER under the
     restrict-to-props + @{const AtStart}/@{const AtEnd} relabeling (numeric analog of the
     propositional @{text restr_to_props_valid}). Numeric conjuncts are transferred via the
     @{locale num_relabel_equiv} interpretation \<open>nre\<close> (fold reparametrization + happening
     reindexing); propositional conjuncts reuse the restrict-to-props machinery
     (@{text conc_ref_impl}/\<open>vp\<close>) and the raw propositional plan (\<open>rat_impl.valid_plan\<close>).\<close>
  subgoal
  proof -
    have bu: "(set \<circ>\<circ>\<circ> action_defs.app_snap at_start) at_end upds = num_plan.num_rat_impl.upds_imp"
      by (rule ext, rename_tac x, case_tac x) (simp_all add: num_plan.num_rat_impl.upds_imp_def)
    have bp: "(set \<circ>\<circ>\<circ> action_defs.app_snap at_start) at_end n_pre = num_plan.num_rat_impl.n_pre_imp"
      by (rule ext, rename_tac x, case_tac x) (simp_all add: num_plan.num_rat_impl.n_pre_imp_def)
    obtain M where
      rvss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and r0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and rsg: "sat_comps (snd (M (length valid_plan_valid_2.plan2.htpl))) (set num_goal)"
      and rnm: "num_plan.num_rat_impl.num_mutex_valid_plan"
      using num_valid unfolding num_plan.num_rat_impl.num_valid_plan_def by blast
    obtain MS where
      pvss: "valid_plan_valid_2.plan2.valid_state_sequence MS"
      and p0: "MS 0 = set (filter (\<lambda>p. p \<in> set props) init)"
      and pg: "set (filter (\<lambda>p. p \<in> set props) goal) \<subseteq> MS (length valid_plan_valid_2.plan2.htpl)"
      and pmx: "valid_plan_valid_2.plan2.mutex_valid_plan"
      and pdg: "valid_plan_valid_2.plan2.durations_ge_0"
      and pdv: "valid_plan_valid_2.plan2.durations_valid"
      and pfp: "valid_plan_valid_2.plan2.finite_plan"
      using conc_ref_impl.vp unfolding valid_plan_valid_2.plan2.valid_plan_def by blast
    define M' where "M' = (\<lambda>i. (MS i, snd (M i)))"
    have fin: "finite {s. (t, s) \<in> valid_plan_valid_2.plan2.plan_happ_seq}" for t
    proof -
      have "{s. (t, s) \<in> valid_plan_valid_2.plan2.plan_happ_seq} \<subseteq> snd ` valid_plan_valid_2.plan2.plan_happ_seq"
        by force
      thus ?thesis using valid_plan_ref_valid_2.valid_plan2.finite_happ_seq by (blast intro: finite_subset)
    qed
    have vss': "numeric_temp_plan_defs.num_valid_state_sequence AtStart AtEnd ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.over_all_restr_list) over_all props) ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.pre_imp_restr_list at_start at_end) pre props) ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.add_imp_list at_start) at_end adds) ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.del_imp_list at_start) at_end dels) (map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>) num_plan.num_rat_impl.n_pre_imp (set \<circ> n_inv) num_plan.num_rat_impl.upds_imp M'"
      unfolding numeric_temp_plan_defs.num_valid_state_sequence_def[OF num_plan.num_rat_impl.numeric_temp_plan_defs_axioms] Let_def
    proof (intro allI impI)
      fix i assume ilt: "i < length valid_plan_valid_2.plan2.htpl"
      from pvss ilt have PROP:
        "ref_correctness.planning_sem.apply_effects (ref_correctness.planning_sem.snap_at valid_plan_valid_2.plan2.plan_happ_seq (valid_plan_valid_2.plan2.time_index i)) (MS i) = MS (Suc i)
         \<and> ref_correctness.planning_sem.invs_at valid_plan_valid_2.plan2.plan_inv_seq (valid_plan_valid_2.plan2.time_index i) \<subseteq> MS i
         \<and> \<Union> ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.pre_imp_restr_list at_start at_end) pre props ` ref_correctness.planning_sem.snap_at valid_plan_valid_2.plan2.plan_happ_seq (valid_plan_valid_2.plan2.time_index i)) \<subseteq> MS i"
        unfolding valid_plan_valid_2.plan2.valid_state_sequence_def Let_def by blast
      note NUM = nre.num_seq_transfer[OF rvss ilt fin]
      show "ref_correctness.planning_sem.apply_effects (ref_correctness.planning_sem.snap_at valid_plan_valid_2.plan2.plan_happ_seq (valid_plan_valid_2.plan2.time_index i)) (fst (M' i)) = fst (M' (Suc i))
         \<and> ref_correctness.planning_sem.invs_at valid_plan_valid_2.plan2.plan_inv_seq (valid_plan_valid_2.plan2.time_index i) \<subseteq> fst (M' i)
         \<and> \<Union> ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.pre_imp_restr_list at_start at_end) pre props ` ref_correctness.planning_sem.snap_at valid_plan_valid_2.plan2.plan_happ_seq (valid_plan_valid_2.plan2.time_index i)) \<subseteq> fst (M' i)
         \<and> nre.plan2.happening_num_update_set (ref_correctness.planning_sem.snap_at valid_plan_valid_2.plan2.plan_happ_seq (valid_plan_valid_2.plan2.time_index i)) (snd (M' i)) = snd (M' (Suc i))
         \<and> (\<forall>s\<in>ref_correctness.planning_sem.snap_at valid_plan_valid_2.plan2.plan_happ_seq (valid_plan_valid_2.plan2.time_index i). sat_comps (snd (M' i)) (num_plan.num_rat_impl.n_pre_imp s))
         \<and> (\<forall>a\<in>nre.plan2.active_actions (valid_plan_valid_2.plan2.time_index i). sat_comps (snd (M' i)) ((set \<circ> n_inv) a))"
        using PROP NUM by (simp add: M'_def)
    qed
    have nmx': "numeric_temp_plan_defs.num_mutex_valid_plan AtStart AtEnd ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.pre_imp_restr_list at_start at_end) pre props) ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.add_imp_list at_start) at_end adds) ((set \<circ>\<circ>\<circ> temp_planning_problem_list_defs.del_imp_list at_start) at_end dels) (rat_of_int \<epsilon>) (map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>) num_plan.num_rat_impl.n_pre_imp num_plan.num_rat_impl.upds_imp"
      unfolding numeric_temp_plan_defs.num_mutex_valid_plan_def[OF num_plan.num_rat_impl.numeric_temp_plan_defs_axioms]
      using pmx nre.num_clauses2[OF rnm] by blast
    have pg': "{x \<in> set goal. x \<in> set props} \<subseteq> MS (length valid_plan_valid_2.plan2.htpl)"
      using pg by (simp add: set_filter)
    have p0': "MS 0 = {x \<in> set init. x \<in> set props}" using p0 by (simp add: set_filter)
    show ?thesis
      unfolding bu bp numeric_temp_plan_defs.num_valid_plan_def[OF num_plan.num_rat_impl.numeric_temp_plan_defs_axioms]
      by (intro exI[of _ M'] conjI vss' nmx' pdg pdv pfp)
         (simp_all add: M'_def r0 rsg p0' pg')
  qed
  subgoal by (fact bound_inv)
  done

end

end

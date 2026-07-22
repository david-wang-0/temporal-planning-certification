theory TP_NTA_Reduction_Numeric_Model_Checking
  imports TP_NTA_Reduction_Correctness TP_NTA_Reduction_Numeric_Defs
begin

subsection \<open>Generic fold reparametrization under a collapsing reindex\<close>

text \<open>Two auxiliary facts on @{const comp_fun_commute_on} obtained by reindexing a commuting family
through a map @{term phi}, followed by the key reparametrization lemma: folding @{term g} over a set
@{term T} equals folding @{term h} over the image @{term \<open>phi ` T\<close>}, even when @{term phi} is not
injective, provided every collapsed duplicate acts as the identity (@{term \<open>h (phi x) = id\<close>}). This is
the numeric analog of the propositional idempotent-union transfer: a non-idempotent fold survives a
snap relabeling that merges snaps only when the merged snaps are numeric no-ops.\<close>

lemma cfc_on_via_reindex:
  assumes gh: "\<And>a. a \<in> S \<Longrightarrow> g a = h (phi a)"
      and comm: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> h (phi a) \<circ> h (phi b) = h (phi b) \<circ> h (phi a)"
    shows "comp_fun_commute_on S g"
proof
  fix a b assume ab: "a \<in> S" "b \<in> S"
  show "g b \<circ> g a = g a \<circ> g b"
  proof (cases "a = b")
    case True thus ?thesis by simp
  next
    case False
    have "g a = h (phi a)" and "g b = h (phi b)" using ab gh by auto
    thus ?thesis using comm[of b a] ab False by simp
  qed
qed

lemma cfc_on_image:
  assumes comm: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> h (phi a) \<circ> h (phi b) = h (phi b) \<circ> h (phi a)"
    shows "comp_fun_commute_on (phi ` S) h"
proof
  fix a b assume ab: "a \<in> phi ` S" "b \<in> phi ` S"
  from ab obtain a' b' where a': "a' \<in> S" "a = phi a'" and b': "b' \<in> S" "b = phi b'" by auto
  show "h b \<circ> h a = h a \<circ> h b"
  proof (cases "a = b")
    case True thus ?thesis by simp
  next
    case False
    hence "a' \<noteq> b'" using a' b' by auto
    thus ?thesis using comm[of b' a'] a' b' by simp
  qed
qed

lemma fold_reindex_collapse:
  fixes phi :: "'b \<Rightarrow> 'a" and g :: "'b \<Rightarrow> 'c \<Rightarrow> 'c" and h :: "'a \<Rightarrow> 'c \<Rightarrow> 'c"
  assumes fin: "finite T"
  shows "(\<forall>x\<in>T. g x = h (phi x)) \<Longrightarrow>
         (\<forall>x\<in>T. \<forall>y\<in>T. x \<noteq> y \<longrightarrow> h (phi x) \<circ> h (phi y) = h (phi y) \<circ> h (phi x)) \<Longrightarrow>
         (\<forall>x\<in>T. \<forall>y\<in>T. x \<noteq> y \<longrightarrow> phi x = phi y \<longrightarrow> h (phi x) = id) \<Longrightarrow>
         Finite_Set.fold g v T = Finite_Set.fold h v (phi ` T)"
  using fin
proof (induction T rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert x F)
  have ghI: "\<And>z. z \<in> insert x F \<Longrightarrow> g z = h (phi z)" using insert.prems(1) by blast
  have commI: "\<And>z w. z \<in> insert x F \<Longrightarrow> w \<in> insert x F \<Longrightarrow> z \<noteq> w
                 \<Longrightarrow> h (phi z) \<circ> h (phi w) = h (phi w) \<circ> h (phi z)" using insert.prems(2) by blast
  have collI: "\<And>z w. z \<in> insert x F \<Longrightarrow> w \<in> insert x F \<Longrightarrow> z \<noteq> w \<Longrightarrow> phi z = phi w
                 \<Longrightarrow> h (phi z) = id" using insert.prems(3) by blast
  have gh_F: "\<forall>z\<in>F. g z = h (phi z)" using insert.prems(1) by blast
  have comm_F: "\<forall>z\<in>F. \<forall>w\<in>F. z \<noteq> w \<longrightarrow> h (phi z) \<circ> h (phi w) = h (phi w) \<circ> h (phi z)"
    using insert.prems(2) by blast
  have coll_F: "\<forall>z\<in>F. \<forall>w\<in>F. z \<noteq> w \<longrightarrow> phi z = phi w \<longrightarrow> h (phi z) = id"
    using insert.prems(3) by blast
  have IH: "Finite_Set.fold g v F = Finite_Set.fold h v (phi ` F)"
    using insert.IH[OF gh_F comm_F coll_F] .
  have cfc_g: "comp_fun_commute_on (insert x F) g" using ghI commI by (rule cfc_on_via_reindex)
  have cfc_h: "comp_fun_commute_on (phi ` insert x F) h" using commI by (rule cfc_on_image)
  have LHS: "Finite_Set.fold g v (insert x F) = h (phi x) (Finite_Set.fold h v (phi ` F))"
  proof -
    have "Finite_Set.fold g v (insert x F) = g x (Finite_Set.fold g v F)"
      by (rule comp_fun_commute_on.fold_insert[OF cfc_g subset_refl insert.hyps(1) insert.hyps(2)])
    also have "\<dots> = h (phi x) (Finite_Set.fold g v F)" using insert.prems(1) by simp
    also have "\<dots> = h (phi x) (Finite_Set.fold h v (phi ` F))" using IH by simp
    finally show ?thesis .
  qed
  show ?case
  proof (cases "phi x \<in> phi ` F")
    case True
    have img: "phi ` insert x F = phi ` F" using True by auto
    obtain y where y: "y \<in> F" "phi y = phi x" using True by auto
    have "h (phi x) = id" using collI[of x y] y insert.hyps(2) by auto
    thus ?thesis using LHS img by simp
  next
    case False
    have img2: "phi ` insert x F = insert (phi x) (phi ` F)" by auto
    have "Finite_Set.fold h v (insert (phi x) (phi ` F)) = h (phi x) (Finite_Set.fold h v (phi ` F))"
      by (rule comp_fun_commute_on.fold_insert[OF cfc_h[unfolded img2] subset_refl finite_imageI[OF insert.hyps(1)] False])
    thus ?thesis using LHS img2 by simp
  qed
qed


text \<open>A snap's update @{term set} is functional (a partial function) when its association list has
distinct keys -- the @{const upds_functional_list} well-formedness the grounder guarantees. (Inlined
here, above the numeric correctness locale, since the downstream \<open>upds_functional_set\<close> is not yet in
scope.)\<close>
lemma upds_functional_set:
  assumes "distinct (map fst us)"
  shows "upds_functional (set us)"
proof -
  have "e = e'" if "(f, e) \<in> set us" and "(f, e') \<in> set us" for f e e'
    using that assms by (metis map_of_is_SomeI option.inject)
  thus ?thesis unfolding upds_functional_def by auto
qed

subsection \<open>Numeric snap-relabeling equivalence (@{const AtStart}/@{const AtEnd})\<close>

text \<open>The numeric analog of the propositional \<open>plan_validity_equivalence\<close>, specialised to the
\<open>AtStart\<close>/\<open>AtEnd\<close> relabeling. A raw numeric temporal plan (over the abstract snap type
\<open>'snap_action\<close>) is placed alongside its annotated twin \<open>plan2\<close> (over \<open>'action snap_action\<close>,
using the \<open>app_snap\<close>-lifted numeric data \<open>n_pre_imp\<close> / \<open>upds_imp\<close>). The reindexing map
\<open>phi = case_snap_action at_start at_end\<close> sends an annotated snap back to the raw snap it stands for; it
need not be injective, so two annotated snaps may collapse -- but only when they are a numeric no-op,
which is exactly the situation \<open>fold_reindex_collapse\<close> handles. The two assumptions are: every plan
happening has functional updates, and the plan is numerically mutex-valid (both hold for a valid
numeric plan).\<close>
locale num_relabel_equiv =
  numeric_temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
    n_pre n_inv upds num_init num_goal
  for at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end   :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition set"
    and lower    :: "'action \<rightharpoonup> ('time::time) lower_bound"
    and upper    :: "'action \<rightharpoonup> 'time upper_bound"
    and pre      :: "'snap_action \<Rightarrow> 'proposition set"
    and adds     :: "'snap_action \<Rightarrow> 'proposition set"
    and dels     :: "'snap_action \<Rightarrow> 'proposition set"
    and init     :: "'proposition set"
    and goal     :: "'proposition set"
    and \<epsilon>        :: "'time"
    and \<pi>        :: "('i, 'action, 'time) temp_plan"
    and n_pre    :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp set"
    and n_inv    :: "'action \<Rightarrow> ('n, 'r) comp set"
    and upds     :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) set"
    and num_init :: "'n \<rightharpoonup> 'r"
    and num_goal :: "('n, 'r) comp set" +
  assumes hfun: "\<And>t s. s \<in> happ_at plan_happ_seq t \<Longrightarrow> upds_functional (upds s)"
      and nmvp: "num_mutex_valid_plan"
begin

definition phi :: "'action snap_action \<Rightarrow> 'snap_action" where
  "phi = case_snap_action at_start at_end"

lemma phi_simps[simp]: "phi (AtStart a) = at_start a" "phi (AtEnd a) = at_end a"
  by (simp_all add: phi_def)

sublocale plan2: numeric_temp_plan_defs AtStart AtEnd over_all lower upper
  pre_imp add_imp del_imp init goal \<epsilon> \<pi> n_pre_imp n_inv upds_imp num_init num_goal
  by unfold_locales

lemma upds_imp_phi: "upds_imp x = upds (phi x)"
  by (cases x) (simp_all add: upds_imp_def)

lemma n_pre_imp_phi: "n_pre_imp x = n_pre (phi x)"
  by (cases x) (simp_all add: n_pre_imp_def)

lemma snu2: "plan2.snap_num_update x = snap_num_update (phi x)"
  by (rule ext) (simp add: plan2.snap_num_update_def snap_num_update_def upds_imp_phi)

lemma htps2: "plan2.htps = htps"
  by (simp only: plan2.htps_def htps_def)

lemma htpl2: "plan2.htpl = htpl"
  unfolding plan2.htpl_def htpl_def by (rule arg_cong[OF htps2])

lemma tidx2: "plan2.time_index = time_index"
  unfolding plan2.time_index_def time_index_def by (rule arg_cong[OF htpl2])

lemma active2: "plan2.active_actions t = active_actions t"
  by (simp only: plan2.active_actions_def active_actions_def)

lemma happ_phi: "happ_at plan_happ_seq t = phi ` plan2.happ_at plan2.plan_happ_seq t"
proof (rule set_eqI, rule iffI)
  fix s assume "s \<in> happ_at plan_happ_seq t"
  hence tp: "(t, s) \<in> plan_happ_seq" by (rule in_happ_atD)
  from in_happ_seq_exD[OF tp] obtain a tt d where
    a: "(a, tt, d) \<in> ran \<pi>"
    and s: "at_start a = s \<and> t = tt \<or> at_end a = s \<and> t = tt + d" by blast
  from s show "s \<in> phi ` plan2.happ_at plan2.plan_happ_seq t"
  proof (elim disjE conjE)
    assume "at_start a = s" and "t = tt"
    hence "(t, AtStart a) \<in> plan2.plan_happ_seq" using a plan2.in_happ_seqI(1) by auto
    thus ?thesis using \<open>at_start a = s\<close> by (auto simp: image_iff intro!: bexI[of _ "AtStart a"] plan2.in_happ_atI)
  next
    assume "at_end a = s" and "t = tt + d"
    hence "(t, AtEnd a) \<in> plan2.plan_happ_seq" using a plan2.in_happ_seqI(2) by auto
    thus ?thesis using \<open>at_end a = s\<close> by (auto simp: image_iff intro!: bexI[of _ "AtEnd a"] plan2.in_happ_atI)
  qed
next
  fix s assume "s \<in> phi ` plan2.happ_at plan2.plan_happ_seq t"
  then obtain x where x: "x \<in> plan2.happ_at plan2.plan_happ_seq t" and sx: "s = phi x" by auto
  have tx: "(t, x) \<in> plan2.plan_happ_seq" using x by (rule plan2.in_happ_atD)
  from plan2.in_happ_seq_exD[OF tx] obtain a tt d where
    a: "(a, tt, d) \<in> ran \<pi>"
    and s: "AtStart a = x \<and> t = tt \<or> AtEnd a = x \<and> t = tt + d" by blast
  from s show "s \<in> happ_at plan_happ_seq t"
  proof (elim disjE conjE)
    assume "AtStart a = x" and "t = tt"
    hence "s = at_start a" using sx by auto
    thus ?thesis using a \<open>t = tt\<close> by (auto intro: in_happ_atI in_happ_seqI(1))
  next
    assume "AtEnd a = x" and "t = tt + d"
    hence "s = at_end a" using sx by auto
    thus ?thesis using a \<open>t = tt + d\<close> by (auto intro: in_happ_atI in_happ_seqI(2))
  qed
qed

text \<open>Two distinct annotated snaps co-occurring in one happening do not numerically interfere as raw
snaps -- the numeric analog of @{text mutex_not_in_same_instant}, read off @{const num_mutex_valid_plan}
(the raw @{const num_mutex_snap_action} being invariant under @{const phi}). Covers both a
@{const phi}-collision (the two snaps map to the same raw snap: instant self-pair) and genuinely
distinct raw snaps.\<close>
lemma noninterfere2:
  assumes x: "x \<in> plan2.happ_at plan2.plan_happ_seq t"
      and y: "y \<in> plan2.happ_at plan2.plan_happ_seq t"
      and xy: "x \<noteq> y"
    shows "\<not> num_mutex_snap_action (phi x) (phi y)"
proof -
  have hx: "(t, x) \<in> plan2.plan_happ_seq" using x by (rule plan2.in_happ_atD)
  have hy: "(t, y) \<in> plan2.plan_happ_seq" using y by (rule plan2.in_happ_atD)
  from plan2.in_happ_seq_exD[OF hx] obtain a ta da where
    A: "(a, ta, da) \<in> ran \<pi>"
    and ax: "AtStart a = x \<and> t = ta \<or> AtEnd a = x \<and> t = ta + da" by blast
  from plan2.in_happ_seq_exD[OF hy] obtain b tb db where
    B: "(b, tb, db) \<in> ran \<pi>"
    and byy: "AtStart b = y \<and> t = tb \<or> AtEnd b = y \<and> t = tb + db" by blast
  obtain k where k: "\<pi> k = Some (a, ta, da)" using A unfolding ran_def by blast
  obtain l where l: "\<pi> l = Some (b, tb, db)" using B unfolding ran_def by blast
  have kdom: "k \<in> dom \<pi>" using k by blast
  have ldom: "l \<in> dom \<pi>" using l by blast
  note nm = nmvp[unfolded num_mutex_valid_plan_def]
  have px: "phi x = at_start a \<and> t = ta \<or> phi x = at_end a \<and> t = ta + da" using ax by auto
  have py: "phi y = at_start b \<and> t = tb \<or> phi y = at_end b \<and> t = tb + db" using byy by auto
  have distinct_clause: "\<not> num_mutex_snap_action sa sb"
    if "k' \<in> dom \<pi>" "l' \<in> dom \<pi>" "k' \<noteq> l'"
       "\<pi> k' = Some (a', ta', da')" "\<pi> l' = Some (b', tb', db')"
       "sa = at_start a' \<and> tt = ta' \<or> sa = at_end a' \<and> tt = ta' + da'"
       "sb = at_start b' \<and> u = tb' \<or> sb = at_end b' \<and> u = tb' + db'"
       "tt - u < \<epsilon> \<and> u - tt < \<epsilon> \<or> tt = u"
     for k' l' a' ta' da' b' tb' db' sa sb tt u
    using nm that by blast
  have instant_clause: "\<not> num_mutex_snap_action (at_start a') (at_end a')"
    if "(a', tt, d') \<in> ran \<pi>" "d' = 0 \<or> d' < \<epsilon>" for a' tt d'
    using nm that by blast
  show ?thesis
  proof (cases "k = l")
    case False
    have tt: "t - t < \<epsilon> \<and> t - t < \<epsilon> \<or> t = t" by simp
    show ?thesis by (rule distinct_clause[OF kdom ldom False k l px py tt])
  next
    case True
    hence eq: "a = b" "ta = tb" "da = db" using k l by auto
    have da0: "da = 0" using ax byy xy eq by auto
    have ni: "\<not> num_mutex_snap_action (at_start a) (at_end a)"
      by (rule instant_clause[OF A]) (simp add: da0)
    have "phi x = at_start a \<and> phi y = at_end a \<or> phi x = at_end a \<and> phi y = at_start a"
      using ax byy xy eq by auto
    thus ?thesis using ni by (metis num_mutex_snap_action_refl)
  qed
qed

text \<open>The crux: the annotated numeric happening update equals the raw one. The annotated happening's
snaps are distinct; folding \<open>plan2.snap_num_update\<close> over them equals folding
\<open>snap_num_update\<close> over the (possibly-collapsed) raw happening, because \<open>noninterfere2\<close>
gives pairwise non-interference (so the folds commute) and forces any \<open>phi\<close>-collision to be a
numeric no-op.\<close>
lemma fold2:
  assumes fin: "finite (plan2.happ_at plan2.plan_happ_seq t)"
  shows "plan2.happening_num_update_set (plan2.happ_at plan2.plan_happ_seq t) v
           = happening_num_update_set (happ_at plan_happ_seq t) v"
proof -
  let ?T = "plan2.happ_at plan2.plan_happ_seq t"
  have fld: "Finite_Set.fold plan2.snap_num_update v ?T
               = Finite_Set.fold snap_num_update v (phi ` ?T)"
  proof (rule fold_reindex_collapse[OF fin])
    show "\<forall>x\<in>?T. plan2.snap_num_update x = snap_num_update (phi x)" using snu2 by blast
  next
    show "\<forall>x\<in>?T. \<forall>y\<in>?T. x \<noteq> y
            \<longrightarrow> snap_num_update (phi x) \<circ> snap_num_update (phi y)
                 = snap_num_update (phi y) \<circ> snap_num_update (phi x)"
    proof (intro ballI impI)
      fix x y assume xy: "x \<in> ?T" "y \<in> ?T" "x \<noteq> y"
      have "phi x \<in> happ_at plan_happ_seq t" using xy(1) by (simp add: happ_phi)
      hence fx: "upds_functional (upds (phi x))" by (rule hfun)
      have "phi y \<in> happ_at plan_happ_seq t" using xy(2) by (simp add: happ_phi)
      hence fy: "upds_functional (upds (phi y))" by (rule hfun)
      have nm: "\<not> num_mutex_snap_action (phi x) (phi y)" using xy by (rule noninterfere2)
      show "snap_num_update (phi x) \<circ> snap_num_update (phi y)
              = snap_num_update (phi y) \<circ> snap_num_update (phi x)"
        by (rule ext) (simp add: snap_num_update_commute[OF fx fy nm] comp_def)
    qed
  next
    show "\<forall>x\<in>?T. \<forall>y\<in>?T. x \<noteq> y \<longrightarrow> phi x = phi y \<longrightarrow> snap_num_update (phi x) = id"
    proof (intro ballI impI)
      fix x y assume xy: "x \<in> ?T" "y \<in> ?T" "x \<noteq> y" and eq: "phi x = phi y"
      have nm: "\<not> num_mutex_snap_action (phi x) (phi y)" using xy by (rule noninterfere2)
      hence "\<not> num_mutex_snap_action (phi x) (phi x)" using eq by simp
      hence "snap_writes (phi x) \<inter> snap_writes (phi x) = {}"
        unfolding num_mutex_snap_action_def by blast
      hence "upds (phi x) = {}" unfolding snap_writes_def by simp
      thus "snap_num_update (phi x) = id"
        by (simp add: fun_eq_iff snap_num_update_empty)
    qed
  qed
  show ?thesis using fld
    by (simp add: plan2.happening_num_update_set_def happening_num_update_set_def happ_phi)
qed

text \<open>The numeric-conjunct transfer: a raw numeric state sequence's fold / precondition / invariant
checks carry over to the annotated (@{text plan2}) side, index by index. The propositional conjuncts
are handled separately by the caller (via the restrict-to-props propositional validity).\<close>
lemma num_seq_transfer:
  assumes vss: "num_valid_state_sequence M"
      and i: "i < length htpl"
      and fin: "finite (plan2.happ_at plan2.plan_happ_seq (time_index i))"
    shows "plan2.happening_num_update_set (plan2.happ_at plan2.plan_happ_seq (time_index i)) (snd (M i))
             = snd (M (Suc i))"
      and "\<forall>s \<in> plan2.happ_at plan2.plan_happ_seq (time_index i). sat_comps (snd (M i)) (n_pre_imp s)"
      and "\<forall>a \<in> active_actions (time_index i). sat_comps (snd (M i)) (n_inv a)"
proof -
  have rawfold: "happening_num_update_set (happ_at plan_happ_seq (time_index i)) (snd (M i)) = snd (M (Suc i))"
    and rawnpre: "\<forall>s \<in> happ_at plan_happ_seq (time_index i). sat_comps (snd (M i)) (n_pre s)"
    and rawninv: "\<forall>a \<in> active_actions (time_index i). sat_comps (snd (M i)) (n_inv a)"
    using vss i unfolding num_valid_state_sequence_def Let_def by auto
  show "plan2.happening_num_update_set (plan2.happ_at plan2.plan_happ_seq (time_index i)) (snd (M i))
          = snd (M (Suc i))"
    using fold2[OF fin] rawfold by simp
  show "\<forall>s \<in> plan2.happ_at plan2.plan_happ_seq (time_index i). sat_comps (snd (M i)) (n_pre_imp s)"
  proof
    fix s' assume "s' \<in> plan2.happ_at plan2.plan_happ_seq (time_index i)"
    hence "phi s' \<in> happ_at plan_happ_seq (time_index i)" using happ_phi by auto
    hence "sat_comps (snd (M i)) (n_pre (phi s'))" using rawnpre by blast
    thus "sat_comps (snd (M i)) (n_pre_imp s')" by (simp add: n_pre_imp_phi)
  qed
  show "\<forall>a \<in> active_actions (time_index i). sat_comps (snd (M i)) (n_inv a)" using rawninv .
qed

text \<open>Numeric interference of two annotated snaps is the raw interference of their @{const phi}-images
(the snap-writes/reads are the @{const app_snap}-lift of the raw ones).\<close>
lemma num_mutex_snap2: "plan2.num_mutex_snap_action x y = num_mutex_snap_action (phi x) (phi y)"
  by (simp add: plan2.num_mutex_snap_action_def num_mutex_snap_action_def
      plan2.snap_writes_def snap_writes_def plan2.snap_reads_def snap_reads_def upds_imp_phi n_pre_imp_phi)

text \<open>The two numeric mutex-schedule clauses transfer from the raw plan to the annotated one: the
annotated snap-time pairs @{term \<open>AtStart a\<close>}/@{term \<open>AtEnd a\<close>} map under @{const phi} to the raw
@{term \<open>at_start a\<close>}/@{term \<open>at_end a\<close>} at the same times, so the raw @{const num_mutex_valid_plan}
clauses apply.\<close>
lemma num_clauses2:
  assumes nm: "num_mutex_valid_plan"
  shows "\<forall>i j a ta da b tb db sa sb t u.
            i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j
            \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db)
            \<and> (sa = AtStart a \<and> t = ta \<or> sa = AtEnd a \<and> t = ta + da)
            \<and> (sb = AtStart b \<and> u = tb \<or> sb = AtEnd b \<and> u = tb + db)
            \<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
            \<longrightarrow> \<not> plan2.num_mutex_snap_action sa sb"
    and "\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> plan2.num_mutex_snap_action (AtStart a) (AtEnd a)"
proof -
  have raw1: "\<forall>i j a ta da b tb db sa sb t u.
            i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j
            \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db)
            \<and> (sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da)
            \<and> (sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db)
            \<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
            \<longrightarrow> \<not> num_mutex_snap_action sa sb"
    and raw2: "\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> num_mutex_snap_action (at_start a) (at_end a)"
    using nm unfolding num_mutex_valid_plan_def by auto
  show "\<forall>i j a ta da b tb db sa sb t u.
            i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j
            \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db)
            \<and> (sa = AtStart a \<and> t = ta \<or> sa = AtEnd a \<and> t = ta + da)
            \<and> (sb = AtStart b \<and> u = tb \<or> sb = AtEnd b \<and> u = tb + db)
            \<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
            \<longrightarrow> \<not> plan2.num_mutex_snap_action sa sb"
  proof (intro allI impI, elim conjE)
    fix i j a ta da b tb db sa sb t u
    assume A1: "i \<in> dom \<pi>" and A2: "j \<in> dom \<pi>" and A3: "i \<noteq> j"
      and A4: "\<pi> i = Some (a, ta, da)" and A5: "\<pi> j = Some (b, tb, db)"
      and A6: "sa = AtStart a \<and> t = ta \<or> sa = AtEnd a \<and> t = ta + da"
      and A7: "sb = AtStart b \<and> u = tb \<or> sb = AtEnd b \<and> u = tb + db"
      and A8: "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u"
    have psa: "phi sa = at_start a \<and> t = ta \<or> phi sa = at_end a \<and> t = ta + da"
      using A6 by (auto simp: phi_simps)
    have psb: "phi sb = at_start b \<and> u = tb \<or> phi sb = at_end b \<and> u = tb + db"
      using A7 by (auto simp: phi_simps)
    have "\<not> num_mutex_snap_action (phi sa) (phi sb)"
      using raw1 A1 A2 A3 A4 A5 psa psb A8 by blast
    thus "\<not> plan2.num_mutex_snap_action sa sb" by (simp add: num_mutex_snap2)
  qed
  show "\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> plan2.num_mutex_snap_action (AtStart a) (AtEnd a)"
  proof (rule ballI, clarify)
    fix a t d
    assume mem: "(a, t, d) \<in> ran \<pi>" and dd: "d = 0 \<or> d < \<epsilon>"
      and contra: "plan2.num_mutex_snap_action (AtStart a) (AtEnd a)"
    have "\<not> num_mutex_snap_action (at_start a) (at_end a)" using raw2 mem dd by auto
    thus False using contra by (simp add: num_mutex_snap2)
  qed
qed

text \<open>The reverse numeric-conjunct transfer (annotated @{text plan2} fold / precondition checks back
to the raw side), used when the caller has an annotated state sequence and needs to feed a raw bounds
plug. Symmetric to @{text num_seq_transfer}: @{text fold2} is an equality, and @{text happ_phi}
reindexes the precondition check.\<close>
lemma num_seq_transfer_rev:
  assumes fin: "finite (plan2.happ_at plan2.plan_happ_seq (time_index i))"
      and F: "plan2.happening_num_update_set (plan2.happ_at plan2.plan_happ_seq (time_index i)) w = w'"
      and P: "\<forall>s \<in> plan2.happ_at plan2.plan_happ_seq (time_index i). sat_comps w (n_pre_imp s)"
    shows "happening_num_update_set (happ_at plan_happ_seq (time_index i)) w = w'"
      and "\<forall>s \<in> happ_at plan_happ_seq (time_index i). sat_comps w (n_pre s)"
proof -
  show "happening_num_update_set (happ_at plan_happ_seq (time_index i)) w = w'"
    using fold2[OF fin] F by simp
  show "\<forall>s \<in> happ_at plan_happ_seq (time_index i). sat_comps w (n_pre s)"
  proof
    fix s assume "s \<in> happ_at plan_happ_seq (time_index i)"
    then obtain s' where "s' \<in> plan2.happ_at plan2.plan_happ_seq (time_index i)" and "s = phi s'"
      using happ_phi by auto
    thus "sat_comps w (n_pre s)" using P by (auto simp: n_pre_imp_phi)
  qed
qed

end

section \<open>Numeric reduction correctness (Layer B)\<close>

text \<open>The numeric correctness locale merges three layers at the @{emph \<open>same\<close>} propositional
parameters: the propositional reduction correctness @{locale tp_nta_reduction_correctness} (which
gives the @{emph \<open>forward\<close>} direction -- a valid plan induces a goal-reaching run via @{text plan_steps}
and the step lemmas, i.e. the soundness-of-certification direction, @{emph \<open>not\<close>} a full bisimulation),
the numeric net @{locale numeric_tp_nta_reduction} (list-valued numeric data, the numeric automata
@{text num_timed_automaton_net}, and the grounder-match well-formedness), and the abstract numeric
plan layer @{locale numeric_temp_plan_for_problem_list_impl_int} instantiated at the @{text \<open>set o _\<close>}
projection of the list numeric data (so its @{text num_rat_impl} interprets @{locale
numeric_temp_plan_defs} at the rat-refined parameters, where @{text num_valid_plan} lives). The one
genuinely new assumption -- everything else is @{emph \<open>fixes\<close>}-only over shared ancestors -- is that
the numeric plan is valid (@{text num_rat_impl.num_valid_plan}), strengthening the propositional
@{text valid_plan} the reduction already assumes.\<close>
locale numeric_tp_nta_reduction_correctness =
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
      \<comment> \<open>(@{text const_to_int_of_int} — the integer-encoding faithfulness fact — is now inherited from
         the base @{locale numeric_tp_nta_reduction}, so it is no longer restated here.)\<close>
      \<comment> \<open>The range-boundedness reachability invariant (grounder-match contract, complementing the
         static integrality assumptions in @{locale numeric_tp_nta_reduction}): along any valid numeric
         state sequence the per-happening valuations stay within the declared fluent variable bounds.
         A certifier checks this against the candidate plan's finite trace; PDDL supplies no bounds, and a
         global closure over all in-range valuations would be false for monotone effects. The intermediate
         partial-fold stores within a happening are derived in range from the @{term i}/@{term \<open>Suc i\<close>}
         endpoints (each fluent is written at most once, so a partial value is one of the two endpoints).
         Indexed by @{term \<open>rat_impl.htpl\<close>}, which the later \<open>rat_impl_htpl_eq\<close> equates with
         @{term \<open>planning_sem.htpl\<close>}.\<close>
      and num_seq_in_bounds:
            "\<And>M i. num_plan.num_rat_impl.num_valid_state_sequence M
               \<Longrightarrow> snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)
               \<Longrightarrow> i \<le> length rat_impl.htpl
               \<Longrightarrow> fluent_in_bounds (snd (M i))"
      and num_goal_comp_ok:
            "\<And>w. num_val_ok w \<Longrightarrow> (\<forall>c \<in> set num_goal. comp_ok w c)"

begin

text \<open>The numeric network's Munta semantics, mirroring the propositional @{text net_impl}/@{text
graph_impl}: same broadcast channels (none), the augmented automata @{const num_timed_automaton_net},
and the augmented variable bounds @{const num_net_bounds}. @{locale Simple_Network_Impl} is
assumption-free, so this is a bare interpretation.\<close>
sublocale num_net_impl: Simple_Network_Impl num_timed_automaton_net net_broadcast num_net_bounds .
sublocale num_graph_impl: Graph_Defs
  "\<lambda>(L, s, u) (L', s', u'). step_u' num_net_impl.sem L s u L' s' u'" .

text \<open>Sanity: both nets and the numeric plan-validity are in scope at the shared parameters.\<close>
lemma num_net_in_scope: "num_timed_automaton_net = num_main_auto # map num_action_to_automaton actions"
  by (simp add: num_timed_automaton_net_def)

definition "num_a\<^sub>0 = (init_locs, map_of num_init_vars, (\<lambda>_::String.literal. 0::real))"

end

text \<open>Primed numeric correctness layer -- the numeric twin of @{locale tp_nta_reduction_correctness'}.
  It replaces the unprimed @{locale numeric_tp_nta_reduction} (which carries the inherited
  @{text snaps_disj} at the raw snaps) with the primed @{locale numeric_tp_nta_reduction_defs'} (the
  numeric net over injective @{const AtStart}/@{const AtEnd} snaps -- no snap-distinctness obligation)
  plus the numeric well-formedness as explicit assumptions over the raw snaps, and the primed numeric
  plan @{locale numeric_temp_plan_for_problem_list_impl_int'}.  The @{text ref_correctness} sublocale
  re-derives the unprimed capstone at the injective snaps.  (The @{text reduction_ref_impl}-qualified
  faithfulness predicates below -- @{text num_val_ok}/@{text nexp_ok}/@{text comp_ok}/@{text
  fluent_in_bounds} -- are snap-independent, so they are exactly the ones @{text ref_correctness}
  needs.)\<close>
locale numeric_tp_nta_reduction_correctness' =
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
      and num_seq_in_bounds:
            "\<And>M i. num_plan.num_rat_impl.num_valid_state_sequence M
               \<Longrightarrow> snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)
               \<Longrightarrow> i \<le> length rat_impl.htpl
               \<Longrightarrow> reduction_ref_impl.fluent_in_bounds (snd (M i))"
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

sublocale ref_correctness: numeric_tp_nta_reduction_correctness
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
  subgoal premises hyps for M i
  proof -
    have bu: "(set \<circ>\<circ>\<circ> action_defs.app_snap at_start) at_end upds = num_plan.num_rat_impl.upds_imp"
      by (rule ext, rename_tac x, case_tac x) (simp_all add: num_plan.num_rat_impl.upds_imp_def)
    have bp: "(set \<circ>\<circ>\<circ> action_defs.app_snap at_start) at_end n_pre = num_plan.num_rat_impl.n_pre_imp"
      by (rule ext, rename_tac x, case_tac x) (simp_all add: num_plan.num_rat_impl.n_pre_imp_def)
    obtain MSr where
      rpvss: "rat_impl.valid_state_sequence MSr" and rp0: "MSr 0 = set init"
      using vp unfolding rat_impl.valid_plan_def by blast
    define M'' where "M'' = (\<lambda>j. (MSr j, snd (M j)))"
    have fin: "finite {s. (t, s) \<in> valid_plan_valid_2.plan2.plan_happ_seq}" for t
    proof -
      have "{s. (t, s) \<in> valid_plan_valid_2.plan2.plan_happ_seq} \<subseteq> snd ` valid_plan_valid_2.plan2.plan_happ_seq"
        by force
      thus ?thesis using valid_plan_ref_valid_2.valid_plan2.finite_happ_seq by (blast intro: finite_subset)
    qed
    note RRvss = hyps(1)[unfolded numeric_temp_plan_defs.num_valid_state_sequence_def[OF num_plan.num_rat_impl.numeric_temp_plan_defs_axioms] Let_def bu bp]
    have rawvss: "num_plan.num_rat_impl.num_valid_state_sequence M''"
      unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def
    proof (intro allI impI)
      fix j assume jlt: "j < length valid_plan_valid_2.plan2.htpl"
      note RNj = RRvss[rule_format, OF jlt]
      note RNfold = RNj[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note RNnpre = RNj[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      note RNninv = RNj[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]
      from rpvss jlt have RP:
        "rat_impl.apply_effects (rat_impl.happ_at rat_impl.plan_happ_seq (valid_plan_valid_2.plan2.time_index j)) (MSr j) = MSr (Suc j)
         \<and> ref_correctness.planning_sem.invs_at unique_ref.plan_inv_seq (valid_plan_valid_2.plan2.time_index j) \<subseteq> MSr j
         \<and> \<Union> ((set \<circ> pre) ` rat_impl.happ_at rat_impl.plan_happ_seq (valid_plan_valid_2.plan2.time_index j)) \<subseteq> MSr j"
        unfolding rat_impl.valid_state_sequence_def Let_def by blast
      note REV = nre.num_seq_transfer_rev[OF fin RNfold RNnpre]
      have Rf: "fst (M'' k) = MSr k" and Rs: "snd (M'' k) = snd (M k)" for k
        by (simp_all add: M''_def)
      show "rat_impl.apply_effects (rat_impl.happ_at rat_impl.plan_happ_seq (valid_plan_valid_2.plan2.time_index j)) (fst (M'' j)) = fst (M'' (Suc j))
         \<and> ref_correctness.planning_sem.invs_at unique_ref.plan_inv_seq (valid_plan_valid_2.plan2.time_index j) \<subseteq> fst (M'' j)
         \<and> \<Union> ((set \<circ> pre) ` rat_impl.happ_at rat_impl.plan_happ_seq (valid_plan_valid_2.plan2.time_index j)) \<subseteq> fst (M'' j)
         \<and> num_plan.num_rat_impl.happening_num_update_set (rat_impl.happ_at rat_impl.plan_happ_seq (valid_plan_valid_2.plan2.time_index j)) (snd (M'' j)) = snd (M'' (Suc j))
         \<and> (\<forall>s\<in>rat_impl.happ_at rat_impl.plan_happ_seq (valid_plan_valid_2.plan2.time_index j). sat_comps (snd (M'' j)) ((set \<circ> n_pre) s))
         \<and> (\<forall>a\<in>num_plan.num_rat_impl.active_actions (valid_plan_valid_2.plan2.time_index j). sat_comps (snd (M'' j)) ((set \<circ> n_inv) a))"
        unfolding Rf Rs
        by (intro conjI; insert RP REV RNninv; blast)
    qed
    have hi: "i \<le> length rat_impl.htpl" using hyps(3) by simp
    have "reduction_ref_impl.fluent_in_bounds (snd (M'' i))"
      by (rule num_seq_in_bounds[OF rawvss _ hi]) (simp add: M''_def hyps(2))
    thus "reduction_ref_impl.fluent_in_bounds (snd (M i))" by (simp add: M''_def)
  qed
  done

end

end

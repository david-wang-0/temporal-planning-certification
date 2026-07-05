theory TP_NTA_Reduction_Numeric_Projection
  imports TP_NTA_Reduction_Numeric_Edges
begin

context numeric_tp_nta_reduction_correctness
begin

subsection \<open>Projection infrastructure for the relational lift (Option A)\<close>

text \<open>The numeric (combined) store @{term v} (@{const num_net_bounds}-bounded) splits into its
propositional projection @{term \<open>v |` dom (map_of net_bounds)\<close>} -- which is @{const net_bounds}-bounded,
so it satisfies the propositional invariants -- and its fluent part @{term \<open>v |` (fluent_to_var ` set nfluents)\<close>},
which carries @{const num_tracks}. The two domains are disjoint by @{thm [source] fluent_vars_fresh}, so
@{term v} is their @{const map_add}.\<close>

lemma dom_map_of_num_net_bounds:
  "dom (map_of num_net_bounds) = dom (map_of net_bounds) \<union> fluent_to_var ` set nfluents"
  by (auto simp: num_all_vars_def num_fluent_vars_def dom_map_of_conv_image_fst)

lemma fluent_var_notin_net_bounds:
  assumes "f \<in> set nfluents"
  shows "fluent_to_var f \<notin> dom (map_of net_bounds)"
  using fluent_vars_fresh assms by (simp add: dom_map_of_conv_image_fst)

lemma map_of_num_net_bounds_eq_on_props:
  assumes "x \<in> dom (map_of net_bounds)"
  shows "map_of num_net_bounds x = map_of net_bounds x"
  using assms by (simp add: num_all_vars_def map_of_append map_add_dom_app_simps(3))

lemma prop_proj_bounded:
  assumes "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "Simple_Network_Language.bounded (map_of net_bounds) (v |` dom (map_of net_bounds))"
proof -
  have domv: "dom v = dom (map_of num_net_bounds)"
    using assms unfolding Simple_Network_Language.bounded_def by blast
  have pv_sub: "dom (map_of net_bounds) \<subseteq> dom v"
    using domv dom_map_of_num_net_bounds by blast
  have dom_pv: "dom (v |` dom (map_of net_bounds)) = dom (map_of net_bounds)"
    using pv_sub by auto
  show ?thesis
    unfolding Simple_Network_Language.bounded_def
  proof (intro conjI)
    show "dom (v |` dom (map_of net_bounds)) = dom (map_of net_bounds)" by (rule dom_pv)
  next
    show "\<forall>x \<in> dom (v |` dom (map_of net_bounds)).
            fst (the (map_of net_bounds x)) \<le> the ((v |` dom (map_of net_bounds)) x)
            \<and> the ((v |` dom (map_of net_bounds)) x) \<le> snd (the (map_of net_bounds x))"
    proof (intro ballI)
      fix x assume "x \<in> dom (v |` dom (map_of net_bounds))"
      hence xpv: "x \<in> dom (map_of net_bounds)" using dom_pv by simp
      have r: "(v |` dom (map_of net_bounds)) x = v x" using xpv by (simp add: restrict_in)
      have b: "map_of num_net_bounds x = map_of net_bounds x" by (rule map_of_num_net_bounds_eq_on_props[OF xpv])
      have "fst (the (map_of num_net_bounds x)) \<le> the (v x) \<and> the (v x) \<le> snd (the (map_of num_net_bounds x))"
        using assms xpv pv_sub unfolding Simple_Network_Language.bounded_def by blast
      thus "fst (the (map_of net_bounds x)) \<le> the ((v |` dom (map_of net_bounds)) x)
            \<and> the ((v |` dom (map_of net_bounds)) x) \<le> snd (the (map_of net_bounds x))"
        unfolding r b by simp
    qed
  qed
qed

lemma store_decomp:
  assumes "Simple_Network_Language.bounded (map_of num_net_bounds) v"
  shows "v = (v |` dom (map_of net_bounds)) ++ (v |` (fluent_to_var ` set nfluents))"
proof (rule ext)
  fix x
  have domv: "dom v = dom (map_of net_bounds) \<union> fluent_to_var ` set nfluents"
    using assms dom_map_of_num_net_bounds unfolding Simple_Network_Language.bounded_def by simp
  show "v x = ((v |` dom (map_of net_bounds)) ++ (v |` (fluent_to_var ` set nfluents))) x"
  proof (cases "x \<in> fluent_to_var ` set nfluents")
    case True
    then obtain y where y: "v x = Some y" using domv by auto
    have "(v |` (fluent_to_var ` set nfluents)) x = Some y" using True y by (simp add: restrict_in)
    thus ?thesis using y by (simp add: map_add_def)
  next
    case nv_no: False
    hence nd: "x \<notin> dom (v |` (fluent_to_var ` set nfluents))" by (simp add: restrict_map_def domIff)
    have mp: "((v |` dom (map_of net_bounds)) ++ (v |` (fluent_to_var ` set nfluents))) x
                = (v |` dom (map_of net_bounds)) x"
      by (rule map_add_dom_app_simps(3)[OF nd])
    show ?thesis
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      then obtain y where y: "v x = Some y" using domv by auto
      have "(v |` dom (map_of net_bounds)) x = Some y" using True y by (simp add: restrict_in)
      thus ?thesis using y mp by simp
    next
      case False
      hence vn: "v x = None" using domv nv_no by (auto simp: domIff)
      have pp: "(v |` dom (map_of net_bounds)) x = None" using False by (simp add: restrict_map_def)
      show ?thesis by (simp only: vn mp pp)
    qed
  qed
qed

lemma map_of_map_inj_on:
  assumes "inj_on key (set xs)"
      and "a \<in> set xs"
    shows "map_of (map (\<lambda>x. (key x, vl x)) xs) (key a) = Some (vl a)"
  using assms
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "a = x")
    case True
    thus ?thesis by simp
  next
    case False
    hence ax: "a \<in> set xs" using Cons.prems(2) by simp
    have inj_xs: "inj_on key (set xs)" using Cons.prems(1) by (rule inj_on_subset) auto
    have xmem: "x \<in> set (x # xs)" by simp
    have "key a \<noteq> key x"
    proof
      assume eq: "key a = key x"
      have "a = x" by (rule inj_onD[OF Cons.prems(1) eq Cons.prems(2) xmem])
      thus False using False by simp
    qed
    thus ?thesis using Cons.IH[OF inj_xs ax] by simp
  qed
qed simp
lemma map_of_num_net_bounds_fluent:
  assumes "f \<in> set nfluents"
  shows "map_of num_net_bounds (fluent_to_var f) = Some (fluent_lo f, fluent_hi f)"
proof -
  have fresh: "fluent_to_var f \<notin> fst ` set all_vars" using fluent_vars_fresh assms by blast
  hence notdom: "fluent_to_var f \<notin> dom (map_of all_vars)" by (simp add: dom_map_of_conv_image_fst)
  have split: "map_of num_net_bounds (fluent_to_var f) = map_of num_fluent_vars (fluent_to_var f)"
    unfolding num_all_vars_def map_of_append using notdom by (simp add: map_add_dom_app_simps(3))
  have "map_of num_fluent_vars (fluent_to_var f) = Some (fluent_lo f, fluent_hi f)"
    unfolding num_fluent_vars_def
    by (rule map_of_map_inj_on[OF fluent_to_var_inj assms])
  thus ?thesis using split by simp
qed

lemma num_tracks_bounded:
  assumes domeq: "dom vn = dom (map_of num_net_bounds)"
      and prop_b: "Simple_Network_Language.bounded (map_of net_bounds) (vn |` dom (map_of net_bounds))"
      and tr: "num_tracks vn w"
      and inb: "fluent_in_bounds w"
    shows "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
  unfolding Simple_Network_Language.bounded_def
proof (intro conjI)
  show "dom vn = dom (map_of num_net_bounds)" by (rule domeq)
next
  show "\<forall>x \<in> dom vn. fst (the (map_of num_net_bounds x)) \<le> the (vn x)
          \<and> the (vn x) \<le> snd (the (map_of num_net_bounds x))"
  proof (intro ballI)
    fix x assume xdom: "x \<in> dom vn"
    have "x \<in> dom (map_of net_bounds) \<union> fluent_to_var ` set nfluents"
      using xdom domeq dom_map_of_num_net_bounds by simp
    thus "fst (the (map_of num_net_bounds x)) \<le> the (vn x)
          \<and> the (vn x) \<le> snd (the (map_of num_net_bounds x))"
    proof
      assume xp: "x \<in> dom (map_of net_bounds)"
      have xrp: "x \<in> dom (vn |` dom (map_of net_bounds))" using xdom xp by simp
      have r: "(vn |` dom (map_of net_bounds)) x = vn x" using xp by (simp add: restrict_in)
      have b: "map_of num_net_bounds x = map_of net_bounds x" by (rule map_of_num_net_bounds_eq_on_props[OF xp])
      have "fst (the (map_of net_bounds x)) \<le> the ((vn |` dom (map_of net_bounds)) x)
            \<and> the ((vn |` dom (map_of net_bounds)) x) \<le> snd (the (map_of net_bounds x))"
        using prop_b xrp unfolding Simple_Network_Language.bounded_def by blast
      thus ?thesis unfolding r b by simp
    next
      assume "x \<in> fluent_to_var ` set nfluents"
      then obtain f where f: "f \<in> set nfluents"
        and xf: "x = fluent_to_var f"
        by auto
      have bx: "map_of num_net_bounds x = Some (fluent_lo f, fluent_hi f)"
        unfolding xf by (rule map_of_num_net_bounds_fluent[OF f])
      obtain r where wf: "w f = Some r" using num_tracks_definedD[OF tr f] by blast
      have vx: "vn x = Some (const_to_int r)" unfolding xf by (rule num_tracks_varD[OF tr f wf])
      have "fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f"
        using inb f wf unfolding fluent_in_bounds_def by force
      thus ?thesis using bx vx by simp
    qed
  qed
qed

text \<open>The per-happening endpoint facts the run-lift consumes: along the init-anchored valid numeric
sequence every @{term \<open>snd (M i)\<close>} (for @{term \<open>i \<le> length planning_sem.htpl\<close>}) is in range -- hence
integer-valued -- by the @{thm [source] num_seq_in_bounds} reachability invariant (re-indexed from
@{term \<open>rat_impl.htpl\<close>} to @{term \<open>planning_sem.htpl\<close>} via @{thm [source] rat_impl_htpl_eq}).\<close>
lemma num_seq_fluent_in_bounds:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i \<le> length planning_sem.htpl"
    shows "fluent_in_bounds (snd (M i))"
proof -
  have "i \<le> length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  thus ?thesis by (rule num_seq_in_bounds[OF vss m0])
qed

lemma num_seq_val_ok:
  assumes "num_plan.num_rat_impl.num_valid_state_sequence M"
      and "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and "i \<le> length planning_sem.htpl"
    shows "num_val_ok (snd (M i))"
  by (rule fluent_in_bounds_imp_num_val_ok[OF num_seq_fluent_in_bounds[OF assms]])

text \<open>R1 (integrality \<Rightarrow> faithfulness) helpers for the numeric run-lift. First the eval/integrality
half of @{thm [source] nexp_ok_is_val}, factored out so it stands without the @{const num_tracks}
premise: an @{const nexp_ok} expression evaluates to a defined, integer-valued result. The arithmetic
cases close by @{thm [source] Ints_add} / @{thm [source] Ints_diff} / @{thm [source] Ints_mult}; the
@{term NDiv} case uses @{thm [source] Ints_div_exact} with the @{text \<open>\<noteq> 0\<close>} and @{text dvd}
side-conditions that @{const nexp_ok} already carries.\<close>
lemma nexp_ok_eval:
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
  thus ?case by (auto simp: Ints_add)
next
  case (NSub a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by (auto simp: Ints_diff)
next
  case (NMul a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  thus ?case by (auto simp: Ints_mult)
next
  case (NDiv a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>"
    by auto
  have nz: "rb \<noteq> 0" and dvd: "const_to_int rb dvd const_to_int ra"
    using NDiv.prems a(1) b(1) by auto
  have ev: "eval_nexp w (NDiv a b) = Some (ra / rb)" using a(1) b(1) nz by simp
  have iv: "ra / rb \<in> \<int>" by (rule Ints_div_exact[OF a(2) b(2) nz dvd])
  thus ?case using ev by blast
qed

text \<open>A single snap update of a start/end snap of a plan action preserves @{const num_val_ok}: every
declared fluent stays defined and integer-valued. A written fluent gets @{term \<open>eval_nexp w e\<close>} for
its @{const nexp_ok} right-hand side (the snap's updates are @{const nexp_ok} over any @{const num_val_ok}
valuation by @{thm [source] snap_upds_nexp_ok_start} / @{thm [source] snap_upds_nexp_ok_end}), integer by
@{thm [source] nexp_ok_eval}; an unwritten fluent keeps its (integer) pre-value. The functional side
condition comes from @{thm [source] upds_functional_start} / @{thm [source] upds_functional_end}.\<close>
lemma snap_num_update_preserves_num_val_ok:
  assumes a: "a \<in> set actions"
      and s: "s = at_start a \<or> s = at_end a"
      and ok: "num_val_ok w"
    shows "num_val_ok (num_plan.num_rat_impl.snap_num_update s w)"
proof -
  have func: "upds_functional ((set \<circ> upds) s)"
    using a s upds_functional_start upds_functional_end
    by (auto simp: upds_functional_set upds_functional_list_def)
  have rhs_ok: "nexp_ok w e" if "(f, e) \<in> set (upds s)" for f e
    using s a ok snap_upds_nexp_ok_start snap_upds_nexp_ok_end that by fastforce
  have "\<exists>r. num_plan.num_rat_impl.snap_num_update s w g = Some r \<and> r \<in> \<int>"
    if g: "g \<in> set nfluents" for g
  proof (cases "g \<in> fst ` set (upds s)")
    case True
    then obtain e where e: "(g, e) \<in> set (upds s)" by auto
    have "num_plan.num_rat_impl.snap_num_update s w g = eval_nexp w e"
      using func e by (simp add: num_plan.num_rat_impl.snap_num_update_writes)
    moreover obtain r where "eval_nexp w e = Some r" and "r \<in> \<int>"
      using nexp_ok_eval[OF rhs_ok[OF e]] by blast
    ultimately show ?thesis by simp
  next
    case False
    hence "g \<notin> num_plan.num_rat_impl.snap_writes s"
      by (simp add: num_plan.num_rat_impl.snap_writes_def)
    hence "num_plan.num_rat_impl.snap_num_update s w g = w g"
      by (rule num_plan.num_rat_impl.snap_num_update_unwritten)
    thus ?thesis using ok g by (auto simp: num_val_ok_def)
  qed
  thus ?thesis by (simp add: num_val_ok_def)
qed

text \<open>Folding a list of start/end snaps (a happening, presented as a list) preserves @{const num_val_ok}:
each fold step is a single @{const num_plan.num_rat_impl.snap_num_update} of one start/end snap, handled by
@{thm [source] snap_num_update_preserves_num_val_ok}; induct on the list, generalising the running
valuation.\<close>
lemma happening_num_update_preserves_num_val_ok:
  assumes "num_val_ok w"
      and "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
    shows "num_val_ok (num_plan.num_rat_impl.happening_num_update ys w)"
  using assms
proof (induction ys arbitrary: w)
  case Nil
  thus ?case using Nil.prems(1)
    by (simp add: num_plan.num_rat_impl.happening_num_update_Nil[unfolded comp_def])
next
  case (Cons y ys)
  obtain a where a: "a \<in> set actions"
    and ay: "y = at_start a \<or> y = at_end a"
    using Cons.prems(2) by auto
  have sok: "num_val_ok (num_plan.num_rat_impl.snap_num_update y w)"
    by (rule snap_num_update_preserves_num_val_ok[OF a ay Cons.prems(1)])
  have step: "num_val_ok (num_plan.num_rat_impl.happening_num_update ys
            (num_plan.num_rat_impl.snap_num_update y w))"
    by (rule Cons.IH[OF sok]) (use Cons.prems(2) in auto)
  show ?case
    by (subst num_plan.num_rat_impl.happening_num_update_Cons) (rule step)
qed

text \<open>The payload R1 fact: every right-hand side of a snap occurring in happening @{term i} is
@{const nexp_ok} over any @{const num_val_ok} valuation. By @{thm [source] happ_at_index_decomp} each
happening snap is @{term \<open>at_start (actions ! j)\<close>} or @{term \<open>at_end (actions ! j)\<close>} for some
@{term \<open>j < length actions\<close>} (so @{term \<open>actions ! j \<in> set actions\<close>}); the locale assumptions
@{thm [source] snap_upds_nexp_ok_start} / @{thm [source] snap_upds_nexp_ok_end} then give
@{const nexp_ok} of each update's right-hand side. Same case-split as
@{thm [source] happening_upds_functional}.\<close>
lemma happening_snap_nexp_ok:
  assumes mem: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and upd: "(f, e) \<in> set (upds s)"
      and ok: "num_val_ok w"
    shows "nexp_ok w e"
proof -
  have "s \<in> at_start ` { actions ! j | j. j < length actions
                            \<and> (is_starting_index (planning_sem.time_index i) j
                               \<or> is_instant_index (planning_sem.time_index i) j) }
          \<union> at_end ` { actions ! j | j. j < length actions
                          \<and> (is_ending_index (planning_sem.time_index i) j
                             \<or> is_instant_index (planning_sem.time_index i) j) }"
    using mem by (simp only: happ_at_index_decomp)
  then consider
      (starting) j where "j < length actions" and "s = at_start (actions ! j)"
    | (ending) j where "j < length actions" and "s = at_end (actions ! j)"
    by blast
  thus ?thesis
  proof cases
    case starting
    hence "actions ! j \<in> set actions" by simp
    thus ?thesis using snap_upds_nexp_ok_start ok upd starting by fastforce
  next
    case ending
    hence "actions ! j \<in> set actions" by simp
    thus ?thesis using snap_upds_nexp_ok_end ok upd ending by fastforce
  qed
qed

text \<open>A happening fold leaves a fluent untouched if no snap in the list writes it: each fold step is
a single @{const num_plan.num_rat_impl.snap_num_update} of an unwritten fluent, which is the identity on
that fluent by @{thm [source] num_plan.num_rat_impl.snap_num_update_unwritten}. Induct on the list,
generalising the running valuation. (The locale write set @{term \<open>num_plan.num_rat_impl.snap_writes s\<close>}
unfolds to @{term \<open>fst ` (set \<circ> upds) s\<close>}.)\<close>
lemma happening_num_update_unwritten:
  assumes "\<And>s. s \<in> set qs \<Longrightarrow> g \<notin> fst ` (set \<circ> upds) s"
  shows "num_plan.num_rat_impl.happening_num_update qs v g = v g"
  using assms
proof (induction qs arbitrary: v)
  case Nil
  show ?case
    by (simp add: num_plan.num_rat_impl.happening_num_update_Nil[unfolded comp_def])
next
  case (Cons q qs)
  have qw: "g \<notin> num_plan.num_rat_impl.snap_writes q"
    using Cons.prems[of q] by (simp add: num_plan.num_rat_impl.snap_writes_def)
  have step: "num_plan.num_rat_impl.happening_num_update qs
                (num_plan.num_rat_impl.snap_num_update q v) g
              = num_plan.num_rat_impl.snap_num_update q v g"
    by (rule Cons.IH) (use Cons.prems in auto)
  have "num_plan.num_rat_impl.snap_num_update q v g = v g"
    by (rule num_plan.num_rat_impl.snap_num_update_unwritten[OF qw])
  thus ?case
    using step by (subst num_plan.num_rat_impl.happening_num_update_Cons) simp
qed

text \<open>The running partial snap-fold over a @{emph \<open>prefix\<close>} @{term ys} of the @{term i}-th happening
stays within the declared fluent bounds. Both endpoints @{term \<open>snd (M i)\<close>} and @{term \<open>snd (M (Suc i))\<close>}
are in bounds (@{thm [source] num_seq_fluent_in_bounds}), and the full fold over the whole happening
@{term \<open>ys @ zs\<close>} equals the after-endpoint (@{thm [source] run_order_fold_eq_happening_num_update_set}).
For a declared fluent @{term g}: if no snap in @{term ys} writes it, the prefix fold leaves it at the
pre-endpoint value; if some @{term ys}-snap writes it, then -- since two snaps of one happening that
both write @{term g} would interfere (@{thm [source] happening_num_noninterfere} contradicted via the
write/write disjunct of @{const num_plan.num_rat_impl.num_mutex_snap_action}) -- no @{term zs}-snap
writes @{term g}, so the @{term zs}-tail of the full fold leaves it untouched, pinning the prefix value
to the after-endpoint value. Either way @{term g} lands in its declared bounds.\<close>
lemma running_prefix_in_bounds:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
      and dist: "distinct (ys @ zs)"
      and full: "set (ys @ zs) = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
    shows "fluent_in_bounds (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
proof -
  let ?w0 = "snd (M i)"
  let ?wpost = "snd (M (Suc i))"
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  have b0: "fluent_in_bounds ?w0"
    using i by (intro num_seq_fluent_in_bounds[OF vss m0]) simp
  have bpost: "fluent_in_bounds ?wpost"
    using i by (intro num_seq_fluent_in_bounds[OF vss m0]) simp
  have full_fold: "num_plan.num_rat_impl.happening_num_update (ys @ zs) ?w0 = ?wpost"
    by (rule run_order_fold_eq_happening_num_update_set[OF i vss dist full])
  have fold_app: "num_plan.num_rat_impl.happening_num_update (ys @ zs) v
                    = num_plan.num_rat_impl.happening_num_update zs
                        (num_plan.num_rat_impl.happening_num_update ys v)" for v
    unfolding num_plan.num_rat_impl.happening_num_update_def
    by (subst fold_append) (rule o_apply)
  have disj: "set ys \<inter> set zs = {}" using dist by auto
  have bound_g: "\<exists>r. num_plan.num_rat_impl.happening_num_update ys ?w0 g = Some r \<and> r \<in> \<int>
                   \<and> fluent_lo g \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi g"
    if g: "g \<in> set nfluents" for g
  proof (cases "\<exists>s \<in> set ys. g \<in> fst ` (set \<circ> upds) s")
    case False
    hence "num_plan.num_rat_impl.happening_num_update ys ?w0 g = ?w0 g"
      by (intro happening_num_update_unwritten) blast
    thus ?thesis using b0 g unfolding fluent_in_bounds_def by simp
  next
    case True
    then obtain s1 where s1: "s1 \<in> set ys" and g1: "g \<in> fst ` (set \<circ> upds) s1" by blast
    have unwr_zs: "g \<notin> fst ` (set \<circ> upds) s2" if s2: "s2 \<in> set zs" for s2
    proof
      assume g2: "g \<in> fst ` (set \<circ> upds) s2"
      have ne: "s1 \<noteq> s2" using s1 s2 disj by blast
      have m1: "s1 \<in> ?S" using s1 full by auto
      have m2: "s2 \<in> ?S" using s2 full by auto
      have "\<not> num_plan.num_rat_impl.num_mutex_snap_action s1 s2"
        by (rule happening_num_noninterfere[OF m1 m2 ne])
      moreover have "num_plan.num_rat_impl.num_mutex_snap_action s1 s2"
        using g1 g2 unfolding num_plan.num_rat_impl.num_mutex_snap_action_def
                              num_plan.num_rat_impl.snap_writes_def by blast
      ultimately show False by simp
    qed
    have "num_plan.num_rat_impl.happening_num_update zs
            (num_plan.num_rat_impl.happening_num_update ys ?w0) g
          = num_plan.num_rat_impl.happening_num_update ys ?w0 g"
      by (intro happening_num_update_unwritten) (rule unwr_zs)
    hence "num_plan.num_rat_impl.happening_num_update ys ?w0 g = ?wpost g"
      using full_fold by (simp add: fold_app)
    thus ?thesis using bpost g unfolding fluent_in_bounds_def by simp
  qed
  show ?thesis unfolding fluent_in_bounds_def using bound_g by blast
qed

text \<open>Per-snap numeric precondition satisfaction extracted from numeric-plan validity: along a valid
numeric state sequence, every snap @{term s} of the @{term i}-th happening has its numeric precondition
@{term \<open>n_pre s\<close>} satisfied at the pre-happening valuation @{term \<open>snd (M i)\<close>}. This is the precondition
conjunct of @{thm [source] num_plan.num_rat_impl.num_valid_state_sequence_def} (where @{term \<open>num_plan\<close>}'s
@{term n_pre} is @{term \<open>set \<circ> n_pre\<close>}, so the comparison set is @{term \<open>set (n_pre s)\<close>}); the happening
membership is bridged from the @{term rat_impl} form by @{thm [source] rat_impl_happ_at_eq}. Same
extraction shape as @{thm [source] run_order_fold_eq_happening_num_update_set} /
@{thm [source] happening_upds_functional}.\<close>
lemma happening_snap_pre_sat:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and i: "i < length planning_sem.htpl"
      and s: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
    shows "sat_comps (snd (M i)) (set (n_pre s))"
proof -
  have iH: "i < length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  have sH: "s \<in> planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)"
    using s by (simp add: rat_impl_happ_at_eq)
  have "\<forall>s \<in> planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i).
          sat_comps (snd (M i)) ((set \<circ> n_pre) s)"
    using vss iH unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def by blast
  thus ?thesis using sH by simp
qed

text \<open>Guard invariance under a @{emph \<open>partial\<close>} (prefix-list) happening fold -- the list-prefix twin of
@{thm [source] sat_comps_happening_num_update_set}. If @{term s} co-occurs in the @{term i}-th happening,
@{term ys} is a @{term s}-free subset of that happening, then folding @{term ys}'s numeric updates over
@{term \<open>snd (M i)\<close>} leaves @{term s}'s numeric precondition satisfaction unchanged: each @{term ys}-snap
@{term s'} is distinct from @{term s} and co-occurs, so does not numerically interfere
(@{thm [source] happening_num_noninterfere}), hence misses every fluent @{term s} reads; the precondition's
read fluents lie in @{term \<open>snap_reads s\<close>} (definitionally), so @{thm [source] happening_num_update_unwritten}
pins them. @{thm [source] sat_comps_cong} reduces to the per-read-fluent agreement. (The @{term rd}
read-containment is derived inline from @{thm [source] num_plan.num_rat_impl.snap_reads_def}, so it is not a
hypothesis.)\<close>
lemma sat_comps_running_prefix:
  assumes s: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and s_notin: "s \<notin> set ys"
    shows "sat_comps (num_plan.num_rat_impl.happening_num_update ys (snd (M i))) (set (n_pre s))
             = sat_comps (snd (M i)) (set (n_pre s))"
proof (rule sat_comps_cong)
  fix c f assume c: "c \<in> set (n_pre s)" and f: "f \<in> comp_fluents c"
  have fr: "f \<in> num_plan.num_rat_impl.snap_reads s"
    using c f unfolding num_plan.num_rat_impl.snap_reads_def by auto
  have unwr: "f \<notin> fst ` (set \<circ> upds) s'" if s': "s' \<in> set ys" for s'
  proof -
    have m': "s' \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      using s' ys_sub by blast
    have ne: "s' \<noteq> s" using s' s_notin by blast
    have "\<not> num_plan.num_rat_impl.num_mutex_snap_action s' s"
      by (rule happening_num_noninterfere[OF m' s ne])
    hence "num_plan.num_rat_impl.snap_writes s' \<inter> num_plan.num_rat_impl.snap_reads s = {}"
      unfolding num_plan.num_rat_impl.num_mutex_snap_action_def by blast
    hence "f \<notin> num_plan.num_rat_impl.snap_writes s'" using fr by blast
    thus ?thesis unfolding num_plan.num_rat_impl.snap_writes_def .
  qed
  show "num_plan.num_rat_impl.happening_num_update ys (snd (M i)) f = snd (M i) f"
    by (rule happening_num_update_unwritten) (rule unwr)
qed

lemma happening_num_update_inv_unchanged:
  assumes g: "g \<in> (\<Union>a \<in> set actions. \<Union>c \<in> set (n_inv a). comp_fluents c)"
      and ys: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
    shows "num_plan.num_rat_impl.happening_num_update ys w g = w g"
proof (rule happening_num_update_unwritten)
  fix s assume s: "s \<in> set ys"
  obtain b c where b: "b \<in> set actions" and c: "c \<in> set (n_inv b)" and gc: "g \<in> comp_fluents c"
    using g by blast
  have ginv_b: "g \<in> (\<Union>c \<in> set (n_inv b). comp_fluents c)" using c gc by blast
  obtain a where a: "a \<in> set actions" and sa: "s = at_start a \<or> s = at_end a"
    using ys[OF s] by blast
  have "(fst ` set (upds (at_start a)) \<union> fst ` set (upds (at_end a)))
          \<inter> (\<Union>c \<in> set (n_inv b). comp_fluents c) = {}"
    using n_inv_readonly a b by blast
  hence "g \<notin> fst ` set (upds (at_start a))" and "g \<notin> fst ` set (upds (at_end a))"
    using ginv_b by auto
  thus "g \<notin> fst ` (set \<circ> upds) s" using sa by (auto simp: comp_def)
qed

lemma num_seq_inv_const:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and i: "i \<le> length planning_sem.htpl"
      and g: "g \<in> (\<Union>a \<in> set actions. \<Union>c \<in> set (n_inv a). comp_fluents c)"
    shows "snd (M i) g = snd (M 0) g"
  using i
proof (induction i)
  case 0
  show ?case by simp
next
  case (Suc i')
  have i'H: "i' < length planning_sem.htpl" using Suc.prems by simp
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i')"
  obtain xs where dist: "distinct xs" and setxs: "set xs = ?S"
    using finite_distinct_list[OF happening_finite] by blast
  have fold_post: "num_plan.num_rat_impl.happening_num_update xs (snd (M i')) = snd (M (Suc i'))"
    by (rule run_order_fold_eq_happening_num_update_set[OF i'H vss dist setxs])
  have ys: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if s: "s \<in> set xs" for s
  proof -
    have "s \<in> at_start ` { actions ! j | j. j < length actions
              \<and> (is_starting_index (planning_sem.time_index i') j \<or> is_instant_index (planning_sem.time_index i') j) }
            \<union> at_end ` { actions ! j | j. j < length actions
              \<and> (is_ending_index (planning_sem.time_index i') j \<or> is_instant_index (planning_sem.time_index i') j) }"
      using s setxs by (simp only: happ_at_index_decomp)
    thus ?thesis by (auto simp: set_nthI)
  qed
  have "num_plan.num_rat_impl.happening_num_update xs (snd (M i')) g = snd (M i') g"
    by (rule happening_num_update_inv_unchanged[OF g ys])
  hence "snd (M (Suc i')) g = snd (M i') g" using fold_post by simp
  thus ?case using Suc.IH Suc.prems by simp
qed

lemma active_action_inv_sat:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and i: "i < length planning_sem.htpl"
      and a: "a \<in> num_plan.num_rat_impl.active_actions (rat_impl.time_index i)"
    shows "sat_comps (snd (M i)) (set (n_inv a))"
proof -
  have iH: "i < length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  have "\<forall>a \<in> num_plan.num_rat_impl.active_actions (rat_impl.time_index i).
          sat_comps (snd (M i)) ((set \<circ> n_inv) a)"
    using vss iH unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def by blast
  thus ?thesis using a by simp
qed

lemma num_inv_guard_sat_at:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and a: "a \<in> set actions"
      and aact: "a \<in> num_plan.num_rat_impl.active_actions (rat_impl.time_index i')"
      and i': "i' < length planning_sem.htpl"
      and wagree: "\<And>g. g \<in> (\<Union>c \<in> set (n_inv a). comp_fluents c) \<Longrightarrow> w g = snd (M i') g"
    shows "sat_comps w (set (n_inv a))"
proof -
  have sat: "sat_comps (snd (M i')) (set (n_inv a))"
    by (rule active_action_inv_sat[OF vss i' aact])
  have "sat_comps w (set (n_inv a)) = sat_comps (snd (M i')) (set (n_inv a))"
  proof (rule sat_comps_cong)
    fix c f assume c: "c \<in> set (n_inv a)" and f: "f \<in> comp_fluents c"
    have "f \<in> (\<Union>c \<in> set (n_inv a). comp_fluents c)" using c f by blast
    thus "w f = snd (M i') f" by (rule wagree)
  qed
  thus ?thesis using sat by simp
qed

text \<open>The bridge to the propositional structural invariant: the projection of a
@{const num_Lv_conds}-store to the propositional bounds domain satisfies @{const Lv_conds}. The
boundedness comes from @{thm [source] prop_proj_bounded}; @{const planning_lock} survives the
restriction because it is a propositional variable (@{thm [source] map_of_net_bounds_planning_lock}
puts it in @{term \<open>dom (map_of net_bounds)\<close>}); length / head location are about @{term L} directly.
This is what supplies the propositional @{const LvP} premise on the projection store when the numeric
run invokes the propositional @{thm [source] happening_steps_possible}.\<close>
lemma num_Lv_conds_imp_Lv_conds:
  assumes "num_Lv_conds L v"
  shows "Lv_conds L (v |` dom (map_of net_bounds))"
proof (rule Lv_condsI)
  show "length L = Suc (length actions)" by (rule num_Lv_conds_dests(1)[OF assms])
  show "L ! 0 = planning_loc" by (rule num_Lv_conds_dests(2)[OF assms])
  show "Simple_Network_Language.bounded (map_of net_bounds) (v |` dom (map_of net_bounds))"
    by (rule prop_proj_bounded[OF num_Lv_conds_dests(3)[OF assms]])
  have "planning_lock \<in> dom (map_of net_bounds)" using map_of_net_bounds_planning_lock by blast
  hence "(v |` dom (map_of net_bounds)) planning_lock = v planning_lock" by (simp add: restrict_in)
  thus "(v |` dom (map_of net_bounds)) planning_lock = Some 1"
    using num_Lv_conds_dests(4)[OF assms] by simp
qed

lemma num_LvP_imp_LvP:
  assumes "num_LvP (L, v, c)"
  shows "LvP (L, v |` dom (map_of net_bounds), c)"
  using assms num_Lv_conds_imp_Lv_conds by simp

subsection \<open>Generic run-lift engine: combining the propositional and numeric nets\<close>

text \<open>The numeric net carries the SAME urgent sets as the propositional net at every automaton index:
@{const augment_edge} touches only edges, not the urgent component (main automaton @{term \<open>{init_loc,
goal_loc}\<close>}, action automata @{term \<open>{starting_loc, ending_loc}\<close>}). This is what lets a propositional
delay step be re-issued verbatim on the numeric net (the urgency side-condition of @{thm [source]
step_u.step_t} transfers).\<close>
lemma num_urgent_eq:
  assumes p: "p < Suc (length actions)"
  shows "urgent (fst (snd num_net_impl.sem) ! p) = urgent (fst (snd net_impl.sem) ! p)"
proof (cases p)
  case 0
  have n: "urgent (fst (snd num_net_impl.sem) ! p) = {init_loc, goal_loc}"
    unfolding num_sem_alt_def fst_conv snd_conv
    apply (subst nth_map, simp add: p length_num_net_automata)
    apply (subst 0) apply (subst nth_Cons_0)
    unfolding comp_def num_main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
      urgent_def fst_conv by auto
  have pr: "urgent (fst (snd net_impl.sem) ! p) = {init_loc, goal_loc}"
    unfolding sem_alt_def fst_conv snd_conv
    apply (subst nth_map, simp add: p length_net_automata)
    apply (subst 0) apply (subst nth_Cons_0)
    unfolding comp_def main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
      urgent_def fst_conv by auto
  show ?thesis using n pr by simp
next
  case (Suc n)
  have nn: "urgent (fst (snd num_net_impl.sem) ! p) = {starting_loc, ending_loc}"
    apply (subst num_sem_alt_def) unfolding fst_conv snd_conv
    apply (subst nth_map, simp add: p length_num_net_automata)
    unfolding Suc apply (subst nth_Cons_Suc) apply (subst nth_map) using Suc p apply simp
    apply (subst num_action_auto_urg) ..
  have pr: "urgent (fst (snd net_impl.sem) ! p) = {starting_loc, ending_loc}"
    apply (subst sem_alt_def) unfolding fst_conv snd_conv
    apply (subst nth_map, simp add: p length_net_automata)
    unfolding Suc apply (subst nth_Cons_Suc) apply (subst nth_map) using Suc p apply simp
    apply (subst action_auto_urg) ..
  show ?thesis using nn pr by simp
qed

text \<open>Lifting a propositional delay step to the numeric net: a @{const Simple_Network_Language.label.Del}
step of @{const net_impl.sem} re-issues verbatim on @{const num_net_impl.sem} (same locations, same delay,
store untouched -- delays only advance clocks). The numeric net has no invariants (@{thm [source]
num_no_invs}) and the same urgent sets (@{thm [source] num_urgent_eq}), so the only new obligation is the
numeric boundedness of the (unchanged) store, supplied by the caller.\<close>
lemma num_step_t_lift:
  assumes propdel: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vp, c'\<rangle>"
      and bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
    shows "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c'\<rangle>"
proof -
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where
      c': "c' = c \<oplus> t"
    and t: "0 \<le> t"
    and urgp: "(\<exists>p<length N. L ! p \<in> urgent (N ! p)) \<longrightarrow> t = 0"
    apply (cases rule: step_u_elims(1)[OF propdel])
    unfolding as unfolding TAG_def by auto
  have lp: "length N = Suc (length actions)" using as length_net_impl by (simp add: comp_def)
  have urgn: "(\<exists>p<length (fst (snd num_net_impl.sem)). L ! p \<in> urgent (fst (snd num_net_impl.sem) ! p)) \<longrightarrow> t = 0"
  proof -
    have ln: "length (fst (snd num_net_impl.sem)) = Suc (length actions)" using length_num_net_impl by (simp add: comp_def)
    have "urgent (fst (snd num_net_impl.sem) ! p) = urgent (N ! p)" if "p < Suc (length actions)" for p
      using num_urgent_eq[OF that] as by simp
    thus ?thesis using urgp lp ln by auto
  qed
  show ?thesis
    unfolding c' num_net_impl.sem_def
    apply (rule step_t)
    subgoal unfolding TAG_def using num_no_invs by auto
    subgoal unfolding TAG_def using t by simp
    subgoal unfolding TAG_def using urgn unfolding num_net_impl.sem_def by simp
    subgoal unfolding TAG_def using bnd by auto
    done
qed

subsection \<open>Run-lifting: the numeric happening and plan runs (forward direction)\<close>

text \<open>The numeric happening run, existentially: from a combined config @{term \<open>(L, vn, c)\<close>} whose store
both satisfies the propositional @{const happening_pre_pre_delay} and tracks the pre-happening numeric
valuation @{term \<open>snd (M i)\<close>}, there is a numeric run that ends in a config satisfying
@{const num_happening_post} (the propositional post-invariant plus tracking of @{term \<open>snd (M (Suc i))\<close>}).
The run shadows the propositional @{const delay_and_apply} run (same locations and clocks), threading the
fluent variables through @{thm [source] num_int_step_lift} per internal step.\<close>

text \<open>Every edge of @{const net_automata} carries a @{const Sil} action (all edge definitions ---
@{const main_auto_init_edge} / @{const main_auto_goal_edge} / @{const main_auto_loop} on the main
automaton and @{const start_edge} / @{const edge_2} / @{const edge_3} / @{const end_edge} /
@{const instant_trans_edge} on the action automata --- are @{term \<open>Sil (STR '''')\<close>}), so no @{const In}
or @{const Out} synchronisation edge exists anywhere in the propositional net.\<close>
lemma net_automata_no_in:
  assumes "p < length net_automata"
  shows "(l, b, g, In aa, f, r, l') \<notin> trans (automaton_of (net_automata ! p))"
proof (cases p)
  case 0
  show ?thesis unfolding 0 main_auto_trans
    unfolding main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def Let_def by simp
next
  case (Suc n)
  have nlt: "n < length actions" using assms unfolding Suc length_net_automata by simp
  show ?thesis unfolding Suc nth_auto_trans[OF nlt]
    unfolding start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def Let_def by simp
qed

lemma net_automata_no_out:
  assumes "p < length net_automata"
  shows "(l, b, g, Out aa, f, r, l') \<notin> trans (automaton_of (net_automata ! p))"
proof (cases p)
  case 0
  show ?thesis unfolding 0 main_auto_trans
    unfolding main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def Let_def by simp
next
  case (Suc n)
  have nlt: "n < length actions" using assms unfolding Suc length_net_automata by simp
  show ?thesis unfolding Suc nth_auto_trans[OF nlt]
    unfolding start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def Let_def by simp
qed

text \<open>The same on the @{emph \<open>conv\<close>}-elaborated automata that @{const net_impl.sem} actually steps over:
@{const conv_automaton} only rewrites the clock guard (@{thm [source] conv_trans}), so it preserves the
@{const In}/@{const Out} action labels and hence introduces no synchronisation edge either.\<close>
lemma conv_net_no_in:
  assumes "p < length net_automata"
  shows "(l, b, g, In aa, f, r, l') \<notin> trans (automaton_of (conv_automaton (net_automata ! p)))"
proof -
  have plen: "p < length (map (automaton_of \<circ> conv_automaton) net_automata)" using assms by simp
  have rw: "automaton_of (conv_automaton (net_automata ! p)) = map (automaton_of \<circ> conv_automaton) net_automata ! p"
    using assms by (simp add: comp_def)
  show ?thesis unfolding rw conv_trans[OF plen] using net_automata_no_in[OF assms] by auto
qed

lemma conv_net_no_out:
  assumes "p < length net_automata"
  shows "(l, b, g, Out aa, f, r, l') \<notin> trans (automaton_of (conv_automaton (net_automata ! p)))"
proof -
  have plen: "p < length (map (automaton_of \<circ> conv_automaton) net_automata)" using assms by simp
  have rw: "automaton_of (conv_automaton (net_automata ! p)) = map (automaton_of \<circ> conv_automaton) net_automata ! p"
    using assms by (simp add: comp_def)
  show ?thesis unfolding rw conv_trans[OF plen] using net_automata_no_out[OF assms] by auto
qed

text \<open>A non-@{const Del} step of @{const net_impl.sem} is necessarily an @{const Internal} step: the
empty broadcast set (@{thm [source] net_broadcast_def}) rules out a @{const Broad} step, and the
absence of any @{const In}/@{const Out} edge (@{thm [source] conv_net_no_in} /
@{thm [source] conv_net_no_out}) rules out a @{const Bin} step.\<close>
lemma prop_non_del_step_internal:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', v', c'\<rangle>"
      and aD: "a \<noteq> Simple_Network_Language.label.Del"
      and L_len: "length L = length net_automata"
  shows "\<exists>aa. a = Internal aa"
proof (cases a)
  case Del
  then show ?thesis using aD by simp
next
  case (Internal aa)
  then show ?thesis by blast
next
  case (Bin aa)
  have F: False
    apply (rule step_u_elims'(3)[OF step[unfolded Bin net_impl.sem_def]])
    unfolding TAG_def
    using L_len by (auto dest: conv_net_no_in)
  then show ?thesis by simp
next
  case (Broad aa)
  have F: False
    apply (rule step_u_elims'(4)[OF step[unfolded Broad net_impl.sem_def]])
    unfolding TAG_def
    using net_broadcast_def by simp
  then show ?thesis by simp
qed

lemma num_step'_lift:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L', v', c'\<rangle>"
      and L_len: "length L = length net_automata"
      and bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
      and num_data:
        "\<And>a p l b g f r l'.
           p < length net_automata \<Longrightarrow>
           (l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p)) \<Longrightarrow>
           L ! p = l \<Longrightarrow> check_bexp v b True \<Longrightarrow> is_upds v f v' \<Longrightarrow>
           \<exists>bg fu vn'.
              (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
              \<and> check_bexp vn bg True
              \<and> is_upds vn fu vn'
              \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
              \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w'"
  shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>
               \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w' \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
proof -
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "a \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', v', c'\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where
      Lieq: "Li = L"
    and vieq: "vi = v"
    and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', v', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain aa where aInt: "a = Internal aa"
    using prop_non_del_step_internal[OF actI aD L_len] by blast
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have nd: "\<exists>bg fu vn'.
              (l, bg, g, Sil aa, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
              \<and> check_bexp vn bg True
              \<and> is_upds vn fu vn'
              \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
              \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w'"
    if "p < length net_automata"
       "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
       "L ! p = l" "check_bexp v b True" "is_upds v f v'"
    for p l b g f r l'
    using num_data that by blast
  have ex: "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal aa\<^esub> \<langle>L', vn', c'\<rangle>
                 \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w' \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    apply (rule num_int_step_lift[OF actI[unfolded aInt] L_len])
    using nd by blast
  obtain vn' where
      numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal aa\<^esub> \<langle>L', vn', c'\<rangle>"
    and le': "v' \<subseteq>\<^sub>m vn'"
    and tr': "num_tracks vn' w'"
    and bnd': "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    using ex by blast
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using le' tr' bnd' by blast
qed

definition run_order_snaps :: "nat \<Rightarrow> 'snap_action list" where
"run_order_snaps i \<equiv>
  (let t = planning_sem.time_index i; acts = [0..<length actions];
       start_indices = filter (is_starting_index t) acts;
       end_indices   = filter (is_ending_index t) acts;
       both          = filter (is_instant_index t) acts
   in concat (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) both)
      @ map (\<lambda>n. at_start (actions!n)) start_indices
      @ map (\<lambda>n. at_end (actions!n)) end_indices)"

lemma set_run_order_snaps:
  "set (run_order_snaps i) = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
proof -
  let ?t = "planning_sem.time_index i"
  have setS: "set (filter (is_starting_index ?t) [0..<length actions])
                = {j. j < length actions \<and> is_starting_index ?t j}"
    by (simp add: set_filter)
  have setE: "set (filter (is_ending_index ?t) [0..<length actions])
                = {j. j < length actions \<and> is_ending_index ?t j}"
    by (simp add: set_filter)
  have setB: "set (filter (is_instant_index ?t) [0..<length actions])
                = {j. j < length actions \<and> is_instant_index ?t j}"
    by (simp add: set_filter)
  show ?thesis
    unfolding run_order_snaps_def Let_def happ_at_index_decomp
    apply (simp only: set_append set_concat set_map setS setE setB)
    by auto
qed

lemma distinct_run_order_snaps:
  "distinct (run_order_snaps i)"
proof -
  let ?t = "planning_sem.time_index i"
  define SI where "SI = filter (is_instant_index ?t) [0..<length actions]"
  define SS where "SS = filter (is_starting_index ?t) [0..<length actions]"
  define SE where "SE = filter (is_ending_index ?t) [0..<length actions]"
  \<comment> \<open>Membership in each index list: the index is below @{term \<open>length actions\<close>} and has the case.\<close>
  have memSI: "n < length actions" "is_instant_index ?t n" if "n \<in> set SI" for n
    using that unfolding SI_def by auto
  have memSS: "n < length actions" "is_starting_index ?t n" if "n \<in> set SS" for n
    using that unfolding SS_def by auto
  have memSE: "n < length actions" "is_ending_index ?t n" if "n \<in> set SE" for n
    using that unfolding SE_def by auto
  \<comment> \<open>Each index list is distinct (a filter of the distinct @{term \<open>[0..<length actions]\<close>}).\<close>
  have distSI: "distinct SI" unfolding SI_def by simp
  have distSS: "distinct SS" unfolding SS_def by simp
  have distSE: "distinct SE" unfolding SE_def by simp
  \<comment> \<open>The three index-cases are mutually exclusive at a fixed time-point.\<close>
  have excl_IS: "\<not> is_starting_index ?t n" if "is_instant_index ?t n" for n
    using that by (simp add: index_case_defs planning_sem.is_instant_action_def
                              planning_sem.is_starting_action_def)
  have excl_IE: "\<not> is_ending_index ?t n" if "is_instant_index ?t n" for n
    using that by (simp add: index_case_defs planning_sem.is_instant_action_def
                              planning_sem.is_ending_action_def)
  have excl_SE: "\<not> is_ending_index ?t n" if "is_starting_index ?t n" for n
    using that by (simp add: index_case_defs planning_sem.is_starting_action_def
                              planning_sem.is_ending_action_def)
  \<comment> \<open>Hence the index lists are pairwise disjoint as sets.\<close>
  have disj_SI_SS: "set SI \<inter> set SS = {}"
    using memSI(2) memSS(2) excl_IS by blast
  have disj_SI_SE: "set SI \<inter> set SE = {}"
    using memSI(2) memSE(2) excl_IE by blast
  have disj_SS_SE: "set SS \<inter> set SE = {}"
    using memSS(2) memSE(2) excl_SE by blast
  \<comment> \<open>Snap-distinctness within and across the index lists.\<close>
  have ne_se: "at_start (actions ! n) \<noteq> at_end (actions ! m)"
    if "n < length actions" "m < length actions" for n m
    using nth_start_end_disj[OF set_nthI[OF that(2)] that(1)] .
  have ne_es: "at_end (actions ! n) \<noteq> at_start (actions ! m)"
    if "n < length actions" "m < length actions" for n m
    using nth_end_start_disj[OF set_nthI[OF that(2)] that(1)] .
  \<comment> \<open>The three component lists.\<close>
  let ?A = "concat (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
  let ?B = "map (\<lambda>n. at_start (actions!n)) SS"
  let ?C = "map (\<lambda>n. at_end (actions!n)) SE"
  \<comment> \<open>@{term ?A} is distinct: distinct outer index list, each 2-element block distinct
     (start \<noteq> end), and distinct blocks are disjoint (action-injectivity + start/end-disjointness).\<close>
  have dA: "distinct ?A"
  proof (rule distinct_concat)
    have inj_SI: "x = y"
      if "x \<in> set SI" "y \<in> set SI"
         "[at_start (actions!x), at_end (actions!x)] = [at_start (actions!y), at_end (actions!y)]"
      for x y
      using that nth_starts_unique[OF memSI(1)[OF that(1)] memSI(1)[OF that(2)]] by force
    show "distinct (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
      unfolding distinct_map using distSI by (auto intro!: inj_onI simp: inj_SI)
  next
    fix ys
    assume "ys \<in> set (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
    then obtain n where n: "n \<in> set SI" "ys = [at_start (actions!n), at_end (actions!n)]" by auto
    show "distinct ys" using n ne_se[OF memSI(1)[OF n(1)] memSI(1)[OF n(1)]] by auto
  next
    fix ys zs
    assume "ys \<in> set (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
       and "zs \<in> set (map (\<lambda>n. [at_start (actions!n), at_end (actions!n)]) SI)"
       and yz: "ys \<noteq> zs"
    then obtain n m where
        nm: "n \<in> set SI"
            "m \<in> set SI"
            "ys = [at_start (actions!n), at_end (actions!n)]"
            "zs = [at_start (actions!m), at_end (actions!m)]"
      by auto
    have "n \<noteq> m" using nm yz by auto
    hence "actions ! n \<noteq> actions ! m"
      using nth_actions_unique[OF memSI(1)[OF nm(1)] memSI(1)[OF nm(2)]] by blast
    thus "set ys \<inter> set zs = {}"
      using nm memSI(1)[OF nm(1)] memSI(1)[OF nm(2)]
            nth_starts_unique nth_ends_unique ne_se ne_es by auto
  qed
  have dB: "distinct ?B"
  proof -
    have "x = y" if "x \<in> set SS" "y \<in> set SS" "at_start (actions!x) = at_start (actions!y)" for x y
      using that nth_starts_unique[OF memSS(1)[OF that(1)] memSS(1)[OF that(2)]] by force
    thus ?thesis unfolding distinct_map using distSS by (auto intro!: inj_onI)
  qed
  have dC: "distinct ?C"
  proof -
    have "x = y" if "x \<in> set SE" "y \<in> set SE" "at_end (actions!x) = at_end (actions!y)" for x y
      using that nth_ends_unique[OF memSE(1)[OF that(1)] memSE(1)[OF that(2)]] by force
    thus ?thesis unfolding distinct_map using distSE by (auto intro!: inj_onI)
  qed
  \<comment> \<open>@{term ?A} disjoint from @{term ?B}: a @{term at_start} from @{term SI} vs @{term SS}
     differs by action-injectivity (disjoint index sets); an @{term at_end} vs @{term at_start}
     by start/end-disjointness.\<close>
  have dAB: "set ?A \<inter> set ?B = {}"
  proof -
    have "x \<noteq> y" if "x \<in> set ?A" "y \<in> set ?B" for x y
    proof -
      from that(2) obtain m where m: "m \<in> set SS" "y = at_start (actions!m)" by auto
      from that(1) obtain n where
          n: "n \<in> set SI" "x = at_start (actions!n) \<or> x = at_end (actions!n)" by auto
      have nm: "n \<noteq> m" using n(1) m(1) disj_SI_SS by blast
      have nlen: "n < length actions" using memSI(1)[OF n(1)] .
      have mlen: "m < length actions" using memSS(1)[OF m(1)] .
      show ?thesis using n(2)
      proof
        assume "x = at_start (actions!n)"
        thus ?thesis using m(2) nm nth_starts_unique[OF nlen mlen] by simp
      next
        assume "x = at_end (actions!n)"
        thus ?thesis using m(2) ne_es[OF nlen mlen] by simp
      qed
    qed
    thus ?thesis by blast
  qed
  \<comment> \<open>@{term ?A} disjoint from @{term ?C}: an @{term at_start} vs @{term at_end} by start/end-disjointness;
     an @{term at_end} from @{term SI} vs @{term SE} by action-injectivity (disjoint index sets).\<close>
  have dAC: "set ?A \<inter> set ?C = {}"
  proof -
    have "x \<noteq> y" if "x \<in> set ?A" "y \<in> set ?C" for x y
    proof -
      from that(2) obtain m where m: "m \<in> set SE" "y = at_end (actions!m)" by auto
      from that(1) obtain n where
          n: "n \<in> set SI" "x = at_start (actions!n) \<or> x = at_end (actions!n)" by auto
      have nm: "n \<noteq> m" using n(1) m(1) disj_SI_SE by blast
      have nlen: "n < length actions" using memSI(1)[OF n(1)] .
      have mlen: "m < length actions" using memSE(1)[OF m(1)] .
      show ?thesis using n(2)
      proof
        assume "x = at_start (actions!n)"
        thus ?thesis using m(2) ne_se[OF nlen mlen] by simp
      next
        assume "x = at_end (actions!n)"
        thus ?thesis using m(2) nm nth_ends_unique[OF nlen mlen] by simp
      qed
    qed
    thus ?thesis by blast
  qed
  \<comment> \<open>@{term ?B} disjoint from @{term ?C}: an @{term at_start} vs @{term at_end}, by start/end-disjointness.\<close>
  have dBC: "set ?B \<inter> set ?C = {}"
  proof -
    have "x \<noteq> y" if "x \<in> set ?B" "y \<in> set ?C" for x y
    proof -
      from that(1) obtain n where n: "n \<in> set SS" "x = at_start (actions!n)" by auto
      from that(2) obtain m where m: "m \<in> set SE" "y = at_end (actions!m)" by auto
      show ?thesis using n m ne_se[OF memSS(1)[OF n(1)] memSE(1)[OF m(1)]] by auto
    qed
    thus ?thesis by blast
  qed
  have "distinct (?A @ ?B @ ?C)"
    using dA dB dC dAB dAC dBC by (simp add: Int_Un_distrib)
  thus ?thesis
    unfolding run_order_snaps_def Let_def SI_def SS_def SE_def .
qed

text \<open>The numeric graph satisfies the @{locale sequence_rules} composition laws (the numeric mirror of
the propositional \<open>steps_seq\<close> interpretation, proved identically: @{const num_graph_impl.steps} is a
@{locale Graph_Defs} step relation, so its singleton intro and the \<open>num_steps_extend\<close> splice
discharge @{text base}/@{text step}). This is the structural combinator the numeric run-lifting
reuses to walk the @{const delay_and_apply} phase decomposition.\<close>
lemma num_steps_extend:
  "num_graph_impl.steps xs
  \<Longrightarrow> num_graph_impl.steps (last xs # ys)
  \<Longrightarrow> num_graph_impl.steps (xs @ ys)"
  by (rule num_graph_impl.steps_append'[where as = xs and bs = "last xs # ys"]) simp+

sublocale num_steps_seq: sequence_rules num_graph_impl.steps
  apply standard
  using num_graph_impl.steps.intros(1) num_steps_extend .


end

end

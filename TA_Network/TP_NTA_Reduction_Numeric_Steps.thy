theory TP_NTA_Reduction_Numeric_Steps
  imports TP_NTA_Reduction_Numeric_Projection
begin

context numeric_tp_nta_reduction_correctness
begin

subsection \<open>Numeric per-phase run-lift: the \<open>edge_3\<close> (ending-duration) phase\<close>

text \<open>The relational invariant carried by the numeric run-lift: the numeric (combined) store
@{term vn} EXTENDS the propositional store @{term vp} (so the propositional run's facts transfer
verbatim by @{thm [source] check_bexp_is_val_mono} / @{thm [source] is_upds_map_le}), it TRACKS the
abstract numeric valuation @{term w} (@{const num_tracks}), and it is @{const num_net_bounds}-bounded.
The locations and clocks are shared (both runs fire the same @{const edge_3} edge), so they are not
part of \<open>REL\<close>; they coincide config-for-config.\<close>
definition REL where
"REL vp vn w \<longleftrightarrow> vp \<subseteq>\<^sub>m vn \<and> num_tracks vn w \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn"

lemma RELI:
  assumes "vp \<subseteq>\<^sub>m vn"
    and "num_tracks vn w"
    and "Simple_Network_Language.bounded (map_of num_net_bounds) vn"
  shows "REL vp vn w"
  using assms unfolding REL_def by blast

lemma REL_leD: "REL vp vn w \<Longrightarrow> vp \<subseteq>\<^sub>m vn"
  and REL_trD: "REL vp vn w \<Longrightarrow> num_tracks vn w"
  and REL_bndD: "REL vp vn w \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn"
  unfolding REL_def by blast+

text \<open>Re-establishing the @{const num_net_bounds} bound on the numeric post-store of a no-fluent-write
edge: the numeric store @{term vn'} extends the propositional post-store @{term vp'} (so on the
propositional variables it equals @{term vp'}, which the propositional run keeps
@{const net_bounds}-bounded), it tracks @{term w} (so the fluent variables are in their fluent bounds
because @{term w} is @{const fluent_in_bounds}), and these two halves cover @{const num_net_bounds}.\<close>
lemma REL_bnd_from_proj:
  assumes le: "vp' \<subseteq>\<^sub>m vn'"
      and vp'_dom: "dom vp' = dom (map_of net_bounds)"
      and pbnd: "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and tr: "num_tracks vn' w"
      and fin: "fluent_in_bounds w"
      and vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    shows "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
proof (rule num_tracks_bounded[OF vn'_dom _ tr fin])
  have "(vn' |` dom (map_of net_bounds)) = vp'"
  proof (rule ext)
    fix x
    show "(vn' |` dom (map_of net_bounds)) x = vp' x"
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      hence "x \<in> dom vp'" using vp'_dom by simp
      then obtain y where y: "vp' x = Some y" by auto
      have "vn' x = Some y" using le y unfolding map_le_def by (metis domI)
      thus ?thesis using True y by (simp add: restrict_in)
    next
      case False
      hence "x \<notin> dom vp'" using vp'_dom by simp
      thus ?thesis using False by (simp add: restrict_map_def domIff)
    qed
  qed
  thus "Simple_Network_Language.bounded (map_of net_bounds) (vn' |` dom (map_of net_bounds))"
    using pbnd by simp
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const edge_3} VERBATIM (third in
the edge list of @{const num_action_to_automaton}), so the numeric net contains the same
@{const edge_3} transition as the propositional net.\<close>
lemma num_nth_auto_edge_3:
  assumes n: "n < length actions"
  shows "edge_3 (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const num_start_edge} (first in the
edge list of @{const num_action_to_automaton}) and @{const num_end_edge} (fourth), so the numeric net
contains the AUGMENTED start/end transitions.\<close>
lemma num_nth_auto_num_start_edge:
  assumes n: "n < length actions"
  shows "num_start_edge (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

lemma num_nth_auto_num_end_edge:
  assumes n: "n < length actions"
  shows "num_end_edge (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const num_edge_2} (second in the
edge list of @{const num_action_to_automaton}), so the numeric net contains the AUGMENTED running-entry
edge -- @{const edge_2} with the numeric @{const num_inv_guard} conjoined (and no extra update).\<close>
lemma num_nth_auto_num_edge_2:
  assumes n: "n < length actions"
  shows "num_edge_2 (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>Among the five edges of an action automaton only @{const edge_3} leaves the @{const running_loc}
location (start: @{const off_loc}, edge_2: @{const starting_loc}, end: @{const ending_loc}, instant:
@{const starting_loc}). So a propositional internal step from a config whose @{term \<open>Suc n\<close>}-th location
is @{const running_loc} must have fired @{const edge_3} at automaton @{term \<open>Suc n\<close>}: the source
location pins the fired edge.\<close>
lemma prop_edge_3_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and run: "L ! Suc n = running_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = edge_3 (actions ! n)"
proof -
  have l_run: "l = running_loc" using Lp run pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_run
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel: lifting ONE propositional @{const edge_3} step (the no-fluent-write
ending-duration edge) to a numeric @{const num_graph_impl.steps} step, preserving @{const REL}. The
propositional step is GIVEN (extracted from the propositional happening run); the numeric guard and
update fire on the extended store @{term vn} by monotonicity, tracking survives because @{const edge_3}
writes only the propositional @{const prop_to_lock} variables (fresh of the fluent variables), and the
@{const num_net_bounds} bound is re-established from the propositional post-bound (@{thm [source]
REL_bnd_from_proj}). The locations and clocks are those of the propositional step.\<close>
lemma num_edge_3_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and run: "L ! Suc n = running_loc"
      and n: "n < length actions"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (edge_3_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and fin: "fluent_in_bounds w"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle> \<and> REL vp' vn' w"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have L'_eq: "L' = L[Suc n := ending_loc]"
    using L'eq by (simp add: edge_3_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const edge_3}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}.\<close>
  have running_ne_ending: "running_loc \<noteq> ending_loc" by (simp add: locations_unique)
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    moreover have "L[Suc n := ending_loc] ! Suc n = ending_loc" using Sn_lt by simp
    ultimately show False using L'eq2 L'_eq run running_ne_ending by simp
  qed
  have edge3: "(l, b, g, Sil a, f, r, l') = edge_3 (actions ! n)"
    by (rule prop_edge_3_pinned[OF P E LOC run n pSuc])
  \<comment> \<open>The fired edge's components, read off @{const edge_3}.\<close>
  note edge_parts = edge3[unfolded edge_3_def Let_def, simplified prod.inject]
  \<comment> \<open>The numeric edge: @{const edge_3} verbatim, with the same guard and update.\<close>
  have NE: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc edge3 by (rule num_nth_auto_edge_3[OF n])
  \<comment> \<open>The numeric guard fires on the extended store; the update fires, preserving tracking.\<close>
  have NB: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  obtain vn' where
      NU: "is_upds vn f vn'"
    and LE: "vp' \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn' x = vn x"
    using is_upds_map_le[OF U le] by blast
  \<comment> \<open>@{const edge_3} writes only @{const prop_to_lock} variables, fresh of the fluents, so tracking
     survives.\<close>
  have f_eq: "f = map (inc_prop_lock_ab (- 1)) (over_all (actions ! n))"
    using edge3 by (simp add: edge_3_def Let_def)
  have fst_f: "fst ` set f = prop_to_lock ` set (over_all (actions ! n))"
    unfolding f_eq set_map image_image inc_prop_lock_ab_def by (simp add: comp_def)
  have aMem: "actions ! n \<in> set actions" using n by simp
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
  proof
    assume "fluent_to_var h \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and ph: "fluent_to_var h = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus False using ph fluent_var_notin_net_bounds[OF h] by simp
  qed
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound from the propositional post-bound and tracking.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  have fset_sub: "fst ` set f \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and xp: "x = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus "x \<in> dom vn" using xp dom_vn dom_map_of_num_net_bounds by auto
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
  proof -
    have "dom vn' = dom vn"
    proof (rule set_eqI)
      fix x
      show "x \<in> dom vn' \<longleftrightarrow> x \<in> dom vn"
      proof (cases "x \<in> fst ` set f")
        case True
        have "x \<in> dom vn" using True fset_sub by blast
        moreover have "x \<in> dom vn'"
          using NU True
        proof (induction f arbitrary: vn)
          case (Cons fe f)
          obtain y e where fe: "fe = (y, e)" by (cases fe)
          obtain v1 where v1: "is_upd vn (y, e) v1" and rest: "is_upds v1 f vn'"
            using Cons.prems(1) fe by (auto simp: is_upds_Cons_iff)
          obtain kk where v1_eq: "v1 = vn(y \<mapsto> kk)" using v1 by (auto simp: is_upd_def)
          show ?case
          proof (cases "x \<in> fst ` set f")
            case True
            show ?thesis using Cons.IH[OF rest True] .
          next
            case False
            hence xy: "x = y" using Cons.prems(2) fe by auto
            have "vn' x = v1 x" using is_upds_unchanged[OF rest] False by blast
            also have "\<dots> = Some kk" using v1_eq xy by simp
            finally show ?thesis by blast
          qed
        qed simp
        ultimately show ?thesis by blast
      next
        case False
        thus ?thesis using OFF[OF False] by (auto simp: domIff)
      qed
    qed
    thus ?thesis using dom_vn by simp
  qed
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TR fin vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TR BND by (auto intro: RELI)
qed

text \<open>A Munta update sequence whose written variables are all already in the store's domain leaves the
domain unchanged: each @{const is_upd} is a point override @{term \<open>v(x \<mapsto> k)\<close>}, which only adds @{term x}
to the domain, and here @{term x} is already present. This is the upper half of the domain-preservation
argument the run-lift needs when re-establishing the @{const num_net_bounds} bound on the numeric
post-store (the lower half is @{const num_tracks} / the propositional projection).\<close>
lemma is_upds_dom_eq:
  assumes "is_upds v us v'"
      and "fst ` set us \<subseteq> dom v"
    shows "dom v' = dom v"
  using assms
proof (induction us arbitrary: v)
  case Nil
  thus ?case by (auto elim: is_upds.cases)
next
  case (Cons u us)
  obtain x e where u: "u = (x, e)" by (cases u)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 us v'"
    using Cons.prems(1) u by (auto simp: is_upds_Cons_iff)
  obtain k where v1_eq: "v1 = v(x \<mapsto> k)" using v1 by (auto simp: is_upd_def)
  have xdom: "x \<in> dom v" using Cons.prems(2) u by simp
  have dom_v1: "dom v1 = dom v" using v1_eq xdom by auto
  have "fst ` set us \<subseteq> dom v1" using Cons.prems(2) dom_v1 by auto
  thus ?case using Cons.IH[OF rest] dom_v1 by simp
qed

text \<open>A Munta update sequence only ever grows the store's domain: each @{const is_upd} point-overrides
its variable, which can add a binding but never deletes one.\<close>
lemma is_upds_dom_mono:
  assumes "is_upds v us v'"
  shows "dom v \<subseteq> dom v'"
  using assms
proof (induction us arbitrary: v)
  case Nil
  thus ?case by (auto elim: is_upds.cases)
next
  case (Cons u us)
  obtain x e where u: "u = (x, e)" by (cases u)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 us v'"
    using Cons.prems u by (auto simp: is_upds_Cons_iff)
  obtain k where v1_eq: "v1 = v(x \<mapsto> k)" using v1 by (auto simp: is_upd_def)
  have "dom v \<subseteq> dom v1" using v1_eq by auto
  thus ?case using Cons.IH[OF rest] by blast
qed

text \<open>Every variable a Munta update sequence writes ends up in the domain of the resulting store:
each @{const is_upd} point-overrides its variable to a defined value, and later updates never delete
it (@{thm [source] is_upds_dom_mono}). Used to place the written propositional/fluent variables inside
the numeric store's domain.\<close>
lemma is_upds_writes_dom:
  assumes "is_upds v us v'"
  shows "fst ` set us \<subseteq> dom v'"
  using assms
proof (induction us arbitrary: v)
  case Nil
  thus ?case by simp
next
  case (Cons u us)
  obtain x e where u: "u = (x, e)" by (cases u)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 us v'"
    using Cons.prems u by (auto simp: is_upds_Cons_iff)
  obtain k where v1_eq: "v1 = v(x \<mapsto> k)" using v1 by (auto simp: is_upd_def)
  have "x \<in> dom v1" using v1_eq by auto
  hence "x \<in> dom v'" using is_upds_dom_mono[OF rest] by blast
  thus ?case using Cons.IH[OF rest] u by auto
qed

text \<open>The @{const off_loc} source location pins the fired edge to @{const start_edge}: among the five
edges of an action automaton only @{const start_edge} leaves @{const off_loc} (edge_2: @{const
starting_loc}, edge_3: @{const running_loc}, end: @{const ending_loc}, instant: @{const starting_loc}).
So a propositional internal step from a config whose @{term \<open>Suc n\<close>}-th location is @{const off_loc} must
have fired @{const start_edge} at automaton @{term \<open>Suc n\<close>}.\<close>
lemma prop_start_edge_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and off: "L ! Suc n = off_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = start_edge (actions ! n)"
proof -
  have l_off: "l = off_loc" using Lp off pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_off
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel for a fluent-WRITING happening edge: lifting ONE propositional
@{const start_edge} step (the @{text at_start} snap of @{term \<open>actions ! n\<close>}) to a numeric
@{const num_graph_impl.steps} step whose numeric edge is the AUGMENTED @{const num_start_edge}, carrying
the numeric guard @{const num_pre_guard} and the appended numeric update @{const num_upd}. Unlike
@{thm [source] num_edge_3_step_lift} this CHANGES the abstract valuation: the numeric post-store tracks
@{term \<open>num_plan.num_rat_impl.snap_num_update s w = apply_upds (set (upds s)) w\<close>}. The numeric guard
holds by @{thm [source] check_bexp_comps_guard} (the snap's @{term n_pre} comparisons are satisfied at
@{term w} and faithful), the numeric update fires by @{thm [source] is_upds_num_upd} landing on
@{const apply_upds}, the two update phases compose by @{thm [source] is_upds_appendI}, and the
@{const num_net_bounds} bound on the post-store is re-established from the propositional post-bound and
the post-fold being @{const fluent_in_bounds} (@{thm [source] REL_bnd_from_proj}). Edge-pinning is by
@{thm [source] prop_start_edge_pinned} (source location @{const off_loc}).\<close>
lemma num_edge_upd_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and off: "L ! Suc n = off_loc"
      and n: "n < length actions"
      and s_eq: "s = at_start (actions ! n)"
      and mem: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (start_edge_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and wok: "num_val_ok w"
      and fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update s w)"
      and sat: "sat_comps w (set (n_pre s))"
      and upd_lhs: "fst ` set (upds s) \<subseteq> set nfluents"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>
                 \<and> REL vp' vn' (num_plan.num_rat_impl.snap_num_update s w)"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have aMem: "actions ! n \<in> set actions" using n by simp
  let ?us = "upds s"
  let ?fn = "num_upd s"
  have fn_eq: "?fn = map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) ?us"
    by (simp add: num_upd_def)
  have w'_eq: "num_plan.num_rat_impl.snap_num_update s w = apply_upds (set ?us) w"
    by (simp add: num_plan.num_rat_impl.snap_num_update_def)
  \<comment> \<open>The numeric post-fold bound, restated in @{const apply_upds} form for @{thm [source] is_upds_num_upd}.\<close>
  have fin': "fluent_in_bounds (apply_upds (set ?us) w)" using fin w'_eq by simp
  \<comment> \<open>The contract facts for the @{text at_start} snap, instantiated at @{term w}.\<close>
  have us_func: "upds_functional_list ?us"
    using upds_functional_start aMem s_eq by blast
  have us_ncr: "upds_no_cross_read_list ?us"
    using upds_no_cross_read_start aMem s_eq by blast
  have us_ok: "fl \<in> set nfluents \<and> nexp_ok w e" if "(fl, e) \<in> set ?us" for fl e
  proof -
    have "nexp_ok w e" using happening_snap_nexp_ok[OF mem _ wok] that by blast
    moreover have "fl \<in> set nfluents" using upd_lhs that by blast
    ultimately show ?thesis by blast
  qed
  have pre_ok: "\<forall>cc \<in> set (n_pre s). comp_ok w cc"
    using snap_pre_comp_ok_start aMem s_eq wok by blast
  \<comment> \<open>The numeric pre-guard holds on the extended store.\<close>
  have guard_ok: "check_bexp vn (num_pre_guard s) True"
    unfolding num_pre_guard_def by (rule check_bexp_comps_guard[OF tr pre_ok sat])
  have L'_eq: "L' = L[Suc n := starting_loc]"
    using L'eq by (simp add: start_edge_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const start_edge}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}, which goes to
     @{const starting_loc} \<noteq> @{const off_loc}.\<close>
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    hence "L' ! Suc n = off_loc" using L'eq2 off by simp
    moreover have "L' ! Suc n = starting_loc" using L'_eq Sn_lt by simp
    ultimately show False by (simp add: locations_unique)
  qed
  have edge_se: "(l, b, g, Sil a, f, r, l') = start_edge (actions ! n)"
    by (rule prop_start_edge_pinned[OF P E LOC off n pSuc])
  \<comment> \<open>The numeric edge: the AUGMENTED @{const num_start_edge}, in the numeric net at @{term \<open>Suc n\<close>}.\<close>
  have NE: "(l, bexp.and b (num_pre_guard s), g, Sil a, f @ ?fn, r, l')
              \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc
    using num_nth_auto_num_start_edge[OF n]
    unfolding num_start_edge_def augment_edge_def edge_se[symmetric] s_eq[symmetric] Let_def
    by (simp add: prod.case)
  \<comment> \<open>Combined guard fires on @{term vn}.\<close>
  have bvn: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have NB: "check_bexp vn (bexp.and b (num_pre_guard s)) True"
    using check_bexp_is_val.intros(3)[OF bvn guard_ok] by simp
  \<comment> \<open>Fluent variables are fresh of the propositional update @{term f}.\<close>
  have f_in_vp': "fst ` set f \<subseteq> dom vp'" by (rule is_upds_writes_dom[OF U])
  have v'_fresh: "fluent_to_var h \<notin> dom vp'" if h: "h \<in> set nfluents" for h
  proof -
    have "dom vp' = dom (map_of net_bounds)"
      using pbnd' unfolding Simple_Network_Language.bounded_def by blast
    thus ?thesis using fluent_var_notin_net_bounds[OF h] by simp
  qed
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
    using f_in_vp' v'_fresh[OF h] by blast
  \<comment> \<open>Propositional updates fire on @{term vn}, preserving tracking.\<close>
  obtain vn_mid where
      NUmid: "is_upds vn f vn_mid"
    and LEmid: "vp' \<subseteq>\<^sub>m vn_mid"
    and OFFmid: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn_mid x = vn x"
    using is_upds_map_le[OF U le] by blast
  have TRmid: "num_tracks vn_mid w" by (rule num_tracks_pres_unwritten[OF tr NUmid fresh])
  \<comment> \<open>Numeric updates fire on @{term vn_mid}, landing on the abstract simultaneous override.\<close>
  obtain vn' where
      NUnum: "is_upds vn_mid ?fn vn'"
    and TRnum: "num_tracks vn' (apply_upds (set ?us) w)"
    and OFFnum: "\<And>x. x \<notin> fluent_to_var ` fst ` set ?us \<Longrightarrow> vn' x = vn_mid x"
    using is_upds_num_upd[OF TRmid us_func us_ncr us_ok, folded fn_eq] by metis
  have NU: "is_upds vn (f @ ?fn) vn'" by (rule is_upds_appendI[OF NUmid NUnum])
  \<comment> \<open>@{term vp'} survives: the numeric half writes only fresh fluent variables.\<close>
  have LE: "vp' \<subseteq>\<^sub>m vn'"
  proof (unfold map_le_def, intro ballI)
    fix x assume xdom: "x \<in> dom vp'"
    have "x \<notin> fluent_to_var ` fst ` set ?us"
    proof
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      hence "fluent_to_var fl \<notin> dom vp'" by (rule v'_fresh)
      thus False using xfl xdom by simp
    qed
    hence "vn' x = vn_mid x" by (rule OFFnum)
    moreover have "vp' x = vn_mid x" using LEmid xdom by (auto simp: map_le_def)
    ultimately show "vp' x = vn' x" by simp
  qed
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound on the post-store.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  \<comment> \<open>The combined update writes only variables already present in @{term vn}: props (net_bounds) and
     fluent variables, both inside @{const num_net_bounds}.\<close>
  have fset_sub: "fst ` set (f @ ?fn) \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set (f @ ?fn)"
    hence "x \<in> fst ` set f \<union> fluent_to_var ` fst ` set ?us" by (auto simp: fn_eq)
    thus "x \<in> dom vn"
    proof
      assume "x \<in> fst ` set f"
      hence "x \<in> dom vp'" using f_in_vp' by blast
      thus "x \<in> dom vn" using vp'_dom dom_vn dom_map_of_num_net_bounds by auto
    next
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      thus "x \<in> dom vn" using xfl dom_vn dom_map_of_num_net_bounds by auto
    qed
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TRnum fin' vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TRnum BND w'_eq by (auto intro: RELI)
qed

text \<open>The configuration-level relation between a propositional config and a numeric config: same
locations, same clocks, and the stores related by @{const REL}.\<close>
definition RELC where
"RELC cp cn w \<longleftrightarrow> (case cp of (Lp, vp, cup) \<Rightarrow> case cn of (Ln, vn, cun) \<Rightarrow>
   Lp = Ln \<and> cup = cun \<and> REL vp vn w)"

lemma RELCI:
  assumes "REL vp vn w"
  shows "RELC (L, vp, c) (L, vn, c) w"
  using assms unfolding RELC_def by simp

lemma RELC_locD: "RELC (Lp, vp, cup) (Ln, vn, cun) w \<Longrightarrow> Lp = Ln"
  and RELC_clkD: "RELC (Lp, vp, cup) (Ln, vn, cun) w \<Longrightarrow> cup = cun"
  and RELC_relD: "RELC (Lp, vp, cup) (Ln, vn, cun) w \<Longrightarrow> REL vp vn w"
  unfolding RELC_def by auto

text \<open>The START phase run-lift, a FOLD-EVOLVING analogue of the \<open>RLP\<close> edge_3 phase-lift: each
@{const start_edge_effect} step both fires a numeric edge AND advances the abstract numeric fold by the
fired snap @{term \<open>at_start (actions ! n)\<close>}. By induction on the index suffix @{term ns}, threading the
running propositional config @{term sp}, the running numeric store @{term vn}, and the accumulated snap
prefix @{term ys} (a distinct sublist of happening @{term i}). The per-step kernel @{thm [source]
num_edge_upd_step_lift} is discharged from the running fold @{term \<open>num_plan.num_rat_impl.happening_num_update ys (snd (M i))\<close>}:
@{const num_val_ok} via @{thm [source] happening_num_update_preserves_num_val_ok}, the post-fold bound via
@{thm [source] running_prefix_in_bounds}, the precondition satisfaction via @{thm [source] happening_snap_pre_sat}
+ @{thm [source] sat_comps_running_prefix}, and the write-set/membership facts from the locale and
@{thm [source] happ_at_index_decomp}. The propositional per-step structural facts (the @{const off_loc} source
location, the length, the projection bound on the post-store) are supplied per run-position by the
caller hypothesis @{text struct}.\<close>
lemma num_start_phase_lift:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
  assumes ns_start: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions
                            \<and> is_starting_index (planning_sem.time_index i) n"
      and ys_act: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and zs_dist: "distinct (ys @ map (\<lambda>n. at_start (actions ! n)) ns @ zs)"
      and zs_full: "set (ys @ map (\<lambda>n. at_start (actions ! n)) ns @ zs)
                      = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and prun: "graph_impl.steps (sp # seq_apply (map start_edge_effect ns) sp)"
      and struct: "\<And>k. k < length ns \<Longrightarrow>
                     fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k) ! Suc (ns ! k) = off_loc
                     \<and> length (fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k)) = length net_automata
                     \<and> Simple_Network_Language.bounded (map_of net_bounds)
                           (fst (snd (start_edge_effect (ns ! k)
                                       ((sp # seq_apply (map start_edge_effect ns) sp) ! k))))"
      and rel0: "RELC sp cn (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
    shows "\<exists>nss. num_graph_impl.steps (cn # nss)
                 \<and> length nss = length ns
                 \<and> RELC (last (sp # seq_apply (map start_edge_effect ns) sp)) (last (cn # nss))
                        (num_plan.num_rat_impl.happening_num_update
                           (ys @ map (\<lambda>n. at_start (actions ! n)) ns) (snd (M i)))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  have base_val_ok: "num_val_ok (snd (M i))"
    using i by (intro num_seq_val_ok[OF vss m0]) simp
  \<comment> \<open>The generalized inductive claim: over any starting-index suffix @{term as}, running config
     @{term s}, accumulated snap-prefix @{term bs} (a distinct happening-sublist), residual @{term cs}.\<close>
  have gen: "\<exists>nss. num_graph_impl.steps (dn # nss)
                   \<and> length nss = length as
                   \<and> RELC (last (s # seq_apply (map start_edge_effect as) s)) (last (dn # nss))
                          (?w (bs @ map (\<lambda>n. at_start (actions ! n)) as))"
    if as_start: "\<And>n. n \<in> set as \<Longrightarrow> n < length actions
                          \<and> is_starting_index (planning_sem.time_index i) n"
       and bs_act: "\<And>t. t \<in> set bs \<Longrightarrow> \<exists>a \<in> set actions. t = at_start a \<or> t = at_end a"
       and bs_sub: "set bs \<subseteq> ?S"
       and cs_dist: "distinct (bs @ map (\<lambda>n. at_start (actions ! n)) as @ cs)"
       and cs_full: "set (bs @ map (\<lambda>n. at_start (actions ! n)) as @ cs) = ?S"
       and srun: "graph_impl.steps (s # seq_apply (map start_edge_effect as) s)"
       and sstruct: "\<And>k. k < length as \<Longrightarrow>
                       fst ((s # seq_apply (map start_edge_effect as) s) ! k) ! Suc (as ! k) = off_loc
                       \<and> length (fst ((s # seq_apply (map start_edge_effect as) s) ! k)) = length net_automata
                       \<and> Simple_Network_Language.bounded (map_of net_bounds)
                             (fst (snd (start_edge_effect (as ! k)
                                         ((s # seq_apply (map start_edge_effect as) s) ! k))))"
       and srel: "RELC s dn (?w bs)"
     for as s dn bs cs
    using that
  proof (induction as arbitrary: s dn bs cs)
    case Nil
    show ?case
    proof (intro exI[where x = "[]"] conjI)
      show "num_graph_impl.steps (dn # [])" by (rule num_graph_impl.steps.intros(1))
    next
      show "length [] = length []" by simp
    next
      show "RELC (last (s # seq_apply (map start_edge_effect []) s)) (last (dn # []))
                 (?w (bs @ map (\<lambda>n. at_start (actions ! n)) []))"
        by (simp only: list.map seq_apply_Nil append_Nil2 last_ConsL) (rule Nil.prems(8))
    qed
  next
    case (Cons n as')
    let ?sn = "at_start (actions ! n)"
    let ?s' = "start_edge_effect n s"
    \<comment> \<open>Decompose the running config and the @{const RELC}-related numeric start.\<close>
    obtain L vp c where s: "s = (L, vp, c)" by (cases s)
    obtain Ln dvn cn0 where dn: "dn = (Ln, dvn, cn0)" by (cases dn)
    have Leq: "Ln = L" by (rule RELC_locD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have ceq: "cn0 = c" by (rule RELC_clkD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have relS: "REL vp dvn (?w bs)" by (rule RELC_relD[OF Cons.prems(8)[unfolded s dn]])
    \<comment> \<open>Head index facts.\<close>
    have nmem: "n \<in> set (n # as')" by simp
    have n_lt: "n < length actions"
      and n_start: "is_starting_index (planning_sem.time_index i) n"
      using Cons.prems(1)[OF nmem] by blast+
    have aMem: "actions ! n \<in> set actions" using n_lt by simp
    \<comment> \<open>The fired start-snap is in happening @{term i}.\<close>
    have sn_mem: "?sn \<in> ?S"
      unfolding happ_at_index_decomp
      using n_lt n_start by blast
    \<comment> \<open>Run decomposition: the first edge and the tail run over @{term \<open>?s'\<close>}.\<close>
    have run_unfold: "s # seq_apply (map start_edge_effect (n # as')) s
                        = s # ?s' # seq_apply (map start_edge_effect as') ?s'"
      by (simp only: list.map seq_apply_Cons_Cons)
    have run_dec: "graph_impl.steps (s # ?s' # seq_apply (map start_edge_effect as') ?s')"
      using Cons.prems(6) run_unfold by simp
    \<comment> \<open>The propositional first edge and the tail run.\<close>
    have pstep0: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst ?s', fst (snd ?s'), snd (snd ?s')\<rangle>"
      using run_dec unfolding s by (cases ?s') (auto elim: graph_impl.steps.cases simp: prod.case)
    have tailrun: "graph_impl.steps (?s' # seq_apply (map start_edge_effect as') ?s')"
      using run_dec by (rule graph_impl.steps_ConsD) simp
    \<comment> \<open>The structural facts at run-position 0 (the head step on @{term s}).\<close>
    have off0: "L ! Suc n = off_loc"
      and Llen0: "length L = length net_automata"
      and pbnd0: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s'))"
      using Cons.prems(7)[of 0] unfolding s by simp_all
    \<comment> \<open>The new accumulated snap-prefix and the list-shape rearrangement that re-targets the
       distinctness/fullness premises of the IH.\<close>
    define bs' where "bs' = bs @ [?sn]"
    have list_rearr: "bs @ map (\<lambda>m. at_start (actions ! m)) (n # as') @ cs
                        = bs' @ map (\<lambda>m. at_start (actions ! m)) as' @ cs"
      unfolding bs'_def by simp
    have cs_dist': "distinct (bs' @ map (\<lambda>m. at_start (actions ! m)) as' @ cs)"
      using Cons.prems(4)[unfolded list_rearr] .
    have cs_full': "set (bs' @ map (\<lambda>m. at_start (actions ! m)) as' @ cs) = ?S"
      using Cons.prems(5)[unfolded list_rearr] .
    \<comment> \<open>@{term \<open>?sn\<close>} is fresh of the already-folded prefix @{term bs}.\<close>
    have sn_notin_bs: "?sn \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr[symmetric])
    \<comment> \<open>The fold-append identity: snapping @{term \<open>?sn\<close>} onto the @{term bs}-fold IS the @{term bs'}-fold
       (the @{const fold} LANDMINE: rewrite via @{thm [source] fold_append}, not @{text simp}).\<close>
    have foldapp: "num_plan.num_rat_impl.snap_num_update ?sn (?w bs) = ?w bs'"
      unfolding bs'_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append) (simp add: comp_def)
    \<comment> \<open>The four numeric-fold kernel hypotheses for the @{term \<open>?sn\<close>} step at @{term \<open>?w bs\<close>}.\<close>
    have wok: "num_val_ok (?w bs)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok Cons.prems(2)])
    have fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      unfolding foldapp by (rule running_prefix_in_bounds[OF vss m0 i cs_dist' cs_full'])
    have sat_eq: "sat_comps (?w bs) (set (n_pre ?sn)) = sat_comps (snd (M i)) (set (n_pre ?sn))"
      by (rule sat_comps_running_prefix[OF sn_mem Cons.prems(3) sn_notin_bs])
    have sat: "sat_comps (?w bs) (set (n_pre ?sn))"
      unfolding sat_eq by (rule happening_snap_pre_sat[OF vss i sn_mem])
    have upd_lhs: "fst ` set (upds ?sn) \<subseteq> set nfluents"
      using snap_writes_nfluents_start aMem by blast
    \<comment> \<open>Apply the per-step kernel: the @{term \<open>?sn\<close>} edge lifts to a numeric step from @{term dn}.\<close>
    have L'eq: "fst ?s' = fst (start_edge_effect n (L, vp, c))" unfolding s by simp
    obtain vn' where
        numstep: "num_net_impl.sem \<turnstile> \<langle>L, dvn, c\<rangle> \<rightarrow> \<langle>fst ?s', vn', snd (snd ?s')\<rangle>"
      and relE: "REL (fst (snd ?s')) vn' (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      using num_edge_upd_step_lift[OF relS Llen0 off0 n_lt HOL.refl sn_mem
              pstep0 L'eq pbnd0 wok fin sat upd_lhs] by blast
    \<comment> \<open>Package the numeric post-config and its @{const RELC}-relation at the advanced fold @{term \<open>?w bs'\<close>}.\<close>
    obtain L' vp' c' where s'eq: "?s' = (L', vp', c')" by (cases ?s')
    define dn' where "dn' = (L', vn', c')"
    have relC': "RELC ?s' dn' (?w bs')"
      unfolding dn'_def s'eq
      using RELCI[OF relE[unfolded foldapp]] unfolding s'eq by simp
    \<comment> \<open>The IH premises for the tail suffix @{term as'} from @{term \<open>?s'\<close>}, @{term dn'}, @{term bs'}.\<close>
    have as'_start: "m < length actions \<and> is_starting_index (planning_sem.time_index i) m"
      if "m \<in> set as'" for m
      using Cons.prems(1) that by simp
    have bs'_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs'" for t
      using that aMem Cons.prems(2) unfolding bs'_def by auto
    have bs'_sub: "set bs' \<subseteq> ?S"
      using Cons.prems(3) sn_mem unfolding bs'_def by auto
    \<comment> \<open>Re-index the per-run-position structural premise: position @{term k} of the tail run is
       position @{term \<open>Suc k\<close>} of the full run.\<close>
    have sstruct': "fst ((?s' # seq_apply (map start_edge_effect as') ?s') ! k) ! Suc (as' ! k) = off_loc
                    \<and> length (fst ((?s' # seq_apply (map start_edge_effect as') ?s') ! k)) = length net_automata
                    \<and> Simple_Network_Language.bounded (map_of net_bounds)
                          (fst (snd (start_edge_effect (as' ! k)
                                      ((?s' # seq_apply (map start_edge_effect as') ?s') ! k))))"
      if k: "k < length as'" for k
    proof -
      have Sk: "Suc k < length (n # as')" using k by simp
      have idx: "(s # seq_apply (map start_edge_effect (n # as')) s) ! Suc k
                   = (?s' # seq_apply (map start_edge_effect as') ?s') ! k"
        unfolding run_unfold by simp
      show ?thesis using Cons.prems(7)[OF Sk] unfolding idx by simp
    qed
    have ih: "\<exists>nss. num_graph_impl.steps (dn' # nss)
                   \<and> length nss = length as'
                   \<and> RELC (last (?s' # seq_apply (map start_edge_effect as') ?s')) (last (dn' # nss))
                          (?w (bs' @ map (\<lambda>m. at_start (actions ! m)) as'))"
      by (rule Cons.IH[OF as'_start bs'_act bs'_sub cs_dist' cs_full' tailrun sstruct' relC'])
    obtain nss' where
        nrun': "num_graph_impl.steps (dn' # nss')"
      and lnss': "length nss' = length as'"
      and rlast': "RELC (last (?s' # seq_apply (map start_edge_effect as') ?s')) (last (dn' # nss'))
                        (?w (bs' @ map (\<lambda>m. at_start (actions ! m)) as'))"
      using ih by (elim exE conjE)
    \<comment> \<open>Splice: the head numeric step from @{term dn} to @{term dn'} in front of the tail numeric run.\<close>
    have headstep: "num_graph_impl.steps [dn, dn']"
      unfolding dn dn'_def Leq ceq s'eq
      by (rule num_single_step_intro) (use numstep s'eq in \<open>simp add: prod.case\<close>)
    have spliced: "num_graph_impl.steps (dn # dn' # nss')"
      using num_steps_extend[OF headstep] nrun' by simp
    show ?case
    proof (intro exI[where x = "dn' # nss'"] conjI)
      show "num_graph_impl.steps (dn # dn' # nss')" by (rule spliced)
    next
      show "length (dn' # nss') = length (n # as')" using lnss' by simp
    next
      have bsrew: "bs' @ map (\<lambda>m. at_start (actions ! m)) as'
                     = bs @ map (\<lambda>m. at_start (actions ! m)) (n # as')"
        unfolding bs'_def by simp
      have lastrew: "last (s # seq_apply (map start_edge_effect (n # as')) s)
                       = last (?s' # seq_apply (map start_edge_effect as') ?s')"
        unfolding run_unfold by simp
      show "RELC (last (s # seq_apply (map start_edge_effect (n # as')) s)) (last (dn # dn' # nss'))
                 (?w (bs @ map (\<lambda>m. at_start (actions ! m)) (n # as')))"
        using rlast' unfolding lastrew bsrew by simp
    qed
  qed
  show ?thesis
    by (rule gen[OF ns_start ys_act ys_sub zs_dist zs_full prun struct rel0])
qed

text \<open>The @{const ending_loc} source location pins the fired edge to @{const end_edge}: among the five
edges of an action automaton only @{const end_edge} leaves @{const ending_loc} (start: @{const off_loc},
edge_2: @{const starting_loc}, edge_3: @{const running_loc}, instant: @{const starting_loc}). So a
propositional internal step from a config whose @{term \<open>Suc n\<close>}-th location is @{const ending_loc} must
have fired @{const end_edge} at automaton @{term \<open>Suc n\<close>}.\<close>
lemma prop_end_edge_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and end0: "L ! Suc n = ending_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = end_edge (actions ! n)"
proof -
  have l_end: "l = ending_loc" using Lp end0 pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_end
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The END analogue of @{thm [source] num_edge_upd_step_lift}: the reusable per-step kernel for a
fluent-WRITING happening edge, lifting ONE propositional @{const end_edge} step (the @{text at_end} snap
of @{term \<open>actions ! n\<close>}) to a numeric @{const num_graph_impl.steps} step whose numeric edge is the
AUGMENTED @{const num_end_edge}. The numeric post-store tracks
@{term \<open>num_plan.num_rat_impl.snap_num_update s w = apply_upds (set (upds s)) w\<close>}; everything is the
START kernel with start swapped to end, the source location pinned to @{const ending_loc} (via
@{thm [source] prop_end_edge_pinned}) and the post location at @{const off_loc}.\<close>
lemma num_edge_upd_step_lift_end:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and end0: "L ! Suc n = ending_loc"
      and n: "n < length actions"
      and s_eq: "s = at_end (actions ! n)"
      and mem: "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (end_edge_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and wok: "num_val_ok w"
      and fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update s w)"
      and sat: "sat_comps w (set (n_pre s))"
      and upd_lhs: "fst ` set (upds s) \<subseteq> set nfluents"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>
                 \<and> REL vp' vn' (num_plan.num_rat_impl.snap_num_update s w)"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have aMem: "actions ! n \<in> set actions" using n by simp
  let ?us = "upds s"
  let ?fn = "num_upd s"
  have fn_eq: "?fn = map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) ?us"
    by (simp add: num_upd_def)
  have w'_eq: "num_plan.num_rat_impl.snap_num_update s w = apply_upds (set ?us) w"
    by (simp add: num_plan.num_rat_impl.snap_num_update_def)
  \<comment> \<open>The numeric post-fold bound, restated in @{const apply_upds} form for @{thm [source] is_upds_num_upd}.\<close>
  have fin': "fluent_in_bounds (apply_upds (set ?us) w)" using fin w'_eq by simp
  \<comment> \<open>The contract facts for the @{text at_end} snap, instantiated at @{term w}.\<close>
  have us_func: "upds_functional_list ?us"
    using upds_functional_end aMem s_eq by blast
  have us_ncr: "upds_no_cross_read_list ?us"
    using upds_no_cross_read_end aMem s_eq by blast
  have us_ok: "fl \<in> set nfluents \<and> nexp_ok w e" if "(fl, e) \<in> set ?us" for fl e
  proof -
    have "nexp_ok w e" using happening_snap_nexp_ok[OF mem _ wok] that by blast
    moreover have "fl \<in> set nfluents" using upd_lhs that by blast
    ultimately show ?thesis by blast
  qed
  have pre_ok: "\<forall>cc \<in> set (n_pre s). comp_ok w cc"
    using snap_pre_comp_ok_end aMem s_eq wok by blast
  \<comment> \<open>The numeric pre-guard holds on the extended store.\<close>
  have guard_ok: "check_bexp vn (num_pre_guard s) True"
    unfolding num_pre_guard_def by (rule check_bexp_comps_guard[OF tr pre_ok sat])
  have L'_eq: "L' = L[Suc n := off_loc]"
    using L'eq by (simp add: end_edge_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const end_edge}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}, which goes to
     @{const off_loc} \<noteq> @{const ending_loc}.\<close>
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    hence "L' ! Suc n = ending_loc" using L'eq2 end0 by simp
    moreover have "L' ! Suc n = off_loc" using L'_eq Sn_lt by simp
    ultimately show False by (simp add: locations_unique)
  qed
  have edge_se: "(l, b, g, Sil a, f, r, l') = end_edge (actions ! n)"
    by (rule prop_end_edge_pinned[OF P E LOC end0 n pSuc])
  \<comment> \<open>The numeric edge: the AUGMENTED @{const num_end_edge}, in the numeric net at @{term \<open>Suc n\<close>}.\<close>
  have NE: "(l, bexp.and b (num_pre_guard s), g, Sil a, f @ ?fn, r, l')
              \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc
    using num_nth_auto_num_end_edge[OF n]
    unfolding num_end_edge_def augment_edge_def edge_se[symmetric] s_eq[symmetric] Let_def
    by (simp add: prod.case)
  \<comment> \<open>Combined guard fires on @{term vn}.\<close>
  have bvn: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have NB: "check_bexp vn (bexp.and b (num_pre_guard s)) True"
    using check_bexp_is_val.intros(3)[OF bvn guard_ok] by simp
  \<comment> \<open>Fluent variables are fresh of the propositional update @{term f}.\<close>
  have f_in_vp': "fst ` set f \<subseteq> dom vp'" by (rule is_upds_writes_dom[OF U])
  have v'_fresh: "fluent_to_var h \<notin> dom vp'" if h: "h \<in> set nfluents" for h
  proof -
    have "dom vp' = dom (map_of net_bounds)"
      using pbnd' unfolding Simple_Network_Language.bounded_def by blast
    thus ?thesis using fluent_var_notin_net_bounds[OF h] by simp
  qed
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
    using f_in_vp' v'_fresh[OF h] by blast
  \<comment> \<open>Propositional updates fire on @{term vn}, preserving tracking.\<close>
  obtain vn_mid where
      NUmid: "is_upds vn f vn_mid"
    and LEmid: "vp' \<subseteq>\<^sub>m vn_mid"
    and OFFmid: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn_mid x = vn x"
    using is_upds_map_le[OF U le] by blast
  have TRmid: "num_tracks vn_mid w" by (rule num_tracks_pres_unwritten[OF tr NUmid fresh])
  \<comment> \<open>Numeric updates fire on @{term vn_mid}, landing on the abstract simultaneous override.\<close>
  obtain vn' where
      NUnum: "is_upds vn_mid ?fn vn'"
    and TRnum: "num_tracks vn' (apply_upds (set ?us) w)"
    and OFFnum: "\<And>x. x \<notin> fluent_to_var ` fst ` set ?us \<Longrightarrow> vn' x = vn_mid x"
    using is_upds_num_upd[OF TRmid us_func us_ncr us_ok, folded fn_eq] by metis
  have NU: "is_upds vn (f @ ?fn) vn'" by (rule is_upds_appendI[OF NUmid NUnum])
  \<comment> \<open>@{term vp'} survives: the numeric half writes only fresh fluent variables.\<close>
  have LE: "vp' \<subseteq>\<^sub>m vn'"
  proof (unfold map_le_def, intro ballI)
    fix x assume xdom: "x \<in> dom vp'"
    have "x \<notin> fluent_to_var ` fst ` set ?us"
    proof
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      hence "fluent_to_var fl \<notin> dom vp'" by (rule v'_fresh)
      thus False using xfl xdom by simp
    qed
    hence "vn' x = vn_mid x" by (rule OFFnum)
    moreover have "vp' x = vn_mid x" using LEmid xdom by (auto simp: map_le_def)
    ultimately show "vp' x = vn' x" by simp
  qed
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound on the post-store.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  \<comment> \<open>The combined update writes only variables already present in @{term vn}: props (net_bounds) and
     fluent variables, both inside @{const num_net_bounds}.\<close>
  have fset_sub: "fst ` set (f @ ?fn) \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set (f @ ?fn)"
    hence "x \<in> fst ` set f \<union> fluent_to_var ` fst ` set ?us" by (auto simp: fn_eq)
    thus "x \<in> dom vn"
    proof
      assume "x \<in> fst ` set f"
      hence "x \<in> dom vp'" using f_in_vp' by blast
      thus "x \<in> dom vn" using vp'_dom dom_vn dom_map_of_num_net_bounds by auto
    next
      assume "x \<in> fluent_to_var ` fst ` set ?us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set ?us" by auto
      obtain e where "(fl, e) \<in> set ?us" using flmem by auto
      hence "fl \<in> set nfluents" using us_ok by blast
      thus "x \<in> dom vn" using xfl dom_vn dom_map_of_num_net_bounds by auto
    qed
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TRnum fin' vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TRnum BND w'_eq by (auto intro: RELI)
qed


text \<open>The END phase run-lift, the END analogue of @{thm [source] num_start_phase_lift}: each
@{const end_edge_effect} step both fires a numeric edge AND advances the abstract numeric fold by the
fired snap @{term \<open>at_end (actions ! n)\<close>}. By induction on the index suffix @{term ns}, threading the
running propositional config @{term sp}, the running numeric store @{term vn}, and the accumulated snap
prefix @{term ys} (a distinct sublist of happening @{term i}). The per-step kernel @{thm [source]
num_edge_upd_step_lift_end} is discharged from the running fold exactly as in the START phase:
@{const num_val_ok} via @{thm [source] happening_num_update_preserves_num_val_ok}, the post-fold bound
via @{thm [source] running_prefix_in_bounds}, the precondition satisfaction via
@{thm [source] happening_snap_pre_sat} + @{thm [source] sat_comps_running_prefix}, and the
write-set/membership facts from the locale and @{thm [source] happ_at_index_decomp} (ENDING indices land
in the @{text at_end}-image). The propositional per-step structural facts (the @{const ending_loc} source
location, the length, the projection bound on the post-store) are supplied per run-position by the caller
hypothesis @{text struct}.\<close>
lemma num_end_phase_lift:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
  assumes ns_end: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions
                          \<and> is_ending_index (planning_sem.time_index i) n"
      and ys_act: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and zs_dist: "distinct (ys @ map (\<lambda>n. at_end (actions ! n)) ns @ zs)"
      and zs_full: "set (ys @ map (\<lambda>n. at_end (actions ! n)) ns @ zs)
                      = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and prun: "graph_impl.steps (sp # seq_apply (map end_edge_effect ns) sp)"
      and struct: "\<And>k. k < length ns \<Longrightarrow>
                     fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k) ! Suc (ns ! k) = ending_loc
                     \<and> length (fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k)) = length net_automata
                     \<and> Simple_Network_Language.bounded (map_of net_bounds)
                           (fst (snd (end_edge_effect (ns ! k)
                                       ((sp # seq_apply (map end_edge_effect ns) sp) ! k))))"
      and rel0: "RELC sp cn (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
    shows "\<exists>nss. num_graph_impl.steps (cn # nss)
                 \<and> length nss = length ns
                 \<and> RELC (last (sp # seq_apply (map end_edge_effect ns) sp)) (last (cn # nss))
                        (num_plan.num_rat_impl.happening_num_update
                           (ys @ map (\<lambda>n. at_end (actions ! n)) ns) (snd (M i)))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  have base_val_ok: "num_val_ok (snd (M i))"
    using i by (intro num_seq_val_ok[OF vss m0]) simp
  \<comment> \<open>The generalized inductive claim: over any ending-index suffix @{term as}, running config
     @{term s}, accumulated snap-prefix @{term bs} (a distinct happening-sublist), residual @{term cs}.\<close>
  have gen: "\<exists>nss. num_graph_impl.steps (dn # nss)
                   \<and> length nss = length as
                   \<and> RELC (last (s # seq_apply (map end_edge_effect as) s)) (last (dn # nss))
                          (?w (bs @ map (\<lambda>n. at_end (actions ! n)) as))"
    if as_end: "\<And>n. n \<in> set as \<Longrightarrow> n < length actions
                          \<and> is_ending_index (planning_sem.time_index i) n"
       and bs_act: "\<And>t. t \<in> set bs \<Longrightarrow> \<exists>a \<in> set actions. t = at_start a \<or> t = at_end a"
       and bs_sub: "set bs \<subseteq> ?S"
       and cs_dist: "distinct (bs @ map (\<lambda>n. at_end (actions ! n)) as @ cs)"
       and cs_full: "set (bs @ map (\<lambda>n. at_end (actions ! n)) as @ cs) = ?S"
       and srun: "graph_impl.steps (s # seq_apply (map end_edge_effect as) s)"
       and sstruct: "\<And>k. k < length as \<Longrightarrow>
                       fst ((s # seq_apply (map end_edge_effect as) s) ! k) ! Suc (as ! k) = ending_loc
                       \<and> length (fst ((s # seq_apply (map end_edge_effect as) s) ! k)) = length net_automata
                       \<and> Simple_Network_Language.bounded (map_of net_bounds)
                             (fst (snd (end_edge_effect (as ! k)
                                         ((s # seq_apply (map end_edge_effect as) s) ! k))))"
       and srel: "RELC s dn (?w bs)"
     for as s dn bs cs
    using that
  proof (induction as arbitrary: s dn bs cs)
    case Nil
    show ?case
    proof (intro exI[where x = "[]"] conjI)
      show "num_graph_impl.steps (dn # [])" by (rule num_graph_impl.steps.intros(1))
    next
      show "length [] = length []" by simp
    next
      show "RELC (last (s # seq_apply (map end_edge_effect []) s)) (last (dn # []))
                 (?w (bs @ map (\<lambda>n. at_end (actions ! n)) []))"
        by (simp only: list.map seq_apply_Nil append_Nil2 last_ConsL) (rule Nil.prems(8))
    qed
  next
    case (Cons n as')
    let ?sn = "at_end (actions ! n)"
    let ?s' = "end_edge_effect n s"
    \<comment> \<open>Decompose the running config and the @{const RELC}-related numeric start.\<close>
    obtain L vp c where s: "s = (L, vp, c)" by (cases s)
    obtain Ln dvn cn0 where dn: "dn = (Ln, dvn, cn0)" by (cases dn)
    have Leq: "Ln = L" by (rule RELC_locD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have ceq: "cn0 = c" by (rule RELC_clkD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have relS: "REL vp dvn (?w bs)" by (rule RELC_relD[OF Cons.prems(8)[unfolded s dn]])
    \<comment> \<open>Head index facts.\<close>
    have nmem: "n \<in> set (n # as')" by simp
    have n_lt: "n < length actions"
      and n_end: "is_ending_index (planning_sem.time_index i) n"
      using Cons.prems(1)[OF nmem] by blast+
    have aMem: "actions ! n \<in> set actions" using n_lt by simp
    \<comment> \<open>The fired end-snap is in happening @{term i}.\<close>
    have sn_mem: "?sn \<in> ?S"
      unfolding happ_at_index_decomp
      using n_lt n_end by blast
    \<comment> \<open>Run decomposition: the first edge and the tail run over @{term \<open>?s'\<close>}.\<close>
    have run_unfold: "s # seq_apply (map end_edge_effect (n # as')) s
                        = s # ?s' # seq_apply (map end_edge_effect as') ?s'"
      by (simp only: list.map seq_apply_Cons_Cons)
    have run_dec: "graph_impl.steps (s # ?s' # seq_apply (map end_edge_effect as') ?s')"
      using Cons.prems(6) run_unfold by simp
    \<comment> \<open>The propositional first edge and the tail run.\<close>
    have pstep0: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst ?s', fst (snd ?s'), snd (snd ?s')\<rangle>"
      using run_dec unfolding s by (cases ?s') (auto elim: graph_impl.steps.cases simp: prod.case)
    have tailrun: "graph_impl.steps (?s' # seq_apply (map end_edge_effect as') ?s')"
      using run_dec by (rule graph_impl.steps_ConsD) simp
    \<comment> \<open>The structural facts at run-position 0 (the head step on @{term s}).\<close>
    have end0: "L ! Suc n = ending_loc"
      and Llen0: "length L = length net_automata"
      and pbnd0: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s'))"
      using Cons.prems(7)[of 0] unfolding s by simp_all
    \<comment> \<open>The new accumulated snap-prefix and the list-shape rearrangement that re-targets the
       distinctness/fullness premises of the IH.\<close>
    define bs' where "bs' = bs @ [?sn]"
    have list_rearr: "bs @ map (\<lambda>m. at_end (actions ! m)) (n # as') @ cs
                        = bs' @ map (\<lambda>m. at_end (actions ! m)) as' @ cs"
      unfolding bs'_def by simp
    have cs_dist': "distinct (bs' @ map (\<lambda>m. at_end (actions ! m)) as' @ cs)"
      using Cons.prems(4)[unfolded list_rearr] .
    have cs_full': "set (bs' @ map (\<lambda>m. at_end (actions ! m)) as' @ cs) = ?S"
      using Cons.prems(5)[unfolded list_rearr] .
    \<comment> \<open>@{term \<open>?sn\<close>} is fresh of the already-folded prefix @{term bs}.\<close>
    have sn_notin_bs: "?sn \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr[symmetric])
    \<comment> \<open>The fold-append identity: snapping @{term \<open>?sn\<close>} onto the @{term bs}-fold IS the @{term bs'}-fold
       (the @{const fold} LANDMINE: rewrite via @{thm [source] fold_append}, not @{text simp}).\<close>
    have foldapp: "num_plan.num_rat_impl.snap_num_update ?sn (?w bs) = ?w bs'"
      unfolding bs'_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append) (simp add: comp_def)
    \<comment> \<open>The four numeric-fold kernel hypotheses for the @{term \<open>?sn\<close>} step at @{term \<open>?w bs\<close>}.\<close>
    have wok: "num_val_ok (?w bs)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok Cons.prems(2)])
    have fin: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      unfolding foldapp by (rule running_prefix_in_bounds[OF vss m0 i cs_dist' cs_full'])
    have sat_eq: "sat_comps (?w bs) (set (n_pre ?sn)) = sat_comps (snd (M i)) (set (n_pre ?sn))"
      by (rule sat_comps_running_prefix[OF sn_mem Cons.prems(3) sn_notin_bs])
    have sat: "sat_comps (?w bs) (set (n_pre ?sn))"
      unfolding sat_eq by (rule happening_snap_pre_sat[OF vss i sn_mem])
    have upd_lhs: "fst ` set (upds ?sn) \<subseteq> set nfluents"
      using snap_writes_nfluents_end aMem by blast
    \<comment> \<open>Apply the per-step kernel: the @{term \<open>?sn\<close>} edge lifts to a numeric step from @{term dn}.\<close>
    have L'eq: "fst ?s' = fst (end_edge_effect n (L, vp, c))" unfolding s by simp
    obtain vn' where
        numstep: "num_net_impl.sem \<turnstile> \<langle>L, dvn, c\<rangle> \<rightarrow> \<langle>fst ?s', vn', snd (snd ?s')\<rangle>"
      and relE: "REL (fst (snd ?s')) vn' (num_plan.num_rat_impl.snap_num_update ?sn (?w bs))"
      using num_edge_upd_step_lift_end[OF relS Llen0 end0 n_lt HOL.refl sn_mem
              pstep0 L'eq pbnd0 wok fin sat upd_lhs] by blast
    \<comment> \<open>Package the numeric post-config and its @{const RELC}-relation at the advanced fold @{term \<open>?w bs'\<close>}.\<close>
    obtain L' vp' c' where s'eq: "?s' = (L', vp', c')" by (cases ?s')
    define dn' where "dn' = (L', vn', c')"
    have relC': "RELC ?s' dn' (?w bs')"
      unfolding dn'_def s'eq
      using RELCI[OF relE[unfolded foldapp]] unfolding s'eq by simp
    \<comment> \<open>The IH premises for the tail suffix @{term as'} from @{term \<open>?s'\<close>}, @{term dn'}, @{term bs'}.\<close>
    have as'_end: "m < length actions \<and> is_ending_index (planning_sem.time_index i) m"
      if "m \<in> set as'" for m
      using Cons.prems(1) that by simp
    have bs'_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs'" for t
      using that aMem Cons.prems(2) unfolding bs'_def by auto
    have bs'_sub: "set bs' \<subseteq> ?S"
      using Cons.prems(3) sn_mem unfolding bs'_def by auto
    \<comment> \<open>Re-index the per-run-position structural premise: position @{term k} of the tail run is
       position @{term \<open>Suc k\<close>} of the full run.\<close>
    have sstruct': "fst ((?s' # seq_apply (map end_edge_effect as') ?s') ! k) ! Suc (as' ! k) = ending_loc
                    \<and> length (fst ((?s' # seq_apply (map end_edge_effect as') ?s') ! k)) = length net_automata
                    \<and> Simple_Network_Language.bounded (map_of net_bounds)
                          (fst (snd (end_edge_effect (as' ! k)
                                      ((?s' # seq_apply (map end_edge_effect as') ?s') ! k))))"
      if k: "k < length as'" for k
    proof -
      have Sk: "Suc k < length (n # as')" using k by simp
      have idx: "(s # seq_apply (map end_edge_effect (n # as')) s) ! Suc k
                   = (?s' # seq_apply (map end_edge_effect as') ?s') ! k"
        unfolding run_unfold by simp
      show ?thesis using Cons.prems(7)[OF Sk] unfolding idx by simp
    qed
    have ih: "\<exists>nss. num_graph_impl.steps (dn' # nss)
                   \<and> length nss = length as'
                   \<and> RELC (last (?s' # seq_apply (map end_edge_effect as') ?s')) (last (dn' # nss))
                          (?w (bs' @ map (\<lambda>m. at_end (actions ! m)) as'))"
      by (rule Cons.IH[OF as'_end bs'_act bs'_sub cs_dist' cs_full' tailrun sstruct' relC'])
    obtain nss' where
        nrun': "num_graph_impl.steps (dn' # nss')"
      and lnss': "length nss' = length as'"
      and rlast': "RELC (last (?s' # seq_apply (map end_edge_effect as') ?s')) (last (dn' # nss'))
                        (?w (bs' @ map (\<lambda>m. at_end (actions ! m)) as'))"
      using ih by (elim exE conjE)
    \<comment> \<open>Splice: the head numeric step from @{term dn} to @{term dn'} in front of the tail numeric run.\<close>
    have headstep: "num_graph_impl.steps [dn, dn']"
      unfolding dn dn'_def Leq ceq s'eq
      by (rule num_single_step_intro) (use numstep s'eq in \<open>simp add: prod.case\<close>)
    have spliced: "num_graph_impl.steps (dn # dn' # nss')"
      using num_steps_extend[OF headstep] nrun' by simp
    show ?case
    proof (intro exI[where x = "dn' # nss'"] conjI)
      show "num_graph_impl.steps (dn # dn' # nss')" by (rule spliced)
    next
      show "length (dn' # nss') = length (n # as')" using lnss' by simp
    next
      have bsrew: "bs' @ map (\<lambda>m. at_end (actions ! m)) as'
                     = bs @ map (\<lambda>m. at_end (actions ! m)) (n # as')"
        unfolding bs'_def by simp
      have lastrew: "last (s # seq_apply (map end_edge_effect (n # as')) s)
                       = last (?s' # seq_apply (map end_edge_effect as') ?s')"
        unfolding run_unfold by simp
      show "RELC (last (s # seq_apply (map end_edge_effect (n # as')) s)) (last (dn # dn' # nss'))
                 (?w (bs @ map (\<lambda>m. at_end (actions ! m)) (n # as')))"
        using rlast' unfolding lastrew bsrew by simp
    qed
  qed
  show ?thesis
    by (rule gen[OF ns_end ys_act ys_sub zs_dist zs_full prun struct rel0])
qed

text \<open>The numeric edge automaton at index @{term \<open>Suc n\<close>} carries @{const instant_trans_edge} VERBATIM
(fifth in the edge list of @{const num_action_to_automaton}), so the numeric net contains the same
@{const instant_trans_edge} transition as the propositional net.\<close>
lemma num_nth_auto_instant_trans_edge:
  assumes n: "n < length actions"
  shows "instant_trans_edge (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! Suc n))"
proof -
  have "trans (automaton_of (num_timed_automaton_net ! Suc n))
          = trans (automaton_of (num_action_to_automaton (actions ! n)))"
    by (simp add: num_timed_automaton_net_def n)
  thus ?thesis
    apply (subst (asm) num_action_auto_trans)
    by simp
qed

text \<open>The @{const starting_loc} source location is shared by @{const edge_2} (target @{const running_loc})
and @{const instant_trans_edge} (target @{const ending_loc}); among the five edges of an action automaton
these are the only two leaving @{const starting_loc}. So a propositional internal step from a config whose
@{term \<open>Suc n\<close>}-th location is @{const starting_loc} AND whose fired edge targets @{const ending_loc} must
have fired @{const instant_trans_edge} at automaton @{term \<open>Suc n\<close>} (the target distinguishes it from
@{const edge_2}).\<close>
lemma prop_instant_trans_edge_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and start0: "L ! Suc n = starting_loc"
      and tgt: "l' = ending_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = instant_trans_edge (actions ! n)"
proof -
  have l_start: "l = starting_loc" using Lp start0 pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_start tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel for the INSTANT internal step: lifting ONE propositional
@{const instant_trans_edge} step (the no-fluent-write start-to-end duration edge of an instant action) to
a numeric @{const num_graph_impl.steps} step, preserving @{const REL}. The structure mirrors
@{thm [source] num_edge_3_step_lift}: the numeric edge is @{const instant_trans_edge} VERBATIM (reused in
@{const num_action_to_automaton} with no augment, no numeric update), so the abstract valuation @{term w}
is UNCHANGED. The only differences are the source location (@{const starting_loc} rather than
@{const running_loc}) and the edge-pinning (@{thm [source] prop_instant_trans_edge_pinned}, distinguishing
@{const instant_trans_edge} from @{const edge_2} by the @{const ending_loc} target).\<close>
lemma num_instant_trans_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and start0: "L ! Suc n = starting_loc"
      and n: "n < length actions"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (instant_trans_edge_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and fin: "fluent_in_bounds w"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle> \<and> REL vp' vn' w"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have L'_eq: "L' = L[Suc n := ending_loc]"
    using L'eq by (simp add: instant_trans_edge_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const instant_trans_edge}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}.\<close>
  have starting_ne_ending: "starting_loc \<noteq> ending_loc" by (simp add: locations_unique)
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    moreover have "L[Suc n := ending_loc] ! Suc n = ending_loc" using Sn_lt by simp
    ultimately show False using L'eq2 L'_eq start0 starting_ne_ending by simp
  qed
  \<comment> \<open>The fired edge targets @{const ending_loc}: position @{term \<open>Suc n\<close>} of the post locations.\<close>
  have tgt: "l' = ending_loc"
  proof -
    have "L[p := l'] ! Suc n = l'" using pSuc Sn_lt by simp
    moreover have "L[Suc n := ending_loc] ! Suc n = ending_loc" using Sn_lt by simp
    ultimately show ?thesis using L'eq2 L'_eq by simp
  qed
  have edgeit: "(l, b, g, Sil a, f, r, l') = instant_trans_edge (actions ! n)"
    by (rule prop_instant_trans_edge_pinned[OF P E LOC start0 tgt n pSuc])
  \<comment> \<open>The numeric edge: @{const instant_trans_edge} verbatim, with the same (empty) update.\<close>
  have NE: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc edgeit by (rule num_nth_auto_instant_trans_edge[OF n])
  \<comment> \<open>The numeric guard fires on the extended store; the (empty) update fires, preserving tracking.\<close>
  have NB: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  obtain vn' where
      NU: "is_upds vn f vn'"
    and LE: "vp' \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn' x = vn x"
    using is_upds_map_le[OF U le] by blast
  \<comment> \<open>@{const instant_trans_edge} writes nothing (empty update), so tracking survives trivially.\<close>
  have f_eq: "f = []" using edgeit by (simp add: instant_trans_edge_def Let_def)
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
    using f_eq by simp
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound from the propositional post-bound and tracking.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  have fset_sub: "fst ` set f \<subseteq> dom vn" using f_eq by simp
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TR fin vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TR BND by (auto intro: RELI)
qed

text \<open>The three configs produced by one @{const apply_snap_action} block: the @{const start_edge_effect}
post-config @{term s1}, the @{const instant_trans_edge_effect} post-config @{term s2}, and the
@{const end_edge_effect} post-config @{term s3} (the snap block of an instant action runs start, then the
internal start-to-end transition, then end).\<close>
lemma apply_snap_action_unfold:
  "apply_snap_action n s
     = [start_edge_effect n s,
        instant_trans_edge_effect n (start_edge_effect n s),
        end_edge_effect n (instant_trans_edge_effect n (start_edge_effect n s))]"
  unfolding apply_snap_action_def
  by (simp add: seq_apply_def upt_rec)

text \<open>Head-split of @{const apply_instant_actions}: the leading instant index @{term n} contributes its
@{const apply_snap_action} block, and the rest of the run continues from that block's last config.\<close>
lemma apply_instant_actions_Cons:
  "apply_instant_actions (n # ns) s
     = apply_snap_action n s @ apply_instant_actions ns (last (apply_snap_action n s))"
proof -
  have ne: "apply_snap_action n s \<noteq> []" by (simp add: apply_snap_action_unfold)
  have "apply_instant_actions (n # ns) s
          = seq_apply' (apply_snap_action n # map apply_snap_action ns) s"
    by (simp add: apply_instant_actions_def)
  also have "\<dots> = ext_seq' (map apply_snap_action ns) (apply_snap_action n s)"
    by (rule seq_apply'_as_ext_seq'[where f = "apply_snap_action n" and x = s, OF ne])
  also have "\<dots> = apply_snap_action n s @ seq_apply' (map apply_snap_action ns) (last (apply_snap_action n s))"
    by (rule ext_seq'_as_seq_apply')
  also have "\<dots> = apply_snap_action n s @ apply_instant_actions ns (last (apply_snap_action n s))"
    by (simp add: apply_instant_actions_def)
  finally show ?thesis .
qed

text \<open>The propositional per-block structural bundle the instant phase-lift consumes at each
@{const apply_snap_action} block: from the block-entry config @{term c} at action index @{term m}, the
three sub-step source locations (@{const off_loc} at @{term c}, @{const starting_loc} at the
@{const start_edge_effect} post-config, @{const ending_loc} at the @{const instant_trans_edge_effect}
post-config), the lengths, and the @{const net_bounds} bounds of the three post-stores. Bundling it as a
single predicate keeps the kernel-instantiation FIRST-ORDER (the induction matches the predicate symbol,
not a @{text let}-body).\<close>
definition instant_block_struct where
"instant_block_struct c m \<longleftrightarrow>
   (let s1 = start_edge_effect m c;
        s2 = instant_trans_edge_effect m s1;
        s3 = end_edge_effect m s2 in
      fst c ! Suc m = off_loc
      \<and> length (fst c) = length net_automata
      \<and> Simple_Network_Language.bounded (map_of net_bounds) (fst (snd s1))
      \<and> fst s1 ! Suc m = starting_loc
      \<and> length (fst s1) = length net_automata
      \<and> Simple_Network_Language.bounded (map_of net_bounds) (fst (snd s2))
      \<and> fst s2 ! Suc m = ending_loc
      \<and> length (fst s2) = length net_automata
      \<and> Simple_Network_Language.bounded (map_of net_bounds) (fst (snd s3)))"

lemma instant_block_structD:
  assumes "instant_block_struct c m"
  shows "fst c ! Suc m = off_loc"
    and "length (fst c) = length net_automata"
    and "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (start_edge_effect m c)))"
    and "fst (start_edge_effect m c) ! Suc m = starting_loc"
    and "length (fst (start_edge_effect m c)) = length net_automata"
    and "Simple_Network_Language.bounded (map_of net_bounds)
            (fst (snd (instant_trans_edge_effect m (start_edge_effect m c))))"
    and "fst (instant_trans_edge_effect m (start_edge_effect m c)) ! Suc m = ending_loc"
    and "length (fst (instant_trans_edge_effect m (start_edge_effect m c))) = length net_automata"
    and "Simple_Network_Language.bounded (map_of net_bounds)
            (fst (snd (end_edge_effect m (instant_trans_edge_effect m (start_edge_effect m c)))))"
  using assms unfolding instant_block_struct_def Let_def by simp_all
text \<open>The INSTANT phase run-lift, the most complex of the four phase-lifts: each
@{const apply_snap_action} block both fires THREE numeric edges (start, the internal start-to-end
duration transition, end) AND advances the abstract numeric fold by TWO snaps, @{term \<open>at_start (actions ! n)\<close>}
then @{term \<open>at_end (actions ! n)\<close>} (the internal duration transition writes nothing). By induction on the
index suffix @{term ns}, threading the running propositional config @{term sp}, the running numeric store,
and the accumulated snap prefix @{term ys}. The three per-block kernels are
@{thm [source] num_edge_upd_step_lift} (start, fold += @{term \<open>at_start (actions ! n)\<close>}),
@{thm [source] num_instant_trans_step_lift} (the no-write internal step, fold unchanged), and
@{thm [source] num_edge_upd_step_lift_end} (end, fold += @{term \<open>at_end (actions ! n)\<close>}). For an INSTANT
index @{term n} BOTH @{term \<open>at_start (actions ! n)\<close>} and @{term \<open>at_end (actions ! n)\<close>} are in happening
@{term i} (it satisfies @{const is_instant_index}, which @{thm [source] happ_at_index_decomp} places in the
starting-or-instant image AND the ending-or-instant image). The propositional per-block structural facts
(the @{const off_loc} / @{const starting_loc} / @{const ending_loc} source locations at the three
sub-configs, the lengths, the projection bounds on the three post-stores) are supplied per run-position by
the caller hypothesis @{text struct}.\<close>
lemma num_instant_phase_lift:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i < length planning_sem.htpl"
  assumes ns_inst: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions
                            \<and> is_instant_index (planning_sem.time_index i) n"
      and ys_act: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      and ys_sub: "set ys \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and zs_dist: "distinct (ys @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns) @ zs)"
      and zs_full: "set (ys @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns) @ zs)
                      = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
      and prun: "graph_impl.steps (sp # apply_instant_actions ns sp)"
      and struct: "\<And>k. k < length ns \<Longrightarrow>
                     instant_block_struct ((sp # apply_instant_actions ns sp) ! (3 * k)) (ns ! k)"
      and rel0: "RELC sp cn (num_plan.num_rat_impl.happening_num_update ys (snd (M i)))"
    shows "\<exists>nss. num_graph_impl.steps (cn # nss)
                 \<and> length nss = length (apply_instant_actions ns sp)
                 \<and> RELC (last (sp # apply_instant_actions ns sp)) (last (cn # nss))
                        (num_plan.num_rat_impl.happening_num_update
                           (ys @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns)) (snd (M i)))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  let ?snaps = "\<lambda>ns. concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ns)"
  have base_val_ok: "num_val_ok (snd (M i))"
    using i by (intro num_seq_val_ok[OF vss m0]) simp
  \<comment> \<open>The generalized inductive claim over any instant-index suffix @{term as}, running config @{term s},
     accumulated snap-prefix @{term bs} (a distinct happening-sublist), residual @{term cs}.\<close>
  have gen: "\<exists>nss. num_graph_impl.steps (dn # nss)
                   \<and> length nss = length (apply_instant_actions as s)
                   \<and> RELC (last (s # apply_instant_actions as s)) (last (dn # nss))
                          (?w (bs @ ?snaps as))"
    if as_inst: "\<And>n. n \<in> set as \<Longrightarrow> n < length actions
                          \<and> is_instant_index (planning_sem.time_index i) n"
       and bs_act: "\<And>t. t \<in> set bs \<Longrightarrow> \<exists>a \<in> set actions. t = at_start a \<or> t = at_end a"
       and bs_sub: "set bs \<subseteq> ?S"
       and cs_dist: "distinct (bs @ ?snaps as @ cs)"
       and cs_full: "set (bs @ ?snaps as @ cs) = ?S"
       and srun: "graph_impl.steps (s # apply_instant_actions as s)"
       and sstruct: "\<And>k. k < length as \<Longrightarrow>
                       instant_block_struct ((s # apply_instant_actions as s) ! (3 * k)) (as ! k)"
       and srel: "RELC s dn (?w bs)"
     for as s dn bs cs
    using that
  proof (induction as arbitrary: s dn bs cs)
    case Nil
    show ?case
    proof (intro exI[where x = "[]"] conjI)
      show "num_graph_impl.steps (dn # [])" by (rule num_graph_impl.steps.intros(1))
    next
      show "length [] = length (apply_instant_actions [] s)"
        by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil)
    next
      show "RELC (last (s # apply_instant_actions [] s)) (last (dn # []))
                 (?w (bs @ ?snaps []))"
        by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil) (rule Nil.prems(8))
    qed
  next
    case (Cons n as')
    let ?sst = "at_start (actions ! n)"
    let ?sen = "at_end (actions ! n)"
    \<comment> \<open>The block configs.\<close>
    let ?s1 = "start_edge_effect n s"
    let ?s2 = "instant_trans_edge_effect n ?s1"
    let ?s3 = "end_edge_effect n ?s2"
    \<comment> \<open>Decompose the running config and the @{const RELC}-related numeric start.\<close>
    obtain L vp c where s: "s = (L, vp, c)" by (cases s)
    obtain Ln dvn cn0 where dn: "dn = (Ln, dvn, cn0)" by (cases dn)
    have Leq: "Ln = L" by (rule RELC_locD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have ceq: "cn0 = c" by (rule RELC_clkD[OF Cons.prems(8)[unfolded s dn], symmetric])
    have relS: "REL vp dvn (?w bs)" by (rule RELC_relD[OF Cons.prems(8)[unfolded s dn]])
    \<comment> \<open>Head index facts.\<close>
    have nmem: "n \<in> set (n # as')" by simp
    have n_lt: "n < length actions"
      and n_inst: "is_instant_index (planning_sem.time_index i) n"
      using Cons.prems(1)[OF nmem] by blast+
    have aMem: "actions ! n \<in> set actions" using n_lt by simp
    \<comment> \<open>An INSTANT index lands in BOTH images: at-start and at-end snaps are both in happening @{term i}.\<close>
    have sst_mem: "?sst \<in> ?S"
      unfolding happ_at_index_decomp using n_lt n_inst by blast
    have sen_mem: "?sen \<in> ?S"
      unfolding happ_at_index_decomp using n_lt n_inst by blast
    \<comment> \<open>Run decomposition: the block and the tail run.\<close>
    have last_snap: "last (apply_snap_action n s) = ?s3"
      by (simp add: apply_snap_action_unfold)
    have run_unfold: "s # apply_instant_actions (n # as') s
                        = s # ?s1 # ?s2 # ?s3 # apply_instant_actions as' ?s3"
      apply (subst apply_instant_actions_Cons)
      apply (subst last_snap)
      apply (subst apply_snap_action_unfold)
      by simp
    have run_dec: "graph_impl.steps (s # ?s1 # ?s2 # ?s3 # apply_instant_actions as' ?s3)"
      using Cons.prems(6) run_unfold by simp
    have tail1: "graph_impl.steps (?s1 # ?s2 # ?s3 # apply_instant_actions as' ?s3)"
      using run_dec by (rule graph_impl.steps_ConsD) simp
    have tail2: "graph_impl.steps (?s2 # ?s3 # apply_instant_actions as' ?s3)"
      using tail1 by (rule graph_impl.steps_ConsD) simp
    have tailrun: "graph_impl.steps (?s3 # apply_instant_actions as' ?s3)"
      using tail2 by (rule graph_impl.steps_ConsD) simp
    \<comment> \<open>The three propositional sub-steps of the block.\<close>
    have pstep0: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst ?s1, fst (snd ?s1), snd (snd ?s1)\<rangle>"
      using run_dec unfolding s by (cases ?s1) (auto elim: graph_impl.steps.cases simp: prod.case)
    have pstep1: "net_impl.sem \<turnstile> \<langle>fst ?s1, fst (snd ?s1), snd (snd ?s1)\<rangle> \<rightarrow> \<langle>fst ?s2, fst (snd ?s2), snd (snd ?s2)\<rangle>"
      using run_dec by (cases ?s1; cases ?s2) (auto elim: graph_impl.steps.cases simp: prod.case)
    have pstep2: "net_impl.sem \<turnstile> \<langle>fst ?s2, fst (snd ?s2), snd (snd ?s2)\<rangle> \<rightarrow> \<langle>fst ?s3, fst (snd ?s3), snd (snd ?s3)\<rangle>"
      using run_dec by (cases ?s2; cases ?s3) (auto elim: graph_impl.steps.cases simp: prod.case)
    \<comment> \<open>The structural facts at run-position 0 (block 0 entry config @{term s}).\<close>
    have ibs0: "instant_block_struct s n"
      using Cons.prems(7)[of 0] by simp
    note struct0 = instant_block_structD[OF ibs0]
    have off0: "L ! Suc n = off_loc" using struct0(1) unfolding s by simp
    have Llen0: "length L = length net_automata" using struct0(2) unfolding s by simp
    \<comment> \<open>The new accumulated snap-prefixes and the list-shape rearrangement re-targeting the IH premises.\<close>
    define bs1 where "bs1 = bs @ [?sst]"
    define bs2 where "bs2 = bs @ [?sst, ?sen]"
    have snaps_Cons: "?snaps (n # as') = ?sst # ?sen # ?snaps as'" by simp
    have list_rearr: "bs @ ?snaps (n # as') @ cs = bs2 @ ?snaps as' @ cs"
      unfolding bs2_def snaps_Cons by simp
    have cs_dist': "distinct (bs2 @ ?snaps as' @ cs)"
      using Cons.prems(4)[unfolded list_rearr] .
    have cs_full': "set (bs2 @ ?snaps as' @ cs) = ?S"
      using Cons.prems(5)[unfolded list_rearr] .
    \<comment> \<open>The intermediate prefix @{term bs1} fullness/distinctness, with @{term \<open>?sen # ?snaps as'\<close>} residual.\<close>
    have list_rearr1: "bs @ ?snaps (n # as') @ cs = bs1 @ (?sen # ?snaps as' @ cs)"
      unfolding bs1_def snaps_Cons by simp
    have cs_dist1: "distinct (bs1 @ (?sen # ?snaps as' @ cs))"
      using Cons.prems(4)[unfolded list_rearr1] .
    have cs_full1: "set (bs1 @ (?sen # ?snaps as' @ cs)) = ?S"
      using Cons.prems(5)[unfolded list_rearr1] .
    \<comment> \<open>The snaps are fresh of the already-folded prefixes.\<close>
    have sst_notin_bs: "?sst \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr1[symmetric] snaps_Cons)
    have sen_notin_bs: "?sen \<notin> set bs"
      using Cons.prems(4) by (simp add: list_rearr1[symmetric] snaps_Cons)
    have sen_ne_sst: "?sen \<noteq> ?sst"
      using Cons.prems(4) by (auto simp add: list_rearr1[symmetric] snaps_Cons)
    have sen_notin_bs1: "?sen \<notin> set bs1"
      using sen_notin_bs sen_ne_sst unfolding bs1_def by simp
    \<comment> \<open>The fold-append identities (the @{const fold} LANDMINE: rewrite via @{thm [source] fold_append}).\<close>
    have foldapp_st: "num_plan.num_rat_impl.snap_num_update ?sst (?w bs) = ?w bs1"
      unfolding bs1_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append) (simp add: comp_def)
    have foldapp_en: "num_plan.num_rat_impl.snap_num_update ?sen (?w bs1) = ?w bs2"
      unfolding bs2_def bs1_def num_plan.num_rat_impl.happening_num_update_def
      by (subst fold_append)+ (simp add: comp_def)
    \<comment> \<open>The kernel hypotheses for the START snap at @{term \<open>?w bs\<close>}.\<close>
    have wok: "num_val_ok (?w bs)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok Cons.prems(2)])
    have fin_st: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sst (?w bs))"
      unfolding foldapp_st by (rule running_prefix_in_bounds[OF vss m0 i cs_dist1 cs_full1])
    have sat_st_eq: "sat_comps (?w bs) (set (n_pre ?sst)) = sat_comps (snd (M i)) (set (n_pre ?sst))"
      by (rule sat_comps_running_prefix[OF sst_mem Cons.prems(3) sst_notin_bs])
    have sat_st: "sat_comps (?w bs) (set (n_pre ?sst))"
      unfolding sat_st_eq by (rule happening_snap_pre_sat[OF vss i sst_mem])
    have upd_lhs_st: "fst ` set (upds ?sst) \<subseteq> set nfluents"
      using snap_writes_nfluents_start aMem by blast
    \<comment> \<open>Apply the START kernel: @{term ?sst} edge lifts to a numeric step from @{term dn} to @{term d1}.\<close>
    have L'eq0: "fst ?s1 = fst (start_edge_effect n (L, vp, c))" unfolding s by simp
    obtain vn1 where
        numstep0: "num_net_impl.sem \<turnstile> \<langle>L, dvn, c\<rangle> \<rightarrow> \<langle>fst ?s1, vn1, snd (snd ?s1)\<rangle>"
      and relE0: "REL (fst (snd ?s1)) vn1 (num_plan.num_rat_impl.snap_num_update ?sst (?w bs))"
      using num_edge_upd_step_lift[OF relS Llen0 off0 n_lt HOL.refl sst_mem
              pstep0 L'eq0 struct0(3) wok fin_st sat_st upd_lhs_st]
      by blast
    have rel1: "REL (fst (snd ?s1)) vn1 (?w bs1)" using relE0[unfolded foldapp_st] .
    \<comment> \<open>Apply the INSTANT-TRANS kernel: @{term ?s1} to @{term ?s2}, fold UNCHANGED.\<close>
    have starting1: "fst ?s1 ! Suc n = starting_loc" using struct0(4) .
    have Llen1: "length (fst ?s1) = length net_automata" using struct0(5) .
    have fin1: "fluent_in_bounds (?w bs1)"
      using fin_st[unfolded foldapp_st] .
    have L'eq1: "fst ?s2 = fst (instant_trans_edge_effect n (fst ?s1, fst (snd ?s1), snd (snd ?s1)))"
      by simp
    obtain vn2 where
        numstep1: "num_net_impl.sem \<turnstile> \<langle>fst ?s1, vn1, snd (snd ?s1)\<rangle> \<rightarrow> \<langle>fst ?s2, vn2, snd (snd ?s2)\<rangle>"
      and rel2: "REL (fst (snd ?s2)) vn2 (?w bs1)"
      using num_instant_trans_step_lift[OF rel1 Llen1 starting1 n_lt pstep1 L'eq1 struct0(6) fin1]
      by blast
    \<comment> \<open>Kernel hypotheses for the END snap at @{term \<open>?w bs1\<close>}.\<close>
    have bs1_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs1" for t
      using that aMem Cons.prems(2) unfolding bs1_def by auto
    have wok1: "num_val_ok (?w bs1)"
      by (rule happening_num_update_preserves_num_val_ok[OF base_val_ok bs1_act])
    have fin_en: "fluent_in_bounds (num_plan.num_rat_impl.snap_num_update ?sen (?w bs1))"
      unfolding foldapp_en by (rule running_prefix_in_bounds[OF vss m0 i cs_dist' cs_full'])
    have bs1_sub: "set bs1 \<subseteq> ?S" using Cons.prems(3) sst_mem unfolding bs1_def by auto
    have sat_en_eq: "sat_comps (?w bs1) (set (n_pre ?sen)) = sat_comps (snd (M i)) (set (n_pre ?sen))"
      by (rule sat_comps_running_prefix[OF sen_mem bs1_sub sen_notin_bs1])
    have sat_en: "sat_comps (?w bs1) (set (n_pre ?sen))"
      unfolding sat_en_eq by (rule happening_snap_pre_sat[OF vss i sen_mem])
    have upd_lhs_en: "fst ` set (upds ?sen) \<subseteq> set nfluents"
      using snap_writes_nfluents_end aMem by blast
    \<comment> \<open>Apply the END kernel: @{term ?s2} to @{term ?s3}, fold += @{term ?sen}.\<close>
    have ending2: "fst ?s2 ! Suc n = ending_loc" using struct0(7) .
    have Llen2: "length (fst ?s2) = length net_automata" using struct0(8) .
    have L'eq2: "fst ?s3 = fst (end_edge_effect n (fst ?s2, fst (snd ?s2), snd (snd ?s2)))"
      by simp
    obtain vn3 where
        numstep2: "num_net_impl.sem \<turnstile> \<langle>fst ?s2, vn2, snd (snd ?s2)\<rangle> \<rightarrow> \<langle>fst ?s3, vn3, snd (snd ?s3)\<rangle>"
      and relE2: "REL (fst (snd ?s3)) vn3 (num_plan.num_rat_impl.snap_num_update ?sen (?w bs1))"
      using num_edge_upd_step_lift_end[OF rel2 Llen2 ending2 n_lt HOL.refl sen_mem
              pstep2 L'eq2 struct0(9) wok1 fin_en sat_en upd_lhs_en] by blast
    have rel3: "REL (fst (snd ?s3)) vn3 (?w bs2)" using relE2[unfolded foldapp_en] .
    \<comment> \<open>Package the numeric block-configs.\<close>
    obtain L1 vp1 c1 where s1eq: "?s1 = (L1, vp1, c1)" by (cases ?s1)
    obtain L2 vp2 c2 where s2eq: "?s2 = (L2, vp2, c2)" by (cases ?s2)
    obtain L3 vp3 c3 where s3eq: "?s3 = (L3, vp3, c3)" by (cases ?s3)
    define d1 where "d1 = (L1, vn1, c1)"
    define d2 where "d2 = (L2, vn2, c2)"
    define d3 where "d3 = (L3, vn3, c3)"
    have relC3: "RELC ?s3 d3 (?w bs2)"
      unfolding d3_def s3eq using RELCI[OF rel3] unfolding s3eq by simp
    \<comment> \<open>The three numeric steps, as single-step runs.\<close>
    have step_st: "num_graph_impl.steps [dn, d1]"
      unfolding dn d1_def Leq ceq
      by (rule num_single_step_intro) (use numstep0 s1eq in \<open>simp add: prod.case\<close>)
    have step_it: "num_graph_impl.steps [d1, d2]"
      unfolding d1_def d2_def
      by (rule num_single_step_intro)
         (use numstep1 s1eq s2eq in \<open>simp add: prod.case\<close>)
    have step_en: "num_graph_impl.steps [d2, d3]"
      unfolding d2_def d3_def
      by (rule num_single_step_intro)
         (use numstep2 s2eq s3eq in \<open>simp add: prod.case\<close>)
    have headblock: "num_graph_impl.steps [dn, d1, d2, d3]"
      using num_steps_extend[OF step_st] num_steps_extend[OF step_it] step_en by simp
    \<comment> \<open>IH premises for the tail suffix @{term as'} from @{term ?s3}, @{term d3}, @{term bs2}.\<close>
    have as'_inst: "m < length actions \<and> is_instant_index (planning_sem.time_index i) m"
      if "m \<in> set as'" for m
      using Cons.prems(1) that by simp
    have bs2_act: "\<exists>a \<in> set actions. t = at_start a \<or> t = at_end a" if "t \<in> set bs2" for t
      using that aMem Cons.prems(2) unfolding bs2_def by auto
    have bs2_sub: "set bs2 \<subseteq> ?S"
      using Cons.prems(3) sst_mem sen_mem unfolding bs2_def by auto
    \<comment> \<open>Re-index the per-block structural premise: block @{term k} of the tail is block @{term \<open>Suc k\<close>}
       of the full run (position @{term \<open>3 * k\<close>} of the tail = position @{term \<open>3 * Suc k\<close>} of the full run).\<close>
    have sstruct':
        "instant_block_struct ((?s3 # apply_instant_actions as' ?s3) ! (3 * k)) (as' ! k)"
      if k: "k < length as'" for k
    proof -
      have Sk: "Suc k < length (n # as')" using k by simp
      have idx: "(s # apply_instant_actions (n # as') s) ! (3 * Suc k)
                   = (?s3 # apply_instant_actions as' ?s3) ! (3 * k)"
        unfolding run_unfold by (simp add: numeral_3_eq_3)
      have m_idx: "(n # as') ! Suc k = as' ! k" by simp
      show ?thesis using Cons.prems(7)[OF Sk] unfolding idx m_idx .
    qed
    \<comment> \<open>Abbreviate the (large) block-end config so the IH instantiation stays first-order.\<close>
    define t3 where "t3 = ?s3"
    have as'_inst_t: "\<And>m. m \<in> set as' \<Longrightarrow> m < length actions
                            \<and> is_instant_index (planning_sem.time_index i) m"
      using as'_inst by blast
    have tailrun_t: "graph_impl.steps (t3 # apply_instant_actions as' t3)"
      unfolding t3_def by (rule tailrun)
    have sstruct_t: "\<And>k. k < length as' \<Longrightarrow>
                       instant_block_struct ((t3 # apply_instant_actions as' t3) ! (3 * k)) (as' ! k)"
      unfolding t3_def using sstruct' by blast
    have relC3_t: "RELC t3 d3 (?w bs2)" unfolding t3_def by (rule relC3)
    have ih: "\<exists>nss. num_graph_impl.steps (d3 # nss)
                   \<and> length nss = length (apply_instant_actions as' t3)
                   \<and> RELC (last (t3 # apply_instant_actions as' t3)) (last (d3 # nss))
                          (?w (bs2 @ ?snaps as'))"
      by (rule Cons.IH[OF as'_inst_t bs2_act bs2_sub cs_dist' cs_full' tailrun_t sstruct_t relC3_t])
    obtain nss' where
        nrun': "num_graph_impl.steps (d3 # nss')"
      and lnss': "length nss' = length (apply_instant_actions as' ?s3)"
      and rlast': "RELC (last (?s3 # apply_instant_actions as' ?s3)) (last (d3 # nss'))
                        (?w (bs2 @ ?snaps as'))"
      using ih unfolding t3_def by (elim exE conjE)
    \<comment> \<open>Splice the head block in front of the tail numeric run.\<close>
    have spliced: "num_graph_impl.steps (dn # d1 # d2 # d3 # nss')"
      using num_steps_extend[OF headblock] nrun' by simp
    show ?case
    proof (intro exI[where x = "d1 # d2 # d3 # nss'"] conjI)
      show "num_graph_impl.steps (dn # d1 # d2 # d3 # nss')" by (rule spliced)
    next
      have len_block: "length (apply_instant_actions (n # as') s)
                         = 3 + length (apply_instant_actions as' ?s3)"
        using run_unfold by (simp del: apply_instant_actions_Cons)
      show "length (d1 # d2 # d3 # nss') = length (apply_instant_actions (n # as') s)"
        using lnss' len_block by simp
    next
      have bsrew: "bs2 @ ?snaps as' = bs @ ?snaps (n # as')"
        unfolding bs2_def snaps_Cons by simp
      have lastrew: "last (s # apply_instant_actions (n # as') s)
                       = last (?s3 # apply_instant_actions as' ?s3)"
        unfolding run_unfold by simp
      have lastnum: "last (dn # d1 # d2 # d3 # nss') = last (d3 # nss')" by simp
      show "RELC (last (s # apply_instant_actions (n # as') s)) (last (dn # d1 # d2 # d3 # nss'))
                 (?w (bs @ ?snaps (n # as')))"
        using rlast' unfolding lastrew lastnum bsrew by simp
    qed
  qed
  show ?thesis
    by (rule gen[OF ns_inst ys_act ys_sub zs_dist zs_full prun struct rel0])
qed

text \<open>The relational lift predicate carried by the numeric run-lift's structural combinator. As a
predicate on the PROPOSITIONAL config-list @{term ps}, @{term \<open>RLP w ps\<close>} says: WHEN @{term ps} is a
propositional run, then for EVERY numeric start config @{const RELC}-related to its head there is a
numeric run of the same length whose last config is @{const RELC}-related to @{term \<open>last ps\<close>}. The
universal quantification over the numeric start is what makes the combinator's @{text step} splice
compose: the first sub-run's @{const RELC}-related endpoint is fed as the second sub-run's start.\<close>
definition RLP where
"RLP w ps \<longleftrightarrow> ps \<noteq> [] \<and> (graph_impl.steps ps \<longrightarrow>
   (\<forall>cn. RELC (hd ps) cn w \<longrightarrow>
      (\<exists>nss. num_graph_impl.steps (cn # nss)
             \<and> length nss = length ps - 1
             \<and> RELC (last ps) (last (cn # nss)) w)))"

lemma RLP_base: "RLP w [x]"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "[x] \<noteq> []" by simp
next
  fix cn assume "RELC (hd [x]) cn w"
  hence "RELC (last [x]) (last (cn # [])) w" by simp
  thus "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length [x] - 1 \<and> RELC (last [x]) (last (cn # nss)) w"
    by (intro exI[where x = "[]"]) (auto intro: num_graph_impl.steps.intros(1))
qed

lemma RLP_step:
  assumes RX: "RLP w xs"
      and RY: "RLP w (last xs # ys)"
      and xs: "xs \<noteq> []"
  shows "RLP w (xs @ ys)"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "xs @ ys \<noteq> []" using xs by simp
next
  fix cn
  assume steps: "graph_impl.steps (xs @ ys)"
     and relhd: "RELC (hd (xs @ ys)) cn w"
  show "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length (xs @ ys) - 1
              \<and> RELC (last (xs @ ys)) (last (cn # nss)) w"
  proof (cases "ys = []")
    case True
    have stepsX: "graph_impl.steps xs" using steps True by simp
    have rhd: "RELC (hd xs) cn w" using relhd True xs by simp
    obtain nss where
        nss: "num_graph_impl.steps (cn # nss)"
      and lnss: "length nss = length xs - 1"
      and rlast: "RELC (last xs) (last (cn # nss)) w"
      using conjunct2[OF RX[unfolded RLP_def], rule_format, OF stepsX rhd] by blast
    show ?thesis
      apply (intro exI[where x = nss] conjI)
      subgoal by (rule nss)
      subgoal using lnss True by simp
      subgoal using rlast True by simp
      done
  next
    case False
    have stepsX: "graph_impl.steps xs" by (rule graph_impl.steps_appendD1[OF steps xs])
    have stepsY: "graph_impl.steps ys" by (rule graph_impl.steps_appendD2[OF steps False])
    have edge: "(case last xs of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). net_impl.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (hd ys)"
      using graph_impl.steps_decomp[OF steps xs False] by simp
    have stepsLY: "graph_impl.steps (last xs # ys)"
      using False edge stepsY by (cases ys) (auto intro: graph_impl.steps.intros)
    \<comment> \<open>First sub-run from @{term cn}.\<close>
    have rhd: "RELC (hd xs) cn w" using relhd xs by simp
    obtain nss1 where
        nss1: "num_graph_impl.steps (cn # nss1)"
      and lnss1: "length nss1 = length xs - 1"
      and rmid: "RELC (last xs) (last (cn # nss1)) w"
      using conjunct2[OF RX[unfolded RLP_def], rule_format, OF stepsX rhd] by blast
    \<comment> \<open>Second sub-run from the @{const RELC}-related endpoint @{term \<open>last (cn # nss1)\<close>}.\<close>
    have relmid: "RELC (hd (last xs # ys)) (last (cn # nss1)) w" using rmid by simp
    obtain nss2 where
        nss2: "num_graph_impl.steps (last (cn # nss1) # nss2)"
      and lnss2: "length nss2 = length (last xs # ys) - 1"
      and rlast2: "RELC (last (last xs # ys)) (last (last (cn # nss1) # nss2)) w"
      using conjunct2[OF RY[unfolded RLP_def], rule_format, OF stepsLY relmid] by blast
    \<comment> \<open>Splice.\<close>
    have spliced: "num_graph_impl.steps ((cn # nss1) @ nss2)"
      by (rule num_steps_extend[OF nss1]) (use nss2 in simp)
    have nss2_ne: "nss2 \<noteq> []" using lnss2 False by (cases ys) auto
    have last_eq: "last ((cn # nss1) @ nss2) = last (last (cn # nss1) # nss2)"
      using nss2_ne by simp
    have last_ys: "last (last xs # ys) = last (xs @ ys)" using False xs by simp
    have len_eq: "length (nss1 @ nss2) = length (xs @ ys) - 1"
      using lnss1 lnss2 xs False by auto
    show ?thesis
      apply (intro exI[where x = "nss1 @ nss2"] conjI)
      subgoal using spliced by simp
      subgoal by (rule len_eq)
      subgoal using rlast2 last_eq last_ys by simp
      done
  qed
qed

text \<open>The per-step kernel, packaged in the @{const RLP} shape the structural combinator's @{text PQ}
case consumes: ONE @{const edge_3} step of the propositional run lifts to a single numeric step
preserving @{const RELC}. The required propositional pre-facts (the @{const running_loc} source
location and @{term \<open>n < length actions\<close>}) and the propositional post-bound are supplied by the
phase's @{const end_start_pre} invariant / @{const LvP} threading; @{term \<open>fluent_in_bounds w\<close>} comes
from the numeric valid-state sequence. The propositional step itself is the antecedent of @{const RLP},
so it is consumed -- not re-derived.\<close>
lemma RLP_edge_3_single:
  assumes run: "fst s ! Suc n = running_loc"
      and n: "n < length actions"
      and Llen: "length (fst s) = length net_automata"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (edge_3_effect n s)))"
      and fin: "fluent_in_bounds w"
    shows "RLP w [s, edge_3_effect n s]"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "[s, edge_3_effect n s] \<noteq> []" by simp
next
  fix cn
  assume pstep: "graph_impl.steps [s, edge_3_effect n s]"
     and relhd: "RELC (hd [s, edge_3_effect n s]) cn w"
  obtain L vp c where s: "s = (L, vp, c)" by (cases s)
  obtain L' vp' c' where t: "edge_3_effect n s = (L', vp', c')" by (cases "edge_3_effect n s")
  obtain Ln vn cnn where cn: "cn = (Ln, vn, cnn)" by (cases cn)
  have Leq: "Ln = L" and ceq: "cnn = c" and relS: "REL vp vn w"
    using relhd unfolding s cn list.sel by (auto dest: RELC_locD RELC_clkD RELC_relD)
  \<comment> \<open>The propositional single step, extracted from the antecedent.\<close>
  have t2: "edge_3_effect n (L, vp, c) = (L', vp', c')" using t unfolding s by simp
  have step1: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using pstep unfolding s t2 by (auto elim: graph_impl.steps.cases)
  have L'fst: "L' = fst (edge_3_effect n (L, vp, c))" using t unfolding s by simp
  have pbnd2: "Simple_Network_Language.bounded (map_of net_bounds) vp'" using pbnd' unfolding t by simp
  have run2: "L ! Suc n = running_loc" using run unfolding s by simp
  have Llen2: "length L = length net_automata" using Llen unfolding s by simp
  obtain vn' where
      numstep: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    and relE: "REL vp' vn' w"
    using num_edge_3_step_lift[OF relS Llen2 run2 n step1 L'fst pbnd2 fin] by blast
  have "num_graph_impl.steps [cn, (L', vn', c')]"
    unfolding cn Leq ceq by (rule num_single_step_intro) (use numstep in \<open>simp add: prod.case\<close>)
  moreover have "RELC (edge_3_effect n s) (L', vn', c') w"
    unfolding t by (rule RELCI[OF relE])
  ultimately show "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length [s, edge_3_effect n s] - 1
                         \<and> RELC (last [s, edge_3_effect n s]) (last (cn # nss)) w"
    by (intro exI[where x = "[(L', vn', c')]"]) (simp add: t)
qed

text \<open>@{const RLP} satisfies the @{locale sequence_rules} composition laws (singleton @{thm [source]
RLP_base} and the splice @{thm [source] RLP_step}), so the @{emph \<open>relational\<close>} run-lift predicate
plugs into the same structural combinator @{const num_graph_impl.steps} uses. This is the numeric
mirror of @{thm [source] steps_seq.ext_seq_comp_seq_apply_induct_list_prop_composable}, but threading
@{const RELC} instead of the propositional happening invariants.\<close>
lemma RLP_neD: "RLP w ps \<Longrightarrow> ps \<noteq> []"
  unfolding RLP_def by blast

lemma RLP_sequence_rules: "sequence_rules (RLP w)"
proof (unfold_locales)
  show "RLP w [x]" for x by (rule RLP_base)
next
  fix xs ys
  assume a: "RLP w xs" and b: "RLP w (last xs # ys)"
  show "RLP w (xs @ ys)" by (rule RLP_step[OF a b RLP_neD[OF a]])
qed

text \<open>The @{const edge_3} phase-lift, via the structural combinator. The propositional happening run
through the @{const edge_3} phase is GIVEN (its existence is the @{const RLP} antecedent fired by the
combinator per step); the per-step @{const edge_3} kernel @{thm [source] RLP_edge_3_single} discharges
the combinator's @{text PQ} obligation under a propositional pre/post invariant pair @{term P} / @{term
Q} that the CALLER threads (in the run-lift this is the @{const end_start_pre} / @{const end_start_post}
bookkeeping established by @{thm [source] end_starts_possible}). Given @{const RELC} at the start config,
the result is a numeric run @{const RELC}-related at the end.\<close>
lemma num_edge_3_phase_lift:
  fixes P Q :: "nat \<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool"
  assumes R0: "RLP w xs \<and> R (last xs)"
      and PQ: "\<And>j s. j < length ns \<Longrightarrow> P j s \<Longrightarrow> Q j (edge_3_effect (ns ! j) s) \<and> RLP w [s, edge_3_effect (ns ! j) s]"
      and QP: "\<And>j s. Suc j < length ns \<Longrightarrow> Q j s \<Longrightarrow> P (Suc j) s"
      and RP0: "\<And>x. 0 < length ns \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. 0 < length ns \<Longrightarrow> Q (length ns - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. length ns = 0 \<Longrightarrow> R x \<Longrightarrow> S x"
      and SR': "\<And>x. S x \<Longrightarrow> R' x"
    shows "RLP w ((ext_seq \<circ> seq_apply) (map edge_3_effect ns) xs)
           \<and> R' (last ((ext_seq \<circ> seq_apply) (map edge_3_effect ns) xs))"
  by (rule sequence_rules.ext_seq_comp_seq_apply_induct_list_prop_composable[
            OF RLP_sequence_rules,
            where R = R and P = P and Q = Q and S = S and R' = R' and fs = "map edge_3_effect ns",
            simplified length_map nth_map, OF R0])
     (use PQ QP RP0 QSl RS0 SR' in blast)+

text \<open>The @{const starting_loc} source location is shared by @{const edge_2} (target @{const running_loc})
and @{const instant_trans_edge} (target @{const ending_loc}); among the five edges of an action automaton
these are the only two leaving @{const starting_loc}. So a propositional internal step from a config whose
@{term \<open>Suc n\<close>}-th location is @{const starting_loc} AND whose fired edge targets @{const running_loc} must
have fired @{const edge_2} at automaton @{term \<open>Suc n\<close>} (the target distinguishes it from
@{const instant_trans_edge}).\<close>
lemma prop_edge_2_pinned:
  assumes p: "p < length net_automata"
      and E: "(l, b, g, Sil aa, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
      and Lp: "L ! p = l"
      and start0: "L ! Suc n = starting_loc"
      and tgt: "l' = running_loc"
      and n: "n < length actions"
      and pSuc: "p = Suc n"
    shows "(l, b, g, Sil aa, f, r, l') = edge_2 (actions ! n)"
proof -
  have l_start: "l = starting_loc" using Lp start0 pSuc by simp
  have "(l, b, g, Sil aa, f, r, l')
          \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                  end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using E unfolding pSuc nth_auto_trans[OF n] action_to_automaton_def Let_def by simp
  thus ?thesis
    using l_start tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>The reusable per-step kernel for the EDGE_2 internal step: lifting ONE propositional
@{const edge_2} step (the @{const starting_loc} \<rightarrow> @{const running_loc} running-entry edge) to a numeric
@{const num_graph_impl.steps} step, preserving @{const REL}. The structure mirrors
@{thm [source] num_edge_3_step_lift}: @{const edge_2} writes only the propositional @{const prop_to_lock}
over_all variables (fresh of the fluents), so the abstract valuation @{term w} is UNCHANGED and tracking
survives. The numeric edge is the AUGMENTED @{const num_edge_2}, which conjoins the numeric over_all guard
@{const num_inv_guard} (and appends no update). Discharging that extra numeric guard is the only difference
from the @{const edge_3} kernel: it needs the over_all comparisons to be @{const comp_ok} at @{term w}
(from @{thm [source] snap_inv_comp_ok} under @{const num_val_ok}) and @{const sat_comps}-satisfied at
@{term w} -- the latter is the deferred active-action over_all fact, supplied as @{text sat_inv} (it is
@{const True} vacuously when @{term \<open>n_inv (actions ! n) = []\<close>}, the common benchmark case).\<close>
lemma num_edge_2_step_lift:
  assumes rel: "REL vp vn w"
      and Llen: "length L = length net_automata"
      and start0: "L ! Suc n = starting_loc"
      and n: "n < length actions"
      and pstep: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and L'eq: "L' = fst (edge_2_effect n (L, vp, c))"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) vp'"
      and fin: "fluent_in_bounds w"
      and wok: "num_val_ok w"
      and sat_inv: "sat_comps w (set (n_inv (actions ! n)))"
    shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle> \<and> REL vp' vn' w"
proof -
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF rel])
  have tr: "num_tracks vn w" by (rule REL_trD[OF rel])
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF rel])
  have aMem: "actions ! n \<in> set actions" using n by simp
  have L'_eq: "L' = L[Suc n := running_loc]"
    using L'eq by (simp add: edge_2_effect_alt)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF pstep]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const edge_2}.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds vp f vp'"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  \<comment> \<open>Pin @{term p} to @{term \<open>Suc n\<close>}: the only changed location is @{term \<open>Suc n\<close>}.\<close>
  have starting_ne_running: "starting_loc \<noteq> running_loc" by (simp add: locations_unique)
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume "p \<noteq> Suc n"
    hence "L[p := l'] ! Suc n = L ! Suc n" by simp
    moreover have "L[Suc n := running_loc] ! Suc n = running_loc" using Sn_lt by simp
    ultimately show False using L'eq2 L'_eq start0 starting_ne_running by simp
  qed
  \<comment> \<open>The fired edge targets @{const running_loc}: position @{term \<open>Suc n\<close>} of the post locations.\<close>
  have tgt: "l' = running_loc"
  proof -
    have "L[p := l'] ! Suc n = l'" using pSuc Sn_lt by simp
    moreover have "L[Suc n := running_loc] ! Suc n = running_loc" using Sn_lt by simp
    ultimately show ?thesis using L'eq2 L'_eq by simp
  qed
  have edge2: "(l, b, g, Sil a, f, r, l') = edge_2 (actions ! n)"
    by (rule prop_edge_2_pinned[OF P E LOC start0 tgt n pSuc])
  \<comment> \<open>The numeric edge: the AUGMENTED @{const num_edge_2}, with the conjoined @{const num_inv_guard}.\<close>
  have NE: "num_edge_2 (actions ! n) \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding pSuc by (rule num_nth_auto_num_edge_2[OF n])
  \<comment> \<open>The numeric edge's components, read off @{const num_edge_2}: same source/target/clocks/reset/update
     as @{const edge_2}, with the guard conjoined with @{const num_inv_guard}.\<close>
  have ne_eq: "num_edge_2 (actions ! n) = (l, bexp.and b (num_inv_guard (actions ! n)), g, Sil a, f, r, l')"
    unfolding num_edge_2_def augment_edge_def edge2[symmetric] by simp
  have NEassembled: "(l, bexp.and b (num_inv_guard (actions ! n)), g, Sil a, f, r, l')
                       \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    using NE unfolding ne_eq .
  \<comment> \<open>The combined numeric guard fires on the extended store: the propositional half by monotonicity,
     the numeric over_all half by @{thm [source] check_bexp_comps_guard}.\<close>
  have NBprop: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have inv_ok: "\<forall>cc \<in> set (n_inv (actions ! n)). comp_ok w cc"
    using snap_inv_comp_ok aMem wok by blast
  have NBinv: "check_bexp vn (num_inv_guard (actions ! n)) True"
    unfolding num_inv_guard_def by (rule check_bexp_comps_guard[OF tr inv_ok sat_inv])
  have NB: "check_bexp vn (bexp.and b (num_inv_guard (actions ! n))) True"
    using check_bexp_is_val.intros(3)[OF NBprop NBinv] by simp
  \<comment> \<open>The (propositional) update fires on the extended store, preserving tracking.\<close>
  obtain vn' where
      NU: "is_upds vn f vn'"
    and LE: "vp' \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn' x = vn x"
    using is_upds_map_le[OF U le] by blast
  \<comment> \<open>@{const edge_2} writes only @{const prop_to_lock} variables, fresh of the fluents, so tracking
     survives.\<close>
  have f_eq: "f = map (inc_prop_lock_ab 1) (over_all (actions ! n))"
    using edge2 by (simp add: edge_2_def Let_def)
  have fst_f: "fst ` set f = prop_to_lock ` set (over_all (actions ! n))"
    unfolding f_eq set_map image_image inc_prop_lock_ab_def by (simp add: comp_def)
  have fresh: "fluent_to_var h \<notin> fst ` set f" if h: "h \<in> set nfluents" for h
  proof
    assume "fluent_to_var h \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and ph: "fluent_to_var h = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus False using ph fluent_var_notin_net_bounds[OF h] by simp
  qed
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound from the propositional post-bound and tracking.\<close>
  have vp'_dom: "dom vp' = dom (map_of net_bounds)"
    using pbnd' unfolding Simple_Network_Language.bounded_def by blast
  have dom_vn: "dom vn = dom (map_of num_net_bounds)"
    using bnd unfolding Simple_Network_Language.bounded_def by blast
  have fset_sub: "fst ` set f \<subseteq> dom vn"
  proof
    fix x assume "x \<in> fst ` set f"
    then obtain p where p: "p \<in> set (over_all (actions ! n))" and xp: "x = prop_to_lock p"
      unfolding fst_f by auto
    have "prop_to_lock p \<in> dom (map_of net_bounds)"
      using map_of_net_bounds_action_inv[OF aMem] p by auto
    thus "x \<in> dom vn" using xp dom_vn dom_map_of_num_net_bounds by auto
  qed
  have vn'_dom: "dom vn' = dom (map_of num_net_bounds)"
    using is_upds_dom_eq[OF NU fset_sub] dom_vn by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    by (rule REL_bnd_from_proj[OF LE vp'_dom pbnd' TR fin vn'_dom])
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, vn, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, vn, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NEassembled NB G LOC Llen_num NU BND])
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    unfolding L'eq2 c'eq
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  thus ?thesis using LE TR BND by (auto intro: RELI)
qed

text \<open>The per-step kernel, packaged in the @{const RLP} shape the structural combinator's @{text PQ}
case consumes: ONE @{const edge_2} step of the propositional run lifts to a single numeric step
preserving @{const RELC}. Mirrors @{thm [source] RLP_edge_3_single}, with the extra over_all discharge
the augmented @{const num_edge_2} guard demands (@{text wok} / @{text sat_inv}) threaded through to
@{thm [source] num_edge_2_step_lift}: @{text sat_inv} is the deferred active-action over_all fact (it is
@{const True} vacuously when @{term \<open>n_inv (actions ! n) = []\<close>}).\<close>
lemma RLP_edge_2_single:
  assumes start0: "fst s ! Suc n = starting_loc"
      and n: "n < length actions"
      and Llen: "length (fst s) = length net_automata"
      and pbnd': "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (edge_2_effect n s)))"
      and fin: "fluent_in_bounds w"
      and wok: "num_val_ok w"
      and sat_inv: "sat_comps w (set (n_inv (actions ! n)))"
    shows "RLP w [s, edge_2_effect n s]"
  unfolding RLP_def
proof (intro conjI impI allI)
  show "[s, edge_2_effect n s] \<noteq> []" by simp
next
  fix cn
  assume pstep: "graph_impl.steps [s, edge_2_effect n s]"
     and relhd: "RELC (hd [s, edge_2_effect n s]) cn w"
  obtain L vp c where s: "s = (L, vp, c)" by (cases s)
  obtain L' vp' c' where t: "edge_2_effect n s = (L', vp', c')" by (cases "edge_2_effect n s")
  obtain Ln vn cnn where cn: "cn = (Ln, vn, cnn)" by (cases cn)
  have Leq: "Ln = L" and ceq: "cnn = c" and relS: "REL vp vn w"
    using relhd unfolding s cn list.sel by (auto dest: RELC_locD RELC_clkD RELC_relD)
  \<comment> \<open>The propositional single step, extracted from the antecedent.\<close>
  have t2: "edge_2_effect n (L, vp, c) = (L', vp', c')" using t unfolding s by simp
  have step1: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using pstep unfolding s t2 by (auto elim: graph_impl.steps.cases)
  have L'fst: "L' = fst (edge_2_effect n (L, vp, c))" using t unfolding s by simp
  have pbnd2: "Simple_Network_Language.bounded (map_of net_bounds) vp'" using pbnd' unfolding t by simp
  have start2: "L ! Suc n = starting_loc" using start0 unfolding s by simp
  have Llen2: "length L = length net_automata" using Llen unfolding s by simp
  obtain vn' where
      numstep: "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow> \<langle>L', vn', c'\<rangle>"
    and relE: "REL vp' vn' w"
    using num_edge_2_step_lift[OF relS Llen2 start2 n step1 L'fst pbnd2 fin wok sat_inv] by blast
  have "num_graph_impl.steps [cn, (L', vn', c')]"
    unfolding cn Leq ceq by (rule num_single_step_intro) (use numstep in \<open>simp add: prod.case\<close>)
  moreover have "RELC (edge_2_effect n s) (L', vn', c') w"
    unfolding t by (rule RELCI[OF relE])
  ultimately show "\<exists>nss. num_graph_impl.steps (cn # nss) \<and> length nss = length [s, edge_2_effect n s] - 1
                         \<and> RELC (last [s, edge_2_effect n s]) (last (cn # nss)) w"
    by (intro exI[where x = "[(L', vn', c')]"]) (simp add: t)
qed

text \<open>The @{const edge_2} phase-lift, via the structural combinator. Identical in shape to
@{thm [source] num_edge_3_phase_lift} (this phase also writes no fluent, so the abstract valuation
@{term w} is fixed throughout): the propositional happening run through the @{const edge_2} phase is the
@{const RLP} antecedent fired per step, and the per-step @{const edge_2} kernel
@{thm [source] RLP_edge_2_single} discharges the combinator's @{text PQ} obligation under the caller's
propositional pre/post invariant pair @{term P} / @{term Q} (the per-step @{const num_val_ok} /
over_all-@{const sat_comps} facts the augmented @{const num_edge_2} guard needs are established by the
caller inside @{text PQ}). Given @{const RELC} at the start config, the result is a numeric run
@{const RELC}-related at the end.\<close>
lemma num_edge_2_phase_lift:
  fixes P Q :: "nat \<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool"
  assumes R0: "RLP w xs \<and> R (last xs)"
      and PQ: "\<And>j s. j < length ns \<Longrightarrow> P j s \<Longrightarrow> Q j (edge_2_effect (ns ! j) s) \<and> RLP w [s, edge_2_effect (ns ! j) s]"
      and QP: "\<And>j s. Suc j < length ns \<Longrightarrow> Q j s \<Longrightarrow> P (Suc j) s"
      and RP0: "\<And>x. 0 < length ns \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. 0 < length ns \<Longrightarrow> Q (length ns - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. length ns = 0 \<Longrightarrow> R x \<Longrightarrow> S x"
      and SR': "\<And>x. S x \<Longrightarrow> R' x"
    shows "RLP w ((ext_seq \<circ> seq_apply) (map edge_2_effect ns) xs)
           \<and> R' (last ((ext_seq \<circ> seq_apply) (map edge_2_effect ns) xs))"
  by (rule sequence_rules.ext_seq_comp_seq_apply_induct_list_prop_composable[
            OF RLP_sequence_rules,
            where R = R and P = P and Q = Q and S = S and R' = R' and fs = "map edge_2_effect ns",
            simplified length_map nth_map, OF R0])
     (use PQ QP RP0 QSl RS0 SR' in blast)+


end

end

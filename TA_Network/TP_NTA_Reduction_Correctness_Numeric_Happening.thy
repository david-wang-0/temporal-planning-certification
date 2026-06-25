theory TP_NTA_Reduction_Correctness_Numeric_Happening
  imports TP_NTA_Reduction_Correctness_Numeric_PhaseLifts
begin

context numeric_tp_nta_reduction_correctness
begin

text \<open>For the @{const num_edge_2} phase the entry guard's @{text sat_inv} obligation (the over_all
  comparisons of the just-started action @{term \<open>actions ! n\<close>}) is discharged at the running fold valuation
  @{term \<open>num_plan.num_rat_impl.happening_num_update ys (snd (M i))\<close>}: the over_all fluents are READ-ONLY along
  the run, so the fold (@{thm [source] happening_num_update_inv_unchanged}) and the state sequence
  (@{thm [source] num_seq_inv_const}) both pin them to the INITIAL valuation, where @{text n_inv_init_sat}
  certifies the over_all hold.\<close>
lemma inv_sat_at_fold:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and i: "i \<le> length planning_sem.htpl"
      and a: "a \<in> set actions"
      and ysmem: "\<And>s. s \<in> set ys \<Longrightarrow> \<exists>b \<in> set actions. s = at_start b \<or> s = at_end b"
    shows "sat_comps (num_plan.num_rat_impl.happening_num_update ys (snd (M i))) (set (n_inv a))"
proof -
  have agree: "num_plan.num_rat_impl.happening_num_update ys (snd (M i)) g = snd (M 0) g"
    if c: "c \<in> set (n_inv a)" and f: "g \<in> comp_fluents c" for c g
  proof -
    have ginv: "g \<in> (\<Union>a \<in> set actions. \<Union>c \<in> set (n_inv a). comp_fluents c)"
      using a c f by blast
    have "num_plan.num_rat_impl.happening_num_update ys (snd (M i)) g = snd (M i) g"
      by (rule happening_num_update_inv_unchanged[OF ginv ysmem])
    also have "\<dots> = snd (M 0) g" by (rule num_seq_inv_const[OF vss i ginv])
    finally show ?thesis .
  qed
  have "sat_comps (num_plan.num_rat_impl.happening_num_update ys (snd (M i))) (set (n_inv a))
          = sat_comps (snd (M 0)) (set (n_inv a))"
    by (rule sat_comps_cong) (use agree in blast)
  thus ?thesis unfolding m0 using n_inv_init_sat a by simp
qed

text \<open>The propositional @{const net_impl.sem} carries @{const net_bounds}-boundedness of the store as a
  PREMISE on the @{const Simple_Network_Language.label.Del} half of every @{const step_u'} (the
  @{thm [source] step_u_elims} extraction), so the HEAD store of any @{const graph_impl.steps} run that has
  a step from it is @{const net_bounds}-bounded. This supplies the @{text pbnd'} (PRE-store bound) the
  per-phase struct facts need, WITHOUT a propositional per-step post-bound invariant -- it is recovered by
  inverting the very step that leaves the config.\<close>
lemma graph_impl_steps_hd_bounded:
  assumes "graph_impl.steps (x # y # xs)"
  shows "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd x))"
proof -
  obtain L vp c where x: "x = (L, vp, c)" by (cases x)
  obtain Ly vy cy where y: "y = (Ly, vy, cy)" by (cases y)
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>Ly, vy, cy\<rangle>"
    using assms unfolding x y by (auto elim: graph_impl.steps.cases simp: prod.case)
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>Ly, vy, cy\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  have B: "B = map_of net_bounds"
    using as unfolding net_impl.sem_def by simp
  have "Simple_Network_Language.bounded B vp"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as TAG_def by blast
  thus ?thesis unfolding x fst_conv snd_conv B .
qed

text \<open>The POST-store of EVERY propositional @{const step_u'} step is @{const net_bounds}-bounded: the
  internal half (@{text step_int}, the only non-@{const Del} action shape reachable in our action nets)
  carries @{term \<open>bounded B s'\<close>} on its post-store as a tagged premise. This is the POST-store companion of
  @{thm [source] graph_impl_steps_hd_bounded} (which bounds the PRE-store): it bounds the store the step
  lands ON, so it reaches every non-head config of a run -- including each phase's LAST config.\<close>
lemma step_u'_net_impl_post_bounded:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
    shows "Simple_Network_Language.bounded (map_of net_bounds) vp'"
proof -
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "a \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding net_impl.sem_def TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain aa where aInt: "a = Internal aa"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
  have B: "B = map_of net_bounds"
    using as unfolding net_impl.sem_def by simp
  have "Simple_Network_Language.bounded B vp'"
    apply (cases rule: step_u_elims'(2)[OF actI[unfolded aInt as]])
    unfolding TAG_def by blast
  thus ?thesis unfolding B .
qed

text \<open>The POST-store of any non-head config @{term \<open>xs ! Suc k\<close>} of a propositional @{const graph_impl.steps}
  run is @{const net_bounds}-bounded: the step @{term \<open>xs ! k \<rightarrow> xs ! Suc k\<close>} lands on it. Cleaner and more
  complete than @{thm [source] graph_impl_steps_hd_bounded}: it reaches the LAST config of every sub-run.\<close>
lemma graph_impl_steps_nth_bounded:
  assumes steps: "graph_impl.steps xs"
      and Sk: "Suc k < length xs"
      and Llen: "length (fst (xs ! k)) = length net_automata"
    shows "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd (xs ! Suc k)))"
proof -
  have k_lt: "k < length xs" using Sk by simp
  have dropNN: "drop k xs \<noteq> []" using Sk by simp
  have split: "take k xs @ drop k xs = xs" by simp
  have stepstake: "graph_impl.steps (take k xs @ drop k xs)" using steps unfolding split .
  have stepsdrop: "graph_impl.steps (drop k xs)"
    by (rule graph_impl.steps_appendD2[OF stepstake dropNN])
  have drop_dec: "drop k xs = xs ! k # xs ! Suc k # drop (Suc (Suc k)) xs"
    using Sk k_lt by (simp add: Cons_nth_drop_Suc Suc_lessD)
  obtain L vp c where xk: "xs ! k = (L, vp, c)" by (cases "xs ! k")
  obtain L' vp' c' where xSk: "xs ! Suc k = (L', vp', c')" by (cases "xs ! Suc k")
  have stepsdec: "graph_impl.steps ((L, vp, c) # (L', vp', c') # drop (Suc (Suc k)) xs)"
    using stepsdrop unfolding drop_dec xk xSk .
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using stepsdec by (auto elim: graph_impl.steps.cases simp: prod.case)
  have Llen': "length L = length net_automata" using Llen unfolding xk by simp
  have "Simple_Network_Language.bounded (map_of net_bounds) vp'"
    by (rule step_u'_net_impl_post_bounded[OF step Llen'])
  thus ?thesis unfolding xSk by simp
qed

text \<open>The location-vector length and the main-automaton location @{const planning_loc} are preserved along
  any @{const seq_apply} run whose every step preserves them (each action edge effect is a list-update at a
  @{text \<open>Suc n\<close>} position, so it touches neither @{term 0} nor the length). Induct on the run position via
  @{thm [source] seq_apply_Cons_nth_Suc}.\<close>
lemma seq_apply_locs_preserved:
  assumes pres: "\<And>j s. j < length fs \<Longrightarrow>
                    length (fst ((fs ! j) s)) = length (fst s) \<and> fst ((fs ! j) s) ! 0 = fst s ! 0"
      and k: "k < length (x # seq_apply fs x)"
    shows "length (fst ((x # seq_apply fs x) ! k)) = length (fst x)
           \<and> fst ((x # seq_apply fs x) ! k) ! 0 = fst x ! 0"
  using k
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have klen: "k < length fs" using Suc.prems by simp
  have ih: "length (fst ((x # seq_apply fs x) ! k)) = length (fst x)
            \<and> fst ((x # seq_apply fs x) ! k) ! 0 = fst x ! 0"
    using Suc.IH Suc.prems by simp
  have step: "(x # seq_apply fs x) ! Suc k = (fs ! k) ((x # seq_apply fs x) ! k)"
    by (rule seq_apply_Cons_nth_Suc[OF klen])
  have "length (fst ((fs ! k) ((x # seq_apply fs x) ! k))) = length (fst ((x # seq_apply fs x) ! k))
        \<and> fst ((fs ! k) ((x # seq_apply fs x) ! k)) ! 0 = fst ((x # seq_apply fs x) ! k) ! 0"
    by (rule pres[OF klen])
  thus ?case using ih step by simp
qed

text \<open>The propositional internal step @{term \<open>xs ! k \<rightarrow> xs ! Suc k\<close>} of a @{const graph_impl.steps} run,
  extracted from the run by dropping the leading @{term k} configs and inverting the head step. Supplies the
  per-position step the source-location pinning lemmas consume.\<close>
lemma graph_impl_steps_nth_step:
  assumes steps: "graph_impl.steps xs"
      and Sk: "Suc k < length xs"
    shows "net_impl.sem \<turnstile> \<langle>fst (xs ! k), fst (snd (xs ! k)), snd (snd (xs ! k))\<rangle>
                          \<rightarrow> \<langle>fst (xs ! Suc k), fst (snd (xs ! Suc k)), snd (snd (xs ! Suc k))\<rangle>"
proof -
  have k_lt: "k < length xs" using Sk by simp
  have dropNN: "drop k xs \<noteq> []" using Sk by simp
  have split: "take k xs @ drop k xs = xs" by simp
  have stepstake: "graph_impl.steps (take k xs @ drop k xs)" using steps unfolding split .
  have stepsdrop: "graph_impl.steps (drop k xs)"
    by (rule graph_impl.steps_appendD2[OF stepstake dropNN])
  have drop_dec: "drop k xs = xs ! k # xs ! Suc k # drop (Suc (Suc k)) xs"
    using Sk k_lt by (simp add: Cons_nth_drop_Suc Suc_lessD)
  obtain L vp c where xk: "xs ! k = (L, vp, c)" by (cases "xs ! k")
  obtain L' vp' c' where xSk: "xs ! Suc k = (L', vp', c')" by (cases "xs ! Suc k")
  have stepsdec: "graph_impl.steps ((L, vp, c) # (L', vp', c') # drop (Suc (Suc k)) xs)"
    using stepsdrop unfolding drop_dec xk xSk .
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
    using stepsdec by (auto elim: graph_impl.steps.cases simp: prod.case)
  show ?thesis using step unfolding xk xSk by simp
qed

text \<open>The per-effect length/@{const planning_loc}-preservation facts for the five action edge effects: each
  is a list-update at @{text \<open>Suc n\<close>} (from the alt-rewrite forms), so it preserves the length and the
  @{term 0}-th (main-automaton) location.\<close>
lemma start_edge_effect_preserves_loc0:
  "length (fst (start_edge_effect n s)) = length (fst s) \<and> fst (start_edge_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: start_edge_effect_alt)

lemma end_edge_effect_preserves_loc0:
  "length (fst (end_edge_effect n s)) = length (fst s) \<and> fst (end_edge_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: end_edge_effect_alt)

lemma edge_2_effect_preserves_loc0:
  "length (fst (edge_2_effect n s)) = length (fst s) \<and> fst (edge_2_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: edge_2_effect_alt)

lemma edge_3_effect_preserves_loc0:
  "length (fst (edge_3_effect n s)) = length (fst s) \<and> fst (edge_3_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: edge_3_effect_alt)

lemma instant_trans_edge_effect_preserves_loc0:
  "length (fst (instant_trans_edge_effect n s)) = length (fst s) \<and> fst (instant_trans_edge_effect n s) ! 0 = fst s ! 0"
  by (cases s) (simp add: instant_trans_edge_effect_alt)

text \<open>Inverting a propositional internal step whose POST-location vector is @{term \<open>L[Suc n := l']\<close>}: under
  @{term \<open>L ! 0 = planning_loc\<close>} (which @{const Lv_conds} pins at every run config) the fired edge sits at
  automaton @{term \<open>Suc n\<close>} -- the main automaton (@{term \<open>p = 0\<close>}) is excluded because from
  @{const planning_loc} its only edge moves to @{const goal_loc}, which would change position @{term 0}; an
  action edge (@{term \<open>p = Suc m\<close>}) strictly moves its location, so the changed position
  @{term \<open>Suc n\<close>} pins @{term \<open>p = Suc n\<close>}. The edge targets @{term l'} and is one of the five action edges,
  so the SOURCE location @{term \<open>L ! Suc n\<close>} is recovered. TARGET analogue of the source-based pinning
  lemmas (@{thm [source] prop_start_edge_pinned} et al.).\<close>
lemma prop_step_edge_at_Sucn:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := l']"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "\<exists>e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                     end_edge (actions ! n), instant_trans_edge (actions ! n)].
             fst e = L ! Suc n \<and> snd (snd (snd (snd (snd (snd e))))) = l'"
proof -
  obtain Li vi ci a where
      del: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "a \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    by (rule step_u'_elims[OF step]) blast
  obtain t where Lieq: "Li = L" and vieq: "vi = vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding net_impl.sem_def TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', vp', c'\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain aa where aInt: "a = Internal aa"
    using prop_non_del_step_internal[OF actI aD Llen] by blast
  obtain p l b g f r l'' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil aa, f, r, l'') \<in> trans (automaton_of (net_automata ! p))"
    and LOC: "L ! p = l"
    and L'eq2: "L' = L[p := l'']"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen])
  have Sn_lt: "Suc n < length L" using Llen n by (simp add: length_net_automata)
  have len0: "0 < length L" using Sn_lt by simp
  \<comment> \<open>The main automaton cannot fire: from @{const planning_loc} its only edge targets @{const goal_loc},
     which would change position @{term 0} -- but @{term L'} fixes position @{term 0}.\<close>
  have p_ne0: "p \<noteq> 0"
  proof
    assume p0: "p = 0"
    have l_pl: "l = planning_loc" using LOC p0 main_planning by simp
    have "(l, b, g, Sil aa, f, r, l'') \<in> set [main_auto_init_edge, main_auto_goal_edge, main_auto_loop]"
      using E unfolding p0 main_auto_trans by simp
    hence l''_goal: "l'' = goal_loc"
      using l_pl
      by (auto simp: main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def
                     Let_def locations_unique)
    have "L' ! 0 = goal_loc" using L'eq2 p0 l''_goal len0 by simp
    moreover have "L' ! 0 = planning_loc" using L'eq main_planning len0 by simp
    ultimately show False by (simp add: locations_unique)
  qed
  \<comment> \<open>So an action automaton fired; its edge strictly moves location (@{term \<open>l \<noteq> l''\<close>}).\<close>
  obtain m where pSucm: "p = Suc m" using p_ne0 by (cases p) auto
  have m_lt: "m < length actions" using P unfolding pSucm length_net_automata by simp
  have edge_m: "(l, b, g, Sil aa, f, r, l'') \<in> set [start_edge (actions ! m), edge_2 (actions ! m),
                  edge_3 (actions ! m), end_edge (actions ! m), instant_trans_edge (actions ! m)]"
    using E unfolding pSucm nth_auto_trans[OF m_lt] action_to_automaton_def Let_def by simp
  have l_ne: "l \<noteq> l''"
    using edge_m
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
  \<comment> \<open>Since the edge changes the location and @{term L'} differs from @{term L} only at @{term \<open>Suc n\<close>},
     the fired automaton is @{term \<open>Suc n\<close>}.\<close>
  have pSuc: "p = Suc n"
  proof (rule ccontr)
    assume pne: "p \<noteq> Suc n"
    have "L' ! p = L ! p" using L'eq pne by simp
    moreover have "L' ! p = l''" using L'eq2 LOC P Llen by (simp add: length_net_automata)
    ultimately show False using LOC l_ne by simp
  qed
  have m_eq_n: "m = n" using pSuc pSucm by simp
  have edge: "(l, b, g, Sil aa, f, r, l'') \<in> set [start_edge (actions ! n), edge_2 (actions ! n),
                edge_3 (actions ! n), end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    using edge_m unfolding m_eq_n .
  have l_src: "l = L ! Suc n" using LOC pSuc by simp
  have l''_tgt: "l'' = l'"
  proof -
    have "L' ! Suc n = l'" using L'eq Sn_lt by simp
    moreover have "L' ! Suc n = l''" using L'eq2 pSuc Sn_lt by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis
    apply (rule bexI[where x = "(l, b, g, Sil aa, f, r, l'')"])
    using l_src l''_tgt edge by auto
qed

text \<open>A propositional internal step whose POST location at @{term \<open>Suc n\<close>} is @{const starting_loc} fired
  @{const start_edge}, so its SOURCE location is @{const off_loc} (only @{const start_edge} targets
  @{const starting_loc} among the five action edges).\<close>
lemma prop_step_source_off:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := starting_loc]"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "L ! Suc n = off_loc"
proof -
  obtain e where e: "e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                              end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    and src: "fst e = L ! Suc n"
    and tgt: "snd (snd (snd (snd (snd (snd e))))) = starting_loc"
    using prop_step_edge_at_Sucn[OF step Llen L'eq main_planning n] by blast
  show ?thesis using e src tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>A propositional internal step whose POST location at @{term \<open>Suc n\<close>} is @{const off_loc} fired
  @{const end_edge}, so its SOURCE location is @{const ending_loc} (only @{const end_edge} targets
  @{const off_loc} among the five action edges).\<close>
lemma prop_step_source_ending:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := off_loc]"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "L ! Suc n = ending_loc"
proof -
  obtain e where e: "e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                              end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    and src: "fst e = L ! Suc n"
    and tgt: "snd (snd (snd (snd (snd (snd e))))) = off_loc"
    using prop_step_edge_at_Sucn[OF step Llen L'eq main_planning n] by blast
  show ?thesis using e src tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed

text \<open>A propositional internal step whose POST location at @{term \<open>Suc n\<close>} is @{const running_loc} fired
  @{const edge_2}, so its SOURCE location is @{const starting_loc} (only @{const edge_2} targets
  @{const running_loc} among the five action edges).\<close>
lemma prop_step_source_starting:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>L', vp', c'\<rangle>"
      and Llen: "length L = length net_automata"
      and L'eq: "L' = L[Suc n := running_loc]"
      and main_planning: "L ! 0 = planning_loc"
      and n: "n < length actions"
    shows "L ! Suc n = starting_loc"
proof -
  obtain e where e: "e \<in> set [start_edge (actions ! n), edge_2 (actions ! n), edge_3 (actions ! n),
                              end_edge (actions ! n), instant_trans_edge (actions ! n)]"
    and src: "fst e = L ! Suc n"
    and tgt: "snd (snd (snd (snd (snd (snd e))))) = running_loc"
    using prop_step_edge_at_Sucn[OF step Llen L'eq main_planning n] by blast
  show ?thesis using e src tgt
    by (auto simp: start_edge_def edge_2_def edge_3_def end_edge_def instant_trans_edge_def
                   Let_def locations_unique)
qed
text \<open>The START-phase @{text struct} export: for a @{const start_edge_effect} @{const seq_apply} sub-run
  whose head config has the @{const planning_loc} main location and the @{const net_automata} length, every
  run-position @{term k} satisfies the three @{text struct} facts @{thm [source] num_start_phase_lift}
  demands -- the @{const off_loc} SOURCE location (recovered from the @{const starting_loc} TARGET via
  @{thm [source] prop_step_source_off}), the length, and the @{const net_bounds} bound on the post-store
  (via @{thm [source] graph_impl_steps_nth_bounded}). Locations/length thread through the run by
  @{thm [source] seq_apply_locs_preserved}, the per-position step by @{thm [source] graph_impl_steps_nth_step}.\<close>
lemma start_phase_struct:
  assumes run: "graph_impl.steps (sp # seq_apply (map start_edge_effect ns) sp)"
      and head0: "fst sp ! 0 = planning_loc"
      and headlen: "length (fst sp) = length net_automata"
      and ns_act: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions"
      and k: "k < length ns"
    shows "fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k) ! Suc (ns ! k) = off_loc
           \<and> length (fst ((sp # seq_apply (map start_edge_effect ns) sp) ! k)) = length net_automata
           \<and> Simple_Network_Language.bounded (map_of net_bounds)
                 (fst (snd (start_edge_effect (ns ! k)
                             ((sp # seq_apply (map start_edge_effect ns) sp) ! k))))"
proof -
  let ?xs = "sp # seq_apply (map start_edge_effect ns) sp"
  let ?ck = "?xs ! k"
  have lenxs: "length ?xs = Suc (length ns)" by simp
  have Sk: "Suc k < length ?xs" using k by simp
  have k_lt_xs: "k < length ?xs" using k by simp
  \<comment> \<open>Per-step location/length preservation along the run.\<close>
  have pres: "length (fst ((map start_edge_effect ns ! j) s)) = length (fst s)
                \<and> fst ((map start_edge_effect ns ! j) s) ! 0 = fst s ! 0"
    if j: "j < length (map start_edge_effect ns)" for j s
    using start_edge_effect_preserves_loc0[of "ns ! j" s] j by simp
  have loc0len: "length (fst ?ck) = length (fst sp) \<and> fst ?ck ! 0 = fst sp ! 0"
    using seq_apply_locs_preserved[OF pres, of k] k_lt_xs by simp
  have ckloc0: "fst ?ck ! 0 = planning_loc" using loc0len head0 by simp
  have cklen: "length (fst ?ck) = length net_automata" using loc0len headlen by simp
  \<comment> \<open>The next config is the @{const start_edge_effect} image, a @{const starting_loc}-targeting update.\<close>
  have nxt: "?xs ! Suc k = start_edge_effect (ns ! k) ?ck"
    using seq_apply_Cons_nth_Suc[of k "map start_edge_effect ns" sp] k by simp
  obtain L vp c where ck: "?ck = (L, vp, c)" by (cases ?ck)
  have nxt_eq: "fst (?xs ! Suc k) = L[Suc (ns ! k) := starting_loc]"
    unfolding nxt ck by (simp add: start_edge_effect_alt)
  \<comment> \<open>The per-position propositional step.\<close>
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?xs ! Suc k), fst (snd (?xs ! Suc k)), snd (snd (?xs ! Suc k))\<rangle>"
    using graph_impl_steps_nth_step[OF run Sk] unfolding ck by simp
  have nk_act: "ns ! k < length actions" using ns_act[of "ns ! k"] k by simp
  have Llen: "length L = length net_automata" using cklen ck by simp
  have main0: "L ! 0 = planning_loc" using ckloc0 ck by simp
  \<comment> \<open>Conjunct 1: the @{const off_loc} source location.\<close>
  have off: "L ! Suc (ns ! k) = off_loc"
    by (rule prop_step_source_off[OF step Llen nxt_eq main0 nk_act])
  have c1: "fst ?ck ! Suc (ns ! k) = off_loc" using off ck by simp
  \<comment> \<open>Conjunct 3: the @{const net_bounds} bound on the post-store.\<close>
  have c3: "Simple_Network_Language.bounded (map_of net_bounds)
              (fst (snd (start_edge_effect (ns ! k) ?ck)))"
    using graph_impl_steps_nth_bounded[OF run Sk] cklen nxt by simp
  show ?thesis using c1 cklen c3 by blast
qed

text \<open>The END-phase @{text struct} export, the mirror of @{thm [source] start_phase_struct}: each
  @{const end_edge_effect} step targets @{const off_loc}, so the SOURCE location is @{const ending_loc}
  (via @{thm [source] prop_step_source_ending}).\<close>
lemma end_phase_struct:
  assumes run: "graph_impl.steps (sp # seq_apply (map end_edge_effect ns) sp)"
      and head0: "fst sp ! 0 = planning_loc"
      and headlen: "length (fst sp) = length net_automata"
      and ns_act: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions"
      and k: "k < length ns"
    shows "fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k) ! Suc (ns ! k) = ending_loc
           \<and> length (fst ((sp # seq_apply (map end_edge_effect ns) sp) ! k)) = length net_automata
           \<and> Simple_Network_Language.bounded (map_of net_bounds)
                 (fst (snd (end_edge_effect (ns ! k)
                             ((sp # seq_apply (map end_edge_effect ns) sp) ! k))))"
proof -
  let ?xs = "sp # seq_apply (map end_edge_effect ns) sp"
  let ?ck = "?xs ! k"
  have Sk: "Suc k < length ?xs" using k by simp
  have k_lt_xs: "k < length ?xs" using k by simp
  have pres: "length (fst ((map end_edge_effect ns ! j) s)) = length (fst s)
                \<and> fst ((map end_edge_effect ns ! j) s) ! 0 = fst s ! 0"
    if j: "j < length (map end_edge_effect ns)" for j s
    using end_edge_effect_preserves_loc0[of "ns ! j" s] j by simp
  have loc0len: "length (fst ?ck) = length (fst sp) \<and> fst ?ck ! 0 = fst sp ! 0"
    using seq_apply_locs_preserved[OF pres, of k] k_lt_xs by simp
  have ckloc0: "fst ?ck ! 0 = planning_loc" using loc0len head0 by simp
  have cklen: "length (fst ?ck) = length net_automata" using loc0len headlen by simp
  have nxt: "?xs ! Suc k = end_edge_effect (ns ! k) ?ck"
    using seq_apply_Cons_nth_Suc[of k "map end_edge_effect ns" sp] k by simp
  obtain L vp c where ck: "?ck = (L, vp, c)" by (cases ?ck)
  have nxt_eq: "fst (?xs ! Suc k) = L[Suc (ns ! k) := off_loc]"
    unfolding nxt ck by (simp add: end_edge_effect_alt)
  have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?xs ! Suc k), fst (snd (?xs ! Suc k)), snd (snd (?xs ! Suc k))\<rangle>"
    using graph_impl_steps_nth_step[OF run Sk] unfolding ck by simp
  have nk_act: "ns ! k < length actions" using ns_act[of "ns ! k"] k by simp
  have Llen: "length L = length net_automata" using cklen ck by simp
  have main0: "L ! 0 = planning_loc" using ckloc0 ck by simp
  have endl: "L ! Suc (ns ! k) = ending_loc"
    by (rule prop_step_source_ending[OF step Llen nxt_eq main0 nk_act])
  have c1: "fst ?ck ! Suc (ns ! k) = ending_loc" using endl ck by simp
  have c3: "Simple_Network_Language.bounded (map_of net_bounds)
              (fst (snd (end_edge_effect (ns ! k) ?ck)))"
    using graph_impl_steps_nth_bounded[OF run Sk] cklen nxt by simp
  show ?thesis using c1 cklen c3 by blast
qed

text \<open>The @{const apply_instant_actions} run has @{term \<open>3 * length ns\<close>} configs (each instant index
  contributes its three-config @{const apply_snap_action} block). Induct on @{term ns}.\<close>
lemma length_apply_instant_actions:
  "length (apply_instant_actions ns s) = 3 * length ns"
proof (induction ns arbitrary: s)
  case Nil
  show ?case by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil)
next
  case (Cons n ns')
  have "apply_instant_actions (n # ns') s
          = apply_snap_action n s @ apply_instant_actions ns' (last (apply_snap_action n s))"
    by (rule apply_instant_actions_Cons)
  thus ?case using Cons.IH by (simp add: apply_snap_action_unfold)
qed

text \<open>The block-config decomposition of an @{const apply_instant_actions} run: for any instant index
  @{term \<open>k < length ns\<close>}, the four configs of block @{term k} in @{term \<open>s # apply_instant_actions ns s\<close>}
  sit at positions @{term \<open>3 * k\<close>}, @{term \<open>3 * k + 1\<close>}, @{term \<open>3 * k + 2\<close>}, @{term \<open>3 * k + 3\<close>} and are
  the @{const start_edge_effect}/@{const instant_trans_edge_effect}/@{const end_edge_effect} chain. Induct
  on @{term ns} (the head block sits at the front, the rest shifts by 3).\<close>
lemma apply_instant_actions_block_nth_conj:
  assumes k: "k < length ns"
  shows "(s # apply_instant_actions ns s) ! (3 * k + 1)
            = start_edge_effect (ns ! k) ((s # apply_instant_actions ns s) ! (3 * k))
         \<and> (s # apply_instant_actions ns s) ! (3 * k + 2)
            = instant_trans_edge_effect (ns ! k) ((s # apply_instant_actions ns s) ! (3 * k + 1))
         \<and> (s # apply_instant_actions ns s) ! (3 * k + 3)
            = end_edge_effect (ns ! k) ((s # apply_instant_actions ns s) ! (3 * k + 2))"
  using k
proof (induction ns arbitrary: s k)
  case Nil
  thus ?case by simp
next
  case (Cons n ns')
  let ?s1 = "start_edge_effect n s"
  let ?s2 = "instant_trans_edge_effect n ?s1"
  let ?s3 = "end_edge_effect n ?s2"
  have run_unfold: "s # apply_instant_actions (n # ns') s
                      = s # ?s1 # ?s2 # ?s3 # apply_instant_actions ns' ?s3"
    by (subst apply_instant_actions_Cons) (simp add: apply_snap_action_unfold)
  show ?case
  proof (cases k)
    case 0
    show ?thesis unfolding run_unfold 0 by simp
  next
    case (Suc k')
    have k'lt: "k' < length ns'" using Cons.prems Suc by simp
    have shift1: "3 * Suc k' + 1 = Suc (Suc (Suc (3 * k' + 1)))" by simp
    have shift2: "3 * Suc k' + 2 = Suc (Suc (Suc (3 * k' + 2)))" by simp
    have shift3: "3 * Suc k' + 3 = Suc (Suc (Suc (3 * k' + 3)))" by simp
    have shift0: "3 * Suc k' = Suc (Suc (Suc (3 * k')))" by simp
    note IH = Cons.IH[OF k'lt, of ?s3]
    show ?thesis
      unfolding run_unfold Suc shift0 shift1 shift2 shift3
      using IH by (simp add: nth_Cons')
  qed
qed

lemmas apply_instant_actions_block_nth = apply_instant_actions_block_nth_conj[THEN conjunct1]
  apply_instant_actions_block_nth_conj[THEN conjunct2, THEN conjunct1]
  apply_instant_actions_block_nth_conj[THEN conjunct2, THEN conjunct2]

text \<open>The location-vector length and the @{const planning_loc} main location are preserved along any
  @{const apply_instant_actions} run: each of the three block effects is a @{text \<open>Suc n\<close>}-update. Induct on
  @{term ns}, threading the block-end config; the head block's three configs preserve loc0/length by the
  per-effect facts, the tail by the IH.\<close>
lemma apply_instant_actions_locs_preserved:
  assumes k: "k < length (s # apply_instant_actions ns s)"
  shows "length (fst ((s # apply_instant_actions ns s) ! k)) = length (fst s)
         \<and> fst ((s # apply_instant_actions ns s) ! k) ! 0 = fst s ! 0"
  using k
proof (induction ns arbitrary: s k)
  case Nil
  show ?case using Nil.prems
    by (simp add: apply_instant_actions_def seq_apply'_def ext_seq'_with_Nil)
next
  case (Cons n ns')
  let ?s1 = "start_edge_effect n s"
  let ?s2 = "instant_trans_edge_effect n ?s1"
  let ?s3 = "end_edge_effect n ?s2"
  have run_unfold: "s # apply_instant_actions (n # ns') s
                      = s # ?s1 # ?s2 # ?s3 # apply_instant_actions ns' ?s3"
    by (subst apply_instant_actions_Cons) (simp add: apply_snap_action_unfold)
  \<comment> \<open>The three head-block configs preserve loc0/length relative to @{term s}.\<close>
  have p1: "length (fst ?s1) = length (fst s) \<and> fst ?s1 ! 0 = fst s ! 0"
    using start_edge_effect_preserves_loc0[of n s] .
  have p2: "length (fst ?s2) = length (fst s) \<and> fst ?s2 ! 0 = fst s ! 0"
    using instant_trans_edge_effect_preserves_loc0[of n ?s1] p1 by simp
  have p3: "length (fst ?s3) = length (fst s) \<and> fst ?s3 ! 0 = fst s ! 0"
    using end_edge_effect_preserves_loc0[of n ?s2] p2 by simp
  show ?case
  proof (cases k)
    case 0
    show ?thesis unfolding run_unfold 0 by simp
  next
    case (Suc k0)
    show ?thesis
    proof (cases k0)
      case 0
      show ?thesis unfolding run_unfold Suc 0 using p1 by simp
    next
      case (Suc k1)
      show ?thesis
      proof (cases k1)
        case 0
        show ?thesis unfolding run_unfold \<open>k = Suc k0\<close> Suc 0 using p2 by simp
      next
        case (Suc k2)
        \<comment> \<open>Positions @{term \<open>k \<ge> 3\<close>} land in the tail run from @{term ?s3}.\<close>
        have keq: "k = 3 + k2" using \<open>k = Suc k0\<close> \<open>k0 = Suc k1\<close> \<open>k1 = Suc k2\<close> by simp
        have ktail: "k2 < length (?s3 # apply_instant_actions ns' ?s3)"
          using Cons.prems unfolding run_unfold keq by simp
        have idx: "(s # apply_instant_actions (n # ns') s) ! k
                     = (?s3 # apply_instant_actions ns' ?s3) ! k2"
          unfolding run_unfold keq by simp
        have ih: "length (fst ((?s3 # apply_instant_actions ns' ?s3) ! k2)) = length (fst ?s3)
                  \<and> fst ((?s3 # apply_instant_actions ns' ?s3) ! k2) ! 0 = fst ?s3 ! 0"
          using Cons.IH[OF ktail] .
        show ?thesis unfolding idx using ih p3 by simp
      qed
    qed
  qed
qed

text \<open>The INSTANT-phase @{text struct} export: for an @{const apply_instant_actions} sub-run whose head
  config has the @{const planning_loc} main location and the @{const net_automata} length, every block index
  @{term k} satisfies @{const instant_block_struct} at run-position @{term \<open>3 * k\<close>}. The block entry config's
  @{const off_loc} source comes from @{thm [source] prop_step_source_off} (its start sub-step targets
  @{const starting_loc}); the two later block source locations (@{const starting_loc} after the start edge,
  @{const ending_loc} after the instant-trans edge) come straight from the effect shapes
  @{thm [source] start_edge_effect_alt} / @{thm [source] instant_trans_edge_effect_alt}; the three post-store
  bounds from @{thm [source] graph_impl_steps_nth_bounded}; lengths from
  @{thm [source] apply_instant_actions_locs_preserved}.\<close>
lemma instant_phase_struct:
  assumes run: "graph_impl.steps (sp # apply_instant_actions ns sp)"
      and head0: "fst sp ! 0 = planning_loc"
      and headlen: "length (fst sp) = length net_automata"
      and ns_act: "\<And>n. n \<in> set ns \<Longrightarrow> n < length actions"
      and k: "k < length ns"
    shows "instant_block_struct ((sp # apply_instant_actions ns sp) ! (3 * k)) (ns ! k)"
proof -
  let ?xs = "sp # apply_instant_actions ns sp"
  let ?m = "ns ! k"
  let ?c = "?xs ! (3 * k)"
  let ?s1 = "start_edge_effect ?m ?c"
  let ?s2 = "instant_trans_edge_effect ?m ?s1"
  let ?s3 = "end_edge_effect ?m ?s2"
  have lenxs: "length ?xs = Suc (3 * length ns)"
    by (simp add: length_apply_instant_actions)
  have m_act: "?m < length actions" using ns_act[of ?m] k by simp
  have Sm_lt: "Suc ?m < length net_automata" using m_act  by (simp add: length_net_automata)
  \<comment> \<open>The block configs at the three positions following @{term \<open>3 * k\<close>}.\<close>
  have b1: "?xs ! (3 * k + 1) = ?s1" by (rule apply_instant_actions_block_nth(1)[OF k])
  have b2: "?xs ! (3 * k + 2) = ?s2" using apply_instant_actions_block_nth(2)[OF k] b1 by simp
  have b3: "?xs ! (3 * k + 3) = ?s3" using apply_instant_actions_block_nth(3)[OF k] b2 by simp
  \<comment> \<open>Position bounds within the run.\<close>
  have p1lt: "3 * k + 1 < length ?xs" using k lenxs by simp
  have p2lt: "3 * k + 2 < length ?xs" using k lenxs by simp
  have p3lt: "3 * k + 3 < length ?xs" using k lenxs by simp
  have c_lt: "3 * k < length ?xs" using p1lt by simp
  \<comment> \<open>Lengths/loc0 along the run.\<close>
  have lc_pair: "length (fst ?c) = length (fst sp) \<and> fst ?c ! 0 = fst sp ! 0"
    using apply_instant_actions_locs_preserved[OF c_lt] .
  have c_len: "length (fst ?c) = length net_automata" using lc_pair headlen by simp
  have c_loc0: "fst ?c ! 0 = planning_loc" using lc_pair head0 by simp
  have s1_len: "length (fst ?s1) = length net_automata"
    using start_edge_effect_preserves_loc0[of ?m ?c] c_len by simp
  have s2_len: "length (fst ?s2) = length net_automata"
    using instant_trans_edge_effect_preserves_loc0[of ?m ?s1] s1_len by simp
  \<comment> \<open>Conjunct 1: the @{const off_loc} block-entry source location.\<close>
  obtain L vp c where ck: "?c = (L, vp, c)" by (cases ?c)
  have s1_alt: "fst (?xs ! (3 * k + 1)) = L[Suc ?m := starting_loc]"
    unfolding b1 ck by (simp add: start_edge_effect_alt)
  have stepc: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?xs ! (3 * k + 1)), fst (snd (?xs ! (3 * k + 1))), snd (snd (?xs ! (3 * k + 1)))\<rangle>"
    using graph_impl_steps_nth_step[OF run, of "3 * k"] p1lt unfolding ck by simp
  have Llen: "length L = length net_automata" using c_len ck by simp
  have main0: "L ! 0 = planning_loc" using c_loc0 ck by simp
  have off: "L ! Suc ?m = off_loc"
    by (rule prop_step_source_off[OF stepc Llen s1_alt main0 m_act])
  have conj1: "fst ?c ! Suc ?m = off_loc" using off ck by simp
  \<comment> \<open>Conjuncts 4, 7: the @{const starting_loc} / @{const ending_loc} source locations from the effect shapes.\<close>
  have Sm_ltL: "Suc ?m < length L" using Sm_lt Llen by simp
  have conj4: "fst ?s1 ! Suc ?m = starting_loc"
    unfolding ck by (simp add: start_edge_effect_alt nth_list_update_eq Sm_ltL)
  have conj7: "fst ?s2 ! Suc ?m = ending_loc"
  proof -
    obtain L1 v1 c1 where s1k: "?s1 = (L1, v1, c1)" by (cases ?s1)
    have l1len: "Suc ?m < length L1" using s1_len Sm_lt s1k by simp
    show ?thesis unfolding s1k by (simp add: instant_trans_edge_effect_alt l1len)
  qed
  \<comment> \<open>Conjuncts 3, 6, 9: the post-store bounds.\<close>
  have conj3: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s1))"
    using graph_impl_steps_nth_bounded[OF run, of "3 * k"] p1lt c_len b1 by simp
  have conj6: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s2))"
    using graph_impl_steps_nth_bounded[OF run, of "3 * k + 1"] p2lt s1_len b1 b2 by simp
  have conj9: "Simple_Network_Language.bounded (map_of net_bounds) (fst (snd ?s3))"
    using graph_impl_steps_nth_bounded[OF run, of "3 * k + 2"] p3lt s2_len b2 b3 by simp
  show ?thesis
    unfolding instant_block_struct_def Let_def
    using conj1 c_len conj3 conj4 s1_len conj6 conj7 s2_len conj9 by blast
qed

lemma num_happening_steps_possible:
  assumes i: "i < length planning_sem.htpl"
      and vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and lvp: "num_LvP cfg"
      and pres: "num_happening_pre_pre_delay M i cfg"
  shows "\<exists>ns. num_graph_impl.steps (cfg # ns)
              \<and> num_happening_post M i (last (cfg # ns)) \<and> num_LvP (last (cfg # ns))"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have ppd: "happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)"
    using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_propD)
  have tr: "num_tracks v (snd (M i))" using pres[unfolded cfg] by (rule num_happening_pre_pre_delay_trackD)
  \<comment> \<open>The boundedness now rides in the separately-carried @{const num_LvP}, from which we re-derive the
     full-store bound (still needed by the run-lift core) and -- via the bridge -- the propositional
     @{const LvP} on the projection store that @{thm [source] happening_steps_possible} now requires.\<close>
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    using lvp[unfolded cfg] by (simp add: num_Lv_conds_dests(3))
  have lvpr: "LvP (L, v |` dom (map_of net_bounds), c)"
    using lvp[unfolded cfg] by (rule num_LvP_imp_LvP)
  \<comment> \<open>The propositional happening run over the net_bounds PROJECTION store v |` dom (map_of net_bounds),
     which num_happening_pre_pre_delay_propD certifies as a valid propositional pre-state; the projected
     @{const LvP} premise is supplied by @{thm [source] num_LvP_imp_LvP}.\<close>
  have prun: "graph_impl.steps ((L, v |` dom (map_of net_bounds), c) # delay_and_apply i (L, v |` dom (map_of net_bounds), c))"
    and ppost: "happening_post i (last (delay_and_apply i (L, v |` dom (map_of net_bounds), c)))"
    using happening_steps_possible[OF i ppd lvpr] by blast+
  \<comment> \<open>TODO (the run-lift core): lift prun to a numeric run over the FULL store v, threading num_tracks
     (the running happening_num_update_set partial fold) and the num_net_bounds bound via num_int_step_lift
     + num_data_no_write_edge / num_data_upd_edge per internal step (L ! p pins the fired edge) and
     num_steps_delay_replace for the leading delay; num_happening_post then follows from ppost since the
     numeric run's last store projects (prop_proj_bounded) to the prop run's last store. The carried
     num_LvP on the last config follows from num_Lv_conds_maintained across the numeric edges (locations
     and planning_lock are preserved; the num_net_bounds bound is re-established per step by the lift).\<close>
  \<comment> \<open>The base configs and the index lists driving the five phases.\<close>
  let ?proj = "(L, v |` dom (map_of net_bounds), c)"
  let ?d = "get_delay i"
  let ?t = "planning_sem.time_index i"
  let ?SS = "filter (is_starting_index ?t) [0..<length actions]"
  let ?SE = "filter (is_ending_index ?t) [0..<length actions]"
  let ?SB = "filter (is_instant_index ?t) [0..<length actions]"
  let ?w = "\<lambda>ys. num_plan.num_rat_impl.happening_num_update ys (snd (M i))"
  \<comment> \<open>The propositional happening run in @{const ext_seq} combinator form (the @{text ?seq} of
     @{thm [source] happening_steps_possible}); @{text prun} relates @{const delay_and_apply} to it.\<close>
  let ?seq = "((ext_seq \<circ> seq_apply) (map edge_2_effect ?SS)
             ((ext_seq \<circ> seq_apply) (map end_edge_effect ?SE)
               ((ext_seq \<circ> seq_apply) (map start_edge_effect ?SS)
                 (fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) ?SB)
                  ((ext_seq \<circ> seq_apply) (map edge_3_effect ?SE) [delay ?d ?proj])))))"

  have delay_non_negative: "0 \<le> ?d"
    unfolding get_delay_def
    apply (cases "i = 0")
     apply (subst if_P, simp)
    using eps_ran apply simp
    apply (subst if_not_P, simp)
    using planning_sem.time_index_sorted_list[of "i - 1" "i"] i
    unfolding planning_sem.time_index_def by auto

  \<comment> \<open>The full prop run in @{text ?seq} form, obtained from @{text prun} by the same algebra the
     propositional assembly uses (lines 110-123 of @{thm [source] happening_steps_possible}).\<close>
  \<comment> \<open>The list-shape facts: @{term \<open>delay_and_apply i ?proj\<close>} is the @{const tl} of the @{text ?seq}
     chain, whose head is @{term \<open>delay ?d ?proj\<close>}.\<close>
  have seq_ne: "?seq \<noteq> []" by simp
  have da_eq_tl: "delay_and_apply i ?proj = tl ?seq"
    unfolding delay_and_apply_def Let_def
    apply (subst apply_nth_happening_def)
    unfolding Let_def apply_edge_3_effects_def apply_start_edge_effects_def apply_end_edge_effects_def apply_edge_2_effects_def apply_snap_action_def apply_instant_actions_alt
    by simp
  have fold_hd_pres: "hd (fold (ext_seq \<circ> seq_apply) gss X) = hd X" if "X \<noteq> []" for gss X
    using that
  proof (induction gss arbitrary: X)
    case Nil
    show ?case by simp
  next
    case (Cons g gss')
    have ne: "(ext_seq \<circ> seq_apply) g X \<noteq> []" using Cons.prems by simp
    have "hd (fold (ext_seq \<circ> seq_apply) (g # gss') X) = hd (fold (ext_seq \<circ> seq_apply) gss' ((ext_seq \<circ> seq_apply) g X))"
      by simp
    also have "\<dots> = hd ((ext_seq \<circ> seq_apply) g X)" by (rule Cons.IH[OF ne])
    also have "\<dots> = hd X" using Cons.prems by (simp add: hd_ext_seq)
    finally show ?case .
  qed
  have hd_seq: "hd ?seq = delay ?d ?proj"
    apply (subst comp_apply)+
    apply (subst hd_ext_seq, simp)+
    apply (subst fold_hd_pres, simp)
    by (subst hd_ext_seq) simp_all
  have seq_cons: "?seq = delay ?d ?proj # delay_and_apply i ?proj"
    using list.collapse[OF seq_ne] unfolding hd_seq da_eq_tl by simp
  \<comment> \<open>@{text prun_seq}: the delay-headed run, rebuilt by the five propositional phase constructors from the
     delay-headed seed -- the same chain @{thm [source] happening_steps_possible} uses internally. The
     @{const happening_pre_end_starts} pre-state on @{term \<open>delay ?d ?proj\<close>} is derived from @{text ppd}
     exactly as in that lemma's @{text pres'} block.\<close>
  have seed_lvp: "LvP (delay ?d ?proj)"
    using lvpr by (simp add: delay_def)
  have pres': "happening_pre_end_starts i (delay ?d ?proj)"
  proof -
    obtain Ld vd cd where
      s': "delay ?d ?proj = (Ld, vd, cd)" by (rule prod_cases3)
    have "happening_pre_post_delay i (delay ?d ?proj)"
      apply (insert ppd)
      apply (induction ?proj)
      unfolding delay_def map_prod_simp id_def
      unfolding happening_pre_pre_delay_def happening_pre_post_delay_def
      by simp
    thus ?thesis
      apply -
      unfolding s'
      apply (rule happening_pre_end_startsI, simp)
         apply (rule end_start_invsI, simp)
                apply (rule happening_invsI, simp)
      using happening_pre_post_delay_dests apply auto[5]
      subgoal by (auto
            simp: planning_sem.open_active_count_eq_closed_active_count_if_only_instant_acts
              index_case_defs planning_sem.action_happening_case_defs
            dest!: happening_pre_post_delay_dests(4))
      subgoal by (auto
            simp: planning_sem.open_active_count_eq_closed_active_count_if_only_instant_acts
              index_case_defs planning_sem.action_happening_case_defs
            dest!: happening_pre_post_delay_dests(5))
      using happening_pre_post_delay_dests apply auto[5]
      subgoal by (auto
            simp: planning_sem.open_active_count_0_if_start_scheduled
              index_case_defs planning_sem.action_happening_case_defs
            dest!: happening_pre_post_delay_dests(4))
      subgoal by (auto
            simp: planning_sem.open_active_count_0_if_start_scheduled
              index_case_defs planning_sem.action_happening_case_defs
            dest!: happening_pre_post_delay_dests(4))
      subgoal using happening_pre_post_delay_dests by auto
      subgoal by (auto
            simp: planning_sem.open_active_count_1_if_ending
              index_case_defs planning_sem.action_happening_case_defs
            dest!: happening_pre_post_delay_dests(5))
      subgoal by (auto dest!: happening_pre_post_delay_dests(7))
      done
  qed
  have prun_seq: "graph_impl.steps ?seq \<and> happening_post i (last ?seq) \<and> LvP (last ?seq)"
      apply (rule start_ends_possible)
        apply (rule end_ends_possible)
          apply (rule start_starts_possible)
            apply (rule instant_actions_possible)
              apply (rule end_starts_possible)
    by (auto intro!: i graph_impl.steps.intros pres' seed_lvp)
  note prun_seq_full = prun_seq
  note ppost_seq = prun_seq_full[THEN conjunct2, THEN conjunct1]
  note prun_seq = prun_seq_full[THEN conjunct1]

  \<comment> \<open>SEED: the projection store is map-le below the full store, so the head configs are RELC-related
     at the pre-happening fold @{term \<open>snd (M i)\<close>}.\<close>
  have rel_stores: "REL (v |` dom (map_of net_bounds)) v (snd (M i))"
  proof (rule RELI)
    show "v |` dom (map_of net_bounds) \<subseteq>\<^sub>m v" by (auto simp: map_le_def)
    show "num_tracks v (snd (M i))" by (rule tr)
    show "Simple_Network_Language.bounded (map_of num_net_bounds) v" by (rule bnd)
  qed
  have seed: "RELC (delay ?d ?proj) (delay ?d (L, v, c)) (snd (M i))"
    unfolding delay_def map_prod_simp id_def prod.case
    by (rule RELCI[OF rel_stores])

  \<comment> \<open>Extracting a phase's cons-form prop sub-run @{term \<open>last xs # f (last xs)\<close>} from the combinator
     form @{term \<open>ext_seq f xs\<close>} of the full run.\<close>
  have steps_ext_seq_tail: "graph_impl.steps (last xs # f (last xs))"
    if steps: "graph_impl.steps (ext_seq f xs)" and xs: "xs \<noteq> []" for f xs
  proof -
    have split: "ext_seq f xs = butlast xs @ (last xs # f (last xs))"
      unfolding ext_seq_def using xs by (simp add: append_butlast_last_id)
    have ne: "last xs # f (last xs) \<noteq> []" by simp
    show ?thesis using steps unfolding split by (rule graph_impl.steps_appendD2[OF _ ne])
  qed

  \<comment> \<open>A combinator step is its prefix appended with the sub-run of the last config: this is the
     append-shape @{thm [source] graph_impl.steps_appendD1} consumes to peel an inner segment.\<close>
  have ext_seq_comp_append: "(ext_seq \<circ> seq_apply) gs ys = ys @ seq_apply gs (last ys)" for gs ys
    by (simp add: ext_seq_def)
  \<comment> \<open>A @{const fold} of @{text \<open>ext_seq \<circ> seq_apply\<close>} extends its base by an appended tail (so the base
     is a prefix), provided the base is non-empty.\<close>
  have fold_ext_seq_append: "\<exists>zs. fold (ext_seq \<circ> seq_apply) gss ys = ys @ zs" if "ys \<noteq> []" for gss ys
    using that
  proof (induction gss arbitrary: ys)
    case Nil
    show ?case by simp
  next
    case (Cons g gss')
    have ne: "(ext_seq \<circ> seq_apply) g ys \<noteq> []" using Cons.prems by simp
    obtain zs where zs: "fold (ext_seq \<circ> seq_apply) gss' ((ext_seq \<circ> seq_apply) g ys) = (ext_seq \<circ> seq_apply) g ys @ zs"
      using Cons.IH[OF ne] by blast
    have "fold (ext_seq \<circ> seq_apply) (g # gss') ys = fold (ext_seq \<circ> seq_apply) gss' ((ext_seq \<circ> seq_apply) g ys)"
      by simp
    also have "\<dots> = (ys @ seq_apply g (last ys)) @ zs" using zs by (simp only: ext_seq_comp_append)
    finally show ?case by (metis append.assoc)
  qed

  \<comment> \<open>The five segments of @{text ?seq}, innermost (edge_3) to outermost (edge_2).\<close>
  define SEG1 where "SEG1 = (ext_seq \<circ> seq_apply) (map edge_3_effect ?SE) [delay ?d ?proj]"
  define SEG2 where "SEG2 = fold (ext_seq \<circ> seq_apply) (map (\<lambda>n. [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n]) ?SB) SEG1"
  define SEG3 where "SEG3 = (ext_seq \<circ> seq_apply) (map start_edge_effect ?SS) SEG2"
  define SEG4 where "SEG4 = (ext_seq \<circ> seq_apply) (map end_edge_effect ?SE) SEG3"
  have SEG1_ne: "SEG1 \<noteq> []" unfolding SEG1_def by (simp add: ext_seq_comp_append)
  \<comment> \<open>The per-segment append equations: each outer segment is its inner prefix appended with the phase's
     sub-run from the inner segment's last config.\<close>
  obtain zs2 where eq2: "SEG2 = SEG1 @ zs2"
    using fold_ext_seq_append[OF SEG1_ne] unfolding SEG2_def by blast
  have SEG2_ne: "SEG2 \<noteq> []" using eq2 SEG1_ne by simp
  have eq3: "SEG3 = SEG2 @ seq_apply (map start_edge_effect ?SS) (last SEG2)"
    unfolding SEG3_def by (rule ext_seq_comp_append)
  have SEG3_ne: "SEG3 \<noteq> []" using eq3 SEG2_ne by simp
  have eq4: "SEG4 = SEG3 @ seq_apply (map end_edge_effect ?SE) (last SEG3)"
    unfolding SEG4_def by (rule ext_seq_comp_append)
  have SEG4_ne: "SEG4 \<noteq> []" using eq4 SEG3_ne by simp
  have seqeq: "?seq = SEG4 @ seq_apply (map edge_2_effect ?SS) (last SEG4)"
    unfolding SEG4_def SEG3_def SEG2_def SEG1_def by (rule ext_seq_comp_append)

  \<comment> \<open>Peel the prop runs of the segments from @{text prun_seq} (inner is a prefix of outer).\<close>
  have steps_SEG4: "graph_impl.steps SEG4"
    using prun_seq unfolding seqeq by (rule graph_impl.steps_appendD1[OF _ SEG4_ne])
  have steps_SEG3: "graph_impl.steps SEG3"
    using steps_SEG4 unfolding eq4 by (rule graph_impl.steps_appendD1[OF _ SEG3_ne])
  have steps_SEG2: "graph_impl.steps SEG2"
    using steps_SEG3 unfolding eq3 by (rule graph_impl.steps_appendD1[OF _ SEG2_ne])
  have steps_SEG1: "graph_impl.steps SEG1"
    using steps_SEG2 unfolding eq2 by (rule graph_impl.steps_appendD1[OF _ SEG1_ne])

  \<comment> \<open>The phase head configs (each is the last config of the previous segment).\<close>
  define h1 where "h1 = delay ?d ?proj"   \<comment> \<open>edge_3 phase head\<close>
  define h2 where "h2 = last SEG1"         \<comment> \<open>instant phase head\<close>
  define h3 where "h3 = last SEG2"         \<comment> \<open>start phase head\<close>
  define h4 where "h4 = last SEG3"         \<comment> \<open>end phase head\<close>
  define h5 where "h5 = last SEG4"         \<comment> \<open>edge_2 phase head\<close>
  have h1_hd: "h1 = hd SEG1" unfolding h1_def SEG1_def by (simp add: hd_ext_seq)

  \<comment> \<open>The three snap prefixes; their concatenation is @{const run_order_snaps}.\<close>
  define snaps_inst where "snaps_inst = concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ?SB)"
  define snaps_start where "snaps_start = map (\<lambda>n. at_start (actions ! n)) ?SS"
  define snaps_end where "snaps_end = map (\<lambda>n. at_end (actions ! n)) ?SE"
  have ros_eq: "run_order_snaps i = snaps_inst @ snaps_start @ snaps_end"
    unfolding run_order_snaps_def Let_def snaps_inst_def snaps_start_def snaps_end_def by simp
  have ros_dist: "distinct (snaps_inst @ snaps_start @ snaps_end)"
    using distinct_run_order_snaps[of i] unfolding ros_eq .
  have ros_set: "set (snaps_inst @ snaps_start @ snaps_end) = planning_sem.happ_at planning_sem.plan_happ_seq ?t"
    using set_run_order_snaps[of i] unfolding ros_eq .

  \<comment> \<open>Index-list membership facts.\<close>
  have SS_mem: "n < length actions \<and> is_starting_index ?t n" if "n \<in> set ?SS" for n using that by auto
  have SE_mem: "n < length actions \<and> is_ending_index ?t n" if "n \<in> set ?SE" for n using that by auto
  have SB_mem: "n < length actions \<and> is_instant_index ?t n" if "n \<in> set ?SB" for n using that by auto

  \<comment> \<open>Every accumulated snap is a start/end of some action (used as @{text ys_act} per phase).\<close>
  have snaps_inst_act: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if "s \<in> set snaps_inst" for s
  proof -
    have "s \<in> (\<Union>n \<in> set ?SB. {at_start (actions ! n), at_end (actions ! n)})"
      using that unfolding snaps_inst_def set_concat set_map by simp
    then obtain n where n: "n \<in> set ?SB" and seq: "s = at_start (actions ! n) \<or> s = at_end (actions ! n)" by blast
    have "actions ! n \<in> set actions" using SB_mem[OF n] by simp
    thus ?thesis using seq by blast
  qed 
  have snaps_start_act: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if "s \<in> set snaps_start" for s
  proof -
    have "s \<in> (\<lambda>n. at_start (actions ! n)) ` set ?SS"
      using that unfolding snaps_start_def set_map .
    then obtain n where n: "n \<in> set ?SS" and seq: "s = at_start (actions ! n)" by blast
    have "actions ! n \<in> set actions" using SS_mem[OF n] by simp
    thus ?thesis using seq by blast
  qed 
  have snaps_inst_start_act: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if "s \<in> set (snaps_inst @ snaps_start)" for s
    using that snaps_inst_act snaps_start_act by auto

  \<comment> \<open>The accumulated prefixes are subsets of the happening.\<close>
  have snaps_inst_sub: "set snaps_inst \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq ?t"
    using ros_set by auto
  have snaps_inst_start_sub: "set (snaps_inst @ snaps_start) \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq ?t"
    using ros_set by auto

  \<comment> \<open>The cons-form prop sub-runs of each phase (head config @{term \<open>h_k\<close>} followed by the phase's run).\<close>
  have prun1: "graph_impl.steps (h1 # seq_apply (map edge_3_effect ?SE) h1)"
  proof -
    have "SEG1 = ext_seq (seq_apply (map edge_3_effect ?SE)) [delay ?d ?proj]"
      unfolding SEG1_def by simp
    thus ?thesis using steps_ext_seq_tail[OF _ ] steps_SEG1 unfolding h1_def by (metis last_ConsL list.distinct(1))
  qed
  have SEG2_inst: "SEG2 = ext_seq (apply_instant_actions ?SB) SEG1"
    unfolding SEG2_def by (simp add: apply_instant_actions_alt)
  have prun2: "graph_impl.steps (h2 # apply_instant_actions ?SB h2)"
    using steps_ext_seq_tail[OF steps_SEG2[unfolded SEG2_inst] SEG1_ne] unfolding h2_def .
  have SEG3_start: "SEG3 = ext_seq (seq_apply (map start_edge_effect ?SS)) SEG2"
    unfolding SEG3_def by simp
  have prun3: "graph_impl.steps (h3 # seq_apply (map start_edge_effect ?SS) h3)"
    using steps_ext_seq_tail[OF steps_SEG3[unfolded SEG3_start] SEG2_ne] unfolding h3_def .
  have SEG4_end: "SEG4 = ext_seq (seq_apply (map end_edge_effect ?SE)) SEG3"
    unfolding SEG4_def by simp
  have prun4: "graph_impl.steps (h4 # seq_apply (map end_edge_effect ?SE) h4)"
    using steps_ext_seq_tail[OF steps_SEG4[unfolded SEG4_end] SEG3_ne] unfolding h4_def .
  have seq_edge2: "?seq = ext_seq (seq_apply (map edge_2_effect ?SS)) SEG4"
    unfolding SEG4_def SEG3_def SEG2_def SEG1_def by simp
  have prun5: "graph_impl.steps (h5 # seq_apply (map edge_2_effect ?SS) h5)"
    using steps_ext_seq_tail[OF prun_seq[unfolded seq_edge2] SEG4_ne] unfolding h5_def .

  \<comment> \<open>Every phase head config has the @{const planning_loc} main location and the @{const net_automata}
     length (the head @{term \<open>delay ?d ?proj\<close>} does, and every edge effect preserves both).\<close>
  have h1_props: "fst h1 ! 0 = planning_loc \<and> length (fst h1) = length net_automata"
  proof -
    have "Lv_conds L (v |` dom (map_of net_bounds))" using lvpr by simp
    thus ?thesis unfolding h1_def delay_def map_prod_simp id_def prod.case fst_conv
      by (simp add: Lv_conds_def length_net_automata)
  qed
  \<comment> \<open>Loc0/length propagate along any @{const seq_apply} sub-run of the edge effects.\<close>
  have seq_head_props: "fst (last (sp # seq_apply (map E ns) sp)) ! 0 = fst sp ! 0
                        \<and> length (fst (last (sp # seq_apply (map E ns) sp))) = length (fst sp)"
    if E_pres: "\<And>n s. length (fst (E n s)) = length (fst s) \<and> fst (E n s) ! 0 = fst s ! 0" for E ns sp
  proof -
    have pres: "length (fst ((map E ns ! j) s)) = length (fst s) \<and> fst ((map E ns ! j) s) ! 0 = fst s ! 0"
      if j: "j < length (map E ns)" for j s
      using E_pres[of "ns ! j" s] j by simp
    have lenxs: "length (sp # seq_apply (map E ns) sp) = Suc (length ns)" by simp
    have k: "length ns < length (sp # seq_apply (map E ns) sp)" by simp
    have idx: "last (sp # seq_apply (map E ns) sp) = (sp # seq_apply (map E ns) sp) ! (length ns)"
      by (subst last_conv_nth) (simp_all add: lenxs)
    show ?thesis using seq_apply_locs_preserved[OF pres k] unfolding idx by simp
  qed
  have inst_head_props: "fst (last (sp # apply_instant_actions ns sp)) ! 0 = fst sp ! 0
                        \<and> length (fst (last (sp # apply_instant_actions ns sp))) = length (fst sp)" for ns sp
  proof -
    have lenxs: "length (sp # apply_instant_actions ns sp) = Suc (3 * length ns)"
      by (simp add: length_apply_instant_actions)
    have k: "3 * length ns < length (sp # apply_instant_actions ns sp)" using lenxs by simp
    have idx: "last (sp # apply_instant_actions ns sp) = (sp # apply_instant_actions ns sp) ! (3 * length ns)"
      by (subst last_conv_nth) (simp_all add: lenxs length_apply_instant_actions)
    show ?thesis using apply_instant_actions_locs_preserved[OF k] unfolding idx by simp
  qed
  \<comment> \<open>Last of an appended list equals the last of @{term \<open>last xs # ys\<close>} (matching the @{const ext_seq}
     last with the phase-lift's cons-form last).\<close>
  have last_app_cons: "last (xs @ ys) = last (last xs # ys)" if "xs \<noteq> []" for xs ys :: "'z list"
    using that by (cases "ys = []") (simp_all add: last_appendR)
  \<comment> \<open>@{term \<open>h2 = last SEG1\<close>}, etc.: chain the per-phase head-property preservation.\<close>
  have h2_props: "fst h2 ! 0 = planning_loc \<and> length (fst h2) = length net_automata"
  proof -
    have e: "h2 = last (h1 # seq_apply (map edge_3_effect ?SE) h1)"
      unfolding h2_def SEG1_def comp_apply ext_seq_def h1_def by simp
    show ?thesis
      unfolding e using seq_head_props[of edge_3_effect h1 ?SE, OF edge_3_effect_preserves_loc0] h1_props
      by argo
  qed
  have h3_props: "fst h3 ! 0 = planning_loc \<and> length (fst h3) = length net_automata"
  proof -
    have "h3 = last (h2 # apply_instant_actions ?SB h2)"
      unfolding h3_def SEG2_inst ext_seq_def using SEG1_ne
      by (subst last_app_cons) (simp_all add: h2_def[symmetric])
    thus ?thesis using inst_head_props[of h2 ?SB] h2_props by simp
  qed
  have h4_props: "fst h4 ! 0 = planning_loc \<and> length (fst h4) = length net_automata"
  proof -
    have e: "h4 = last (h3 # seq_apply (map start_edge_effect ?SS) h3)"
      unfolding h4_def SEG3_start ext_seq_def using SEG2_ne
      by (subst last_app_cons) (simp_all add: h3_def[symmetric])
    show ?thesis
      unfolding e using seq_head_props[of start_edge_effect h3 ?SS, OF start_edge_effect_preserves_loc0] h3_props
      by argo
  qed
  have h5_props: "fst h5 ! 0 = planning_loc \<and> length (fst h5) = length net_automata"
  proof -
    have e: "h5 = last (h4 # seq_apply (map end_edge_effect ?SE) h4)"
      unfolding h5_def SEG4_end ext_seq_def using SEG3_ne
      by (subst last_app_cons) (simp_all add: h4_def[symmetric])
    show ?thesis
      unfolding e using seq_head_props[of end_edge_effect h4 ?SE, OF end_edge_effect_preserves_loc0] h4_props
      by argo
  qed

  \<comment> \<open>Each phase head is the last config of the previous segment's cons-form run.\<close>
  have h2_last: "last (h1 # seq_apply (map edge_3_effect ?SE) h1) = h2"
    unfolding h2_def SEG1_def comp_apply ext_seq_def h1_def by simp
  have h3_last: "last (h2 # apply_instant_actions ?SB h2) = h3"
    unfolding h3_def SEG2_inst ext_seq_def using SEG1_ne
    by (subst last_app_cons) (simp_all add: h2_def[symmetric])
  have h4_last: "last (h3 # seq_apply (map start_edge_effect ?SS) h3) = h4"
    unfolding h4_def SEG3_start ext_seq_def using SEG2_ne
    by (subst last_app_cons) (simp_all add: h3_def[symmetric])
  have h5_last: "last (h4 # seq_apply (map end_edge_effect ?SE) h4) = h5"
    unfolding h5_def SEG4_end ext_seq_def using SEG3_ne
    by (subst last_app_cons) (simp_all add: h4_def[symmetric])
  have seq_last: "last (h5 # seq_apply (map edge_2_effect ?SS) h5) = last ?seq"
    unfolding seq_edge2 ext_seq_def using SEG4_ne
    by (subst last_app_cons) (simp_all add: h5_def[symmetric])

  \<comment> \<open>The five numeric phase results, threading RELC and the growing @{text happening_num_update} fold.
     Each carries its sub-run length (for the non-emptiness of the spliced run).\<close>
  \<comment> \<open>The two NO-WRITE phases (edge_3, edge_2) are lifted via the RLP combinator @{thm [source]
     num_edge_3_phase_lift} / @{thm [source] num_edge_2_phase_lift}; threading their caller-supplied
     propositional pre/post invariants (the @{const end_start_pre} / @{const start_end_pre}
     bookkeeping that @{thm [source] end_starts_possible} / @{thm [source] start_ends_possible}
     establish) is the one remaining obligation. The edge_3 result is a concrete run from the seed;
     the edge_2 result is stated parametrically over the entry numeric config (the RLP shape), so both
     no-write phases share a SINGLE obligation.\<close>
  \<comment> \<open>The two no-write phase RLP facts: the @{const edge_3} entry run and the @{const edge_2} exit run.
     Both fold-valuations are CONSTANT (no fluent writes), so the lift is the structural combinator
     with the threaded config PINNED to its run position.\<close>
  have rlp3: "RLP (snd (M i)) (h1 # seq_apply (map edge_3_effect ?SE) h1)"
  proof -
    let ?run3 = "h1 # seq_apply (map edge_3_effect ?SE) h1"
    have fin3: "fluent_in_bounds (snd (M i))"
      using i by (intro num_seq_fluent_in_bounds[OF vss m0]) simp
    \<comment> \<open>The @{const edge_3} effect only re-targets the FIRED automaton location, so the location at any
       not-yet-fired position is preserved along the @{const seq_apply} run (induct on the run position).\<close>
    have loc_pres: "fst (?run3 ! k) ! Suc q = fst h1 ! Suc q"
      if "k \<le> length ?SE" and "\<And>j. j < k \<Longrightarrow> ?SE ! j \<noteq> q" for k q
      using that
    proof (induction k)
      case 0
      show ?case by simp
    next
      case (Suc k)
      have k_lt: "k < length ?SE" using Suc.prems(1) by simp
      have IH: "fst (?run3 ! k) ! Suc q = fst h1 ! Suc q"
        using Suc.IH Suc.prems(1) Suc.prems(2) by simp
      have step: "?run3 ! Suc k = edge_3_effect (?SE ! k) (?run3 ! k)"
        using seq_apply_Cons_nth_Suc[of k "map edge_3_effect ?SE" h1] k_lt by simp
      obtain L vp c where ck: "?run3 ! k = (L, vp, c)" by (cases "?run3 ! k")
      have ne: "?SE ! k \<noteq> q" using Suc.prems(2)[of k] by simp
      have "fst (?run3 ! Suc k) ! Suc q = (L[Suc (?SE ! k) := ending_loc]) ! Suc q"
        unfolding step ck by (simp add: edge_3_effect_alt)
      also have "\<dots> = L ! Suc q" using ne by (simp add: nth_list_update_neq)
      also have "\<dots> = fst (?run3 ! k) ! Suc q" unfolding ck by simp
      also have "\<dots> = fst h1 ! Suc q" by (rule IH)
      finally show ?case .
    qed
    \<comment> \<open>The ending-index source location @{const running_loc} at @{term h1} (from the entry invariant
       @{text pres'}), propagated to each run-position @{term k} since @{term \<open>?SE\<close>} is distinct.\<close>
    have h1_end_loc: "fst h1 ! Suc n = running_loc" if n: "n < length actions" "is_ending_index ?t n" for n
    proof -
      obtain Lh vh ch where lh: "h1 = (Lh, vh, ch)" by (rule prod_cases3)
      have "\<forall>i'<length actions. is_ending_index ?t i' \<longrightarrow> Lh ! Suc i' = running_loc"
        by (rule happening_pre_end_starts_dests(3)[OF pres'[folded h1_def] lh])
      thus ?thesis using n unfolding lh by simp
    qed
    \<comment> \<open>Per-position structural facts for the @{const edge_3} entry run: source @{const running_loc}
       (propagated from @{term h1}), the @{const net_automata} length, and the post-store bound.\<close>
    have struct3: "fst (?run3 ! k) ! Suc (?SE ! k) = running_loc
                   \<and> length (fst (?run3 ! k)) = length net_automata
                   \<and> Simple_Network_Language.bounded (map_of net_bounds)
                         (fst (snd (edge_3_effect (?SE ! k) (?run3 ! k))))"
      if k: "k < length ?SE" for k
    proof -
      have Sk: "Suc k < length ?run3" using k by simp
      have k_lt: "k < length ?run3" using k by simp
      have pres: "length (fst ((map edge_3_effect ?SE ! j) s)) = length (fst s)
                    \<and> fst ((map edge_3_effect ?SE ! j) s) ! 0 = fst s ! 0"
        if j: "j < length (map edge_3_effect ?SE)" for j s
        using edge_3_effect_preserves_loc0[of "?SE ! j" s] j by simp
      have loc0len: "length (fst (?run3 ! k)) = length (fst h1) \<and> fst (?run3 ! k) ! 0 = fst h1 ! 0"
        using seq_apply_locs_preserved[OF pres, of k] k_lt by simp
      have cklen: "length (fst (?run3 ! k)) = length net_automata" using loc0len conjunct2[OF h1_props] by simp
      have nxt: "?run3 ! Suc k = edge_3_effect (?SE ! k) (?run3 ! k)"
        using seq_apply_Cons_nth_Suc[of k "map edge_3_effect ?SE" h1] k by simp
      \<comment> \<open>The fired index is an ending index distinct from all previously-fired ones.\<close>
      have kmem: "?SE ! k \<in> set ?SE" by (rule nth_mem[OF k])
      have nk_act: "?SE ! k < length actions" and nk_end: "is_ending_index ?t (?SE ! k)"
        using SE_mem[OF kmem] by blast+
      have distSE: "distinct ?SE" by simp
      have notin: "?SE ! j \<noteq> ?SE ! k" if jk: "j < k" for j
      proof -
        have jlt: "j < length ?SE" using jk k by simp
        show ?thesis using nth_eq_iff_index_eq[OF distSE jlt k] jk by simp
      qed
      \<comment> \<open>Conjunct 1: source @{const running_loc}.\<close>
      have c1: "fst (?run3 ! k) ! Suc (?SE ! k) = running_loc"
        using loc_pres[of k "?SE ! k", OF less_imp_le[OF k] notin] h1_end_loc[OF nk_act nk_end] by simp
      \<comment> \<open>Conjunct 3: the @{const net_bounds} bound on the post-store.\<close>
      have c3: "Simple_Network_Language.bounded (map_of net_bounds)
                  (fst (snd (edge_3_effect (?SE ! k) (?run3 ! k))))"
        using graph_impl_steps_nth_bounded[OF prun1 Sk] cklen nxt by simp
      show ?thesis using c1 cklen c3 by blast
    qed
    \<comment> \<open>Apply the @{const edge_3} phase-lift combinator with P/Q pinned to run positions.\<close>
    have run3eq: "(ext_seq \<circ> seq_apply) (map edge_3_effect ?SE) [h1] = ?run3"
      by (subst ext_seq_comp_append) simp
    have combinator:
      "RLP (snd (M i)) ((ext_seq \<circ> seq_apply) (map edge_3_effect ?SE) [h1])
       \<and> (\<lambda>x. True) (last ((ext_seq \<circ> seq_apply) (map edge_3_effect ?SE) [h1]))"
    proof (rule num_edge_3_phase_lift[where
            xs = "[h1]" and ns = "?SE" and w = "snd (M i)"
            and R = "\<lambda>x. x = h1"
            and P = "\<lambda>j s. s = ?run3 ! j"
            and Q = "\<lambda>j s. s = ?run3 ! Suc j"
            and S = "\<lambda>x. True" and R' = "\<lambda>x. True"])
      show "RLP (snd (M i)) [h1] \<and> (\<lambda>x. x = h1) (last [h1])" by (simp add: RLP_base)
    next
      fix j s
      assume j: "j < length ?SE" and Pj: "s = ?run3 ! j"
      have nxt: "?run3 ! Suc j = edge_3_effect (?SE ! j) s"
        unfolding Pj using seq_apply_Cons_nth_Suc[of j "map edge_3_effect ?SE" h1] j by simp
      have src: "fst s ! Suc (?SE ! j) = running_loc"
        and len: "length (fst s) = length net_automata"
        and pbnd: "Simple_Network_Language.bounded (map_of net_bounds)
                      (fst (snd (edge_3_effect (?SE ! j) s)))"
        using struct3[OF j] unfolding Pj by simp_all
      have nk_act: "?SE ! j < length actions"
        using SE_mem[OF nth_mem[OF j]] by simp
      have rlp_single: "RLP (snd (M i)) [s, edge_3_effect (?SE ! j) s]"
        by (rule RLP_edge_3_single[OF src nk_act len pbnd fin3])
      show "(\<lambda>j s. s = ?run3 ! Suc j) j (edge_3_effect (?SE ! j) s)
            \<and> RLP (snd (M i)) [s, edge_3_effect (?SE ! j) s]"
        using nxt rlp_single by simp
    next
      fix j s assume "Suc j < length ?SE" "s = ?run3 ! Suc j"
      thus "(\<lambda>j s. s = ?run3 ! j) (Suc j) s" by simp
    next
      fix x assume "0 < length ?SE" "(\<lambda>x. x = h1) x"
      thus "(\<lambda>j s. s = ?run3 ! j) 0 x" by simp
    next
      fix x assume "0 < length ?SE" "(\<lambda>j s. s = ?run3 ! Suc j) (length ?SE - 1) x"
      thus "(\<lambda>x. True) x" by simp
    next
      fix x assume "length ?SE = 0" "(\<lambda>x. x = h1) x"
      thus "(\<lambda>x. True) x" by simp
    next
      fix x assume "(\<lambda>x. True) x"
      thus "(\<lambda>x. True) x" by simp
    qed
    show ?thesis using conjunct1[OF combinator] unfolding run3eq .
  qed
  have rlp5: "RLP (?w (snaps_inst @ snaps_start @ snaps_end)) (h5 # seq_apply (map edge_2_effect ?SS) h5)"
  proof -
    let ?w5 = "?w (snaps_inst @ snaps_start @ snaps_end)"
    let ?run5 = "h5 # seq_apply (map edge_2_effect ?SS) h5"
    \<comment> \<open>The constant fold valuation lands in bounds, is val-ok, and satisfies any action's over_all
       invariants (the deferred @{text sat_inv} the augmented @{const num_edge_2} guard demands).\<close>
    have fin5: "fluent_in_bounds ?w5"
      using running_prefix_in_bounds[OF vss m0 i, where ys = "snaps_inst @ snaps_start @ snaps_end" and zs = "[]"]
            ros_dist ros_set by simp
    have wok5: "num_val_ok ?w5" by (rule fluent_in_bounds_imp_num_val_ok[OF fin5])
    \<comment> \<open>Every accumulated snap is the at_start/at_end of some action (the @{text ys_act} the over_all
       satisfaction lemma needs).\<close>
    have snaps_end_act: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if "s \<in> set snaps_end" for s
    proof -
      have "s \<in> (\<lambda>n. at_end (actions ! n)) ` set ?SE"
        using that unfolding snaps_end_def set_map .
      then obtain n where n: "n \<in> set ?SE" and seq: "s = at_end (actions ! n)" by blast
      have "actions ! n \<in> set actions" using SE_mem[OF n] by simp
      thus ?thesis using seq by blast
    qed
    have ys5_act: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a"
      if "s \<in> set (snaps_inst @ snaps_start @ snaps_end)" for s
      using that snaps_inst_act snaps_start_act snaps_end_act by auto
    have sat5: "sat_comps ?w5 (set (n_inv (actions ! n)))" if n: "n < length actions" for n
    proof -
      have ile: "i \<le> length planning_sem.htpl" using i by simp
      have aMem: "actions ! n \<in> set actions" using n by simp
      show ?thesis by (rule inv_sat_at_fold[OF vss m0 ile aMem ys5_act])
    qed
    \<comment> \<open>Per-position structural facts for the @{const edge_2} exit run (mirror of @{thm [source]
       start_phase_struct}): source @{const starting_loc} (via TARGET-pinning, only @{const edge_2}
       targets @{const running_loc}), the @{const net_automata} length, and the post-store bound.\<close>
    have struct5: "fst (?run5 ! k) ! Suc (?SS ! k) = starting_loc
                   \<and> length (fst (?run5 ! k)) = length net_automata
                   \<and> Simple_Network_Language.bounded (map_of net_bounds)
                         (fst (snd (edge_2_effect (?SS ! k) (?run5 ! k))))"
      if k: "k < length ?SS" for k
    proof -
      let ?ck = "?run5 ! k"
      have Sk: "Suc k < length ?run5" using k by simp
      have k_lt: "k < length ?run5" using k by simp
      have pres: "length (fst ((map edge_2_effect ?SS ! j) s)) = length (fst s)
                    \<and> fst ((map edge_2_effect ?SS ! j) s) ! 0 = fst s ! 0"
        if j: "j < length (map edge_2_effect ?SS)" for j s
        using edge_2_effect_preserves_loc0[of "?SS ! j" s] j by simp
      have loc0len: "length (fst ?ck) = length (fst h5) \<and> fst ?ck ! 0 = fst h5 ! 0"
        using seq_apply_locs_preserved[OF pres, of k] k_lt by simp
      have ckloc0: "fst ?ck ! 0 = planning_loc" using loc0len conjunct1[OF h5_props] by simp
      have cklen: "length (fst ?ck) = length net_automata" using loc0len conjunct2[OF h5_props] by simp
      have nxt: "?run5 ! Suc k = edge_2_effect (?SS ! k) ?ck"
        using seq_apply_Cons_nth_Suc[of k "map edge_2_effect ?SS" h5] k by simp
      obtain L vp c where ck: "?ck = (L, vp, c)" by (cases ?ck)
      have nxt_eq: "fst (?run5 ! Suc k) = L[Suc (?SS ! k) := running_loc]"
        unfolding nxt ck by (simp add: edge_2_effect_alt)
      have step: "net_impl.sem \<turnstile> \<langle>L, vp, c\<rangle> \<rightarrow> \<langle>fst (?run5 ! Suc k), fst (snd (?run5 ! Suc k)), snd (snd (?run5 ! Suc k))\<rangle>"
        using graph_impl_steps_nth_step[OF prun5 Sk] unfolding ck by simp
      have nk_act: "?SS ! k < length actions"
        using SS_mem[OF nth_mem[OF k]] by simp
      have Llen: "length L = length net_automata" using cklen ck by simp
      have main0: "L ! 0 = planning_loc" using ckloc0 ck by simp
      \<comment> \<open>Conjunct 1: source @{const starting_loc}, recovered from the @{const running_loc} target.\<close>
      have start_src: "L ! Suc (?SS ! k) = starting_loc"
        by (rule prop_step_source_starting[OF step Llen nxt_eq main0 nk_act])
      have c1: "fst ?ck ! Suc (?SS ! k) = starting_loc" using start_src ck by simp
      \<comment> \<open>Conjunct 3: the @{const net_bounds} bound on the post-store.\<close>
      have c3: "Simple_Network_Language.bounded (map_of net_bounds)
                  (fst (snd (edge_2_effect (?SS ! k) ?ck)))"
        using graph_impl_steps_nth_bounded[OF prun5 Sk] cklen nxt by simp
      show ?thesis using c1 cklen c3 by blast
    qed
    \<comment> \<open>Apply the @{const edge_2} phase-lift combinator with P/Q pinned to run positions. The
       @{const ext_seq}-form output @{term \<open>(ext_seq \<circ> seq_apply) (map edge_2_effect ?SS) [h5]\<close>} is the
       run @{term ?run5}.\<close>
    have run5eq: "(ext_seq \<circ> seq_apply) (map edge_2_effect ?SS) [h5] = ?run5"
      by (subst ext_seq_comp_append) simp
    have combinator:
      "RLP ?w5 ((ext_seq \<circ> seq_apply) (map edge_2_effect ?SS) [h5])
       \<and> (\<lambda>x. True) (last ((ext_seq \<circ> seq_apply) (map edge_2_effect ?SS) [h5]))"
    proof (rule num_edge_2_phase_lift[where
            xs = "[h5]" and ns = "?SS" and w = "?w5"
            and R = "\<lambda>x. x = h5"
            and P = "\<lambda>j s. s = ?run5 ! j"
            and Q = "\<lambda>j s. s = ?run5 ! Suc j"
            and S = "\<lambda>x. True" and R' = "\<lambda>x. True"])
      show "RLP ?w5 [h5] \<and> (\<lambda>x. x = h5) (last [h5])" by (simp add: RLP_base)
    next
      fix j s
      assume j: "j < length ?SS" and Pj: "s = ?run5 ! j"
      have nxt: "?run5 ! Suc j = edge_2_effect (?SS ! j) s"
        unfolding Pj using seq_apply_Cons_nth_Suc[of j "map edge_2_effect ?SS" h5] j by simp
      have src: "fst s ! Suc (?SS ! j) = starting_loc"
        and len: "length (fst s) = length net_automata"
        and pbnd: "Simple_Network_Language.bounded (map_of net_bounds)
                      (fst (snd (edge_2_effect (?SS ! j) s)))"
        using struct5[OF j] unfolding Pj by simp_all
      have nk_act: "?SS ! j < length actions"
        using SS_mem[OF nth_mem[OF j]] by simp
      have rlp_single: "RLP ?w5 [s, edge_2_effect (?SS ! j) s]"
        by (rule RLP_edge_2_single[OF src nk_act len pbnd fin5 wok5 sat5[OF nk_act]])
      show "(\<lambda>j s. s = ?run5 ! Suc j) j (edge_2_effect (?SS ! j) s)
            \<and> RLP ?w5 [s, edge_2_effect (?SS ! j) s]"
        using nxt rlp_single by simp
    next
      fix j s assume "Suc j < length ?SS" "s = ?run5 ! Suc j"
      thus "(\<lambda>j s. s = ?run5 ! j) (Suc j) s" by simp
    next
      fix x assume "0 < length ?SS" "(\<lambda>x. x = h5) x"
      thus "(\<lambda>j s. s = ?run5 ! j) 0 x" by simp
    next
      fix x assume "0 < length ?SS" "(\<lambda>j s. s = ?run5 ! Suc j) (length ?SS - 1) x"
      thus "(\<lambda>x. True) x" by simp
    next
      fix x assume "length ?SS = 0" "(\<lambda>x. x = h5) x"
      thus "(\<lambda>x. True) x" by simp
    next
      fix x assume "(\<lambda>x. True) x"
      thus "(\<lambda>x. True) x" by simp
    qed
    show ?thesis using conjunct1[OF combinator] unfolding run5eq .
  qed
  have edge_phases:
    "(\<exists>nss1 cn1. num_graph_impl.steps (delay ?d (L, v, c) # nss1)
                 \<and> RELC h2 cn1 (snd (M i))
                 \<and> cn1 = last (delay ?d (L, v, c) # nss1)
                 \<and> length nss1 = length ?SE)
     \<and> (\<forall>cn. RELC h5 cn (?w (snaps_inst @ snaps_start @ snaps_end)) \<longrightarrow>
            (\<exists>nss5. num_graph_impl.steps (cn # nss5)
                    \<and> RELC (last ?seq) (last (cn # nss5)) (?w (snaps_inst @ snaps_start @ snaps_end))
                    \<and> length nss5 = length ?SS))"
  proof (rule conjI)
    \<comment> \<open>Part 1 (edge_3 entry phase): instantiate @{text rlp3} at the numeric delay-seed.\<close>
    show "\<exists>nss1 cn1. num_graph_impl.steps (delay ?d (L, v, c) # nss1)
                     \<and> RELC h2 cn1 (snd (M i))
                     \<and> cn1 = last (delay ?d (L, v, c) # nss1)
                     \<and> length nss1 = length ?SE"
    proof -
      have hd_run3: "hd (h1 # seq_apply (map edge_3_effect ?SE) h1) = h1" by simp
      have last_run3: "last (h1 # seq_apply (map edge_3_effect ?SE) h1) = h2" by (rule h2_last)
      have len_run3: "length (seq_apply (map edge_3_effect ?SE) h1) = length ?SE" by simp
      have seedh1: "RELC h1 (delay ?d (L, v, c)) (snd (M i))"
        using seed unfolding h1_def .
      have rlp3_body: "\<forall>cn. RELC h1 cn (snd (M i)) \<longrightarrow>
                        (\<exists>nss. num_graph_impl.steps (cn # nss)
                               \<and> length nss = length (h1 # seq_apply (map edge_3_effect ?SE) h1) - 1
                               \<and> RELC (last (h1 # seq_apply (map edge_3_effect ?SE) h1)) (last (cn # nss)) (snd (M i)))"
        using rlp3 prun1 unfolding RLP_def hd_run3 by blast
      obtain nss where
          n3run: "num_graph_impl.steps (delay ?d (L, v, c) # nss)"
        and n3len: "length nss = length (h1 # seq_apply (map edge_3_effect ?SE) h1) - 1"
        and n3rel: "RELC (last (h1 # seq_apply (map edge_3_effect ?SE) h1)) (last (delay ?d (L, v, c) # nss)) (snd (M i))"
        using rlp3_body seedh1 by blast
      show ?thesis
        apply (intro exI[where x = nss] exI[where x = "last (delay ?d (L, v, c) # nss)"] conjI)
        subgoal by (rule n3run)
        subgoal using n3rel unfolding last_run3 .
        subgoal by (rule HOL.refl)
        subgoal using n3len len_run3 by simp
        done
    qed
  next
    \<comment> \<open>Part 2 (edge_2 exit phase): @{text rlp5} unfolded IS the parametric all-cn conjunct.\<close>
    show "\<forall>cn. RELC h5 cn (?w (snaps_inst @ snaps_start @ snaps_end)) \<longrightarrow>
            (\<exists>nss5. num_graph_impl.steps (cn # nss5)
                    \<and> RELC (last ?seq) (last (cn # nss5)) (?w (snaps_inst @ snaps_start @ snaps_end))
                    \<and> length nss5 = length ?SS)"
    proof (intro allI impI)
      fix cn
      assume relcn: "RELC h5 cn (?w (snaps_inst @ snaps_start @ snaps_end))"
      have hd_run5: "hd (h5 # seq_apply (map edge_2_effect ?SS) h5) = h5" by simp
      have last_run5: "last (h5 # seq_apply (map edge_2_effect ?SS) h5) = last ?seq" by (rule seq_last)
      have len_run5: "length (seq_apply (map edge_2_effect ?SS) h5) = length ?SS" by simp
      have rlp5_body: "\<forall>cn. RELC h5 cn (?w (snaps_inst @ snaps_start @ snaps_end)) \<longrightarrow>
                        (\<exists>nss. num_graph_impl.steps (cn # nss)
                               \<and> length nss = length (h5 # seq_apply (map edge_2_effect ?SS) h5) - 1
                               \<and> RELC (last (h5 # seq_apply (map edge_2_effect ?SS) h5)) (last (cn # nss))
                                      (?w (snaps_inst @ snaps_start @ snaps_end)))"
        using rlp5 prun5 unfolding RLP_def hd_run5 by blast
      obtain nss where
          n5run: "num_graph_impl.steps (cn # nss)"
        and n5len: "length nss = length (h5 # seq_apply (map edge_2_effect ?SS) h5) - 1"
        and n5rel: "RELC (last (h5 # seq_apply (map edge_2_effect ?SS) h5)) (last (cn # nss))
                         (?w (snaps_inst @ snaps_start @ snaps_end))"
        using rlp5_body relcn by blast
      show "\<exists>nss5. num_graph_impl.steps (cn # nss5)
                   \<and> RELC (last ?seq) (last (cn # nss5)) (?w (snaps_inst @ snaps_start @ snaps_end))
                   \<and> length nss5 = length ?SS"
        apply (intro exI[where x = nss] conjI)
        subgoal by (rule n5run)
        subgoal using n5rel unfolding last_run5 .
        subgoal using n5len len_run5 by simp
        done
    qed
  qed
  obtain nss1 cn1 where
      nrun1: "num_graph_impl.steps (delay ?d (L, v, c) # nss1)"
    and rel1: "RELC h2 cn1 (snd (M i))"
    and last1: "cn1 = last (delay ?d (L, v, c) # nss1)"
    and len1: "length nss1 = length ?SE"
    using edge_phases by blast
  \<comment> \<open>INSTANT phase: lift @{term \<open>apply_instant_actions ?SB h2\<close>} from @{term cn1}, growing the fold by
     both at-start and at-end snaps of the instant indices (@{term snaps_inst}).\<close>
  have w_Nil: "?w [] = snd (M i)"
    by (simp add: num_plan.num_rat_impl.happening_num_update_def)
  have inst_struct: "instant_block_struct ((h2 # apply_instant_actions ?SB h2) ! (3 * k)) (?SB ! k)"
    if k: "k < length ?SB" for k
    by (rule instant_phase_struct[OF prun2 conjunct1[OF h2_props] conjunct2[OF h2_props] _ k])
       (rule conjunct1[OF SB_mem])
  obtain nss2 cn2 where
      nrun2: "num_graph_impl.steps (cn1 # nss2)"
    and rel2: "RELC h3 cn2 (?w snaps_inst)"
    and last2: "cn2 = last (cn1 # nss2)"
    and len2: "length nss2 = 3 * length ?SB"
  proof -
    have ya: "\<exists>a \<in> set actions. s = at_start a \<or> s = at_end a" if "s \<in> set []" for s using that by simp
    have ys: "set [] \<subseteq> planning_sem.happ_at planning_sem.plan_happ_seq ?t" by simp
    have zsd: "distinct ([] @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ?SB) @ (snaps_start @ snaps_end))"
      using ros_dist unfolding snaps_inst_def by simp
    have zsf: "set ([] @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ?SB) @ (snaps_start @ snaps_end))
                 = planning_sem.happ_at planning_sem.plan_happ_seq ?t"
      using ros_set unfolding snaps_inst_def by simp
    have rel0: "RELC h2 cn1 (?w [])" using rel1 unfolding w_Nil .
    obtain nss where
        ph2: "num_graph_impl.steps (cn1 # nss)"
      and ph2len: "length nss = length (apply_instant_actions ?SB h2)"
      and ph2rel: "RELC (last (h2 # apply_instant_actions ?SB h2)) (last (cn1 # nss))
                        (?w ([] @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ?SB)))"
      using num_instant_phase_lift[OF vss m0 i SB_mem ya ys zsd zsf prun2 inst_struct rel0] by blast
    have rew: "[] @ concat (map (\<lambda>n. [at_start (actions ! n), at_end (actions ! n)]) ?SB) = snaps_inst"
      unfolding snaps_inst_def by simp
    have lenrew: "length (apply_instant_actions ?SB h2) = 3 * length ?SB"
      by (rule length_apply_instant_actions)
    show ?thesis
      apply (rule that[of nss "last (cn1 # nss)"])
      subgoal by (rule ph2)
      subgoal using ph2rel unfolding h3_last rew .
      subgoal by simp
      subgoal using ph2len lenrew by simp
      done
  qed
  \<comment> \<open>START phase: lift @{term \<open>seq_apply (map start_edge_effect ?SS) h3\<close>} from @{term cn2}, growing the
     fold by the start snaps @{term snaps_start}.\<close>
  have start_struct: "fst ((h3 # seq_apply (map start_edge_effect ?SS) h3) ! k) ! Suc (?SS ! k) = off_loc
                      \<and> length (fst ((h3 # seq_apply (map start_edge_effect ?SS) h3) ! k)) = length net_automata
                      \<and> Simple_Network_Language.bounded (map_of net_bounds)
                            (fst (snd (start_edge_effect (?SS ! k)
                                        ((h3 # seq_apply (map start_edge_effect ?SS) h3) ! k))))"
    if k: "k < length ?SS" for k
    by (rule start_phase_struct[OF prun3 conjunct1[OF h3_props] conjunct2[OF h3_props] _ k])
       (rule conjunct1[OF SS_mem])
  obtain nss3 cn3 where
      nrun3: "num_graph_impl.steps (cn2 # nss3)"
    and rel3: "RELC h4 cn3 (?w (snaps_inst @ snaps_start))"
    and last3: "cn3 = last (cn2 # nss3)"
    and len3: "length nss3 = length ?SS"
  proof -
    obtain nss where
        ph3: "num_graph_impl.steps (cn2 # nss)"
      and ph3len: "length nss = length ?SS"
      and ph3rel: "RELC (last (h3 # seq_apply (map start_edge_effect ?SS) h3)) (last (cn2 # nss))
                        (?w (snaps_inst @ map (\<lambda>n. at_start (actions ! n)) ?SS))"
      using num_start_phase_lift[OF vss m0 i SS_mem snaps_inst_act snaps_inst_sub
              ros_dist[unfolded snaps_start_def snaps_end_def] ros_set[unfolded snaps_start_def snaps_end_def]
              prun3 start_struct rel2] by blast
    have rew: "snaps_inst @ map (\<lambda>n. at_start (actions ! n)) ?SS = snaps_inst @ snaps_start"
      unfolding snaps_start_def by simp
    show ?thesis
      apply (rule that[of nss "last (cn2 # nss)"])
      subgoal by (rule ph3)
      subgoal using ph3rel unfolding h4_last rew .
      subgoal by simp
      subgoal by (rule ph3len)
      done
  qed
  \<comment> \<open>END phase: lift @{term \<open>seq_apply (map end_edge_effect ?SE) h4\<close>} from @{term cn3}, growing the
     fold by the end snaps @{term snaps_end}.\<close>
  have end_struct: "fst ((h4 # seq_apply (map end_edge_effect ?SE) h4) ! k) ! Suc (?SE ! k) = ending_loc
                    \<and> length (fst ((h4 # seq_apply (map end_edge_effect ?SE) h4) ! k)) = length net_automata
                    \<and> Simple_Network_Language.bounded (map_of net_bounds)
                          (fst (snd (end_edge_effect (?SE ! k)
                                      ((h4 # seq_apply (map end_edge_effect ?SE) h4) ! k))))"
    if k: "k < length ?SE" for k
    by (rule end_phase_struct[OF prun4 conjunct1[OF h4_props] conjunct2[OF h4_props] _ k])
       (rule conjunct1[OF SE_mem])
  obtain nss4 cn4 where
      nrun4: "num_graph_impl.steps (cn3 # nss4)"
    and rel4: "RELC h5 cn4 (?w (snaps_inst @ snaps_start @ snaps_end))"
    and last4: "cn4 = last (cn3 # nss4)"
    and len4: "length nss4 = length ?SE"
  proof -
    have rew: "(snaps_inst @ snaps_start) @ map (\<lambda>n. at_end (actions ! n)) ?SE = snaps_inst @ snaps_start @ snaps_end"
      unfolding snaps_end_def by simp
    have zsd: "distinct ((snaps_inst @ snaps_start) @ map (\<lambda>n. at_end (actions ! n)) ?SE @ [])"
      using ros_dist unfolding snaps_end_def by simp
    have zsf: "set ((snaps_inst @ snaps_start) @ map (\<lambda>n. at_end (actions ! n)) ?SE @ [])
                 = planning_sem.happ_at planning_sem.plan_happ_seq ?t"
      using ros_set unfolding snaps_end_def by simp
    obtain nss where
        ph4: "num_graph_impl.steps (cn3 # nss)"
      and ph4len: "length nss = length ?SE"
      and ph4rel: "RELC (last (h4 # seq_apply (map end_edge_effect ?SE) h4)) (last (cn3 # nss))
                        (?w ((snaps_inst @ snaps_start) @ map (\<lambda>n. at_end (actions ! n)) ?SE))"
      using num_end_phase_lift[OF vss m0 i SE_mem snaps_inst_start_act snaps_inst_start_sub
              zsd zsf prun4 end_struct rel3] by blast
    show ?thesis
      apply (rule that[of nss "last (cn3 # nss)"])
      subgoal by (rule ph4)
      subgoal using ph4rel unfolding h5_last rew .
      subgoal by simp
      subgoal by (rule ph4len)
      done
  qed
  \<comment> \<open>EDGE_2 phase: instantiate the parametric RLP result from @{text edge_phases} at @{term cn4}.\<close>
  obtain nss5 cn5 where
      nrun5: "num_graph_impl.steps (cn4 # nss5)"
    and rel5: "RELC (last ?seq) cn5 (?w (snaps_inst @ snaps_start @ snaps_end))"
    and last5: "cn5 = last (cn4 # nss5)"
    and len5: "length nss5 = length ?SS"
  proof -
    have ex5: "\<exists>nss5. num_graph_impl.steps (cn4 # nss5)
                      \<and> RELC (last ?seq) (last (cn4 # nss5)) (?w (snaps_inst @ snaps_start @ snaps_end))
                      \<and> length nss5 = length ?SS"
      by (rule conjunct2[OF edge_phases, rule_format, OF rel4])
    obtain nss where
        ph5: "num_graph_impl.steps (cn4 # nss)"
      and ph5rel: "RELC (last ?seq) (last (cn4 # nss)) (?w (snaps_inst @ snaps_start @ snaps_end))"
      and ph5len: "length nss = length ?SS"
      using ex5 by (elim exE conjE)
    show ?thesis
      by (rule that[of nss "last (cn4 # nss)"]) (use ph5 ph5rel ph5len in simp_all)
  qed

  \<comment> \<open>The terminal fold is the after-happening valuation.\<close>
  have term_fold: "?w (snaps_inst @ snaps_start @ snaps_end) = snd (M (Suc i))"
    using run_order_fold_eq_happening_num_update_set[OF i vss ros_dist[unfolded ros_eq[symmetric]] ros_set[unfolded ros_eq[symmetric]]]
    unfolding ros_eq[symmetric] .

  \<comment> \<open>Splice the five numeric sub-runs into one run from @{term \<open>delay ?d (L, v, c)\<close>}.\<close>
  define NSS where "NSS = nss1 @ nss2 @ nss3 @ nss4 @ nss5"
  have spliced: "num_graph_impl.steps (delay ?d (L, v, c) # NSS)"
  proof -
    have s12: "num_graph_impl.steps (delay ?d (L, v, c) # nss1 @ nss2)"
      using num_graph_impl.steps_append[OF nrun1 nrun2[unfolded last1]] by simp
    have s123: "num_graph_impl.steps (delay ?d (L, v, c) # nss1 @ nss2 @ nss3)"
      using num_graph_impl.steps_append[OF s12 nrun3[unfolded last2 last1]] by simp
    have s1234: "num_graph_impl.steps (delay ?d (L, v, c) # nss1 @ nss2 @ nss3 @ nss4)"
      using num_graph_impl.steps_append[OF s123 nrun4[unfolded last3 last2 last1]] by simp
    have s12345: "num_graph_impl.steps (delay ?d (L, v, c) # nss1 @ nss2 @ nss3 @ nss4 @ nss5)"
      using num_graph_impl.steps_append[OF s1234 nrun5[unfolded last4 last3 last2 last1]] by simp
    show ?thesis using s12345 unfolding NSS_def by (simp only: append_assoc)
  qed
  \<comment> \<open>The numeric run from @{term \<open>(L, v, c)\<close>}: absorb the leading delay. The
     @{const happening_pre_pre_delay} on the FULL store follows from the projected one (the predicate
     reads the store only on @{const net_bounds}-domain variables, where the two stores agree).\<close>
  have hp_proj_eq: "happening_pre i (L, va, c') = happening_pre i (L, va |` dom (map_of net_bounds), c')"
    for va c'
  proof -
    have aa: "acts_active \<in> dom (map_of net_bounds)" using map_of_net_bounds_acts_active by blast
    have "va x = (va |` dom (map_of net_bounds)) x" if "x \<in> dom (map_of net_bounds)" for x
      using that by (simp add: restrict_in)
    note ag = this
    show ?thesis
      unfolding happening_pre_def Let_def prod.case
      using ag[OF aa] by (simp cong: conj_cong)
  qed
  have ppd_full: "happening_pre_pre_delay i (L, v, c)"
    using ppd unfolding happening_pre_pre_delay_def Let_def prod.case
    by (subst hp_proj_eq) (simp add: restrict_map_def)
  have num_no_urg: "\<forall>p<length (fst (snd num_net_impl.sem)). fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
    by (rule num_no_urgent[OF ppd_full lvp[unfolded cfg]])
  have nrun_full: "num_graph_impl.steps ((L, v, c) # NSS)"
    using num_steps_delay_replace[OF spliced delay_non_negative num_no_urg] .
  \<comment> \<open>The spliced run is non-empty: the happening fires at least one snap (so at least one phase grows),
     hence the terminal numeric config is the run's last.\<close>
  have NSS_ne: "NSS \<noteq> []"
  proof -
    have "0 < length ?SS + length ?SE + length ?SB"
    proof (rule time_index_action_index_happening_cases[OF i])
      fix n assume "n < length actions" "is_starting_index ?t n"
      hence "n \<in> set ?SS" by (simp add: set_filter)
      thus "0 < length ?SS + length ?SE + length ?SB" by (cases ?SS) auto
    next
      fix n assume "n < length actions" "is_ending_index ?t n"
      hence "n \<in> set ?SE" by (simp add: set_filter)
      thus "0 < length ?SS + length ?SE + length ?SB" by (cases ?SE) auto
    next
      fix n assume "n < length actions" "is_instant_index ?t n"
      hence "n \<in> set ?SB" by (simp add: set_filter)
      thus "0 < length ?SS + length ?SE + length ?SB" by (cases ?SB) auto
    qed
    hence "0 < length NSS"
      unfolding NSS_def using len1 len2 len3 len4 len5 by simp
    thus ?thesis by simp
  qed
  have last_spliced: "last (delay ?d (L, v, c) # NSS) = cn5"
  proof -
    have "last (delay ?d (L, v, c) # nss1 @ nss2 @ nss3 @ nss4 @ nss5) = cn5"
      unfolding last5 last4 last3 last2 last1 by (simp add: last_append)
    thus ?thesis unfolding NSS_def .
  qed
  have last_full: "last ((L, v, c) # NSS) = cn5"
    using last_spliced NSS_ne by (simp add: last_ConsR)
  have rel_term: "RELC (last ?seq) (last ((L, v, c) # NSS)) (snd (M (Suc i)))"
    using rel5 unfolding last_full term_fold[symmetric] .

  \<comment> \<open>Conclude: the run, the post-invariant, and the carried @{const num_LvP}.\<close>
  obtain Lp vp cp where lp: "last ?seq = (Lp, vp, cp)" by (rule prod_cases3)
  obtain Ln vn cn where ln: "last ((L, v, c) # NSS) = (Ln, vn, cn)" by (rule prod_cases3)
  have Leq: "Lp = Ln" using rel_term unfolding lp ln by (rule RELC_locD)
  have ceq: "cp = cn" using rel_term unfolding lp ln by (rule RELC_clkD)
  have relS: "REL vp vn (snd (M (Suc i)))" using rel_term unfolding lp ln by (rule RELC_relD)
  have le: "vp \<subseteq>\<^sub>m vn" by (rule REL_leD[OF relS])
  have trk: "num_tracks vn (snd (M (Suc i)))" by (rule REL_trD[OF relS])
  have bndn: "Simple_Network_Language.bounded (map_of num_net_bounds) vn" by (rule REL_bndD[OF relS])
  \<comment> \<open>The propositional post-invariant and the carried @{const LvP} of @{term \<open>last ?seq\<close>}.\<close>
  have ppost_last: "happening_post i (last ?seq)" by (rule ppost_seq)
  have lvp_last: "LvP (last ?seq)" using prun_seq_full by simp
  have lv_p: "Lv_conds Lp vp" using lvp_last unfolding lp by simp
  have pbnd_p: "Simple_Network_Language.bounded (map_of net_bounds) vp"
    by (rule Lv_conds_dests(3)[OF lv_p])
  \<comment> \<open>The propositional last store is the net_bounds-projection of the numeric last store.\<close>
  have vp_dom: "dom vp = dom (map_of net_bounds)"
    using pbnd_p unfolding Simple_Network_Language.bounded_def by blast
  have proj_eq: "vn |` dom (map_of net_bounds) = vp"
  proof (rule ext)
    fix x
    show "(vn |` dom (map_of net_bounds)) x = vp x"
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      hence "x \<in> dom vp" using vp_dom by simp
      then obtain y where y: "vp x = Some y" by auto
      have "vn x = Some y" using le y unfolding map_le_def by (metis domI)
      thus ?thesis using True y by (simp add: restrict_in)
    next
      case False
      hence "x \<notin> dom vp" using vp_dom by simp
      thus ?thesis using False by (simp add: restrict_map_def domIff)
    qed
  qed
  \<comment> \<open>The propositional post-invariant transports to the numeric last config via the projection.\<close>
  have nppost: "num_happening_post M i (last ((L, v, c) # NSS))"
    unfolding ln
  proof (rule num_happening_postI)
    show "happening_post i (Ln, vn |` dom (map_of net_bounds), cn)"
      using ppost_last unfolding lp proj_eq Leq ceq .
    show "num_tracks vn (snd (M (Suc i)))" by (rule trk)
  qed
  \<comment> \<open>The carried @{const num_LvP}: locations and the planning lock are preserved, the bound from the
     terminal @{const REL}.\<close>
  have num_lv0: "num_Lv_conds L v" using lvp[unfolded cfg] by simp
  have planning_lock_dom: "planning_lock \<in> dom (map_of net_bounds)"
    using map_of_net_bounds_planning_lock by blast
  have vp_pl: "vp planning_lock = Some 1" by (rule Lv_conds_dests(4)[OF lv_p])
  have vn_pl: "vn planning_lock = Some 1"
    using le vp_pl unfolding map_le_def by (metis domI planning_lock_dom restrict_in vp_dom)
  have nlvp: "num_LvP (last ((L, v, c) # NSS))"
    unfolding ln num_LvP.simps
  proof (rule num_Lv_conds_maintained[OF num_lv0])
    show "length L = length Ln"
      using num_Lv_conds_dests(1)[OF num_lv0] Lv_conds_dests(1)[OF lv_p] Leq by simp
    show "L ! 0 = Ln ! 0"
      using num_Lv_conds_dests(2)[OF num_lv0] Lv_conds_dests(2)[OF lv_p] Leq by simp
    show "vn planning_lock = v planning_lock"
      using vn_pl num_Lv_conds_dests(4)[OF num_lv0] by simp
    show "Simple_Network_Language.bounded (map_of num_net_bounds) v \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn"
      using bndn by simp
  qed
  show "\<exists>ns. num_graph_impl.steps (cfg # ns) \<and> num_happening_post M i (last (cfg # ns)) \<and> num_LvP (last (cfg # ns))"
    unfolding cfg using nrun_full nppost nlvp by blast
qed


end

end

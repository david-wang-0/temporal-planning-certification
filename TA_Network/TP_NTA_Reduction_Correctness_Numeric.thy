theory TP_NTA_Reduction_Correctness_Numeric
  imports TP_NTA_Reduction_Numeric_Steps
begin

context numeric_tp_nta_reduction_correctness
begin


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
    have wok3: "num_val_ok (snd (M i))" by (rule fluent_in_bounds_imp_num_val_ok[OF fin3])
    \<comment> \<open>The over_all invariants hold at @{term \<open>snd (M i)\<close>} for every ending-index action (from plan
       validity's active clause, @{thm [source] ending_index_inv_sat}): the deferred @{text sat_inv}
       the augmented @{const num_edge_3} guard demands.\<close>
    have sat3: "sat_comps (snd (M i)) (set (n_inv (actions ! n)))"
      if n: "n < length actions" and iend: "is_ending_index ?t n" for n
      by (rule ending_index_inv_sat[OF vss i n iend])
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
        and nk_end: "is_ending_index ?t (?SE ! j)"
        using SE_mem[OF nth_mem[OF j]] by simp_all
      have rlp_single: "RLP (snd (M i)) [s, edge_3_effect (?SE ! j) s]"
        by (rule RLP_edge_3_single[OF src nk_act len pbnd fin3 wok3 sat3[OF nk_act nk_end]])
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
    \<comment> \<open>The terminal fold equality @{term \<open>?w5 = snd (M (Suc i))\<close>}: re-derived here (mirror of
       @{text term_fold} below), so the honest edge_2 over_all discharge @{thm [source]
       starting_index_active_Suc} -- scoped to a just-started (hence active) action -- applies.\<close>
    have term_fold5: "?w5 = snd (M (Suc i))"
      using run_order_fold_eq_happening_num_update_set[OF i vss ros_dist[unfolded ros_eq[symmetric]] ros_set[unfolded ros_eq[symmetric]]]
      unfolding ros_eq[symmetric] .
    have sat5: "sat_comps ?w5 (set (n_inv (actions ! n)))"
      if n: "n < length actions" and ist: "is_starting_index ?t n" for n
    proof -
      have "sat_comps (snd (M (Suc i))) (set (n_inv (actions ! n)))"
        by (rule starting_index_active_Suc(2)[OF vss i n ist])
      thus ?thesis using term_fold5 by simp
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
        and nk_ist: "is_starting_index ?t (?SS ! j)"
        using SS_mem[OF nth_mem[OF j]] by simp_all
      have rlp_single: "RLP ?w5 [s, edge_2_effect (?SS ! j) s]"
        by (rule RLP_edge_2_single[OF src nk_act len pbnd fin5 wok5 sat5[OF nk_act nk_ist]])
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




text \<open>The propositional invariant transfers between consecutive happenings, extracted (config-generic)
from @{thm [source] plan_steps_possible}'s cases. They thread the @{text planning_sem} bookkeeping
across the index boundary; the numeric run-lifting reuses them verbatim and only adds the (identity)
tracking transfer.\<close>
lemma pp_post_imp_pre_pre_delay_Suc:
  assumes ib: "i < length planning_sem.htpl - 1"
      and post: "happening_post i (L, v, c)"
  shows "happening_pre_pre_delay (Suc i) (L, v, c)"
proof -
  have ib1: "i < length planning_sem.htpl"
    and ib2: "Suc i < length planning_sem.htpl" using ib by linarith+
  note D = happening_post_dests[OF post HOL.refl]
  have c2: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ (Suc i) p)"
    using D(1) ib1 ib2 by (auto simp: prop_state_after_happ_def prop_state_before_happ_def planning_sem.state_seq_Suc_is_upd_state)
  have c3: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index (Suc i)) p))"
    using D(2) ib1 ib2 by (auto simp: planning_sem.locked_after_indexed_timepoint_is_locked_before_Suc[symmetric])
  have c4: "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index (Suc i))))"
    using D(3) ib1 ib2 by (auto simp: planning_sem.active_after_indexed_timepoint_is_active_before_Suc[symmetric])
  have c5: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 0 \<longrightarrow> L ! Suc j = off_loc"
    using D(4) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c6: "\<forall>j<length actions. planning_sem.open_active_count (planning_sem.time_index (Suc i)) (actions ! j) = 1 \<longrightarrow> L ! Suc j = running_loc"
    using D(5) ib1 ib2 by (auto simp: planning_sem.closed_active_count_on_indexed_timepoint_is_open_active_count_Suc[symmetric])
  have c7: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_start_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(6) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  have c8: "\<forall>j<length actions. act_clock_pre_happ (c \<oplus> get_delay (Suc i)) act_to_end_clock (actions ! j) (planning_sem.time_index (Suc i))"
    apply (intro strip)
    apply (subst act_clock_pre_happ_simps)
    apply (subst planning_sem.updated_exec_time_and_next)
    using D(7) ib1 ib2 by (auto simp: planning_sem.time_index_def planning_sem.updated_exec_time_and_next of_rat_add cval_add_def get_delay_def)
  show ?thesis by (rule happening_pre_pre_delayI[OF HOL.refl c2 c3 c4 c5 c6 c7 c8])
qed

lemma pp_init_imp_pre_pre_delay_0:
  assumes hlen: "0 < length planning_sem.htpl"
      and props': "init_planning_state_props' x"
  shows "happening_pre_pre_delay 0 x"
proof (rule init_planning_state_props'E[OF props'])
  fix L v c
  assume s: "x = (L, v, c)"
    and va: "v acts_active = Some 0"
    and Leq: "L = planning_loc # map (\<lambda>x. off_loc) actions"
    and pv: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state (set init) p)"
    and pl: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    and cs: "\<forall>i<length actions. c (act_to_start_clock (actions ! i)) = 0"
    and ce: "\<forall>i<length actions. c (act_to_end_clock (actions ! i)) = 0"
  have c2: "\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state_before_happ 0 p)"
    using pv hlen by (auto simp: planning_sem.plan_state_seq_props prop_state_before_happ_def)
  have c3: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some (int (planning_sem.locked_before (planning_sem.time_index 0) p))"
    using pl by (auto simp: int_of_nat_def planning_sem.locked_before_initial_is_0)
  have c4: "v acts_active = Some (int (planning_sem.active_before (planning_sem.time_index 0)))"
    using va by (auto simp: int_of_nat_def planning_sem.active_before_initial_is_0)
  have c5: "\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index 0) (actions ! i) = 0 \<longrightarrow> L ! Suc i = off_loc"
    using Leq by (auto simp: planning_sem.open_active_count_initial_is_0)
  have c6: "\<forall>i<length actions. planning_sem.open_active_count (planning_sem.time_index 0) (actions ! i) = 1 \<longrightarrow> L ! Suc i = running_loc"
    using Leq by (auto simp: planning_sem.open_active_count_initial_is_0)
  have c7: "\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay 0) act_to_start_clock (actions ! i) (planning_sem.time_index 0)"
    using cs hlen by (subst act_clock_pre_happ_simps cval_add_def planning_sem.exec_time_at_init)+
      (auto simp: get_delay_def planning_sem.card_htps_len_htpl of_rat_add Rat.of_int_def)
  have c8: "\<forall>i<length actions. act_clock_pre_happ (c \<oplus> get_delay 0) act_to_end_clock (actions ! i) (planning_sem.time_index 0)"
    using ce hlen by (subst act_clock_pre_happ_simps cval_add_def planning_sem.exec_time_at_init)+
      (auto simp: get_delay_def planning_sem.card_htps_len_htpl of_rat_add Rat.of_int_def)
  show "happening_pre_pre_delay 0 x" by (rule happening_pre_pre_delayI[OF s c2 c3 c4 c5 c6 c7 c8])
qed

lemma pp_post_last_imp_goal_trans_pre:
  assumes hlen: "0 < length planning_sem.htpl"
      and lvp: "LvP x"
      and post: "happening_post (length planning_sem.htpl - 1) x"
  shows "goal_trans_pre x"
proof -
  obtain L v c where s: "x = (L, v, c)" by (rule prod_cases3)
  have lv: "Lv_conds L v" using lvp unfolding s by simp
  note D = happening_post_dests[OF post s]
  have c3: "v acts_active = Some 0"
    using D(3) by (subst (asm) planning_sem.active_after_final_is_0) simp
  have c4: "L = planning_loc # map (\<lambda>x. off_loc) actions"
  proof (subst list_eq_iff_nth_eq, intro conjI allI impI)
    show "length L = length (planning_loc # map (\<lambda>x. off_loc) actions)"
      using Lv_conds_dests(1)[OF lv] by simp
  next
    fix i assume i: "i < length L"
    show "L ! i = (planning_loc # map (\<lambda>x. off_loc) actions) ! i"
    proof (cases i)
      case 0
      thus ?thesis using Lv_conds_dests(2)[OF lv] by simp
    next
      case (Suc i')
      hence i': "i' < length actions" using i Lv_conds_dests(1)[OF lv] by simp
      have "planning_sem.closed_active_count (planning_sem.time_index (length planning_sem.htpl - 1)) (actions ! i') = 0"
        by (rule planning_sem.closed_active_count_final_is_0[OF nth_mem[OF i']])
      hence "L ! Suc i' = off_loc" using D(4) i' by blast
      thus ?thesis using Suc i' by simp
    qed
  qed
  have c5: "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p))"
    apply (rule exI[of _ "planning_sem.upd_state (length planning_sem.htpl - 1)"])
    using D(1) hlen
    apply (subst planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    apply (rule conjI)
    using planning_sem.plan_state_seq_valid apply fastforce
    apply (subst (asm) prop_state_after_happ_def, simp)
    apply (subst (asm) planning_sem.state_seq_Suc_is_upd_state[symmetric], simp)+
    by blast
  have c6: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0"
    using D(2) unfolding planning_sem.locked_after_final_is_0 int_of_nat_def by simp
  show ?thesis by (rule goal_trans_preI[OF s c3 c4 c5 c6])
qed

lemma pp_init_imp_goal_trans_pre:
  assumes hlen: "0 = length planning_sem.htpl"
      and props': "init_planning_state_props' x"
  shows "goal_trans_pre x"
proof -
  have init_is_goal: "set goal \<subseteq> set init"
    using hlen planning_sem.valid_plan_state_seq by auto
  show ?thesis
    apply (rule init_planning_state_props'E[OF props'])
    apply (rule goal_trans_preI)
    using init_is_goal by auto
qed

text \<open>The numeric twins of the four transfers: each is its propositional counterpart plus the
(essentially identity) tracking transfer at the matching index.\<close>
lemma num_post_imp_pre_pre_delay_Suc:
  assumes ib: "i < length planning_sem.htpl - 1"
      and lvp: "num_LvP cfg"
      and post: "num_happening_post M i cfg"
  shows "num_happening_pre_pre_delay M (Suc i) cfg \<and> num_LvP cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "happening_post i (L, v |` dom (map_of net_bounds), c)" using post[unfolded cfg] by (rule num_happening_post_propD)
  have t: "num_tracks v (snd (M (Suc i)))" using post[unfolded cfg] by (rule num_happening_post_trackD)
  have "num_happening_pre_pre_delay M (Suc i) cfg" unfolding cfg
    by (rule num_happening_pre_pre_delayI[where M = M and i = "Suc i", OF pp_post_imp_pre_pre_delay_Suc[OF ib p] t])
  thus ?thesis using lvp by blast
qed

lemma num_init_imp_pre_pre_delay_0:
  assumes hlen: "0 < length planning_sem.htpl"
      and lvp: "num_LvP cfg"
      and props': "num_init_planning_state_props' M cfg"
  shows "num_happening_pre_pre_delay M 0 cfg \<and> num_LvP cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" using props'[unfolded cfg] by (rule num_init_planning_state_props'_propD)
  have t: "num_tracks v (snd (M 0))" using props'[unfolded cfg] by (rule num_init_planning_state_props'_trackD)
  have "num_happening_pre_pre_delay M 0 cfg" unfolding cfg
    by (rule num_happening_pre_pre_delayI[where M = M and i = 0, OF pp_init_imp_pre_pre_delay_0[OF hlen p] t])
  thus ?thesis using lvp by blast
qed

lemma num_post_last_imp_goal_trans_pre:
  assumes hlen: "0 < length planning_sem.htpl"
      and lvp: "num_LvP cfg"
      and post: "num_happening_post M (length planning_sem.htpl - 1) cfg"
  shows "num_goal_trans_pre M cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have lvpr: "LvP (L, v |` dom (map_of net_bounds), c)" using lvp[unfolded cfg] by (rule num_LvP_imp_LvP)
  have p: "happening_post (length planning_sem.htpl - 1) (L, v |` dom (map_of net_bounds), c)" using post[unfolded cfg] by (rule num_happening_post_propD)
  have t0: "num_tracks v (snd (M (Suc (length planning_sem.htpl - 1))))" using post[unfolded cfg] by (rule num_happening_post_trackD)
  have suc_eq: "Suc (length planning_sem.htpl - 1) = length planning_sem.htpl" using hlen by simp
  have t: "num_tracks v (snd (M (length planning_sem.htpl)))" using t0 unfolding suc_eq .
  show ?thesis unfolding cfg
    by (rule num_goal_trans_preI[where M = M, OF pp_post_last_imp_goal_trans_pre[OF hlen lvpr p] t])
qed

lemma num_init_imp_goal_trans_pre:
  assumes hlen: "0 = length planning_sem.htpl"
      and props': "num_init_planning_state_props' M cfg"
  shows "num_goal_trans_pre M cfg"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  have p: "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" using props'[unfolded cfg] by (rule num_init_planning_state_props'_propD)
  have t0: "num_tracks v (snd (M 0))" using props'[unfolded cfg] by (rule num_init_planning_state_props'_trackD)
  have t: "num_tracks v (snd (M (length planning_sem.htpl)))" using t0 by (simp add: hlen[symmetric])
  show ?thesis unfolding cfg
    by (rule num_goal_trans_preI[where M = M, OF pp_init_imp_goal_trans_pre[OF hlen p] t])
qed

text \<open>The numeric plan run, existentially: from a combined initial config (propositional
@{const init_planning_state_props'} plus tracking of @{term \<open>snd (M 0)\<close>}), the numeric net has a run
reaching a @{const num_goal_trans_pre} config. Mirrors @{thm [source] plan_steps_possible} but threads
the existential numeric run happening-by-happening (rather than via the @{const ext_seq'} combinator,
since the numeric configs differ from the propositional ones): the inner @{text chain} runs happenings
@{term j}..@{term \<open>length htpl - 1\<close>}, extending the run by @{thm [source] num_happening_steps_possible}
and carrying @{const num_happening_post} to the next happening's @{const num_happening_pre_pre_delay}.\<close>
lemma num_plan_steps_possible:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and lvp: "num_LvP cfg"
      and pres: "num_init_planning_state_props' M cfg"
  shows "\<exists>ms. num_graph_impl.steps (cfg # ms) \<and> num_goal_trans_pre M (last (cfg # ms))
              \<and> num_LvP (last (cfg # ms))"
proof (cases "length planning_sem.htpl = 0")
  case True
  have g: "num_goal_trans_pre M cfg" by (rule num_init_imp_goal_trans_pre[OF True[symmetric] pres])
  show ?thesis
  proof (intro exI[of _ "[]"] conjI)
    show "num_graph_impl.steps (cfg # [])" by (rule num_graph_impl.steps.Single)
    show "num_goal_trans_pre M (last (cfg # []))" using g by simp
    show "num_LvP (last (cfg # []))" using lvp by simp
  qed
next
  case False
  hence hlen: "0 < length planning_sem.htpl" by simp
  \<comment> \<open>@{const num_LvP} is threaded as a SEPARATE conjunct through the run, mirroring @{const LvP} in
     @{thm [source] plan_steps_possible}: each step's @{thm [source] num_happening_steps_possible} both
     consumes and re-produces it, and the transfer to the next happening passes it through unchanged
     (same store).\<close>
  have chain: "\<exists>ms. num_graph_impl.steps (cfg' # ms)
                   \<and> num_happening_post M (length planning_sem.htpl - 1) (last (cfg' # ms))
                   \<and> num_LvP (last (cfg' # ms))"
    if "num_happening_pre_pre_delay M j cfg'" "num_LvP cfg'" "j < length planning_sem.htpl" for j cfg'
    using that
  proof (induction "length planning_sem.htpl - 1 - j" arbitrary: j cfg')
    case 0
    hence jeq: "j = length planning_sem.htpl - 1" using "0.prems"(3) by linarith
    obtain ms where ms: "num_graph_impl.steps (cfg' # ms)"
                        "num_happening_post M j (last (cfg' # ms))"
                        "num_LvP (last (cfg' # ms))"
      using num_happening_steps_possible[OF "0.prems"(3) vss m0 "0.prems"(2) "0.prems"(1)] by blast
    show ?case using ms jeq by blast
  next
    case (Suc d)
    have jlt1: "j < length planning_sem.htpl - 1" using Suc.hyps(2) by linarith
    obtain ms1 where ms1: "num_graph_impl.steps (cfg' # ms1)"
                          "num_happening_post M j (last (cfg' # ms1))"
                          "num_LvP (last (cfg' # ms1))"
      using num_happening_steps_possible[OF Suc.prems(3) vss m0 Suc.prems(2) Suc.prems(1)] by blast
    have preSuc: "num_happening_pre_pre_delay M (Suc j) (last (cfg' # ms1))"
      and lvpSuc: "num_LvP (last (cfg' # ms1))"
      using num_post_imp_pre_pre_delay_Suc[OF jlt1 ms1(3) ms1(2)] by blast+
    have meas: "d = length planning_sem.htpl - 1 - Suc j" using Suc.hyps(2) by linarith
    have sucjlt: "Suc j < length planning_sem.htpl" using jlt1 by linarith
    obtain ms2 where ms2: "num_graph_impl.steps (last (cfg' # ms1) # ms2)"
                          "num_happening_post M (length planning_sem.htpl - 1) (last (last (cfg' # ms1) # ms2))"
                          "num_LvP (last (last (cfg' # ms1) # ms2))"
      using Suc.hyps(1)[OF meas preSuc lvpSuc sucjlt] by blast
    have steps: "num_graph_impl.steps (cfg' # ms1 @ ms2)"
      using num_graph_impl.steps_append[OF ms1(1) ms2(1)] by simp
    have lasteq: "last (cfg' # ms1 @ ms2) = last (last (cfg' # ms1) # ms2)"
      by (cases ms2) auto
    have "num_happening_post M (length planning_sem.htpl - 1) (last (cfg' # ms1 @ ms2))"
      and "num_LvP (last (cfg' # ms1 @ ms2))"
      using ms2(2) ms2(3) lasteq by simp_all
    thus ?case using steps by blast
  qed
  have pre0: "num_happening_pre_pre_delay M 0 cfg"
    and lvp0: "num_LvP cfg"
    using num_init_imp_pre_pre_delay_0[OF hlen lvp pres] by blast+
  obtain ms where ms: "num_graph_impl.steps (cfg # ms)"
                      "num_happening_post M (length planning_sem.htpl - 1) (last (cfg # ms))"
                      "num_LvP (last (cfg # ms))"
    using chain[OF pre0 lvp0 hlen] by blast
  have "num_goal_trans_pre M (last (cfg # ms))"
    by (rule num_post_last_imp_goal_trans_pre[OF hlen ms(3) ms(2)])
  thus ?thesis using ms(1) ms(3) by blast
qed


text \<open>The numeric net's initial config, mirroring the propositional @{const a\<^sub>0}: the same locations
@{const init_locs} and the zero clock valuation, with the numeric initial variable store
@{const num_init_vars} (the propositional init vars plus each fluent variable at its lower bound; the
init edge later writes @{term num_init}).\<close>

text \<open>The store after firing the numeric init update @{const num_init_upd}: each fluent variable is set
to the integer encoding of its initial value. The propositional variables are untouched (the numeric
half writes only fluent variables), so this is exactly @{term v} overwritten on
@{term \<open>fluent_to_var ` set nfluents\<close>}.\<close>
lemma is_upds_num_init_upd_gen:
  "is_upds v (map (\<lambda>f. (fluent_to_var f, exp.const (const_to_int (num_init f)))) xs)
             (foldl (\<lambda>v f. v(fluent_to_var f \<mapsto> const_to_int (num_init f))) v xs)"
proof (induction xs arbitrary: v)
  case Nil
  show ?case by (simp add: is_upds.intros(1))
next
  case (Cons x xs)
  have hd: "is_upd v (fluent_to_var x, exp.const (const_to_int (num_init x)))
                 (v(fluent_to_var x \<mapsto> const_to_int (num_init x)))"
    by (simp add: is_upd_const_simp)
  show ?case
    apply (simp only: list.map foldl_Cons)
    apply (rule is_upds.intros(2)[OF hd])
    by (rule Cons.IH)
qed

lemma foldl_num_init_upd_unwritten:
  assumes "x \<notin> fluent_to_var ` set xs"
  shows "foldl (\<lambda>v f. v(fluent_to_var f \<mapsto> const_to_int (num_init f))) v xs x = v x"
  using assms by (induction xs arbitrary: v) auto

lemma foldl_num_init_upd_written:
  assumes "g \<in> set xs"
      and "inj_on fluent_to_var (set xs)"
  shows "foldl (\<lambda>v f. v(fluent_to_var f \<mapsto> const_to_int (num_init f))) v xs (fluent_to_var g)
           = Some (const_to_int (num_init g))"
  using assms
proof (induction xs arbitrary: v)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "g \<in> set xs")
    case True
    thus ?thesis using Cons.IH Cons.prems(2) by (simp add: inj_on_Un)
  next
    case False
    hence gx: "g = x" using Cons.prems(1) by simp
    have nx: "fluent_to_var x \<notin> fluent_to_var ` set xs"
      using Cons.prems(2) False gx by (auto simp: inj_on_def)
    show ?thesis
      unfolding gx
      apply (subst foldl_Cons)
      by (subst foldl_num_init_upd_unwritten[OF nx]) simp
  qed
qed

text \<open>The numeric init-edge step, the BOTTOM rung of the numeric-net completeness ladder and the
numeric analogue of @{thm [source] initial_step_possible}. The pre-init config @{const num_a\<^sub>0} sits at
@{const init_loc} with @{const planning_lock} at its lower bound @{term 0} and each fluent variable at
its lower bound, so it satisfies neither @{const num_LvP} (loc/lock) nor
@{const num_init_planning_state_props'}. Firing the numeric init edge @{const num_main_auto_init_edge}
moves loc @{term 0} to @{const planning_loc}, sets @{const planning_lock} to @{term 1}, records the
initial propositions and -- via the appended @{const num_init_upd} -- writes @{term num_init} into each
fluent variable, landing in a config that both structural invariants hold on.\<close>
lemma num_initial_step_possible:
  assumes vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
  shows "\<exists>cfg1. num_graph_impl.steps [num_a\<^sub>0, cfg1]
              \<and> num_LvP cfg1 \<and> num_init_planning_state_props' M cfg1"
proof -
  let ?vn = "map_of num_init_vars"
  let ?c = "\<lambda>_::String.literal. 0::real"
  let ?props = "map prop_to_var init"
  let ?vn_mid = "?vn(planning_lock \<mapsto> 1, acts_active \<mapsto> 0, ?props [\<mapsto>] map (\<lambda>x. 1) ?props)"
  let ?vn' = "foldl (\<lambda>v f. v(fluent_to_var f \<mapsto> const_to_int (num_init f))) ?vn_mid nfluents"
  have prop_upds: "is_upds ?vn (permit_planning # set_active # map (set_prop_ab 1) init) ?vn_mid"
    if "permit_planning = set_var 1 planning_lock" "set_active = set_var 0 acts_active"
    for permit_planning set_active
    unfolding that
    apply (rule is_upds.intros)
     apply (simp add: is_upd_const_simp)
    apply (rule is_upds.intros)
     apply (simp add: is_upd_const_simp)
    unfolding set_prop_ab_def
    apply (rule is_upds_set_vars_map)
     apply (subst map_map[symmetric])
     apply (rule HOL.refl)
    by simp
  have prop_upds': "is_upds ?vn (set_var 1 planning_lock # set_var 0 acts_active # map (set_prop_ab 1) init) ?vn_mid"
    by (rule prop_upds) (rule HOL.refl)+
  have num_upds: "is_upds ?vn_mid num_init_upd ?vn'"
    unfolding num_init_upd_def
    by (rule is_upds_num_init_upd_gen)
  have niv_split: "num_init_vars = init_vars @ map (\<lambda>f. (fluent_to_var f, fluent_lo f)) nfluents"
    unfolding num_init_vars_def num_all_vars_def init_vars_def num_fluent_vars_def
    by (simp add: map_prod_def)
  have proj: "?vn |` dom (map_of net_bounds) = map_of init_vars"
  proof (rule ext)
    fix x
    show "(?vn |` dom (map_of net_bounds)) x = map_of init_vars x"
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      hence xdom: "x \<in> dom (map_of init_vars)"
        using init_vars_bounded unfolding bounded_def by simp
      have "?vn x = map_of init_vars x"
        unfolding niv_split map_of_append
      proof -
        have "x \<notin> dom (map_of (map (\<lambda>f. (fluent_to_var f, fluent_lo f)) nfluents))"
        proof
          assume "x \<in> dom (map_of (map (\<lambda>f. (fluent_to_var f, fluent_lo f)) nfluents))"
          hence "x \<in> fluent_to_var ` set nfluents"
            by (simp add: dom_map_of_conv_image_fst image_image)
          then obtain f where "f \<in> set nfluents" "x = fluent_to_var f" by auto
          thus False using fluent_var_notin_net_bounds True by blast
        qed
        thus "(map_of (map (\<lambda>f. (fluent_to_var f, fluent_lo f)) nfluents) ++ map_of init_vars) x = map_of init_vars x"
          by (simp add: map_add_dom_app_simps(3))
      qed
      thus ?thesis using True by (simp add: restrict_in)
    next
      case False
      hence "map_of init_vars x = None"
        using init_vars_bounded unfolding bounded_def by (auto simp: domIff)
      thus ?thesis using False by (simp add: restrict_map_def)
    qed
  qed
  have isp: "init_state_props (init_locs, map_of init_vars, ?c)"
  proof (rule init_state_propsI)
    show "(init_locs, map_of init_vars, ?c) = (init_locs, map_of init_vars, ?c)" ..
    show "bounded (map_of net_bounds) (map_of init_vars)" by (rule init_vars_bounded)
    show "init_locs = init_loc # map (\<lambda>x. off_loc) actions" by (simp add: init_locs_def)
    show "map_of init_vars x = Some 0" if "x \<in> set (map fst net_bounds)" for x
      using that
      unfolding init_vars_alt
      apply (rule_tac map_of_determ)
       apply fastforce
      by auto
    show "map_of init_vars x = None" if "x \<notin> set (map fst net_bounds)" for x
      using that
      apply (subst map_of_eq_None_iff)
      by (auto simp: init_vars_alt)
    show "?c = (\<lambda>_. 0)" ..
  qed
  have vn_pl0: "?vn planning_lock = Some 0"
  proof -
    have pl_mem: "planning_lock \<in> set (map fst net_bounds)"
      using map_of_net_bounds_planning_lock
      by (simp add: dom_map_of_conv_image_fst[symmetric] domI)
    have ivpl: "map_of init_vars planning_lock = Some 0"
      by (rule init_state_props_dests(3)[OF isp HOL.refl pl_mem])
    have "planning_lock \<in> dom (map_of net_bounds)" using map_of_net_bounds_planning_lock by blast
    thus ?thesis using proj ivpl by (metis restrict_in)
  qed
  have tr': "num_tracks ?vn' (snd (M 0))"
  proof (rule num_tracksI)
    fix g
    assume g: "g \<in> set nfluents"
    have wg: "snd (M 0) g = Some (num_init g)" using m0 g by simp
    have "?vn' (fluent_to_var g) = Some (const_to_int (num_init g))"
      by (rule foldl_num_init_upd_written[OF g fluent_to_var_inj])
    thus "\<exists>r. snd (M 0) g = Some r \<and> ?vn' (fluent_to_var g) = Some (const_to_int r)"
      using wg by blast
  qed
  have fib: "fluent_in_bounds (snd (M 0))"
    by (rule num_seq_fluent_in_bounds[OF vss m0]) simp
  have dom_vn: "dom ?vn = dom (map_of num_net_bounds)"
    unfolding num_init_vars_def
    by (simp add: dom_map_of_conv_image_fst image_image map_prod_def case_prod_beta)
  have midd: "dom ?vn_mid = dom (map_of num_net_bounds)"
  proof -
    have "acts_active \<in> dom ?vn" "planning_lock \<in> dom ?vn"
      using dom_vn dom_map_of_num_net_bounds map_of_net_bounds_acts_active map_of_net_bounds_planning_lock
      by (auto simp: domIff)
    moreover
    have "prop_to_var p \<in> dom ?vn" if "p \<in> set init" for p
    proof -
      have "map_of net_bounds (prop_to_var p) = Some (0, 1)"
        using that by (intro map_of_net_bounds_init_goal) simp
      hence "prop_to_var p \<in> dom (map_of net_bounds)" by blast
      thus ?thesis using dom_vn dom_map_of_num_net_bounds by simp
    qed
    ultimately
    have "dom ?vn_mid = dom ?vn" by (auto simp: domIff)
    thus ?thesis using dom_vn by simp
  qed
  have vn'_dom: "dom ?vn' = dom (map_of num_net_bounds)"
  proof -
    have dfold: "dom (foldl (\<lambda>v f. v(fluent_to_var f \<mapsto> const_to_int (num_init f))) w xs)
                   = dom w \<union> fluent_to_var ` set xs" for w xs
      by (induction xs arbitrary: w) auto
    have "fluent_to_var ` set nfluents \<subseteq> dom (map_of num_net_bounds)"
      using dom_map_of_num_net_bounds by blast
    thus ?thesis using dfold[of ?vn_mid nfluents] midd by auto
  qed
  let ?pv = "(map_of init_vars)(planning_lock \<mapsto> 1, acts_active \<mapsto> 0, ?props [\<mapsto>] map (\<lambda>x. 1) ?props)"
  have proj': "?vn' |` dom (map_of net_bounds) = ?pv"
  proof (rule ext)
    fix x
    show "(?vn' |` dom (map_of net_bounds)) x = ?pv x"
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      have xnf: "x \<notin> fluent_to_var ` set nfluents"
        using True fluent_var_notin_net_bounds by blast
      have "?vn' x = ?vn_mid x"
        using foldl_num_init_upd_unwritten[OF xnf] by simp
      also
      have "\<dots> = ?pv x"
      proof (cases "x \<in> set ?props")
        case True
        have "?vn_mid x = Some 1"
          apply (rule map_upds_with_map[of x "?props" "?props" _ 1])
          using True by simp_all
        moreover
        have "?pv x = Some 1"
          apply (rule map_upds_with_map[of x "?props" "?props" _ 1])
          using True by simp_all
        ultimately
        show ?thesis by simp
      next
        case False
        have "?vn_mid x = (?vn(planning_lock \<mapsto> 1, acts_active \<mapsto> 0)) x"
          using False by (simp add: map_upds_apply_nontin)
        moreover
        have "?pv x = ((map_of init_vars)(planning_lock \<mapsto> 1, acts_active \<mapsto> 0)) x"
          using False by (simp add: map_upds_apply_nontin)
        moreover
        have "?vn x = map_of init_vars x"
          using proj True by (metis restrict_in)
        ultimately
        show ?thesis by (cases "x = planning_lock"; cases "x = acts_active"; simp)
      qed
      finally
      show ?thesis using True by (simp add: restrict_in)
    next
      case False
      have "?pv x = None"
      proof -
        have x_notin_props: "x \<notin> set ?props"
        proof
          assume "x \<in> set ?props"
          then obtain p where p: "p \<in> set init" "x = prop_to_var p" by auto
          have "map_of net_bounds (prop_to_var p) = Some (0, 1)"
            using p(1) by (intro map_of_net_bounds_init_goal) simp
          hence "prop_to_var p \<in> dom (map_of net_bounds)" by blast
          thus False using False p by simp
        qed
        moreover
        have "x \<noteq> planning_lock" "x \<noteq> acts_active"
          using False map_of_net_bounds_planning_lock map_of_net_bounds_acts_active by (auto simp: domIff)
        moreover
        have "map_of init_vars x = None"
          using False init_vars_bounded unfolding bounded_def by (auto simp: domIff)
        ultimately
        show ?thesis by (simp add: map_upds_apply_nontin)
      qed
      thus ?thesis using False by (simp add: restrict_map_def)
    qed
  qed
  have pv_bnd: "bounded (map_of net_bounds) ?pv"
  proof -
    have bv: "bounded (map_of net_bounds) (map_of init_vars)" by (rule init_vars_bounded)
    have b1: "bounded (map_of net_bounds) ((map_of init_vars)(planning_lock \<mapsto> 1))"
      by (rule single_upd_bounded[OF bv map_of_net_bounds_planning_lock]; simp)
    have b2: "bounded (map_of net_bounds) ((map_of init_vars)(planning_lock \<mapsto> 1, acts_active \<mapsto> 0))"
      by (rule single_upd_bounded[OF b1 map_of_net_bounds_acts_active]; simp)
    show ?thesis
    proof (rule upds_bounded[OF b2])
      show "length ?props = length (map (\<lambda>x. 1) ?props)" by simp
      show "\<forall>n<length ?props. \<exists>l u.
          map_of net_bounds (?props ! n) = Some (l, u)
          \<and> l \<le> map (\<lambda>x. 1) ?props ! n
          \<and> map (\<lambda>x. 1) ?props ! n \<le> u"
      proof (intro allI impI)
        fix n
        assume n: "n < length ?props"
        have "?props ! n \<in> set (map prop_to_var init) \<union> set (map prop_to_var goal)"
          using n by simp
        hence "map_of net_bounds (?props ! n) = Some (0, 1)"
          by (rule map_of_net_bounds_init_goal)
        thus "\<exists>l u. map_of net_bounds (?props ! n) = Some (l, u)
          \<and> l \<le> map (\<lambda>x. 1) ?props ! n
          \<and> map (\<lambda>x. 1) ?props ! n \<le> u"
          using n by simp
      qed
    qed
  qed
  have bnd': "bounded (map_of num_net_bounds) ?vn'"
    by (rule num_tracks_bounded[OF vn'_dom _ tr' fib]) (unfold proj', rule pv_bnd)
  let ?upds = "set_var 1 planning_lock # set_var 0 acts_active # map (set_prop_ab 1) init"
  have all_upds: "is_upds ?vn (?upds @ num_init_upd) ?vn'"
    by (rule is_upds_appendI[OF prop_upds' num_upds])
  have guard: "check_bexp ?vn (bexp.and (var_is 0 planning_lock) bexp.true) True"
    using vn_pl0 by (auto simp: check_bexp_simps is_val_simps)
  let ?L' = "init_locs[0 := planning_loc]"
  let ?cfg1 = "(?L', ?vn', ?c)"
  have step: "num_net_impl.sem \<turnstile> \<langle>init_locs, ?vn, ?c\<rangle> \<rightarrow>\<^bsub>Internal (STR '''')\<^esub> \<langle>?L', ?vn', [[]\<rightarrow>0]?c\<rangle>"
  proof (rule num_step_int_lift[where p = 0])
    show "(0::nat) < length num_timed_automaton_net"
      by (simp add: length_num_net_automata)
    have edge_eq: "(init_loc, bexp.and (var_is 0 planning_lock) bexp.true, [], Sil (STR ''''), ?upds @ num_init_upd, [], planning_loc)
            = num_main_auto_init_edge"
      unfolding num_main_auto_init_edge_def augment_edge_def main_auto_init_edge_def Let_def prod.case
      by simp
    show "(init_loc, bexp.and (var_is 0 planning_lock) bexp.true, [], Sil (STR ''''), ?upds @ num_init_upd, [], planning_loc)
            \<in> trans (automaton_of (num_timed_automaton_net ! 0))"
      unfolding edge_eq num_main_auto_trans
      by (rule insertI1)
    show "check_bexp ?vn (bexp.and (var_is 0 planning_lock) bexp.true) True"
      by (rule guard)
    show "?c \<turnstile> conv_cc []" by simp
    show "init_locs ! 0 = init_loc" by (simp add: init_locs_def)
    show "length init_locs = length num_timed_automaton_net"
      by (simp add: init_locs_def length_num_net_automata)
    show "is_upds ?vn (?upds @ num_init_upd) ?vn'" by (rule all_upds)
    show "bounded (map_of num_net_bounds) ?vn'" using bnd' .
  qed
  have niv_apply_gen: "map_of (map (map_prod id fst) ys) x = map_option fst (map_of ys x)" for ys :: "(String.literal \<times> int \<times> int) list" and x
    by (induction ys) (auto simp: map_prod_def)
  have niv_apply: "?vn x = map_option fst (map_of num_net_bounds x)" for x
    unfolding num_init_vars_def
    by (rule niv_apply_gen)
  have bnd0_lu: "l \<le> u \<and> ?vn x = Some l"
    if lu: "map_of num_net_bounds x = Some (l, u)" for x l u
  proof -
    have vnx: "?vn x = Some l" using niv_apply[of x] lu by simp
    have lu_mem: "(x, l, u) \<in> set num_net_bounds" using lu by (rule map_of_SomeD)
    have "l \<le> u"
      using lu_mem
      unfolding num_all_vars_def all_vars_def num_fluent_vars_def Let_def
      using fluent_bounds_valid
      by (auto split: if_splits)
    thus ?thesis using vnx by simp
  qed
  have bnd0: "bounded (map_of num_net_bounds) ?vn"
    unfolding Simple_Network_Language.bounded_def
  proof (intro conjI ballI)
    show "dom ?vn = dom (map_of num_net_bounds)" by (rule dom_vn)
  next
    fix x assume x: "x \<in> dom ?vn"
    have "x \<in> dom (map_of num_net_bounds)" using x dom_vn by simp
    then obtain l u where lu: "map_of num_net_bounds x = Some (l, u)"
      by (metis domD surj_pair)
    show "fst (the (map_of num_net_bounds x)) \<le> the (?vn x)" using bnd0_lu[OF lu] lu by simp
  next
    fix x assume x: "x \<in> dom ?vn"
    have "x \<in> dom (map_of num_net_bounds)" using x dom_vn by simp
    then obtain l u where lu: "map_of num_net_bounds x = Some (l, u)"
      by (metis domD surj_pair)
    show "the (?vn x) \<le> snd (the (map_of num_net_bounds x))" using bnd0_lu[OF lu] lu by simp
  qed
  have cc0: "([[]\<rightarrow>(0::real)]?c) = ?c" by simp
  have step': "num_net_impl.sem \<turnstile> \<langle>init_locs, ?vn, ?c\<rangle> \<rightarrow> \<langle>?L', ?vn', ?c\<rangle>"
  proof (rule num_non_t_step_intro)
    show "num_net_impl.sem \<turnstile> \<langle>init_locs, ?vn, ?c\<rangle> \<rightarrow>\<^bsub>Internal (STR '''')\<^esub> \<langle>?L', ?vn', ?c\<rangle>"
      using step cc0 by simp
    show "Internal (STR '''') \<noteq> Simple_Network_Language.label.Del" by simp
    show "bounded (map_of num_net_bounds) ?vn" by (rule bnd0)
  qed
  have steps: "num_graph_impl.steps [num_a\<^sub>0, ?cfg1]"
    unfolding num_a\<^sub>0_def
    apply (rule num_single_step_intro)
    unfolding prod.case
    by (rule step')
  have pl1: "?vn' planning_lock = Some 1"
  proof -
    have "planning_lock \<notin> fluent_to_var ` set nfluents"
      using fluent_var_notin_net_bounds map_of_net_bounds_planning_lock
      by (force simp: domIff)
    hence "?vn' planning_lock = ?vn_mid planning_lock"
      by (rule foldl_num_init_upd_unwritten)
    also
    have "\<dots> = Some 1"
      apply (subst map_upds_apply_nontin)
      subgoal by (rule variable_sets_unique(12))
      by (simp add: variables_unique)
    finally
    show ?thesis .
  qed
  have lvp: "num_LvP ?cfg1"
    unfolding num_LvP.simps
    apply (rule num_Lv_condsI)
    subgoal by (simp add: init_locs_def)
    subgoal by (simp add: init_locs_def nth_list_update planning_loc_def init_loc_def)
    subgoal using bnd' .
    subgoal by (rule pl1)
    done
  have props': "num_init_planning_state_props' M ?cfg1"
  proof (rule num_init_planning_state_props'I)
    show "num_tracks ?vn' (snd (M 0))" by (rule tr')
    have isp_run: "init_planning_state_props' (last ((ext_seq \<circ> seq_apply) [main_auto_init_edge_effect] [a\<^sub>0]))"
      using initial_step_possible by blast
    have "(ext_seq \<circ> seq_apply) [main_auto_init_edge_effect] [a\<^sub>0] = [a\<^sub>0, main_auto_init_edge_effect a\<^sub>0]"
      by (simp add: comp_def seq_apply_1 ext_seq_def)
    hence "init_planning_state_props' (main_auto_init_edge_effect a\<^sub>0)"
      using isp_run by simp
    moreover
    have "main_auto_init_edge_effect a\<^sub>0 = (?L', ?pv, ?c)"
      unfolding a\<^sub>0_alt
      by (simp add: main_auto_init_edge_effect_alt init_locs_def init_vars_alt)
    ultimately
    show "init_planning_state_props' (?L', ?vn' |` dom (map_of net_bounds), ?c)"
      using proj' by simp
  qed
  show ?thesis using steps lvp props' by blast
qed

text \<open>The numeric goal self-loop stream, mirroring @{const goal_run}. The numeric config type coincides
with the propositional one, so the coinductive shape is identical.\<close>
primcorec num_goal_run::"
  (nat list \<times>
    (String.literal \<rightharpoonup> int) \<times>
    (String.literal, real) cval)
\<Rightarrow> (nat list \<times>
    (String.literal \<rightharpoonup> int) \<times>
    (String.literal, real) cval) stream" where
"num_goal_run s = s ## (num_goal_run s)"

text \<open>The numeric reached goal config, mirroring @{const goal_state_conds}: the numeric goal edge
only flips location @{term 0} to @{const goal_loc} and @{const planning_lock} to @{term 2}, so every
conjunct coincides with @{const goal_state_conds} except the boundedness, which is stated against the
FULL numeric bounds @{const num_net_bounds} (the numeric store carries the fresh fluent variables).
The propositional value/lock conjuncts are stated over @{term \<open>map_of net_bounds\<close>} (the numeric goal
edge does not touch propositional variables beyond @{const planning_lock}).\<close>
definition "num_goal_state_conds Lvc \<equiv>
let
  (L, v, c) = Lvc;
  bounded = Simple_Network_Language.bounded (map_of num_net_bounds) v;

  acts_active = v acts_active = Some 0;
  planning_state = v planning_lock = Some 2;

  locs = (L = goal_loc # map (\<lambda> x. off_loc) actions);
  prop_state = (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)));
  lock_state = (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)

in
  bounded
\<and> acts_active
\<and> planning_state
\<and> locs
\<and> prop_state
\<and> lock_state"

lemma num_goal_state_condsI:
  assumes "x = (L, v, c)"
    "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    "v acts_active = Some 0"
    "v planning_lock = Some 2"
    "L = goal_loc # map (\<lambda> x. off_loc) actions"
    "(\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)))"
    "(\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)"
  shows "num_goal_state_conds x"
  using assms by (auto simp: num_goal_state_conds_def)

lemma num_goal_state_condsE:
  assumes "num_goal_state_conds x"
      and "\<And>L v c. x = (L, v, c)
        \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v
        \<Longrightarrow> v acts_active = Some 0
        \<Longrightarrow> v planning_lock = Some 2
        \<Longrightarrow> L = goal_loc # map (\<lambda> x. off_loc) actions
        \<Longrightarrow> L ! 0 = goal_loc
        \<Longrightarrow> (\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_var p) = Some (prop_state S p)))
        \<Longrightarrow> (\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> v (prop_to_lock p) = Some 0)
        \<Longrightarrow> thesis"
    shows thesis
  apply (cases x)
  using assms unfolding num_goal_state_conds_def by simp

lemma num_final_step_possible:
  assumes gtp: "num_goal_trans_pre M cfg"
      and lvp: "num_LvP cfg"
      and goalsat: "sat_comps (snd (M (length planning_sem.htpl))) (set num_goal)"
      and goalok: "\<forall>c \<in> set num_goal. comp_ok (snd (M (length planning_sem.htpl))) c"
  shows "\<exists>cfg'. num_graph_impl.steps [cfg, cfg'] \<and> num_goal_state_conds cfg'"
proof -
  obtain L v c where cfg: "cfg = (L, v, c)" by (rule prod_cases3)
  let ?w = "snd (M (length planning_sem.htpl))"
  \<comment> \<open>The numeric structural invariant on the source config.\<close>
  have nlv: "num_Lv_conds L v"
    using lvp unfolding cfg by simp
  have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    by (rule num_Lv_conds_dests(3)[OF nlv])
  have vpl1: "v planning_lock = Some 1"
    by (rule num_Lv_conds_dests(4)[OF nlv])
  have Llen: "length L = Suc (length actions)"
    by (rule num_Lv_conds_dests(1)[OF nlv])
  \<comment> \<open>The propositional goal-transition pre-conditions on the projected store, and the tracking fact.\<close>
  have gtpp: "goal_trans_pre (L, v |` dom (map_of net_bounds), c)"
    by (rule num_goal_trans_pre_propD[OF gtp[unfolded cfg]])
  have tr: "num_tracks v ?w" by (rule num_goal_trans_pre_trackD[OF gtp[unfolded cfg]])
  let ?vp = "v |` dom (map_of net_bounds)"
  let ?xp = "(L, ?vp, c)"
  have lvpp: "LvP ?xp" by (rule num_LvP_imp_LvP[OF lvp[unfolded cfg]])
  \<comment> \<open>The propositional goal step and reached goal config, reused verbatim from @{thm [source] final_step_possible}
      on the singleton list.\<close>
  have "graph_impl.steps ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] [?xp])
        \<and> goal_state_conds (last ((ext_seq \<circ> seq_apply) [main_auto_goal_edge_effect] [?xp]))"
  proof (rule final_step_possible, intro conjI)
    show "graph_impl.steps [?xp]" by (rule graph_impl.steps.Single)
    show "goal_trans_pre (last [?xp])" using gtpp by simp
    show "LvP (last [?xp])" using lvpp by simp
  qed
  hence pstep: "graph_impl.steps [?xp, main_auto_goal_edge_effect ?xp]"
    and gsc: "goal_state_conds (main_auto_goal_edge_effect ?xp)"
    by (simp_all add: comp_def ext_seq_def seq_apply_def)
  \<comment> \<open>The propositional reached goal config; its store, from @{thm [source] main_auto_goal_edge_effect_alt}.\<close>
  have g_eq: "main_auto_goal_edge_effect ?xp = (L[0 := goal_loc], ?vp(planning_lock \<mapsto> 2), c)"
    by (rule main_auto_goal_edge_effect_alt)
  \<comment> \<open>Extract the single propositional step from the two-element @{const graph_impl.steps} list.\<close>
  have pstep': "net_impl.sem \<turnstile> \<langle>L, ?vp, c\<rangle> \<rightarrow> \<langle>L[0 := goal_loc], ?vp(planning_lock \<mapsto> 2), c\<rangle>"
  proof (cases rule: graph_impl.steps.cases[OF pstep[unfolded g_eq]])
    case (2 x y xs)
    hence "x = (L, ?vp, c)" "y = (L[0 := goal_loc], ?vp(planning_lock \<mapsto> 2), c)"
      by simp_all
    thus ?thesis using 2(2) by simp
  qed simp
  have gsc': "goal_state_conds (L[0 := goal_loc], ?vp(planning_lock \<mapsto> 2), c)"
    using gsc unfolding g_eq .
  have Llen': "length L = length net_automata"
    using Llen by (simp add: length_net_automata)
  \<comment> \<open>The projected store is @{const net_bounds}-bounded, and @{term v} extends it.\<close>
  have pbnd: "Simple_Network_Language.bounded (map_of net_bounds) ?vp"
    by (rule prop_proj_bounded[OF bnd])
  have le: "?vp \<subseteq>\<^sub>m v"
    by (simp add: map_le_def)
  \<comment> \<open>Split the propositional step into its (vacuous) delay and the internal goal-edge firing.\<close>
  obtain Li vi ci aa where
      del: "net_impl.sem \<turnstile> \<langle>L, ?vp, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>Li, vi, ci\<rangle>"
    and aD: "aa \<noteq> Simple_Network_Language.label.Del"
    and act: "net_impl.sem \<turnstile> \<langle>Li, vi, ci\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L[0 := goal_loc], ?vp(planning_lock \<mapsto> 2), c\<rangle>"
    by (rule step_u'_elims[OF pstep']) blast
  obtain broad N B where as: "net_impl.sem = (broad, N, B)"
    by (cases net_impl.sem) auto
  obtain t where Lieq: "Li = L" and vieq: "vi = ?vp" and cieq: "ci = c \<oplus> t"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as unfolding TAG_def by auto
  have actI: "net_impl.sem \<turnstile> \<langle>L, ?vp, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>aa\<^esub> \<langle>L[0 := goal_loc], ?vp(planning_lock \<mapsto> 2), c\<rangle>"
    using act unfolding Lieq vieq cieq .
  obtain a where aInt: "aa = Internal a"
    using prop_non_del_step_internal[OF actI aD Llen']
    by blast
  \<comment> \<open>Invert the internal step to recover the fired edge and pin it to @{const main_auto_goal_edge} at p=0.\<close>
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp ?vp b True"
    and G: "(c \<oplus> t) \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq2: "L[0 := goal_loc] = L[p := l']"
    and c'eq: "c = [r\<rightarrow>0](c \<oplus> t)"
    and U: "is_upds ?vp f (?vp(planning_lock \<mapsto> 2))"
    by (rule prop_int_step_invert[OF actI[unfolded aInt] Llen'])
  \<comment> \<open>Pin @{term p} to @{term 0}: only position @{term 0} changed, to @{const goal_loc}.\<close>
  have len0: "0 < length L"
    using Llen by simp
  have L0_pl: "L ! 0 = planning_loc"
    by (rule num_Lv_conds_dests(2)[OF nlv])
  have pl_ne_goal: "planning_loc \<noteq> goal_loc"
    by (simp add: locations_unique)
  have p0: "p = 0"
  proof (rule ccontr)
    assume "p \<noteq> 0"
    hence "L[p := l'] ! 0 = L ! 0" by simp
    hence "L[0 := goal_loc] ! 0 = planning_loc"
      using L'eq2 L0_pl by simp
    moreover
    have "L[0 := goal_loc] ! 0 = goal_loc" using len0 by simp
    ultimately
    show False using pl_ne_goal by simp
  qed
  \<comment> \<open>The fired edge is @{const main_auto_goal_edge}; read off its components.\<close>
  have l_pl: "l = planning_loc"
    using LOC p0 L0_pl by simp
  have Emem: "(l, b, g, Sil a, f, r, l') \<in> set [main_auto_init_edge, main_auto_goal_edge, main_auto_loop]"
    using E unfolding p0 main_auto_trans by simp
  have edge_goal: "(l, b, g, Sil a, f, r, l') = main_auto_goal_edge"
    using Emem l_pl
    by (auto simp: main_auto_init_edge_def main_auto_goal_edge_def main_auto_loop_def
                   Let_def locations_unique)
  note goal_parts = edge_goal[unfolded main_auto_goal_edge_def Let_def, simplified prod.inject]
  have g_nil: "g = []"
    and f_eq: "f = [set_var 2 planning_lock]"
    and r_nil: "r = []"
    and l'_goal: "l' = goal_loc"
    using goal_parts by simp_all
  \<comment> \<open>The numeric edge is the AUGMENTED @{const num_main_auto_goal_edge} at p=0.\<close>
  have NE: "(l, bexp.and b num_goal_guard, g, Sil a, f @ [], r, l')
              \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    unfolding p0 num_main_auto_trans
    using edge_goal
    unfolding num_main_auto_goal_edge_def augment_edge_def main_auto_goal_edge_def Let_def
    by (simp add: prod.case)
  \<comment> \<open>The combined guard fires on @{term v}: the propositional half by monotonicity, the numeric
     @{const num_goal_guard} half by @{thm [source] check_bexp_comps_guard}.\<close>
  have bvn: "check_bexp v b True"
    by (rule check_bexp_is_val_mono(1)[OF B le])
  have guard_num: "check_bexp v num_goal_guard True"
    unfolding num_goal_guard_def
    by (rule check_bexp_comps_guard[OF tr goalok goalsat])
  have NB: "check_bexp v (bexp.and b num_goal_guard) True"
    using check_bexp_is_val.intros(3)[OF bvn guard_num]
    by simp
  \<comment> \<open>The (empty-numeric) update fires on @{term v}, landing on @{term \<open>v(planning_lock \<mapsto> 2)\<close>}.\<close>
  obtain vn' where
      NU: "is_upds v (f @ []) vn'"
    and LE: "?vp(planning_lock \<mapsto> 2) \<subseteq>\<^sub>m vn'"
    and OFF: "\<And>x. x \<notin> fst ` set (f @ []) \<Longrightarrow> vn' x = v x"
    using is_upds_map_le[OF U le]
    by (metis append_Nil2)
  \<comment> \<open>The update writes only @{const planning_lock} (a propositional variable, fresh of the fluents),
     so @{term \<open>vn' = v(planning_lock \<mapsto> 2)\<close>} and tracking survives.\<close>
  have fset_f: "fst ` set (f @ []) = {planning_lock}"
    using f_eq by simp
  have vn'_eq: "vn' = v(planning_lock \<mapsto> 2)"
  proof (rule ext)
    fix x
    show "vn' x = (v(planning_lock \<mapsto> 2)) x"
    proof (cases "x = planning_lock")
      case True
      have "vn' planning_lock = (?vp(planning_lock \<mapsto> 2)) planning_lock"
        using LE by (auto simp: map_le_def)
      thus ?thesis using True by simp
    next
      case False
      hence "x \<notin> fst ` set (f @ [])" using fset_f by simp
      thus ?thesis using OFF False by simp
    qed
  qed
  have fresh: "fluent_to_var h \<notin> fst ` set (f @ [])" if h: "h \<in> set nfluents" for h
  proof -
    have "planning_lock \<in> dom (map_of net_bounds)" using map_of_net_bounds_planning_lock by blast
    thus ?thesis using fset_f fluent_var_notin_net_bounds[OF h] by auto
  qed
  have TR: "num_tracks vn' ?w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  \<comment> \<open>Re-establish the @{const num_net_bounds} bound on @{term \<open>v(planning_lock \<mapsto> 2)\<close>}.\<close>
  have plock_dom: "planning_lock \<in> dom (map_of net_bounds)" using map_of_net_bounds_planning_lock by blast
  have plock_bnd: "map_of num_net_bounds planning_lock = Some (0, 2)"
    using map_of_num_net_bounds_eq_on_props[OF plock_dom] map_of_net_bounds_planning_lock by simp
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    unfolding vn'_eq
    by (rule single_upd_bounded[OF bnd plock_bnd]; simp)
  \<comment> \<open>Assemble the numeric step: vacuous delay + the lifted internal goal edge.\<close>
  have numDel: "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L, v, c \<oplus> t\<rangle>"
    by (rule num_step_t_lift[OF del[unfolded Lieq vieq cieq] bnd])
  have plen_num: "p < length num_timed_automaton_net"
    using P by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have Llen_num: "length L = length num_timed_automaton_net"
    using Llen' by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have numInt: "num_net_impl.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  have Lupd_eq: "L[p := l'] = L[0 := goal_loc]" using p0 l'_goal by simp
  have clk_eq: "[r\<rightarrow>0](c \<oplus> t) = c" using c'eq by simp
  have numstep0: "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L[p := l'], vn', [r\<rightarrow>0](c \<oplus> t)\<rangle>"
    by (rule step_u'.intros[OF numDel _ numInt]) simp
  have numstep: "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L[0 := goal_loc], vn', c\<rangle>"
    using numstep0 unfolding Lupd_eq clk_eq .
  \<comment> \<open>The numeric reached goal config satisfies @{const num_goal_state_conds}: locations/props/locks
     from @{const goal_state_conds} on the projection, boundedness from @{const num_net_bounds}.\<close>
  let ?cfg' = "(L[0 := goal_loc], vn', c)"
  have proj_eq: "?vp(planning_lock \<mapsto> 2) = vn' |` dom (map_of net_bounds)"
  proof (rule ext)
    fix x
    show "(?vp(planning_lock \<mapsto> 2)) x = (vn' |` dom (map_of net_bounds)) x"
    proof (cases "x \<in> dom (map_of net_bounds)")
      case True
      hence "(vn' |` dom (map_of net_bounds)) x = vn' x" by (simp add: restrict_in)
      moreover
      have "vn' x = (v(planning_lock \<mapsto> 2)) x" using vn'_eq by simp
      moreover
      have "(?vp(planning_lock \<mapsto> 2)) x = (v(planning_lock \<mapsto> 2)) x" using True by (simp add: restrict_in)
      ultimately
      show ?thesis by simp
    next
      case False
      hence "(vn' |` dom (map_of net_bounds)) x = None" by (simp add: restrict_map_def)
      moreover
      have "x \<noteq> planning_lock" using False plock_dom by blast
      hence "(?vp(planning_lock \<mapsto> 2)) x = ?vp x" by simp
      moreover
      have "?vp x = None" using False by (simp add: restrict_map_def)
      ultimately
      show ?thesis by simp
    qed
  qed
  have gsc'': "goal_state_conds (L[0 := goal_loc], vn' |` dom (map_of net_bounds), c)"
    using gsc' unfolding proj_eq .
  have "num_goal_state_conds ?cfg'"
  proof (rule goal_state_condsE[OF gsc''])
    fix L'' vv'' c''
    assume s: "(L[0 := goal_loc], vn' |` dom (map_of net_bounds), c) = (L'', vv'', c'')"
      and va: "vv'' acts_active = Some 0"
      and pl2: "vv'' planning_lock = Some 2"
      and Leq: "L'' = goal_loc # map (\<lambda> x. off_loc) actions"
      and pv: "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> vv'' (prop_to_var p) = Some (prop_state S p))"
      and plk: "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> vv'' (prop_to_lock p) = Some 0"
    have L''eq: "L'' = L[0 := goal_loc]"
      and vv''eq: "vv'' = vn' |` dom (map_of net_bounds)"
      using s by simp_all
    show "num_goal_state_conds ?cfg'"
    proof (rule num_goal_state_condsI[OF HOL.refl BND])
      have "acts_active \<in> dom (map_of net_bounds)" using map_of_net_bounds_acts_active by blast
      thus "vn' acts_active = Some 0" using va vv''eq by (simp add: restrict_in)
      show "vn' planning_lock = Some 2" using vn'_eq by simp
      show "L[0 := goal_loc] = goal_loc # map (\<lambda> x. off_loc) actions" using Leq L''eq by simp
      show "\<exists>S. set goal \<subseteq> S \<and> (\<forall>p. p \<in> set props \<and> prop_to_var p \<in> dom (map_of net_bounds) \<longrightarrow> vn' (prop_to_var p) = Some (prop_state S p))"
        using pv vv''eq by (auto simp: restrict_in)
      show "\<forall>p. p \<in> set props \<and> prop_to_lock p \<in> dom (map_of net_bounds) \<longrightarrow> vn' (prop_to_lock p) = Some 0"
        using plk vv''eq by (auto simp: restrict_in)
    qed
  qed
  moreover
  have "num_graph_impl.steps [cfg, ?cfg']"
    unfolding cfg
    apply (rule num_graph_impl.steps.Cons[OF _ num_graph_impl.steps.Single])
    using numstep by simp
  ultimately
  show ?thesis by blast
qed


text \<open>The numeric goal self-loop stream is a run of the numeric graph, mirroring @{thm [source]
goal_run_is_run}. At @{const goal_loc} the main automaton fires the (un-augmented) @{const
main_auto_loop} edge -- guard-free, empty update, empty reset -- so it self-loops on the numeric net.\<close>
lemma num_goal_run_is_run:
  assumes "num_goal_state_conds s"
  shows "num_graph_impl.run (num_goal_run s)"
proof -
  have x: "num_goal_state_conds (shd (num_goal_run s))" using assms by simp
  show ?thesis
  proof (rule num_graph_impl.run.coinduct[where X = "\<lambda>x. num_goal_state_conds (shd x) \<and> x = num_goal_run (shd x)"], goal_cases)
    case 1
    show ?case using x by auto
  next
    case (2 x)
    hence conds_x: "num_goal_state_conds (shd x)"
      and xeq: "x = num_goal_run (shd x)" by auto
    have ctr: "x = shd x ## shd x ## (num_goal_run (shd x))"
    proof -
      have "shd x ## (num_goal_run (shd x)) = (num_goal_run (shd x))"
        by (subst (2) num_goal_run.ctr) simp
      thus ?thesis using xeq by auto
    qed
    obtain L v c where Lvc: "shd x = (L, v, c)" using prod_cases3 by blast
    hence conds: "num_goal_state_conds (L, v, c)" using conds_x by simp
    \<comment> \<open>Read off the facts the self-step needs: the goal location, the location list, and boundedness.\<close>
    have L0: "L ! 0 = goal_loc" using conds num_goal_state_condsE by force
    have Lloc: "L = goal_loc # map (\<lambda>x. off_loc) actions" using conds num_goal_state_condsE by force
    have bnd: "Simple_Network_Language.bounded (map_of num_net_bounds) v"
      using conds num_goal_state_condsE by force
    \<comment> \<open>The @{const main_auto_loop} edge lives at position @{term 0} of the numeric net.\<close>
    have Emem: "main_auto_loop \<in> trans (automaton_of (num_timed_automaton_net ! 0))"
      unfolding num_main_auto_trans main_auto_loop_def by simp
    have edge: "(goal_loc, bexp.true, [], Sil (STR ''''), [], [], goal_loc)
                  \<in> trans (automaton_of (num_timed_automaton_net ! 0))"
      using Emem unfolding main_auto_loop_def .
    have plen: "(0::nat) < length num_timed_automaton_net"
      by (simp add: num_timed_automaton_net_def)
    have Llen: "length L = length num_timed_automaton_net"
      unfolding Lloc by (simp add: num_timed_automaton_net_def length_map)
    have upds: "is_upds v [] v" by (rule is_upds.intros)
    have step0: "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal (STR '''')\<^esub> \<langle>L[0 := goal_loc], v, [[]\<rightarrow>0]c\<rangle>"
      by (rule num_step_int_lift[OF plen edge _ _ L0 Llen upds bnd]) (simp add: check_bexp_simps)+
    have Leq: "L[0 := goal_loc] = L" using L0 by (cases L) (simp_all add: locations_unique)
    have ceq: "[[]\<rightarrow>0]c = c" by simp
    have trans: "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow> \<langle>L, v, c\<rangle>"
      by (rule num_non_t_step_intro[OF step0[unfolded Leq ceq] bnd]) simp
    have conds': "num_goal_state_conds (shd (shd x ## num_goal_run (shd x)))"
      using conds_x by simp
    have ctr': "shd x ## (num_goal_run (shd x)) = num_goal_run (shd ((shd x) ## (num_goal_run (shd x))))"
      using num_goal_run.ctr stream.sel by simp
    show ?case
      apply (intro exI conjI)
        apply (rule ctr)
       apply (subst Lvc)+
      unfolding prod.case
      using trans ctr' conds' by simp+
  qed
qed

text \<open>The numeric-net completeness assembly, mirroring @{thm [source] valid_plan_imp_form_holds}:
from a valid numeric state sequence, the strengthened @{thm [source] num_plan_steps_possible} yields a
plan prefix ending at @{const num_goal_trans_pre} with @{const num_LvP} preserved; @{thm [source]
num_final_step_possible} appends the goal edge to a @{const num_goal_state_conds} config; and the
@{const num_goal_run} self-loop extends it to an infinite run whose goal location satisfies @{const
reach_formula}.\<close>
lemma num_valid_state_seq_imp_form_holds:
  assumes vss:  "num_plan.num_rat_impl.num_valid_state_sequence M"
      and m0:   "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
      and goalsat: "sat_comps (snd (M (length planning_sem.htpl))) (set num_goal)"
      and goalok:  "\<forall>c \<in> set num_goal. comp_ok (snd (M (length planning_sem.htpl))) c"
  shows "num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula"
proof -
  \<comment> \<open>The init edge from @{const num_a\<^sub>0} to the post-init config @{term cfg1}.\<close>
  obtain cfg1 where
      init_steps: "num_graph_impl.steps [num_a\<^sub>0, cfg1]"
    and lvp1: "num_LvP cfg1"
    and pres1: "num_init_planning_state_props' M cfg1"
    using num_initial_step_possible[OF vss m0] by blast
  \<comment> \<open>The plan prefix from @{term cfg1} to a @{const num_goal_trans_pre} config.\<close>
  obtain ms where
      plan_steps: "num_graph_impl.steps (cfg1 # ms)"
    and gtp_last: "num_goal_trans_pre M (last (cfg1 # ms))"
    and lvp_last: "num_LvP (last (cfg1 # ms))"
    using num_plan_steps_possible[OF vss m0 lvp1 pres1] by blast
  \<comment> \<open>The final goal edge to a @{const num_goal_state_conds} config @{term cfg'}.\<close>
  obtain cfg' where
      final_steps: "num_graph_impl.steps [last (cfg1 # ms), cfg']"
    and gsc: "num_goal_state_conds cfg'"
    using num_final_step_possible[OF gtp_last lvp_last goalsat goalok] by blast
  \<comment> \<open>Concatenate the three step lists into a single plan prefix.\<close>
  have steps01: "num_graph_impl.steps (num_a\<^sub>0 # cfg1 # ms)"
    using num_graph_impl.steps_append[OF init_steps plan_steps] by simp
  have last01: "last (num_a\<^sub>0 # cfg1 # ms) = last (cfg1 # ms)" by simp
  define stepsL where "stepsL = num_a\<^sub>0 # cfg1 # ms @ [cfg']"
  have stepsL_eq: "stepsL = (num_a\<^sub>0 # cfg1 # ms) @ [cfg']"
    unfolding stepsL_def by simp
  have steps_all: "num_graph_impl.steps stepsL"
    unfolding stepsL_eq
    using num_graph_impl.steps_append[OF steps01 final_steps[unfolded last01[symmetric]]] by simp
  have last_all: "last stepsL = cfg'" unfolding stepsL_def by simp
  have stepsL_not_Nil: "stepsL \<noteq> []" unfolding stepsL_def by simp
  \<comment> \<open>The infinite run: the plan prefix followed by the goal self-loop.\<close>
  have run: "num_graph_impl.run (stepsL @- num_goal_run cfg')"
  proof (rule num_graph_impl.extend_run')
    show "num_graph_impl.steps stepsL" using steps_all .
    show "num_graph_impl.run (num_goal_run cfg')" using num_goal_run_is_run[OF gsc] .
    show "last stepsL = shd (num_goal_run cfg')" using last_all num_goal_run.simps(1) by simp
    show "stepsL @- stl (num_goal_run cfg') = stepsL @- num_goal_run cfg'"
      using num_goal_run.sel(2) by simp
  qed
  have run_alt: "num_a\<^sub>0 ## (stl (stepsL @- num_goal_run cfg')) = stepsL @- num_goal_run cfg'"
    apply (subst shift_simps(2))
    apply (subst if_not_P)
     apply (rule stepsL_not_Nil)
    apply (subst shift.simps(2)[symmetric])
    using stepsL_def by simp
  hence run': "num_graph_impl.run (num_a\<^sub>0 ## (stl (stepsL @- num_goal_run cfg')))"
    using run by simp
  \<comment> \<open>The goal location holds at the reached goal config.\<close>
  have form_holds: "holds (\<lambda>(L, v, _). check_sexp (sexp.loc 0 goal_loc) L (the \<circ> v)) (num_goal_run cfg')"
  proof -
    obtain L v c where Lvc: "shd (num_goal_run cfg') = (L, v, c)"
      using prod_cases3 by blast
    hence "cfg' = (L, v, c)" using num_goal_run.simps(1) by simp
    hence "num_goal_state_conds (L, v, c)" using gsc by simp
    hence "L ! 0 = goal_loc" using num_goal_state_condsE by force
    hence "check_sexp (sexp.loc 0 goal_loc) L (the \<circ> v)" by auto
    thus ?thesis unfolding holds.simps Lvc by simp
  qed
  show ?thesis
    unfolding reach_formula_def
    unfolding models_def
    unfolding formula.case
    unfolding num_graph_impl.Ex_ev_def
    unfolding Sequence_LTL.ev_alt_def
    using run' run_alt form_holds by blast
qed

text \<open>The hypothesis-free numeric completeness capstone: the numeric net's Munta semantics reaches
the goal formula from the pre-init config @{const num_a\<^sub>0}. Every hypothesis of
@{thm [source] num_valid_state_seq_imp_form_holds} is discharged from the locale's own assumptions --
the numeric plan validity @{thm [source] num_valid} witnesses the state sequence @{term M} (giving
@{text vss}, @{text m0}, @{text goalsat} after the @{thm [source] rat_impl_htpl_eq} bridge), and
the goal comparisons are @{const comp_ok} at the integer-valued final valuation by
@{thm [source] num_goal_comp_ok} (its @{const num_val_ok} premise from the reachability invariant
@{thm [source] num_seq_val_ok}).\<close>
lemma num_valid_plan_imp_form_holds:
  "num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula"
proof -
  obtain M where
      vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
    and m0: "snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)"
    and gsat: "sat_comps (snd (M (length rat_impl.htpl))) (set num_goal)"
    using num_valid unfolding num_plan.num_rat_impl.num_valid_plan_def by blast
  have goalsat: "sat_comps (snd (M (length planning_sem.htpl))) (set num_goal)"
    using gsat unfolding rat_impl_htpl_eq .
  have vok: "num_val_ok (snd (M (length planning_sem.htpl)))"
    by (rule num_seq_val_ok[OF vss m0 order.refl])
  have goalok: "\<forall>c \<in> set num_goal. comp_ok (snd (M (length planning_sem.htpl))) c"
    by (rule num_goal_comp_ok[OF vok])
  show ?thesis by (rule num_valid_state_seq_imp_form_holds[OF vss m0 goalsat goalok])
qed


end
end

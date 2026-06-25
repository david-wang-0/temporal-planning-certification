theory TP_NTA_Reduction_Correctness_Numeric_StepInfra
  imports TP_NTA_Reduction_Correctness_Numeric_Tracking
begin

context numeric_tp_nta_reduction_correctness
begin

subsection \<open>Numeric network step infrastructure (mirroring the propositional Edges layer)\<close>

text \<open>The numeric automata carry no committed locations and no location invariants -- @{const
augment_edge} only conjoins a guard and appends updates -- so the structural facts the @{text
num_net_impl} step relation needs mirror the propositional @{text no_committed}/@{text no_invs}/@{text
step_t_possible} on @{const num_timed_automaton_net}. @{thm [source] conv_trans} and @{thm [source]
conv_committed} are already stated generically over the automata list, so they apply to the numeric
net unchanged.\<close>

lemma num_no_committed:
  assumes "p < length num_timed_automaton_net"
  shows "committed (map automaton_of num_timed_automaton_net ! p) = {}"
  using assms
  unfolding num_timed_automaton_net_def automaton_of_def committed_def num_main_auto_def Let_def
    num_action_to_automaton_def
  apply (cases p)
  by simp+

lemma num_no_invs': assumes "p < length num_timed_automaton_net"
  shows "inv (automaton_of (num_timed_automaton_net ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding num_timed_automaton_net_def Let_def prod.case
    by simp+
  show ?thesis
    unfolding num_timed_automaton_net_def Let_def prod.case
  unfolding num_main_auto_def Let_def num_action_to_automaton_def
  unfolding comp_apply
  unfolding inv_def
  apply (cases p)
   apply simp
   apply (subst automaton_of_def)
   apply (subst prod.case)+
   apply (subst snd_conv)+
   apply (subst default_map_of_def) apply simp
  subgoal for p'
    apply (rule ssubst[of p])
     apply assumption
    apply (subst nth_Cons_Suc)
    apply (drule 1)
    apply (subst nth_map)
     apply assumption
    unfolding automaton_of_def prod.case snd_conv
    apply (subst default_map_of_def)
    by simp
  done
qed

lemma num_conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of num_timed_automaton_net ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "num_timed_automaton_net ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(num_timed_automaton_net ! p)"])
    apply (subst comp_apply)
    apply (subst conv_automaton_def)
    apply (subst prod.case)+
    apply (subst automaton_of_def)
    apply (subst prod.case)+
    apply (subst snd_conv)+
    apply (subst automaton_of_def)
    apply (subst prod.case)+
    apply (subst snd_conv)+
    apply (induction d)
     apply (subst list.map)
    unfolding default_map_of_def
     apply simp
    subgoal for d ds
      apply (induction d)
      subgoal for i c
        apply (rule ext)
        subgoal for x
          apply (subst list.map)
          apply (subst prod.case)+
          unfolding map_of_Cons_code
          apply (subst map_default_def)+
          apply (cases "i = x")
           apply (subst if_P, assumption)+
           apply simp
          apply (subst if_not_P, assumption)+
          apply (subst (asm) map_default_def)
          apply (rule subst[of "FinFun.map_default [] (map_of (map (\<lambda>(s, cc). (s, map conv_ac cc)) ds)) x" "map conv_ac (case map_of ds x of None \<Rightarrow> [] | Some b' \<Rightarrow> b')"])
           apply simp
          apply (subst map_default_def)
          by blast
        done
      done
    done
  done

lemma num_no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)"
  shows "inv (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net ! p) = (\<lambda>x. [])"
  apply (subst num_conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using num_no_invs'
  apply (subst num_no_invs')
  using assms by auto

text \<open>A delay step of length 0 is always available (no invariants to block it), and the
single-step/internal-step intros for the numeric graph -- the numeric counterparts of @{text
step_t_possible} / @{text single_step_intro} / @{text non_t_step_intro}.\<close>
lemma num_step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of num_net_bounds) y"
  shows "num_net_impl.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding num_net_impl.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using num_no_invs by auto
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by auto
  done

lemmas num_single_step_intro = num_graph_impl.steps.Cons[OF _ num_graph_impl.steps.Single]
lemmas num_non_t_step_intro = num_step_t_possible[THEN step_u'.intros, rotated, rotated]

text \<open>Per-automaton transition/urgency characterisations of the numeric net, the inputs to a
@{text step_u.step_int} edge-firing (mirroring @{thm [source] main_auto_trans} / @{thm [source]
action_auto_urg}; action-automaton transitions are reached via the generic @{thm [source] conv_trans}
at the action's index, then @{text num_action_auto_trans}).\<close>
schematic_goal num_main_auto_trans:
  shows "trans (automaton_of (num_timed_automaton_net ! 0)) = ?x"
  apply (subst num_timed_automaton_net_def)
  apply (subst nth_Cons_0)
  unfolding num_main_auto_def Let_def comp_def snd_conv trans_def automaton_of_def
    prod.case fst_conv list.set ..

schematic_goal num_action_auto_trans:
  shows "trans (automaton_of (num_action_to_automaton a)) = ?x"
  unfolding num_action_to_automaton_def Let_def comp_def snd_conv trans_def automaton_of_def
    prod.case fst_conv list.set ..

schematic_goal num_action_auto_urg:
  shows "urgent ((automaton_of \<circ> conv_automaton) (num_action_to_automaton a)) = ?x"
  unfolding urgent_def num_action_to_automaton_def Let_def comp_apply fst_conv snd_conv
    conv_automaton_def prod.case automaton_of_def list.set ..

text \<open>The numeric edge-effect config transformers reuse the @{emph \<open>generic\<close>} @{const edge_effect}
(it applies an edge's updates/location/reset, with no guard check) at the @{const augment_edge}'d
edges, so each fires the propositional @{emph \<open>and\<close>} the numeric updates. The duration edge
@{const edge_3} and the instant edge @{const instant_trans_edge} carry no numeric data, so their
propositional effects @{const edge_3_effect} / @{const instant_trans_edge_effect} are reused unchanged.\<close>
definition "num_start_edge_effect n = edge_effect (Suc n) (num_start_edge (actions ! n))"
definition "num_end_edge_effect n = edge_effect (Suc n) (num_end_edge (actions ! n))"
definition "num_edge_2_effect n = edge_effect (Suc n) (num_edge_2 (actions ! n))"
definition "num_main_auto_init_edge_effect = edge_effect 0 num_main_auto_init_edge"
definition "num_main_auto_goal_edge_effect = edge_effect 0 num_main_auto_goal_edge"

text \<open>@{const augment_edge} only conjoins a guard and appends numeric updates -- it keeps the target
location and the clock resets -- so applying it via @{const edge_effect} yields the @{emph \<open>same\<close>}
location and clock valuation as the un-augmented edge; only the variable store differs (by the appended
numeric updates, which touch the fresh fluent variables). These two generic facts are load-bearing for
the run-lifting: the numeric run's locations and clocks coincide with the propositional run's.\<close>
lemma edge_effect_augment_loc:
  "fst (edge_effect n (augment_edge gn fn e) Lvc) = fst (edge_effect n e Lvc)"
  by (simp add: augment_edge_def edge_effect_def Let_def case_prod_beta split: prod.splits)

lemma edge_effect_augment_clk:
  "snd (snd (edge_effect n (augment_edge gn fn e) Lvc)) = snd (snd (edge_effect n e Lvc))"
  by (simp add: augment_edge_def edge_effect_def Let_def case_prod_beta split: prod.splits)

text \<open>Per-edge corollaries: each numeric edge-effect agrees with its propositional counterpart on the
location and clock components (only the variable store -- the fluent vars -- differs).\<close>
lemmas num_edge_effect_defs =
  num_start_edge_effect_def num_end_edge_effect_def num_edge_2_effect_def
  num_main_auto_init_edge_effect_def num_main_auto_goal_edge_effect_def
  start_edge_effect_def end_edge_effect_def edge_2_effect_def
  main_auto_init_edge_effect_def main_auto_goal_edge_effect_def
  num_start_edge_def num_end_edge_def num_edge_2_def
  num_main_auto_init_edge_def num_main_auto_goal_edge_def

lemma num_start_edge_effect_loc: "fst (num_start_edge_effect n Lvc) = fst (start_edge_effect n Lvc)"
  and num_start_edge_effect_clk: "snd (snd (num_start_edge_effect n Lvc)) = snd (snd (start_edge_effect n Lvc))"
  and num_end_edge_effect_loc: "fst (num_end_edge_effect n Lvc) = fst (end_edge_effect n Lvc)"
  and num_end_edge_effect_clk: "snd (snd (num_end_edge_effect n Lvc)) = snd (snd (end_edge_effect n Lvc))"
  and num_edge_2_effect_loc: "fst (num_edge_2_effect n Lvc) = fst (edge_2_effect n Lvc)"
  and num_edge_2_effect_clk: "snd (snd (num_edge_2_effect n Lvc)) = snd (snd (edge_2_effect n Lvc))"
  and num_main_auto_init_edge_effect_loc: "fst (num_main_auto_init_edge_effect Lvc) = fst (main_auto_init_edge_effect Lvc)"
  and num_main_auto_init_edge_effect_clk: "snd (snd (num_main_auto_init_edge_effect Lvc)) = snd (snd (main_auto_init_edge_effect Lvc))"
  and num_main_auto_goal_edge_effect_loc: "fst (num_main_auto_goal_edge_effect Lvc) = fst (main_auto_goal_edge_effect Lvc)"
  and num_main_auto_goal_edge_effect_clk: "snd (snd (num_main_auto_goal_edge_effect Lvc)) = snd (snd (main_auto_goal_edge_effect Lvc))"
  by (simp_all add: num_edge_effect_defs edge_effect_augment_loc edge_effect_augment_clk)

lemma length_num_net_automata: "length num_timed_automaton_net = Suc (length actions)"
  by (simp add: num_timed_automaton_net_def)

text \<open>Monotonicity of Munta evaluation under store extension: extending the variable store (here with
the fresh fluent variables) preserves every @{const check_bexp}/@{const is_val} judgement. This is how a
propositional guard or update value transfers verbatim to the numeric store, which agrees with the
propositional one on the propositional variables and only adds fluent variables (so @{term \<open>v \<subseteq>\<^sub>m vn\<close>}).\<close>
lemma check_bexp_is_val_mono:
  shows "check_bexp v b bv \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> check_bexp v' b bv"
    and "is_val v e k \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> is_val v' e k"
proof -
  have "check_bexp v b bv \<Longrightarrow> (\<forall>v'. v \<subseteq>\<^sub>m v' \<longrightarrow> check_bexp v' b bv)"
    and "is_val v e k \<Longrightarrow> (\<forall>v'. v \<subseteq>\<^sub>m v' \<longrightarrow> is_val v' e k)"
  proof (induction rule: check_bexp_is_val.inducts)
    case (12 s x val)
    then show ?case by (auto simp: map_le_def dom_def intro: check_bexp_is_val.intros)
  qed (blast intro: check_bexp_is_val.intros)+
  thus "check_bexp v b bv \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> check_bexp v' b bv"
    and "is_val v e k \<Longrightarrow> v \<subseteq>\<^sub>m v' \<Longrightarrow> is_val v' e k"
    by blast+
qed

text \<open>A propositional update sequence lifts to any store extension: it can fire on @{term vn} (which
extends @{term v} with the fresh fluent variables), leaving the extension untouched outside the written
variables and producing a result that again extends the propositional result. This is the update-side
counterpart of @{thm [source] check_bexp_is_val_mono}, the second half of the per-step lifting glue.\<close>
lemma is_upds_map_le:
  assumes "is_upds v f v'" and "v \<subseteq>\<^sub>m vn"
  shows "\<exists>vn'. is_upds vn f vn' \<and> v' \<subseteq>\<^sub>m vn' \<and> (\<forall>x. x \<notin> fst ` set f \<longrightarrow> vn' x = vn x)"
  using assms
proof (induction f arbitrary: v vn)
  case Nil
  hence "v' = v" by (auto simp: is_upds_Nil_iff)
  thus ?case using Nil.prems(2) by (auto intro: is_upds.intros)
next
  case (Cons fe f)
  obtain x e where fe: "fe = (x, e)" by (cases fe)
  obtain v1 where v1: "is_upd v (x, e) v1" and rest: "is_upds v1 f v'"
    using Cons.prems(1) fe by (auto simp: is_upds_Cons_iff)
  obtain k where k: "is_val v e k" and v1_eq: "v1 = v(x \<mapsto> k)"
    using v1 by (auto simp: is_upd_def)
  have "is_val vn e k" by (rule check_bexp_is_val_mono(2)[OF k Cons.prems(2)])
  hence upd_vn: "is_upd vn (x, e) (vn(x \<mapsto> k))" by (auto simp: is_upd_def)
  have "v1 \<subseteq>\<^sub>m vn(x \<mapsto> k)" using Cons.prems(2) v1_eq by (auto simp: map_le_def)
  then obtain vn' where vn':
      "is_upds (vn(x \<mapsto> k)) f vn'"
      "v' \<subseteq>\<^sub>m vn'"
      "\<forall>y. y \<notin> fst ` set f \<longrightarrow> vn' y = (vn(x \<mapsto> k)) y"
    using Cons.IH[OF rest] by blast
  have "is_upds vn (fe # f) vn'" using upd_vn vn'(1) fe by (auto intro: is_upds.intros)
  moreover have "\<forall>y. y \<notin> fst ` set (fe # f) \<longrightarrow> vn' y = vn y"
    using vn'(3) fe by auto
  ultimately show ?case using vn'(2) by blast
qed

text \<open>The keystone generic per-step lifting: an internal transition of the numeric network firing any
edge of @{const num_timed_automaton_net} -- assembled directly from @{thm [source] step_u.step_int}, with
its committed/invariant side-conditions discharged by @{thm [source] num_no_committed}/@{thm [source]
num_no_invs} and the transition-membership by the generic @{thm [source] conv_trans}. The caller supplies
the augmented edge, the (combined) guard @{term \<open>check_bexp vn bg True\<close>}, the clock guard, the update
@{term \<open>is_upds vn fu vn'\<close>}, and numeric boundedness; the guard/update are split into propositional and
numeric halves at the call site (via @{thm [source] check_bexp_is_val_mono} / @{thm [source] is_upds_map_le}
and @{thm [source] check_bexp_comps_guard} / @{thm [source] is_upds_num_upd}).\<close>
lemma num_step_int_lift:
  assumes p_len: "p < length num_timed_automaton_net"
      and edge: "(l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
      and bexp: "check_bexp vn bg True"
      and guard: "c \<turnstile> conv_cc g"
      and loc: "L ! p = l"
      and L_len: "length L = length num_timed_automaton_net"
      and isupds: "is_upds vn fu vn'"
      and bounded: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    shows "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0]c\<rangle>"
proof -
  have p_len': "p < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)"
    using p_len by simp
  have conv_edge:
    "(l, bg, conv_cc g, Sil a, fu, r, l')
       \<in> trans ((map (automaton_of \<circ> conv_automaton) num_timed_automaton_net) ! p)"
    apply (subst conv_trans[OF p_len'])
    using edge by (force intro: image_eqI[where x = "(l, bg, g, Sil a, fu, r, l')"])
  have committed_empty:
    "committed (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net ! q) = {}"
    if q: "q < length num_timed_automaton_net" for q
  proof -
    have q': "q < length (map (automaton_of \<circ> conv_automaton) num_timed_automaton_net)" using q by simp
    show ?thesis using conv_committed[OF q'] num_no_committed[OF q] by simp
  qed
  show ?thesis
    unfolding num_net_impl.sem_def
    apply (rule step_u.step_int[where p = p])
    unfolding TAG_def
              apply (rule conv_edge)
             apply (rule disjI2, rule allI, rule impI)
             apply (subst committed_empty)
              apply simp
             apply simp
            apply (rule bexp)
           apply (rule guard)
          apply (rule allI, rule impI, subst num_no_invs, assumption, simp)
         apply (rule loc)
        using L_len p_len apply simp
       apply (rule HOL.refl)
      apply (rule HOL.refl)
     apply (rule isupds)
    apply (rule bounded)
    done
qed

text \<open>Inversion workhorse: invert a propositional internal Munta step to recover the fired edge,
its (combined) guard and updates. The dual of @{thm [source] num_step_int_lift} for the propositional
net: @{thm [source] step_u_elims'} peels off the @{term step_u} (@{text step_int}) premises -- the
fired edge in the @{emph \<open>conv\<close>} net, the bexp/clock guards, and the location/update side-conditions --
then @{thm [source] conv_trans} un-@{const conv_automaton}s the edge back to a plain
@{const net_automata} edge with @{term \<open>g'' = conv_cc g\<close>}.\<close>
lemma prop_int_step_invert:
  assumes "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', v', c'\<rangle>"
      and "length L = length net_automata"
  obtains p l b g f r l' where
    "p < length net_automata"
    "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    "check_bexp v b True"
    "c \<turnstile> conv_cc g"
    "L ! p = l"
    "L' = L[p := l']"
    "c' = [r\<rightarrow>0]c"
    "is_upds v f v'"
proof -
  note step = assms(1)[unfolded net_impl.sem_def]
  show thesis
    apply (rule step_u_elims'(2)[OF step])
    apply (unfold TAG_def)
    subgoal premises prems for l b g'' f r l' p
    proof -
      have plen: "p < length net_automata"
        using prems(7) assms(2) by simp
      have plen': "p < length (map (automaton_of \<circ> conv_automaton) net_automata)"
        using plen by simp
      have "(l, b, g'', Sil a, f, r, l')
              \<in> (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) `
                  trans (automaton_of (net_automata ! p))"
        using prems(1) unfolding conv_trans[OF plen'] .
      then obtain g where
          edge: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
          and g''_eq: "g'' = conv_cc g"
        by auto
      show thesis
        using plen edge prems(3) prems(4)[unfolded g''_eq] prems(6) prems(8) prems(9) prems(10)
        by (rule that)
    qed
    done
qed

text \<open>The per-step internal lift, combining @{thm [source] prop_int_step_invert} (invert the
propositional step) with the keystone @{thm [source] num_step_int_lift} (reconstruct the numeric step).
The edge-dependent numeric data is supplied by the caller through @{term num_data}: for the inverted
fired edge it must exhibit the augmented numeric edge in @{const num_timed_automaton_net}, the numeric
guard holding on the extended store @{term vn}, the appended numeric update firing to some @{term vn'}
in @{const num_net_bounds}, that @{term vn'} still extends the propositional post-store @{term v'}, and
that @{term vn'} tracks the post-step numeric valuation @{term w'} (the valuation the abstract sequence
assigns after this snap). In the run-lifting the happening index fixes the snap and @{text
num_valid_state_sequence} discharges the guard/update; the source location @{term \<open>L ! p = l\<close>} pins down
which edge fired, and @{term w'} threads the numeric valuation config-by-config.\<close>
lemma num_int_step_lift:
  assumes step: "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', v', c'\<rangle>"
      and L_len: "length L = length net_automata"
      and num_data:
        "\<And>p l b g f r l'.
           p < length net_automata \<Longrightarrow>
           (l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p)) \<Longrightarrow>
           L ! p = l \<Longrightarrow> check_bexp v b True \<Longrightarrow> is_upds v f v' \<Longrightarrow>
           \<exists>bg fu vn'.
              (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
              \<and> check_bexp vn bg True
              \<and> is_upds vn fu vn'
              \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
              \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w'"
  shows "\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', vn', c'\<rangle>
               \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w' \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
proof -
  obtain p l b g f r l' where
      P: "p < length net_automata"
    and E: "(l, b, g, Sil a, f, r, l') \<in> trans (automaton_of (net_automata ! p))"
    and B: "check_bexp v b True"
    and G: "c \<turnstile> conv_cc g"
    and LOC: "L ! p = l"
    and L'eq: "L' = L[p := l']"
    and c'eq: "c' = [r\<rightarrow>0]c"
    and U: "is_upds v f v'"
    by (rule prop_int_step_invert[OF step L_len])
  obtain bg fu vn' where
      NE: "(l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
    and NB: "check_bexp vn bg True"
    and NU: "is_upds vn fu vn'"
    and BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    and LE: "v' \<subseteq>\<^sub>m vn'"
    and TR: "num_tracks vn' w'"
    using num_data[OF P E LOC B U] by blast
  have len_eq: "length net_automata = length num_timed_automaton_net"
    by (simp add: timed_automaton_net_def num_timed_automaton_net_def)
  have plen_num: "p < length num_timed_automaton_net" using P len_eq by simp
  have Llen_num: "length L = length num_timed_automaton_net" using L_len len_eq by simp
  have "num_net_impl.sem \<turnstile> \<langle>L, vn, c\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L[p := l'], vn', [r\<rightarrow>0]c\<rangle>"
    by (rule num_step_int_lift[OF plen_num NE NB G LOC Llen_num NU BND])
  thus ?thesis using L'eq c'eq LE TR BND by blast
qed

text \<open>A Munta update sequence leaves every variable it does not write unchanged.\<close>
lemma is_upds_unchanged:
  assumes "is_upds s us s'" and "x \<notin> fst ` set us"
  shows "s' x = s x"
  using assms by (induction rule: is_upds.induct) (auto simp: is_upd_def)

text \<open>Numeric tracking survives a propositional update sequence that writes no fluent variable. The
propositional edge updates touch only propositional variables, which are disjoint from the fresh fluent
variables (@{thm [source] fluent_vars_fresh}), so the integer encodings the fluent variables carry are
untouched.\<close>
lemma num_tracks_pres_unwritten:
  assumes tr: "num_tracks vn w"
      and upd: "is_upds vn f vn'"
      and fresh: "\<And>g. g \<in> set nfluents \<Longrightarrow> fluent_to_var g \<notin> fst ` set f"
    shows "num_tracks vn' w"
proof (rule num_tracksI)
  fix g assume g: "g \<in> set nfluents"
  obtain r where r: "w g = Some r" using num_tracks_definedD[OF tr g] by blast
  have v: "vn (fluent_to_var g) = Some (const_to_int r)" by (rule num_tracks_varD[OF tr g r])
  have "vn' (fluent_to_var g) = vn (fluent_to_var g)" by (rule is_upds_unchanged[OF upd fresh[OF g]])
  thus "\<exists>r. w g = Some r \<and> vn' (fluent_to_var g) = Some (const_to_int r)" using r v by auto
qed

text \<open>Discharging the @{term num_data} provider for an edge with @{emph \<open>no numeric update\<close>}
(@{term \<open>fu = f\<close>}): the unchanged edges that appear verbatim in @{const num_timed_automaton_net}
(@{const edge_3} / @{const instant_trans_edge} / @{const main_auto_loop}) and the guard-only augmented
edges (@{const num_edge_2} / @{const num_main_auto_goal_edge}, whose @{const augment_edge} appends the
empty update list). The propositional update sequence @{term f} fires on the extended store via @{thm
[source] is_upds_map_le}, and -- writing no fluent variable -- preserves tracking by @{thm [source]
num_tracks_pres_unwritten}. The caller supplies the assembled (combined) guard
@{term \<open>check_bexp vn bg True\<close>}, the numeric edge's membership, the freshness of @{term f}, and
boundedness of the result; no abstract numeric data beyond that is consumed.\<close>
lemma num_data_no_write_edge:
  assumes le: "v \<subseteq>\<^sub>m vn"
      and tr: "num_tracks vn w"
      and num_edge: "(l, bg, g, Sil a, f, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))"
      and NB: "check_bexp vn bg True"
      and U: "is_upds v f v'"
      and fresh: "\<And>h. h \<in> set nfluents \<Longrightarrow> fluent_to_var h \<notin> fst ` set f"
      and bnd: "\<And>vn'. is_upds vn f vn' \<Longrightarrow> v' \<subseteq>\<^sub>m vn'
                 \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    shows "\<exists>bg fu vn'.
             (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
             \<and> check_bexp vn bg True \<and> is_upds vn fu vn'
             \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
             \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' w"
proof -
  obtain vn' where NU: "is_upds vn f vn'" and LE: "v' \<subseteq>\<^sub>m vn'"
    using is_upds_map_le[OF U le] by blast
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'" using bnd[OF NU LE] .
  have TR: "num_tracks vn' w" by (rule num_tracks_pres_unwritten[OF tr NU fresh])
  show ?thesis using num_edge NB NU BND LE TR by blast
qed

text \<open>Discharging the @{term num_data} provider for an edge that carries a numeric @{emph \<open>update\<close>}
(the @{const augment_edge} of a @{text start}/@{text end}/@{text init} edge, whose appended update list
is @{term \<open>num_upd s\<close>} for @{term \<open>us = upds s\<close>}). The combined update is @{term \<open>f @ num_upd s\<close>}: the
propositional half @{term f} fires on the extended store via @{thm [source] is_upds_map_le} (writing no
fluent variable, so tracking survives by @{thm [source] num_tracks_pres_unwritten}), then the numeric half
fires via @{thm [source] is_upds_num_upd}, landing on the abstract simultaneous update @{const apply_upds}
of @{term us}. The two phases compose by @{thm [source] is_upds_appendI}; @{term \<open>v' \<subseteq>\<^sub>m vn'\<close>}
survives because the fluent variables the numeric half writes are fresh for @{term v'}.\<close>
lemma num_data_upd_edge:
  assumes le: "v \<subseteq>\<^sub>m vn"
      and tr: "num_tracks vn w"
      and num_edge: "(l, bexp.and b gn, g, Sil a,
                       f @ map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) us, r, l')
                     \<in> trans (automaton_of (num_timed_automaton_net ! p))"
      and B: "check_bexp v b True"
      and gn: "check_bexp vn gn True"
      and U: "is_upds v f v'"
      and fresh: "\<And>h. h \<in> set nfluents \<Longrightarrow> fluent_to_var h \<notin> fst ` set f"
      and v'_fresh: "\<And>h. h \<in> set nfluents \<Longrightarrow> fluent_to_var h \<notin> dom v'"
      and fn_func: "upds_functional_list us"
      and fn_ncr: "upds_no_cross_read_list us"
      and fn_ok: "\<And>fl e. (fl, e) \<in> set us \<Longrightarrow> fl \<in> set nfluents \<and> nexp_ok w e"
      and bnd: "\<And>vn'. v' \<subseteq>\<^sub>m vn' \<Longrightarrow> num_tracks vn' (apply_upds (set us) w)
                  \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    shows "\<exists>bg fu vn'.
             (l, bg, g, Sil a, fu, r, l') \<in> trans (automaton_of (num_timed_automaton_net ! p))
             \<and> check_bexp vn bg True \<and> is_upds vn fu vn'
             \<and> Simple_Network_Language.bounded (map_of num_net_bounds) vn'
             \<and> v' \<subseteq>\<^sub>m vn' \<and> num_tracks vn' (apply_upds (set us) w)"
proof -
  let ?fn = "map (\<lambda>(fl,e). (fluent_to_var fl, nexp_to_exp fluent_to_var const_to_int e)) us"
  \<comment> \<open>Combined guard fires on @{term vn}.\<close>
  have bvn: "check_bexp vn b True" by (rule check_bexp_is_val_mono(1)[OF B le])
  have NB: "check_bexp vn (bexp.and b gn) True"
    using check_bexp_is_val.intros(3)[OF bvn gn] by simp
  \<comment> \<open>Propositional updates fire on @{term vn}, preserving tracking.\<close>
  obtain vn_mid where
      NUmid: "is_upds vn f vn_mid"
    and LEmid: "v' \<subseteq>\<^sub>m vn_mid"
    and OFFmid: "\<And>x. x \<notin> fst ` set f \<Longrightarrow> vn_mid x = vn x"
    using is_upds_map_le[OF U le] by blast
  have TRmid: "num_tracks vn_mid w" by (rule num_tracks_pres_unwritten[OF tr NUmid fresh])
  \<comment> \<open>Numeric updates fire on @{term vn_mid}.\<close>
  obtain vn' where
      NUnum: "is_upds vn_mid ?fn vn'"
    and TRnum: "num_tracks vn' (apply_upds (set us) w)"
    and OFFnum: "\<And>x. x \<notin> fluent_to_var ` fst ` set us \<Longrightarrow> vn' x = vn_mid x"
    using is_upds_num_upd[OF TRmid fn_func fn_ncr fn_ok] by metis
  \<comment> \<open>Compose the two update phases.\<close>
  have NU: "is_upds vn (f @ ?fn) vn'" by (rule is_upds_appendI[OF NUmid NUnum])
  \<comment> \<open>@{term v'} survives: the numeric half writes only fresh fluent variables.\<close>
  have LE: "v' \<subseteq>\<^sub>m vn'"
  proof (unfold map_le_def, intro ballI)
    fix x assume xdom: "x \<in> dom v'"
    have "x \<notin> fluent_to_var ` fst ` set us"
    proof
      assume "x \<in> fluent_to_var ` fst ` set us"
      then obtain fl where xfl: "x = fluent_to_var fl" and flmem: "fl \<in> fst ` set us" by auto
      obtain e where "(fl, e) \<in> set us" using flmem by auto
      hence "fl \<in> set nfluents" using fn_ok by blast
      hence "fluent_to_var fl \<notin> dom v'" by (rule v'_fresh)
      thus False using xfl xdom by simp
    qed
    hence "vn' x = vn_mid x" by (rule OFFnum)
    moreover have "v' x = vn_mid x" using LEmid xdom by (auto simp: map_le_def)
    ultimately show "v' x = vn' x" by simp
  qed
  \<comment> \<open>Boundedness from the caller's provider.\<close>
  have BND: "Simple_Network_Language.bounded (map_of num_net_bounds) vn'"
    using bnd[OF LE TRnum] .
  show ?thesis using num_edge NB NU BND LE TRnum by blast
qed

subsection \<open>Numeric guards depend only on the fluents they read (the non-interference foundation)\<close>

text \<open>A comparison's truth depends only on the values at the fluents it reads (@{const comp_fluents}) --
@{thm [source] eval_nexp_cong} lifted to @{const sat_comp}. This is the foundation of the intra-happening
non-interference argument for the run-lifting: a snap's guard, evaluated against the @{emph \<open>partially
updated\<close>} valuation reached after earlier co-occurring snaps fire, still agrees with its value at the
pre-happening valuation, because those snaps write only fluents the guard does not read (numeric
non-interference, @{term num_mutex_snap_action}). NB these are general facts about @{const sat_comp};
they belong in the abstract @{theory_text Temporal_Plans} layer and should move there in the refactor.\<close>
lemma sat_comp_cong:
  assumes "\<And>f. f \<in> comp_fluents c \<Longrightarrow> w f = w' f"
  shows "sat_comp w c = sat_comp w' c"
proof (cases c)
  case (Comp p a b)
  have ea: "eval_nexp w a = eval_nexp w' a" by (rule eval_nexp_cong) (use assms Comp in auto)
  have eb: "eval_nexp w b = eval_nexp w' b" by (rule eval_nexp_cong) (use assms Comp in auto)
  show ?thesis unfolding sat_comp_def Comp by (simp only: comp.case ea eb)
qed

lemma sat_comps_cong:
  assumes "\<And>c f. c \<in> C \<Longrightarrow> f \<in> comp_fluents c \<Longrightarrow> w f = w' f"
  shows "sat_comps w C = sat_comps w' C"
proof -
  have "sat_comp w c = sat_comp w' c" if "c \<in> C" for c
    by (rule sat_comp_cong) (use assms that in blast)
  thus ?thesis unfolding sat_comps_def by blast
qed

text \<open>The set-level happening update agrees with the pre-happening valuation off the fluents the
happening writes: if @{term f} is written by no snap in the (functional, pairwise-non-interfering)
happening @{term S}, then applying @{term S}'s simultaneous numeric update leaves @{term f} unchanged.
Finite induction on @{term S} via the @{thm [source] num_plan.num_rat_impl.happening_num_update_set_insert}
recursion (each step peels one snap and the residual reads the running valuation, so @{term w} is
generalised); each peeled snap @{term a} leaves @{term f} alone by
@{thm [source] num_plan.num_rat_impl.snap_num_update_unwritten}.\<close>
lemma happening_num_update_set_unwritten:
  assumes fin: "finite S"
      and func: "\<And>x. x \<in> S \<Longrightarrow> upds_functional ((set \<circ> upds) x)"
      and noint: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      and unwr: "f \<notin> (\<Union>s\<in>S. num_plan.num_rat_impl.snap_writes s)"
    shows "num_plan.num_rat_impl.happening_num_update_set S w f = w f"
  using fin func noint unwr
proof (induction arbitrary: w rule: finite_induct)
  case empty
  show ?case by (simp add: num_plan.num_rat_impl.happening_num_update_set_empty[unfolded comp_def])
next
  case (insert a S)
  have fa: "f \<notin> num_plan.num_rat_impl.snap_writes a"
   and fS: "f \<notin> (\<Union>s\<in>S. num_plan.num_rat_impl.snap_writes s)"
    using insert.prems(3) by (auto simp: comp_def)
  have ins: "num_plan.num_rat_impl.happening_num_update_set (insert a S) w
               = num_plan.num_rat_impl.happening_num_update_set S (num_plan.num_rat_impl.snap_num_update a w)"
    by (rule num_plan.num_rat_impl.happening_num_update_set_insert[OF insert.hyps(1,2) insert.prems(1,2)])
  have step: "num_plan.num_rat_impl.happening_num_update_set S (num_plan.num_rat_impl.snap_num_update a w) f
                = num_plan.num_rat_impl.snap_num_update a w f"
    by (rule insert.IH) (use insert.prems(1,2) fS in \<open>auto simp: comp_def\<close>)
  have "num_plan.num_rat_impl.snap_num_update a w f = w f"
    by (rule num_plan.num_rat_impl.snap_num_update_unwritten[OF fa])
  thus ?case using ins step by (simp add: comp_def)
qed

text \<open>The set-level happening update equals the list-level fold over any @{emph \<open>distinct\<close>}
enumeration of the happening, under the functional + pairwise-non-interference side conditions:
@{const Finite_Set.fold} collapses to a @{const fold} on a distinct list whose snaps pairwise commute.
This is the bridge that lets the run-order fold of the numeric edge updates (a list) be identified with
@{const num_plan.num_rat_impl.happening_num_update_set} (the order-independent set update that
@{const num_plan.num_rat_impl.num_valid_state_sequence} pins to @{term \<open>snd (M (Suc i))\<close>}).\<close>
lemma happening_num_update_set_eq_fold_list:
  assumes "distinct xs"
      and "\<And>a. a \<in> set xs \<Longrightarrow> upds_functional ((set \<circ> upds) a)"
      and "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action a b"
    shows "num_plan.num_rat_impl.happening_num_update_set (set xs) w = num_plan.num_rat_impl.happening_num_update xs w"
  using assms
proof (induction xs arbitrary: w)
  case Nil
  show ?case
    by (simp add: num_plan.num_rat_impl.happening_num_update_set_empty[unfolded comp_def]
                  num_plan.num_rat_impl.happening_num_update_Nil[unfolded comp_def])
next
  case (Cons x xs)
  have "num_plan.num_rat_impl.happening_num_update_set (insert x (set xs)) w
          = num_plan.num_rat_impl.happening_num_update_set (set xs) (num_plan.num_rat_impl.snap_num_update x w)"
    by (rule num_plan.num_rat_impl.happening_num_update_set_insert)
       (use Cons.prems in \<open>auto simp: comp_def\<close>)
  also have "\<dots> = num_plan.num_rat_impl.happening_num_update xs (num_plan.num_rat_impl.snap_num_update x w)"
    using Cons.IH Cons.prems by (auto simp: comp_def)
  also have "\<dots> = num_plan.num_rat_impl.happening_num_update (x # xs) w"
    by (simp add: num_plan.num_rat_impl.happening_num_update_Cons)
  finally show ?case by (simp add: comp_def)
qed

text \<open>FACT-1 of the numeric run-lift: re-express a single happening as a union over action
@{emph \<open>indices\<close>}. The abstract @{thm [source] planning_sem.happ_at_is_union_of_starting_ending_instant}
splits the happening into instant/ending/starting snap sets; regrouping the @{term at_start} and
@{term at_end} images and converting each @{term \<open>{a \<in> set actions. P a}\<close>} to its index form via
@{thm [source] set_conv_nth} (folding the @{term is_starting_index} / @{term is_ending_index} /
@{term is_instant_index} abbreviations) yields the index-indexed shape the run-order list consumes:
the at-start snaps of the starting-or-instant indices, unioned with the at-end snaps of the
ending-or-instant indices. Stated for an arbitrary time @{term t}; instantiate @{term \<open>t = planning_sem.time_index i\<close>}
for the @{term i}-th happening.\<close>
lemma happ_at_index_decomp:
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

text \<open>S-property export (1): the @{term i}-th happening is finite. The whole happening sequence
@{const planning_sem.plan_happ_seq} is finite for a finite plan (@{thm [source]
planning_sem.finite_happ_seq}), and a single happening is the @{term snd}-image of the slice of
@{const planning_sem.plan_happ_seq} at @{term \<open>planning_sem.time_index i\<close>}.\<close>
lemma happening_finite:
  "finite (planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i))"
proof -
  have "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)
          = snd ` {p \<in> planning_sem.plan_happ_seq. fst p = planning_sem.time_index i}"
    by (force simp: image_iff)
  thus ?thesis by (simp add: planning_sem.finite_happ_seq)
qed

text \<open>S-property export (2): every snap in a happening has a functional update set. By
@{thm [source] happ_at_index_decomp} each snap is @{term \<open>at_start (actions ! j)\<close>} or
@{term \<open>at_end (actions ! j)\<close>} for some @{term \<open>j < length actions\<close>}, hence applied to an action in
@{term \<open>set actions\<close>}; the locale's @{thm [source] upds_functional_start} /
@{thm [source] upds_functional_end} give @{const upds_functional_list} of its updates, which
@{thm [source] upds_functional_set} lifts to @{const upds_functional} on the @{term set}.\<close>
lemma happening_upds_functional:
  assumes "s \<in> planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  shows "upds_functional ((set \<circ> upds) s)"
proof -
  have "s \<in> at_start ` { actions ! j | j. j < length actions
                            \<and> (is_starting_index (planning_sem.time_index i) j
                               \<or> is_instant_index (planning_sem.time_index i) j) }
          \<union> at_end ` { actions ! j | j. j < length actions
                          \<and> (is_ending_index (planning_sem.time_index i) j
                             \<or> is_instant_index (planning_sem.time_index i) j) }"
    using assms by (simp only: happ_at_index_decomp)
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
      using starting by (simp add: upds_functional_set upds_functional_list_def)
  next
    case ending
    hence "actions ! j \<in> set actions" by simp
    hence "upds_functional_list (upds (at_end (actions ! j)))"
      using upds_functional_end by blast
    thus ?thesis
      using ending by (simp add: upds_functional_set upds_functional_list_def)
  qed
qed

text \<open>The numeric mutex-validity of the plan is one conjunct of the numeric plan validity carried by
the @{thm [source] num_valid} locale assumption.\<close>
lemma num_mutex_valid_plan: "num_plan.num_rat_impl.num_mutex_valid_plan"
  using num_valid unfolding num_plan.num_rat_impl.num_valid_plan_def by blast

text \<open>S-property export (3): two distinct snaps that co-occur in one happening do not numerically
interfere. Both snaps live at the same time @{term \<open>planning_sem.time_index i\<close>}; unfolding
@{const planning_sem.plan_happ_seq} exposes their plan-entry witnesses in @{term \<open>ran \<pi>_sem\<close>}, lifted
to @{term \<open>dom \<pi>_sem\<close>}. From two @{emph \<open>distinct\<close>} plan entries, the first conjunct of
@{const num_plan.num_rat_impl.num_mutex_valid_plan} applies at equal times (\<epsilon>-distance @{term 0});
from the @{emph \<open>same\<close>} entry the two distinct co-occurring snaps must be the start/end pair of an
instantaneous (@{term \<open>d = 0\<close>}) action, discharged by its instant-action clause.
NB the numeric @{term num_mutex_snap_action} machinery resolves through @{text num_plan.num_rat_impl},
but the happening sequence is the shared @{const planning_sem.plan_happ_seq} (both interpretations are
instantiated at the same @{term \<open>\<pi>_sem\<close>} / @{term \<open>rat_of_int \<epsilon>\<close>}).\<close>
lemma happening_num_noninterfere:
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
  note nmvp = num_mutex_valid_plan[unfolded num_plan.num_rat_impl.num_mutex_valid_plan_def, folded \<pi>_sem_def]
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

text \<open>Bridge: the rat-level @{text rat_impl} interpretation (the ancestor that
@{const num_plan.num_rat_impl.num_valid_state_sequence} unfolds into) and the propositional
@{text planning_sem} interpretation are instantiated with the SAME plan -- @{text rat_impl}'s plan
@{term \<open>map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ> \<pi>\<close>} is exactly @{const \<pi>_sem} --
so all plan-derived constants (@{const planning_sem.htps}/@{const planning_sem.htpl}/
@{const planning_sem.time_index}/@{const planning_sem.plan_happ_seq}) coincide across the two. This lets
the @{const num_plan.num_rat_impl.num_valid_state_sequence} fold-conjunct (stated over @{text rat_impl}'s
happening) feed the @{text planning_sem}-keyed S-property exports.\<close>
lemma rat_impl_plan_happ_seq_eq: "rat_impl.plan_happ_seq = planning_sem.plan_happ_seq"
  unfolding rat_impl.plan_happ_seq_def planning_sem.plan_happ_seq_def \<pi>_sem_def by simp

lemma rat_impl_htps_eq: "rat_impl.htps = planning_sem.htps"
  unfolding rat_impl.htps_def planning_sem.htps_def \<pi>_sem_def by simp

lemma rat_impl_htpl_eq: "rat_impl.htpl = planning_sem.htpl"
  by (simp add: rat_impl.htpl_def planning_sem.htpl_def rat_impl_htps_eq)

lemma rat_impl_time_index_eq: "rat_impl.time_index = planning_sem.time_index"
  by (simp add: rat_impl.time_index_def planning_sem.time_index_def rat_impl_htpl_eq)

lemma rat_impl_happ_at_eq:
  "planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)
     = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  by (simp add: rat_impl_plan_happ_seq_eq rat_impl_time_index_eq)

text \<open>Item 3 (the heart of Part 1): the run-order list fold of the numeric snap updates over ANY distinct
enumeration @{term xs} of the @{term i}-th happening equals the abstract after-valuation
@{term \<open>snd (M (Suc i))\<close>}. The happening's snaps pairwise commute
(@{thm [source] happening_num_noninterfere}), so FACT-2 (@{thm [source] happening_num_update_set_eq_fold_list})
collapses the order-dependent list fold to the order-independent set update
@{const num_plan.num_rat_impl.happening_num_update_set}, which
@{const num_plan.num_rat_impl.num_valid_state_sequence} pins to @{term \<open>snd (M (Suc i))\<close>} (after the
@{thm [source] rat_impl_happ_at_eq} namespace bridge).\<close>
lemma run_order_fold_eq_happening_num_update_set:
  assumes i: "i < length planning_sem.htpl"
      and vss: "num_plan.num_rat_impl.num_valid_state_sequence M"
      and dist: "distinct xs"
      and setxs: "set xs = planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
    shows "num_plan.num_rat_impl.happening_num_update xs (snd (M i)) = snd (M (Suc i))"
proof -
  let ?S = "planning_sem.happ_at planning_sem.plan_happ_seq (planning_sem.time_index i)"
  have fold_eq: "num_plan.num_rat_impl.happening_num_update_set (set xs) (snd (M i))
                   = num_plan.num_rat_impl.happening_num_update xs (snd (M i))"
  proof (rule happening_num_update_set_eq_fold_list[OF dist])
    show "upds_functional ((set \<circ> upds) a)" if "a \<in> set xs" for a
    proof -
      have "a \<in> ?S" using that setxs by simp
      thus ?thesis by (rule happening_upds_functional)
    qed
  next
    show "\<not> num_plan.num_rat_impl.num_mutex_snap_action a b"
      if "a \<in> set xs" "b \<in> set xs" "a \<noteq> b" for a b
    proof -
      have "a \<in> ?S" and "b \<in> ?S" using that setxs by simp_all
      thus ?thesis using that(3) by (rule happening_num_noninterfere)
    qed
  qed
  have iH: "i < length rat_impl.htpl" using i by (simp add: rat_impl_htpl_eq)
  have vss_i: "num_plan.num_rat_impl.happening_num_update_set ?S (snd (M i)) = snd (M (Suc i))"
  proof -
    have "num_plan.num_rat_impl.happening_num_update_set
            (planning_sem.happ_at rat_impl.plan_happ_seq (rat_impl.time_index i)) (snd (M i))
          = snd (M (Suc i))"
      using vss iH unfolding num_plan.num_rat_impl.num_valid_state_sequence_def Let_def by blast
    thus ?thesis by (simp add: rat_impl_happ_at_eq)
  qed
  have "num_plan.num_rat_impl.happening_num_update xs (snd (M i))
          = num_plan.num_rat_impl.happening_num_update_set (set xs) (snd (M i))"
    by (rule fold_eq[symmetric])
  also have "\<dots> = num_plan.num_rat_impl.happening_num_update_set ?S (snd (M i))"
    by (simp only: setxs)
  also have "\<dots> = snd (M (Suc i))" by (rule vss_i)
  finally show ?thesis .
qed

text \<open>Guard invariance under a partial happening update by non-interfering snaps -- the heart of the
intra-happening numeric content. If a guard set @{term C} reads only fluents of @{term s} (its read
fluents lie in @{term \<open>snap_reads s\<close>}) and every snap in the co-occurring happening @{term S} does
@{emph \<open>not\<close>} numerically interfere with @{term s} (@{term \<open>\<not> num_mutex_snap_action s s'\<close>}), then
@{term S}'s simultaneous numeric update misses every fluent the guard reads, so the guard holds at the
partially-updated valuation @{term \<open>happening_num_update_set S w\<close>} iff it held at the pre-happening
@{term w}. Hence checking an intra-happening Munta guard at the running (partially-updated) store agrees
with the abstract guard at the pre-happening valuation. Proof: @{thm [source] sat_comps_cong} reduces to
the per-read-fluent agreement, and non-interference (third disjunct of
@{thm [source] num_plan.num_rat_impl.num_mutex_snap_action_def}) puts each read fluent outside @{term S}'s
writes, so @{thm [source] happening_num_update_set_unwritten} leaves it fixed.\<close>
lemma sat_comps_happening_num_update_set:
  assumes fin: "finite S"
      and func: "\<And>x. x \<in> S \<Longrightarrow> upds_functional ((set \<circ> upds) x)"
      and noint: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action x y"
      and sint: "\<And>s'. s' \<in> S \<Longrightarrow> \<not> num_plan.num_rat_impl.num_mutex_snap_action s s'"
      and rd: "(\<Union>c\<in>C. comp_fluents c) \<subseteq> num_plan.num_rat_impl.snap_reads s"
    shows "sat_comps (num_plan.num_rat_impl.happening_num_update_set S w) C = sat_comps w C"
proof (rule sat_comps_cong)
  fix c f assume c: "c \<in> C" and f: "f \<in> comp_fluents c"
  have fr: "f \<in> num_plan.num_rat_impl.snap_reads s" using rd c f by blast
  have notin: "f \<notin> (\<Union>s'\<in>S. num_plan.num_rat_impl.snap_writes s')"
  proof
    assume "f \<in> (\<Union>s'\<in>S. num_plan.num_rat_impl.snap_writes s')"
    then obtain s' where s': "s' \<in> S"
      and fw: "f \<in> num_plan.num_rat_impl.snap_writes s'" by blast
    have "num_plan.num_rat_impl.snap_writes s' \<inter> num_plan.num_rat_impl.snap_reads s = {}"
      using sint[OF s'] unfolding num_plan.num_rat_impl.num_mutex_snap_action_def by blast
    thus False using fw fr by blast
  qed
  show "num_plan.num_rat_impl.happening_num_update_set S w f = w f"
    by (rule happening_num_update_set_unwritten[OF fin func noint notin])
qed

subsection \<open>Numeric delay primitives for the run-lifting\<close>

text \<open>Head-replacement for the numeric graph (the numeric mirror of @{thm [source] steps_replace_Cons_hd}):
a one-step run @{term \<open>[x, hd ys]\<close>} and a run @{term \<open>y # ys\<close>} splice to a run @{term \<open>x # ys\<close>}. Pure
@{locale Graph_Defs} plumbing on @{const num_graph_impl.steps}, identical to the propositional proof.\<close>
lemma num_steps_replace_Cons_hd:
  assumes "num_graph_impl.steps [x, hd ys]"
          "num_graph_impl.steps (y # ys)"
    shows "num_graph_impl.steps (x # ys)"
proof (cases ys)
  case Nil
  then show ?thesis using assms(1) by blast
next
  case (Cons a list)
  hence 1: "num_graph_impl.steps ys" using assms num_graph_impl.steps_ConsD by blast
  show ?thesis using num_graph_impl.steps_append[OF assms(1) 1] Cons by simp
qed

text \<open>Absorbing a leading delay on the numeric run (the numeric mirror of
@{thm [source] steps_delay_replace}): if @{term \<open>delay t x # xs\<close>} is a numeric run, @{term \<open>0 \<le> t\<close>}, and
no automaton sits on an urgent location at @{term x}, then @{term \<open>x # xs\<close>} is a numeric run -- the
leading length-@{term t} delay merges into the first delay step. Same proof as the propositional one:
invert the first @{const Simple_Network_Language.label.Del} step and re-issue a longer one via
@{thm [source] step_u.step_t}. The numeric net carries the SAME clocks/locations as the propositional one,
so the delay machinery transfers verbatim; @{term not_urgent} is supplied by the caller (the run-lifting,
where @{const num_happening_pre_pre_delay} pins the locations).\<close>
lemma num_steps_delay_replace:
  assumes "num_graph_impl.steps (delay t x # xs)"
      and t: "0 \<le> t"
      and not_urgent: "(\<forall>p < length (fst (snd num_net_impl.sem)). (fst x) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p))"
    shows "num_graph_impl.steps (x # xs)"
proof (cases rule: num_graph_impl.steps.cases[OF assms(1)])
  case 1
  then show ?thesis by blast
next
  fix tx y ys
  assume a: "delay t x # xs = tx # y # ys"
    "(case tx of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). num_net_impl.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) y"
    "num_graph_impl.steps (y # ys)"

  have xs: "xs = y # ys" using a by simp

  obtain Ly vy cy where
    y: "y = (Ly, vy, cy)" by (cases y; auto)

  obtain L v c where
    x: "x = (L, v, c)" by (cases x; auto)

  from a(1)
  have tx: "tx = (L, v, c \<oplus> t)" unfolding delay_def map_prod_def x prod.case id_def by simp

  from a(2)[simplified tx prod.case y, THEN step_u'_elims]
  obtain L' v' c' a where
    del: "num_net_impl.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>"
    and a: "a \<noteq> Simple_Network_Language.label.Del" "num_net_impl.sem \<turnstile> \<langle>L', v', c'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>Ly, vy, cy\<rangle>" by blast

  obtain broad N B where
    as: "num_net_impl.sem = (broad, N, B)" by (cases num_net_impl.sem) auto
  obtain t' where
    "c' = (c \<oplus> t) \<oplus> t'"
    and L': "L' = L"
    and v': "v' = v"
    and t': "0 \<le> t'"
    and other: "\<forall>p<length N. c' \<turnstile> Simple_Network_Language.inv (N ! p) (L ! p)"
      "(\<exists>p<length N. L ! p \<in> urgent (N ! p)) \<longrightarrow> t' = 0"
      "Simple_Network_Language.bounded B v"
    apply (cases rule: step_u_elims(1)[OF del])
    unfolding as
    unfolding TAG_def
    by auto
  hence c': "c' = c \<oplus> (t + t')" unfolding cval_add_def by auto
  have del': "num_net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>"
    unfolding as
    unfolding L' v' c'
    apply (rule step_u.step_t)
    unfolding TAG_def
    subgoal using other c' by blast
    subgoal using assms(2) t' by simp
    subgoal using other(2) t' assms(2) not_urgent unfolding x as fst_conv snd_conv by blast
    by (rule other(3))

  show ?thesis
    apply (rule num_steps_replace_Cons_hd[OF _ assms(1)])
    unfolding xs list.sel
    apply (rule num_single_step_intro)
    unfolding x y prod.case
    by (rule step_u'.intros[OF del' a])
qed

text \<open>Structure of the numeric network's Munta semantics (the numeric mirror of @{thm [source]
sem_alt_def}) and its automata-list length (mirror of @{thm [source] length_net_impl}). These unblock
the per-automaton urgency/location reasoning the run-lifting needs over @{const num_net_impl.sem}.\<close>
schematic_goal num_sem_alt_def: "num_net_impl.sem = ?x"
  unfolding num_net_impl.sem_def num_timed_automaton_net_def
  unfolding Simple_Network_Impl.sem_def fst_conv snd_conv ..

lemma length_num_net_impl: "length ((fst o snd) num_net_impl.sem) = Suc (length actions)"
  unfolding num_net_impl.sem_def
  using length_num_net_automata by auto

text \<open>No automaton sits on an urgent location at a @{const happening_pre_pre_delay} configuration of the
numeric net -- the @{term not_urgent} hypothesis @{thm [source] num_steps_delay_replace} needs. The numeric
net carries the SAME locations (from the shared @{const happening_pre_pre_delay}) and the SAME urgent sets
(@{const augment_edge} leaves the urgent component untouched: main automaton @{term \<open>{init_loc, goal_loc}\<close>},
action automata @{term \<open>{starting_loc, ending_loc}\<close>}) as the propositional net, so this is the inline
@{text no_urgent} block of @{thm [source] happening_steps_possible} with @{text num_} structure facts.\<close>
lemma num_no_urgent:
  assumes pres: "happening_pre_pre_delay i (L, v, c)"
      and lvp: "num_LvP (L, v, c)"
  shows "\<forall>p<length (fst (snd num_net_impl.sem)). fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
proof (intro allI impI)
  have num_lv: "num_Lv_conds L v" using lvp by simp
  have len_L: "length L = Suc (length actions)" by (rule num_Lv_conds_dests(1)[OF num_lv])

  fix p
  assume "p < length (fst (snd num_net_impl.sem))"
  hence pl: "p < Suc (length actions)"
        "p < length L"
    using length_num_net_impl
    using len_L by simp+

  show "fst (L, v, c) ! p \<notin> urgent (fst (snd num_net_impl.sem) ! p)"
  proof (cases p)
    case 0
    then have 1: "L ! p = planning_loc" using num_Lv_conds_dests(2)[OF num_lv] by simp

    have 2: "urgent (fst (snd num_net_impl.sem) ! p) = {init_loc, goal_loc}"
      unfolding num_sem_alt_def fst_conv snd_conv
      apply (subst nth_map, simp add: pl)
      apply (subst 0)
      apply (subst nth_Cons_0)
      unfolding comp_def num_main_auto_def Let_def snd_conv automaton_of_def conv_automaton_def prod.case
        urgent_def fst_conv by auto

    show ?thesis unfolding 2 fst_conv 1
      using locations_unique
      by blast
  next
    case (Suc n)
    hence a: "actions ! n \<in> set actions" using pl by simp
    consider "L ! p = off_loc" | "L ! p = running_loc"
      using pres unfolding happening_pre_pre_delay_def Let_def happening_pre_def prod.case
      using pl unfolding Suc
      apply (cases rule: planning_sem.open_active_count_cases[OF a])
      by blast+
    note c = this
    have "urgent (fst (snd num_net_impl.sem) ! p) = {starting_loc, ending_loc} "
      apply (subst num_sem_alt_def)
      unfolding fst_conv snd_conv
      apply (subst nth_map, simp add: pl)
      unfolding Suc
      apply (subst nth_Cons_Suc)
      apply (subst nth_map)
      using Suc pl apply blast
      apply (subst num_action_auto_urg)
      ..
    then
    show ?thesis
      unfolding fst_conv
      apply (cases rule: c; elim ssubst)
      using locations_unique by blast+
  qed
qed


end

end

theory TP_NTA_Reduction_Correctness_Edges
  imports TP_NTA_Reduction_Correctness_Prelims
begin
context tp_nta_reduction_correctness
begin
subsection \<open>Effects of Edges\<close>

definition edge_effect::"
  nat 
  \<Rightarrow> nat \<times> (String.literal, int) Simple_Expressions.bexp 
    \<times> (String.literal, int) acconstraint list \<times> String.literal act 
    \<times> (String.literal \<times> (String.literal, int) exp) list 
    \<times> String.literal list \<times> nat 
  \<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) 
  \<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real))" where
"edge_effect n e Lvc \<equiv> 
let 
  (_, _, _, _, u, r, s') = e;
  (L, v, c) = Lvc;
  (vs, as) = unzip (map (map_prod id (eval (the o v))) u);
  L' = L[n := s'];
  v' = v(vs [\<mapsto>] as);
  c' = clock_set r 0 c
in (L', v', c')
"
definition "start_edge_effect n = edge_effect (Suc n) (start_edge (actions ! n))"

definition "edge_2_effect n = edge_effect (Suc n) (edge_2 (actions ! n))"

definition "edge_3_effect n = edge_effect (Suc n) (edge_3 (actions ! n))"

definition "end_edge_effect n = edge_effect (Suc n) (end_edge (actions ! n))"

definition "instant_trans_edge_effect n = edge_effect (Suc n) (instant_trans_edge (actions ! n))"

definition "main_auto_init_edge_effect = edge_effect 0 main_auto_init_edge"

definition "main_auto_goal_edge_effect = edge_effect 0 main_auto_goal_edge"

lemma start_edge_effect_alt: "start_edge_effect n (L, v, c) = 
  (L[Suc n := starting_loc],
     v(acts_active \<mapsto> plus_int (the (v acts_active)) 1,
         map prop_to_var (dels (at_start (actions ! n))) [\<mapsto>] map (\<lambda>x. 0) (dels (at_start (actions ! n))),
         map prop_to_var (adds (at_start (actions ! n))) [\<mapsto>] map (\<lambda>x. 1) (adds (at_start (actions ! n)))),
     c(act_to_start_clock (actions ! n) := 0))"
  unfolding start_edge_effect_def start_edge_def
  unfolding  edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append fst_conv snd_conv
  by (auto simp: map_upds_append eval.simps)

lemma edge_2_effect_alt: "edge_2_effect n (L, v, c) = 
  (L[Suc n := running_loc],
    v(map prop_to_lock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. (the (v x)) + 1) (map prop_to_lock (over_all (actions ! n)))), 
    c)"
  unfolding edge_2_effect_def edge_2_def
  unfolding edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append fst_conv snd_conv 
    inc_prop_lock_ab_def
  by (auto simp: map_upds_append eval.simps)

lemma edge_3_effect_alt: "edge_3_effect n (L, v, c) = 
  (L[Suc n := ending_loc],
    v(map prop_to_lock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. plus_int (the (v x)) (- 1)) (map prop_to_lock (over_all (actions ! n)))),
    c(act_to_end_clock (actions ! n) := 0))"
  unfolding edge_3_effect_def edge_3_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma end_edge_effect_alt: "end_edge_effect n (L, v, c) = 
  (L[Suc n := off_loc],
    v(acts_active \<mapsto> plus_int (the (v acts_active)) (- 1),
      map prop_to_var (dels (at_end (actions ! n))) [\<mapsto>] map (\<lambda>x. 0) (map prop_to_var (dels (at_end (actions ! n)))),
      map prop_to_var (adds (at_end (actions ! n))) [\<mapsto>] map (\<lambda>x. 1) (map prop_to_var (adds (at_end (actions ! n))))),
    c)"
  unfolding end_edge_effect_def end_edge_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by (auto simp: map_upds_append)

lemma instant_trans_edge_effect_alt: "instant_trans_edge_effect n (L, v, c) = 
  (L[Suc n := ending_loc], v, c(act_to_end_clock (actions ! n):=0))"
  unfolding instant_trans_edge_effect_def instant_trans_edge_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma main_auto_init_edge_effect_alt: "main_auto_init_edge_effect (L, v, c) =
  (L[0 := planning_loc], v(planning_lock \<mapsto> 1, acts_active \<mapsto> 0, map prop_to_var init [\<mapsto>] map (\<lambda>x. 1) (map prop_to_var init)), c)"
  unfolding main_auto_init_edge_effect_def main_auto_init_edge_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

lemma main_auto_goal_edge_effect_alt: "main_auto_goal_edge_effect (L, v, c) = 
  (L[0 := goal_loc], v(planning_lock \<mapsto> 2), c)"
  unfolding main_auto_goal_edge_effect_def main_auto_goal_edge_def
  unfolding 
    edge_effect_def Let_def prod.case unzip_def set_prop_ab_def
    map_map comp_def fst_map_prod snd_map_prod id_def list.map map_append
    comp_def fst_conv snd_conv unzip_def inc_prop_lock_ab_def eval.simps
  by auto

definition apply_start_edge_effects::"
nat list
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) 
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) list" where
"apply_start_edge_effects ns s \<equiv>
  seq_apply (map start_edge_effect ns) s
"

definition "apply_edge_2_effects ns s = seq_apply (map edge_2_effect ns) s"

definition "apply_edge_3_effects ns s \<equiv> seq_apply (map edge_3_effect ns) s"

definition "apply_end_edge_effects ns s \<equiv> seq_apply (map end_edge_effect ns) s"

definition "apply_snap_action n s \<equiv> seq_apply [start_edge_effect n, instant_trans_edge_effect n, end_edge_effect n] s"

definition "apply_instant_actions ns s \<equiv> seq_apply' (map apply_snap_action ns) s"


(* apply all snap actions of the nth happening in the plan *)
definition apply_nth_happening::"
nat
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) 
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) list" where
"apply_nth_happening n s \<equiv>
let
  t = planning_sem.time_index n;
  act_indices = [0..<length actions];
  start_indices = filter (is_starting_index t) act_indices;
  end_indices = filter (is_ending_index t) act_indices;
  both = filter (is_instant_index t) act_indices
in [s] 
    |> ext_seq (apply_edge_3_effects end_indices)
    |> ext_seq (apply_instant_actions both)
    |> ext_seq (apply_start_edge_effects start_indices)
    |> ext_seq (apply_end_edge_effects end_indices)
    |> ext_seq (apply_edge_2_effects start_indices)
    |> tl
"

definition delay::"
real
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real))
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal, real) cval)" where
"delay t s \<equiv> map_prod id (map_prod id (\<lambda>clock_asmt. clock_asmt \<oplus> t)) s"

definition get_delay::"nat \<Rightarrow> real" where
"get_delay i \<equiv>
  if (i = 0) 
  then real_of_int (\<epsilon> + 1)
  else real_of_rat (planning_sem.htpl ! i - planning_sem.htpl ! (i - 1)) 
"

definition delay_and_apply::"
nat
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) 
\<Rightarrow> (nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) list" where
"delay_and_apply i s \<equiv>
let
  d = get_delay i
in
  s 
  |> delay d  
  |> apply_nth_happening i
"

primcorec goal_run::"
  (nat list \<times>
    (String.literal \<rightharpoonup> int) \<times>
    (String.literal, real) cval) 
\<Rightarrow> (nat list \<times>
    (String.literal \<rightharpoonup> int) \<times>
    (String.literal, real) cval) stream" where
"goal_run s = s ## (goal_run s)"


definition plan_steps::"(nat list \<times>
    (String.literal \<Rightarrow> int option) \<times>
    (String.literal, real) cval) list" where
"plan_steps \<equiv> 
  [a\<^sub>0]
    |> ext_seq (seq_apply [main_auto_init_edge_effect])
    |> ext_seq' (map delay_and_apply [0..<length planning_sem.htpl])
    |> ext_seq (seq_apply [main_auto_goal_edge_effect])"

definition plan_state_sequence::"(nat list \<times>
    (String.literal \<Rightarrow> int option) \<times>
    (String.literal, real) cval) stream" where
"plan_state_sequence \<equiv> plan_steps @- (goal_run (last plan_steps))"

subsection \<open>General properties of the automaton\<close>

lemma time_index_Suc_and_delay:
  assumes "i < length planning_sem.htpl"
  shows "real_of_rat (planning_sem.time_index (Suc i)) = real_of_rat (planning_sem.time_index i) + get_delay (Suc i)"
  unfolding get_delay_def planning_sem.time_index_def
  by (simp add: of_rat_add[symmetric])

lemma conv_trans:
assumes "p < length (map (automaton_of o conv_automaton) autos)"
shows "Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) autos ! p) = (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) ` (trans (automaton_of  (autos ! p)))"
  apply (subst nth_map)
  using assms apply simp
  apply (subst comp_def)
  apply (cases "autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "autos ! p"])
     apply assumption
    unfolding conv_automaton_def prod.case
    unfolding automaton_of_def prod.case
    unfolding trans_def fst_conv snd_conv
    unfolding set_map by blast
  done

lemma conv_committed: 
  assumes "p < length (map (automaton_of o conv_automaton) autos)"
  shows "committed (map (automaton_of \<circ> conv_automaton) autos ! p) = committed (map automaton_of autos ! p)"
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "autos ! p"])
     apply simp
    unfolding comp_apply
    unfolding conv_automaton_def automaton_of_def committed_def prod.case fst_conv ..
  done

lemma no_committed: 
  assumes "p < length net_automata"
  shows "committed (map automaton_of net_automata ! p) = {}"
  using assms
  unfolding timed_automaton_net_def automaton_of_def committed_def main_auto_def Let_def action_to_automaton_def
  apply (cases p)
  by simp+

lemma conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) net_automata)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) net_automata ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of net_automata ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "net_automata ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(net_automata ! p)"])
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

lemma no_invs': assumes "p < length net_automata"
  shows "inv (automaton_of (net_automata ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding timed_automaton_net_def Let_def prod.case 
    by simp+
  show ?thesis
    unfolding timed_automaton_net_def Let_def prod.case
  unfolding main_auto_def Let_def action_to_automaton_def
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

lemma no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) net_automata)"
  shows "inv (map (automaton_of \<circ> conv_automaton) net_automata ! p) = (\<lambda>x. [])"
  apply (subst conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using no_invs'
  apply (subst no_invs')
  using assms by auto

lemma cval_add_0: "z\<oplus>(0::real) = z" unfolding cval_add_def 
  by simp


lemma step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of net_bounds) y"
  shows "net_impl.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding net_impl.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using no_invs by auto
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by auto
  done


lemmas single_step_intro = graph_impl.steps.Cons[OF _ graph_impl.steps.Single]
lemmas non_t_step_intro = step_t_possible[THEN step_u'.intros, rotated, rotated]

subsection \<open>Proofs\<close>

lemma init_vars_alt: "init_vars = map (\<lambda>x. (fst x, 0)) net_bounds"
  unfolding init_vars_def
  unfolding map_prod_def
  unfolding all_vars_def Let_def prod.case
  by auto

lemma a\<^sub>0_alt: "a\<^sub>0 = (init_loc # map (\<lambda> x. off_loc) actions, map_of (map (\<lambda>x. (fst x, 0)) net_bounds), \<lambda>_. 0)"
proof -
  have a: "map (\<lambda>(x, y). (id x, fst y)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props @ map (\<lambda>p. (prop_to_var p, 0, 1)) props))
    = map (\<lambda>x. (fst x, 0)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props @ map (\<lambda>p. (prop_to_var p, 0, 1)) props))"
  proof -
    have 1: "map (\<lambda>(x, y). (id x, fst y)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props)) =
      map (\<lambda>x. (fst x, 0)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props))"
      by (induction props) auto
     
    have 2: "map (\<lambda>(x, y). (id x, fst y)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_var p, 0, 1)) props)) =
      map (\<lambda>x. (fst x, 0)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_var p, 0, 1)) props))"
      by (induction props) auto
    
    have "map (\<lambda>(x, y). (id x, fst y)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props @ map (\<lambda>p. (prop_to_var p, 0, 1)) props))
      = map (\<lambda>x. (fst x, 0)) (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props @ map (\<lambda>p. (prop_to_var p, 0, 1)) props))"
      unfolding filter_append
      unfolding map_append
      apply (subst 1, subst 2)
      by auto
    thus ?thesis by blast
  qed
  show ?thesis 
    unfolding a\<^sub>0_def
    unfolding init_vars_def init_locs_def all_vars_def 
    unfolding Let_def map_prod_def map_append
    apply (subst a)
    by simp
qed
  

(* Todo?: Change the locale definition to make sure that the set of propositions occurring in actions
  is exactly the set of fluents *)

lemma map_of_zip_dom_to_range':
  "a \<in> set A \<Longrightarrow> length A = length B \<Longrightarrow> \<exists>x. map_of (zip A B) a = Some x \<and> x \<in> set B"
  apply (frule map_of_zip_fst)
   apply assumption
  apply (rule ssubst[of "map_of (zip A B) a"])
   apply assumption
  apply (subst (asm) index_less_size_conv[symmetric])
  by simp

subsubsection \<open>Relating maps and bounds\<close>

lemma is_upds_set_vars_replicate: 
  assumes "upds = (map (set_var n) xs)"
      and "v' = (v(xs [\<mapsto>] (replicate (length xs) n)))"
    shows "is_upds v upds v'"
  unfolding assms
  by (induction xs arbitrary: v) (auto intro: is_upds.intros simp: is_upd_def check_bexp_simps is_val_simps)

lemma map_const_eq_conv_length_eq:
  "map (\<lambda>x. n) xs = map (\<lambda>y. m) ys \<longleftrightarrow> length xs = length ys \<and> ((xs \<noteq> []) \<longrightarrow> n = m)"
  apply (rule iffI)
   apply (induction xs arbitrary: ys)
    apply simp
  subgoal for x xs ys
    apply (induction ys)
    by auto
  apply (induction xs arbitrary: ys)
   apply simp
  subgoal for x xs ys
    apply (induction ys)
    by auto
  done

lemma is_upds_set_vars_map: 
  assumes "upds = (map (set_var n) xs)"
      and "v' = (v(xs [\<mapsto>] (map (\<lambda>x. n) xs)))"
    shows "is_upds v upds v'"
  unfolding assms
  by (induction xs arbitrary: v) (auto intro: is_upds.intros simp: is_upd_def check_bexp_simps is_val_simps)

lemma is_upds_inc_vars: 
  assumes "set xs \<subseteq> dom v"
      and "distinct xs"
      and "upds = (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs)"
      and "v' = v(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the o v) xs))"
  shows "is_upds v upds v'"
  using assms(1,2)
  unfolding assms(3,4)
proof (induction xs arbitrary: v)
  case Nil
  then show ?case 
    apply simp
    by (rule is_upds.intros)
next
  case (Cons x xs v)
  have 1: "is_upd v (x, binop plus_int (var x) (exp.const n)) (v(x \<mapsto> the (v x) + n))" (is "is_upd v ?upd ?v'")
    unfolding is_upd_def
     apply (intro exI conjI)
       apply (rule HOL.refl)
      apply (rule check_bexp_is_val.intros(14)[of _ _ "the (v x)"])
      apply (rule check_bexp_is_val.intros)
       using Cons(2) apply auto[1]
        apply (rule check_bexp_is_val.intros)
       by simp
   from Cons(3)
   have "\<forall>x' \<in> set xs. x \<noteq> x'" by auto
   hence 2: "map (the o v) xs = map (the o ?v') xs"
     unfolding comp_def using fun_upd_other by auto

   have "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the \<circ> ?v') xs)))"
     apply (rule Cons.IH)
     using Cons(2,3) by auto
   hence 3: "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the \<circ> v) xs)))"
     apply (subst 2) by simp
   show ?case 
    apply (subst list.map)+
    apply (subst map_upds_Cons)
     apply (rule is_upds.intros(2)[OF 1])
     using 3 unfolding comp_apply by simp
qed

lemma single_upd_bounded:
  assumes "bounded M v"
      and "M x = Some (l, u)"
      and "l \<le> y"
      and "y \<le> u"
    shows "bounded M (v(x \<mapsto> y))"
proof -
  from assms[simplified bounded_def]
  have dom_v_M: "dom v = dom M"
    and bounds: "\<forall>x \<in> dom v. fst (the (M x)) \<le> the (v x) \<and> the (v x) \<le> snd (the (M x))"
    by auto
  
  from assms(2) dom_v_M
  have dom': "dom (v (x \<mapsto> y)) = dom v" by auto

  have "fst (the (M a)) \<le> the ((v (x \<mapsto> y)) a) \<and> the ((v (x \<mapsto> y)) a) \<le> snd (the (M a))" if "a \<in> dom (v (x \<mapsto> y))" for a
  proof (cases "a = x")
    case True
    then show ?thesis using assms(2,3,4) by simp
  next
    case False
    hence 1: "the (v a) = the ((v (x \<mapsto> y)) a)" using that by simp
    
    have "a \<in> dom v" using dom' that by argo
    from bounds[THEN bspec, OF this]
    show ?thesis unfolding 1 by simp
  qed
  with dom' dom_v_M
  show ?thesis unfolding bounded_def by simp
qed

find_theorems name: "map_upds"

lemma upds_bounded:
  assumes "bounded M v"
      and "length xs = length ys"
      and "\<forall>n < length xs. \<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> (ys ! n) \<and> (ys ! n) \<le> u"   
    shows "bounded M (v(xs [\<mapsto>] ys))"
  using assms
proof (induction xs arbitrary: ys v)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y' ys' where
    ys': "ys = y'#ys'"
    "length (x # xs) = length (y' # ys')" apply (cases ys) by simp+
  obtain l u where
    "M x = Some (l, u)"
    "l \<le> y'"
    "y' \<le> u" using Cons(4)[simplified ys'(1)] by auto
  with Cons(2)
  have 1: "Simple_Network_Language.bounded M (v(x \<mapsto> y'))" by (auto intro: single_upd_bounded)
  have 2: "\<forall>n<length xs. \<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> ys' ! n \<and> ys' ! n \<le> u"
  proof (intro allI impI)
    fix n
    assume a: "n < length xs"
    hence 1: "Suc n < length (x # xs)" by simp
    have "xs ! n = (x # xs) ! Suc n" by simp
    moreover
    have "ys' ! n = (y' # ys') ! Suc n" using ys' by simp
    ultimately
    show "\<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> ys' ! n \<and> ys' ! n \<le> u" using Cons(4)[simplified ys'(1), THEN spec[of _ "Suc n"], THEN mp[OF _ 1]] by simp 
  qed
  with 1 ys'(2) Cons(4)
  have "Simple_Network_Language.bounded M ((v(x \<mapsto> y'))(xs [\<mapsto>] ys'))"
    apply -
    apply (rule Cons.IH)
      apply assumption
    by simp+
  thus ?case unfolding ys'(1) by simp
qed

lemma updated_bounded:
  assumes previous: "bounded M v"
      and l: "length xs = length ys"
      and v': "v' = v(xs [\<mapsto>] ys)"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u)"   
    shows "bounded M v'"
  unfolding bounded_def
proof (rule conjI)
  show 1: "dom v' = dom M"
    apply (intro equalityI subsetI)
    subgoal for x
      using assms(2)[symmetric] bounds previous unfolding  v' bounded_def by auto
    subgoal for x
      unfolding v'
      apply (subst dom_map_upds)
      using previous unfolding bounded_def by blast
    done
  show "\<forall>x\<in>dom v'. fst (the (M x)) \<le> the (v' x) \<and> the (v' x) \<le> snd (the (M x))"
    apply (rule ballI)
    subgoal for x
      apply (subst (asm) v')
      apply (subst (asm) dom_map_upds)
      apply (subst (asm) assms(2)[symmetric])
      apply (subst (asm) take_all, simp)
      apply (erule UnE)
      subgoal using bounds by auto
      apply (cases "x \<in> set xs")
      subgoal using bounds by auto
      unfolding v'
      apply (subst map_upds_apply_nontin)
      apply simp
      apply (subst map_upds_apply_nontin)
       apply simp
      using previous unfolding bounded_def by simp
    done
qed

lemma all_zip_replicate:
  assumes "x \<in> set xs"
  shows "\<forall>m. (x, m) \<in> set (zip xs (replicate (length xs) n)) \<longrightarrow> m = n"
  using assms
proof (induction xs arbitrary: n x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have IH: "\<forall>m. (x, m) \<in> set (zip as (replicate (length as) n)) \<longrightarrow> m = n"
    using Cons apply (cases "x \<in> set as")
     apply simp using set_zip_leftD by metis
  show ?case 
    apply (subst length_Cons)
    apply (subst replicate.simps)
    apply (subst zip_Cons_Cons)
    apply (rule allI)
    subgoal for m
      apply (cases "m = n")
       apply simp
      apply (subst list.set)
      using IH by auto
    done
qed

lemma map_of_determ:
  assumes "\<forall>m. (x, m) \<in> set xs \<longrightarrow> m = n"
          and "(x, n) \<in> set xs"
        shows "map_of xs x = Some n"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain c d where
    a: "a = (c, d)" by fastforce
  then show ?case 
  proof (cases "a = (x,n)")
    case True
    then show ?thesis by simp
  next
    case False
    then 
    consider "x \<noteq> c" | "x = c \<and> n \<noteq> d" using a by blast
    then show ?thesis 
    proof cases
      case 1
      hence "map_of (a # xs) x = map_of xs x" using a map_of_Cons_code by auto
      moreover
      have i: "(x, n) \<in> set xs" using Cons (3) a 1 by auto
      moreover
      from Cons(2) i 1 False a
      have "\<forall>m. (x, m) \<in> set xs \<longrightarrow> m = n" by force
      ultimately
      show ?thesis using Cons.IH by metis
    next
      case 2
      then show ?thesis using a Cons by simp
    qed
  qed
qed

lemma map_upds_with_replicate:
  assumes "x \<in> set xs"
  shows "(v(xs [\<mapsto>] (replicate (length xs) n))) x = Some n"
proof -
  have "(x, n) \<in> set (zip xs (replicate (length xs) n))"
    apply (subst set_zip)
    using length_replicate assms
    using nth_replicate
    by (auto simp: set_conv_nth)
  thus ?thesis
    using assms 
    unfolding map_upds_def 
    apply (subst map_add_find_right)
     apply (rule map_of_determ)
    apply (subst set_rev)
    using all_zip_replicate
    by (fast, auto)
qed


lemma map_upds_with_map:
  assumes "x \<in> set xs"
      and "length xs = length ys"
  shows "(v(xs [\<mapsto>] (map (\<lambda>x. n) ys))) x = Some n"
proof -
  have "\<forall>m. (x, m) \<in> set (zip xs (map (\<lambda>x. n) ys)) \<longrightarrow> m = n"
    apply (subst set_zip)
    by auto
  moreover
  have "(x, n) \<in> set (zip xs (map (\<lambda>x. n) ys))"
    apply (subst set_zip)
    using assms
    by (auto simp: set_conv_nth set_zip)
  ultimately
  show ?thesis
    using assms unfolding map_upds_def 
    apply (subst map_add_find_right)
    by (auto intro: map_of_determ)
qed

lemma upds_replicate_bounded:
  assumes previous: "bounded M v"
      and v': "v' = v(xs [\<mapsto>] (replicate (length xs) n))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded[OF assms(1) length_replicate[symmetric] assms(2)])
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_replicate[OF a]) 
      by simp
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed

lemma upds_map_bounded':
  assumes previous: "bounded M v"
      and length: "length xs = length ys"
      and v': "v' = v(xs [\<mapsto>] (map (\<lambda>x. n) ys))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded)
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_map) 
      using assms a by auto
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed (use assms in auto)

lemma upds_map_bounded:
  assumes previous: "bounded M v"
      and v': "v' = v(xs [\<mapsto>] (map (\<lambda>x. n) xs))"
      and bounds: "\<forall>x \<in> set xs. (\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u)"   
    shows "bounded M v'"
proof (rule updated_bounded)
  show "\<forall>x\<in>set xs. \<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
  proof (rule ballI)
    fix x
    assume a: "x \<in> set xs"
    with bounds
    have "\<exists>l u. M x = Some (l, u) \<and> l \<le> n \<and> n \<le> u" by simp
    moreover
    have "the (v' x) = n" unfolding v' 
      apply (subst map_upds_with_map) 
      using assms a by auto
    ultimately
    show "\<exists>l u. M x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u" by simp
  qed
qed (use assms in auto)

lemma distinct_map_upds:
  assumes "x \<in> set xs"
      and "distinct xs"
    shows "(v(xs [\<mapsto>] (map f xs))) x = Some (f x)"
  using assms 
  unfolding map_upds_def
  apply (subst map_add_find_right)
   apply (subst zip_rev[symmetric])
    apply simp
   apply (rule map_of_is_SomeI[where y = "f x"])
    apply simp
   apply (subst zip_rev)
    apply simp
   apply (subst set_rev)
   apply (subst in_set_zip)
   apply (subst (asm) in_set_conv_nth)
  by auto

  
text \<open>The bounds of net_bounds\<close>

lemma init_vars_bounded: "bounded (map_of net_bounds) (map_of init_vars)"
  unfolding bounded_def
proof (intro conjI ballI)
  have *: "(\<lambda>x. (fst x, 0)) = (\<lambda>(x, y). (x, 0))" by auto
  show 1: "dom (map_of init_vars) = dom (map_of net_bounds)" unfolding init_vars_alt
    apply (subst *) 
    apply (subst dom_map_of_map)
    apply (subst dom_map_of_conv_image_fst) by blast
  { fix x
    assume "x \<in> dom (map_of init_vars)" 
    then obtain y where
      y: "map_of net_bounds x = Some y" using 1 by auto
    hence "fst y = 0"  unfolding all_vars_def Let_def
      apply -
      apply (drule map_of_SomeD)
      by auto
    thus "fst (the (map_of net_bounds x)) \<le> the (map_of init_vars x)" unfolding init_vars_alt map_of_map comp_apply *
      using y by simp
      
  }
  { fix x
    assume "x \<in> dom (map_of init_vars)"then obtain y where
      y: "map_of net_bounds x = Some y" using 1 by auto
    hence "snd y \<ge> 0" unfolding all_vars_def Let_def
      apply -
      apply (drule map_of_SomeD)
      unfolding set_append
      apply (induction y)
      by auto
    thus "the (map_of init_vars x) \<le> snd (the (map_of net_bounds x))" unfolding init_vars_alt map_of_map comp_apply *
      using y by simp
  }
qed

lemma map_of_net_bounds_acts_active: 
  "map_of net_bounds acts_active = Some (0, int (length actions))" using all_vars_def by simp

lemma map_of_net_bounds_planning_lock:
  "map_of net_bounds planning_lock = Some (0, 2)" 
  unfolding all_vars_def variables_unique 
  unfolding Let_def unfolding map_of_append
  apply (rule map_add_find_right)
  apply (subst map_of_Cons_code)
  apply (subst if_not_P)
  apply (rule variables_unique)
  by simp
 

lemma map_prop_var_simp: "map (\<lambda>p. (prop_to_var p, 0, 1)) xs = map (\<lambda>(v, b). (v, id b)) (map (\<lambda>v. (v, 0, 1)) (map prop_to_var xs))"
  by auto

lemma map_of_net_bounds_init_goal:
  assumes "v \<in> set (map prop_to_var init) \<union> set (map prop_to_var goal)"
  shows "map_of net_bounds v = Some (0, 1)"
proof-
  from assms 
  obtain p where
    p: "p \<in> set init \<union> set goal"
    "p \<in> set props"
    "v = prop_to_var p" 
    using init_in_props goal_in_props by auto

  hence 1: "p \<in> set (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)" by auto
  have distinct: "distinct (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)" using distinct_props by simp
  have 2:"(map_of (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    using distinct
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply simp
    using 1 by simp
  have 3: "map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props) = 
    map (\<lambda>(p, v). (prop_to_var p, v)) (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props))"
    by simp
  have 4: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) 
    = (map_of (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) p)" 
    apply (subst 3)
    apply (subst map_of_map_inj_on_fst)
     apply (rule inj_on_subset)
    apply (rule variables_inj)
    using p(2) by auto 
    
  have 5: "prop_to_var p \<notin> fst ` set (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars actions) {} \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props))"
     apply (subst image_set)
     apply (subst filter_map)
     apply (subst map_map)
     apply (subst comp_def)+
     apply (subst fst_conv)+
     apply (subst set_map)
    apply (subst set_filter)
    apply (rule notI)
    apply (erule imageE)  
    using variables_unique by blast

  have 6: "map (\<lambda>p. (f p, 0, 1)) xs = map (\<lambda>x. (x, 0, 1)) (map f xs)" for f xs by simp
  show ?thesis 
    unfolding all_vars_def Let_def
    apply (subst p)
    apply (subst map_of_append)+
    apply (subst map_add_find_left)
     apply (simp add: variables_unique map_of_Cons_code)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (rule 5)
    apply (subst 6)
    apply (subst filter_map)
    apply (subst comp_def)
    apply (subst fst_conv)
    apply (subst filter_map)
    apply (subst comp_def)
    apply (subst map_map)
    apply (subst comp_def)
    apply (subst fold_union')
    using 4 2 by metis
qed


lemma map_of_net_bounds_action_inv:
  assumes "a \<in> set actions"
    "v \<in> set (map prop_to_lock (over_all a))"
  shows "map_of net_bounds v = Some (0, int (length actions))"
proof -
  from assms 
  obtain p where
    p: "p \<in> set (over_all a)"
    "p \<in> set props"
    "v = prop_to_lock p" using planning_sem.domain_acts_ref_props unfolding planning_sem.act_ref_props_def by auto
  hence 1: "p \<in> set (filter (\<lambda>x. prop_to_lock x \<in> \<Union> (set (map action_vars actions))) props)" 
    unfolding action_vars_def Let_def set_map inv_vars_def using assms by auto

  have 2: "map_of (map (\<lambda>p. (prop_to_lock p, y)) (filter (\<lambda>x. prop_to_lock x \<in> S) props)) (prop_to_lock p) 
    = (map_of (map (\<lambda>p. (p, y)) (filter (\<lambda>x. prop_to_lock x \<in> S) props)) p)" for S y
    apply (subst map_of_map_inj_on_fst[symmetric, where f = prop_to_lock])
     apply (rule inj_on_subset)
      apply (rule variables_inj)
    using p apply force
    apply (subst map_map)
    apply (subst comp_def)
    unfolding prod.case
    by blast


  show ?thesis
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    apply (subst map_of_append)+
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_right)
     apply (subst filter_map)
     apply (subst comp_def)
     apply (subst fst_conv)
    apply (subst 2)
     apply (rule map_of_is_SomeI)
    using distinct_props unfolding map_map comp_apply apply simp
    using 1 apply fastforce
    by simp
qed

lemma map_of_net_bounds_action_inv_props:
  assumes "a \<in> set actions"
    "v \<in> set (map prop_to_var (over_all a))"
  shows "map_of net_bounds v = Some (0, 1)"
proof -
  from assms 
  obtain p where
    p: "p \<in> set (over_all a)"
    "p \<in> set props"
    "v = prop_to_var p" using planning_sem.domain_acts_ref_props unfolding planning_sem.act_ref_props_def by auto
  hence 1: "p \<in> set (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions))) props)" 
    unfolding action_vars_def Let_def inv_vars_def set_map using assms
    by auto

  have 2: "map_of (map (\<lambda>p. (prop_to_var p, y)) (filter (\<lambda>x. prop_to_var x \<in> S) props)) (prop_to_var p) 
    = (map_of (map (\<lambda>p. (p, y)) (filter (\<lambda>x. prop_to_var x \<in> S) props)) p)" for S y 
    apply (subst map_of_map_inj_on_fst[symmetric, where f = prop_to_var])
     apply (rule inj_on_subset)
      apply (rule variables_inj)
    using p apply force
    apply (subst map_map)
    apply (subst comp_def)
    unfolding prod.case
    by blast

  have 3: "map (\<lambda>p. (f p, y)) xs = map (\<lambda>x. (x, y)) (map f xs)" for f xs y by simp

  have 4: "map_of (filter (\<lambda>x. fst x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) (map (\<lambda>p. (prop_to_lock p, 0, int (length actions))) props)) (prop_to_var p) = None"
    apply (rule map_of_NoneI)
    unfolding image_set filter_map comp_def map_map fst_conv
    apply (subst set_map)
    apply (rule notI)
    apply (erule imageE)
    using variables_unique by metis

  show ?thesis
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    apply (subst map_of_append)+
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
     apply (rule 4)
    unfolding filter_map comp_def fst_conv
    apply (subst 2)
     apply (rule map_of_is_SomeI)
    using distinct_props unfolding map_map comp_apply apply simp
    using 1 by auto
qed

lemma map_of_net_bounds_action_start_del:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map prop_to_var (dels (at_start a)))"
    shows "map_of net_bounds v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (dels (at_start a))"
    "v = prop_to_var p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) 
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_var p \<in> action_vars a"
    using p(1) unfolding action_vars_def Let_def snap_vars_def by force

  have 1: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using inj_on_subset variables_inj apply fastforce
    using a_in_actions p_in_props p_in_a_vars by auto

  show ?thesis 
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    unfolding map_of_append
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
    unfolding filter_map comp_def map_map fst_conv
     apply (rule map_of_NoneI)
    unfolding image_set map_map fst_conv comp_def
     apply (subst set_map)
     apply (rule notI)
     apply (erule imageE)
    using variables_unique apply metis
    using 1 by blast
qed

lemma map_of_net_bounds_action_start_add:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map prop_to_var (adds (at_start a)))"
    shows "map_of net_bounds v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (adds (at_start a))"
    "v = prop_to_var p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) 
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_var p \<in> action_vars a"
    using p(1) unfolding action_vars_def Let_def snap_vars_def by force

  have 1: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using inj_on_subset variables_inj apply fastforce
    using a_in_actions p_in_props p_in_a_vars by auto

  show ?thesis 
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    unfolding map_of_append
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
    unfolding filter_map comp_def map_map fst_conv
     apply (rule map_of_NoneI)
    unfolding image_set map_map fst_conv comp_def
     apply (subst set_map)
     apply (rule notI)
     apply (erule imageE)
    using variables_unique apply metis
    using 1 by blast
qed

lemma map_of_net_bounds_action_start_del_lock:
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map prop_to_lock (dels (at_start a)))"
          "v \<notin> set (map prop_to_lock (adds (at_start a)))"
    shows "map_of net_bounds v = Some (0, int (length actions))"
proof -
  obtain p where
    p: "p \<in> set (dels (at_start a))"
       "p \<notin> set (adds (at_start a))"
       "v = prop_to_lock p" using v by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1)
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_lock p \<in> action_vars a"
    using p unfolding action_vars_def Let_def snap_vars_def by auto

  show ?thesis 
    unfolding map_of_all_vars_exact map_of_append p
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    unfolding filter_append filter_map comp_def fst_conv map_of_append
    apply (rule map_add_find_right)
    apply (rule map_of_is_SomeI)
    unfolding map_map comp_def fst_conv
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using variables_inj inj_on_subset apply force
    apply (subst set_map)
    apply (rule imageI)
    using p_in_props p_in_a_vars a_in_acts by auto
qed

lemma map_of_net_bounds_action_end_del:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map prop_to_var (dels (at_end a)))"
    shows "map_of net_bounds v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (dels (at_end a))"
    "v = prop_to_var p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) 
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_var p \<in> action_vars a"
    using p(1) unfolding action_vars_def Let_def snap_vars_def by force

  have 1: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using inj_on_subset variables_inj apply fastforce
    using a_in_actions p_in_props p_in_a_vars by auto

  show ?thesis 
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    unfolding map_of_append
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
    unfolding filter_map comp_def map_map fst_conv
     apply (rule map_of_NoneI)
    unfolding image_set map_map fst_conv comp_def
     apply (subst set_map)
     apply (rule notI)
     apply (erule imageE)
    using variables_unique apply metis
    using 1 by blast
qed

lemma map_of_net_bounds_action_end_add:
  assumes a_in_actions: "a \<in> set actions"
      and "v \<in> set (map prop_to_var (adds (at_end a)))"
    shows "map_of net_bounds v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (adds (at_end a))"
    "v = prop_to_var p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) 
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_var p \<in> action_vars a"
    using p(1) unfolding action_vars_def Let_def snap_vars_def by force

  have 1: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using inj_on_subset variables_inj apply fastforce
    using a_in_actions p_in_props p_in_a_vars by auto

  show ?thesis 
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    unfolding map_of_append
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
    unfolding filter_map comp_def map_map fst_conv
     apply (rule map_of_NoneI)
    unfolding image_set map_map fst_conv comp_def
     apply (subst set_map)
     apply (rule notI)
     apply (erule imageE)
    using variables_unique apply metis
    using 1 by blast
qed

lemma map_of_net_bounds_action_end_del_lock:
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map prop_to_lock (dels (at_end a)))"
          "v \<notin> set (map prop_to_lock (adds (at_end a)))"
    shows "map_of net_bounds v = Some (0, int (length actions))"
proof -
  obtain p where
    p: "p \<in> set (dels (at_end a))"
       "p \<notin> set (adds (at_end a))"
       "v = prop_to_lock p" using v by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1)
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_lock p \<in> action_vars a"
    using p unfolding action_vars_def Let_def snap_vars_def by auto

  show ?thesis 
    unfolding map_of_all_vars_exact map_of_append p
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    unfolding filter_append filter_map comp_def fst_conv map_of_append
    apply (rule map_add_find_right)
    apply (rule map_of_is_SomeI)
    unfolding map_map comp_def fst_conv
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using variables_inj inj_on_subset apply force
    apply (subst set_map)
    apply (rule imageI)
    using p_in_props p_in_a_vars a_in_acts by auto
qed

lemma map_of_net_bounds_action_end_pre:
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map prop_to_var (pre (at_end a)))"
    shows "map_of net_bounds v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (pre (at_end a))"
    "v = prop_to_var p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) 
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_var p \<in> action_vars a"
    using p(1) unfolding action_vars_def Let_def snap_vars_def by force

  have 1: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using inj_on_subset variables_inj apply fastforce
    using a_in_acts p_in_props p_in_a_vars by auto

  show ?thesis 
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    unfolding map_of_append
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
    unfolding filter_map comp_def map_map fst_conv
     apply (rule map_of_NoneI)
    unfolding image_set map_map fst_conv comp_def
     apply (subst set_map)
     apply (rule notI)
     apply (erule imageE)
    using variables_unique apply metis
    using 1 by blast
qed



lemma map_of_net_bounds_action_start_pre:
  assumes a_in_acts: "a \<in> set actions"
      and v: "v \<in> set (map prop_to_var (pre (at_start a)))"
    shows "map_of net_bounds v = Some (0, 1)"
proof -
  obtain p where
  p: "p \<in> set (pre (at_start a))"
    "v = prop_to_var p" using assms(2) by auto

  have p_in_props: "p \<in> set props" using assms(1) p(1) 
    using planning_sem.domain_acts_ref_props 
    unfolding planning_sem.act_ref_props_def planning_sem.snap_ref_props_def by auto

  have p_in_a_vars: "prop_to_var p \<in> action_vars a"
    using p(1) unfolding action_vars_def Let_def snap_vars_def by force

  have 1: "map_of (map (\<lambda>p. (prop_to_var p, 0, 1)) (filter (\<lambda>x. prop_to_var x \<in> \<Union> (set (map action_vars actions)) \<union> set (map prop_to_var init) \<union> set (map prop_to_var goal)) props)) (prop_to_var p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply (subst distinct_map)
    using distinct_filter distinct_props
    using inj_on_subset variables_inj apply fastforce
    using a_in_acts p_in_props p_in_a_vars by auto

  show ?thesis 
    apply (subst map_of_all_vars_exact)
    apply (subst p)
    unfolding map_of_append
    apply (subst map_add_find_left)
     apply (simp add: variables_unique)
    apply (subst filter_append)
    apply (subst map_of_append)
    apply (subst map_add_find_left)
    unfolding filter_map comp_def map_map fst_conv
     apply (rule map_of_NoneI)
    unfolding image_set map_map fst_conv comp_def
     apply (subst set_map)
     apply (rule notI)
     apply (erule imageE)
    using variables_unique apply metis
    using 1 by blast
qed

subsubsection \<open>The initial transition\<close>

lemma main_auto_init_edge_simp: "main_auto_init_edge = 
    (init_loc, 
      Simple_Expressions.bexp.eq (var planning_lock) (exp.const 0), [], 
      Sil STR '''', 
      (planning_lock, exp.const 1) # (acts_active, exp.const 0) # map (set_prop_ab 1) init, [], 
      planning_loc)"
  unfolding main_auto_init_edge_def Let_def ..

subsubsection \<open>Rules for constructing a run\<close>


lemma steps_extend: 
  "graph_impl.steps xs 
  \<Longrightarrow> graph_impl.steps (last xs # ys) 
  \<Longrightarrow> graph_impl.steps (xs @ ys)"
  apply (rule graph_impl.steps_append'[where as = xs and bs = "last xs # ys"])
  by simp+

lemma steps_replace_Cons_hd:
  assumes "graph_impl.steps [x, hd ys]"
          "graph_impl.steps (y # ys)"
    shows "graph_impl.steps (x # ys)"
proof (cases ys)
  case Nil
  then show ?thesis using assms(1) by blast
next
  case (Cons a list)
  hence 1: "graph_impl.steps ys" using assms graph_impl.steps_ConsD by blast
  show ?thesis using graph_impl.steps_append[OF assms(1) 1] Cons by simp
qed


lemma steps_delay_replace:
  assumes "graph_impl.steps (delay t x # xs)"
      and t: "0 \<le> t"
      and not_urgent: "(\<forall>p < length (fst (snd net_impl.sem)). (fst x) ! p \<notin> urgent (fst (snd net_impl.sem) ! p))"
    shows "graph_impl.steps (x # xs)"
proof (cases rule: graph_impl.steps.cases[OF assms(1)])
  case 1
  then show ?thesis by blast
next
  fix tx y ys
  assume a: "delay t x # xs = tx # y # ys"
    "(case tx of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). net_impl.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) y"
    "graph_impl.steps (y # ys)"

  have xs: "xs = y # ys" using a by simp

  obtain Ly vy cy where
    y: "y = (Ly, vy, cy)" by (cases y; auto)

  obtain L v c where
    x: "x = (L, v, c)" by (cases x; auto)

  from a(1)
  have tx: "tx = (L, v, c \<oplus> t)" unfolding delay_def map_prod_def x prod.case id_def by simp

  from a(2)[simplified tx prod.case y, THEN step_u'_elims]
  obtain L' v' c' a where
    del: "net_impl.sem \<turnstile> \<langle>L, v, c \<oplus> t\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>" 
    and a: "a \<noteq> Simple_Network_Language.label.Del" "net_impl.sem \<turnstile> \<langle>L', v', c'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>Ly, vy, cy\<rangle>" by blast

  obtain broad N B where
    as: "net_impl.sem = (broad, N, B)" by (cases net_impl.sem) auto
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
  have del': "net_impl.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>L', v', c'\<rangle>"
    unfolding as
    unfolding L' v' c'
    apply (rule step_u.step_t)
    unfolding TAG_def 
    subgoal using other c' by blast
    subgoal using assms(2) t' by simp
    subgoal using other(2) t' assms(2) not_urgent unfolding x as fst_conv snd_conv by blast
    by (rule other(3))

  show ?thesis
    apply (rule steps_replace_Cons_hd[OF _ assms(1)])
    unfolding xs list.sel
    apply (rule single_step_intro)
    unfolding x y prod.case
    by (rule step_u'.intros[OF del' a])
qed



schematic_goal nth_auto_trans:
  assumes "n < length actions"
  shows "trans (automaton_of (net_automata ! Suc n)) = ?x"
  apply (subst timed_automaton_net_def)
  apply (subst nth_Cons_Suc)
  apply (subst nth_map)
  apply (rule assms)
  unfolding action_to_automaton_def Let_def comp_def snd_conv trans_def 
    automaton_of_def prod.case fst_conv list.set ..

schematic_goal main_auto_trans:
  shows "trans (automaton_of (net_automata ! 0)) = ?x"
  apply (subst timed_automaton_net_def)
  apply (subst nth_Cons_0)
  unfolding main_auto_def Let_def comp_def snd_conv trans_def automaton_of_def 
    prod.case fst_conv list.set ..


(* Indices of locations and automata are offset by 1 w.r.t. actions' indices *)

subsection \<open>Definitions for conditions\<close>
definition act_clock_pre_happ where
"act_clock_pre_happ c cons a t = (
  if (cons = act_to_start_clock) 
  then (c (act_to_start_clock a) = real_of_rat (planning_sem.exec_time (at_start a) t))
  else 
  if (cons = act_to_end_clock) 
  then (c (act_to_end_clock a) = real_of_rat (planning_sem.exec_time (at_end a) t)) 
  else undefined)"

lemma act_clock_pre_happ_simps[simp]:
  "act_clock_pre_happ c act_to_end_clock a t =  (c (act_to_end_clock a) = real_of_rat (planning_sem.exec_time (at_end a) t))"
  "act_clock_pre_happ c act_to_start_clock a t =  (c (act_to_start_clock a) = real_of_rat (planning_sem.exec_time (at_start a) t))"
  using act_clock_pre_happ_def clock_cons_unique by auto
  

subsubsection \<open>Mutex constraints\<close>

text \<open>This only works for the direction from plan to run.\<close>
(* goal cases*)
schematic_goal net_int_clocks_alt:
  shows "set (net_int_clocks h) = ?x"
  unfolding net_int_clocks_def Let_def filter_append set_append set_map set_filter ..

lemma mutex_0_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.plan_happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.plan_happ_seq \<or> h = at_start a \<longrightarrow> act_clock_pre_happ c act_to_start_clock a t"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.plan_happ_seq \<or> h = at_end a \<longrightarrow> act_clock_pre_happ c act_to_end_clock a t"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap_action h b \<Longrightarrow> 0 < planning_sem.exec_time b t" for b by blast

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_start act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_start act) t" by simp
    moreover
    have "(t, at_start act) \<notin> planning_sem.plan_happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (act_to_start_clock act)" using s_corr act_clock_pre_happ_def a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (act_to_start_clock act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map act_to_start_clock (filter (\<lambda>a. mutex_effects h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by simp
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_end act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_end act) t" by simp
    moreover
    have "(t, at_end act) \<notin> planning_sem.plan_happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (act_to_end_clock act)" using e_corr act_clock_pre_happ_def clock_cons_unique a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (act_to_end_clock act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map act_to_end_clock (filter (\<lambda>a. mutex_effects h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by simp
    done
  ultimately
  show ?thesis 
    unfolding net_int_clocks_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed

lemma mutex_eps_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.plan_happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.plan_happ_seq \<or> h = at_start a \<longrightarrow> act_clock_pre_happ c act_to_start_clock a t"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.plan_happ_seq \<or> h = at_end a \<longrightarrow> act_clock_pre_happ c act_to_end_clock a t"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap_action h b \<Longrightarrow> rat_of_int \<epsilon> \<le> planning_sem.exec_time b t" for b 
    unfolding Rat.of_int_def by simp

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_start act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_start act) t" by simp
    have c: "(t, at_start act) \<notin> planning_sem.plan_happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (act_to_start_clock act)"
      using s_corr[THEN bspec, OF a(1), THEN mp, OF c, simplified]
      using x of_rat_less_eq unfolding act_clock_pre_happ_def
      by metis
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (act_to_start_clock act) \<epsilon>)"
      by auto
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map act_to_start_clock (filter (\<lambda>a. mutex_effects h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by blast
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap_action h (at_end act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_end act) t" by simp
    have c: "(t, at_end act) \<notin> planning_sem.plan_happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (act_to_end_clock act)"
      using e_corr[THEN bspec, OF a(1), THEN mp, OF c, simplified]
      using x of_rat_less_eq unfolding act_clock_pre_happ_def
      using clock_cons_unique by metis
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (act_to_end_clock act) \<epsilon>)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map act_to_end_clock (filter (\<lambda>a. mutex_effects h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_action_def comp_apply action_defs.mutex_snap_action_def by simp
    done
  ultimately
  show ?thesis 
    unfolding net_int_clocks_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed 

text \<open>Some duration constraints\<close>
lemma check_bexp_all: "check_bexp s (bexp_and_all bs) True" 
  if "\<forall>b \<in> set bs. check_bexp s b True"
  using that
  apply (induction bs)
   apply (subst bexp_and_all.simps)
    apply (rule check_bexp_is_val.intros)
  subgoal for b bs
    apply (subst bexp_and_all.simps)
    apply (subst simp_thms(21)[of True, symmetric])
    apply (rule check_bexp_is_val.intros)
    by auto
  done

lemma check_bexp_all_append: 
  assumes "check_bexp s (bexp_and_all bs) True"
      and "check_bexp s (bexp_and_all cs) True"
    shows "check_bexp s (bexp_and_all (bs @ cs)) True"
  using assms
  apply (induction bs arbitrary: cs)
  apply simp
  subgoal for b bs cs
    apply (subst append_Cons)
    apply (subst bexp_and_all.simps)
    apply (subst (asm) bexp_and_all.simps)
    apply (erule check_bexp_elims)
    apply (subst check_bexp_simps(3))
    by auto
  done

lemma check_bexp_Cons:
  assumes "check_bexp s b True"
      and "check_bexp s c True"
    shows "check_bexp s (bexp.and b c) True"
  apply (subst check_bexp_simps)
  using assms by simp


lemma l_dur_sat_if: 
  assumes "planning_sem.satisfies_duration_bounds act r"
      and "((cv (act_to_start_clock act))::real) = of_rat r"
    shows "cv \<turnstile> map conv_ac (l_dur act)"
  using assms
  unfolding planning_sem.satisfies_duration_bounds_def l_dur_def lower_sem_def comp_def Let_def 
  apply (subst (asm) temp_plan_defs.satisfies_duration_bounds_def)
  unfolding temp_plan_defs_def temp_planning_problem_def 
  using eps_ran apply blast
  apply (cases "lower act")
   apply simp
  subgoal for lb
    apply (cases lb)
    subgoal for tl
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less of_rat_of_int_eq)
    subgoal for tl
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct1)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less_eq of_rat_of_int_eq)
    done
  done
(* coercions *)
(* declare [[show_sorts]] *)
(* show sorts *)
find_theorems "?x < ?y"
lemma u_dur_sat_if:
  assumes "planning_sem.satisfies_duration_bounds act r"
      and "((cv (act_to_start_clock act))::real) = of_rat r"
    shows "cv \<turnstile> map conv_ac (u_dur act)"
  using assms
  unfolding planning_sem.satisfies_duration_bounds_def u_dur_def Let_def upper_sem_def comp_def
  apply (subst (asm) temp_plan_defs.satisfies_duration_bounds_def)
  unfolding temp_plan_defs_def temp_planning_problem_def 
  using eps_ran apply blast
  apply (cases "upper act")
   apply simp
  subgoal for ub
    apply (cases ub)
    subgoal for tu
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct2)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less of_rat_of_int_eq)
    subgoal for tu
      apply (subst clock_val_def)
      apply simp
      apply (rule)
      apply (drule conjunct2)
      apply (erule ssubst[of "cv (act_to_start_clock act)"])
      by (metis of_rat_less_eq of_rat_of_int_eq)
    done
  done

lemma ending_actions_sat_dur_const_specs:
  assumes "a \<in> set actions"
      and "planning_sem.is_ending_action t a"
      and "act_clock_pre_happ c act_to_start_clock a t"
    shows "c \<turnstile> map conv_ac (u_dur a)" "c \<turnstile> map conv_ac (l_dur a)"
  apply -
   apply (rule u_dur_sat_if)
    apply (rule planning_sem.ending_act_sat_dur_bounds)
  apply (rule assms)+
  using assms unfolding act_clock_pre_happ_def apply simp
   apply (rule l_dur_sat_if)
    apply (rule planning_sem.ending_act_sat_dur_bounds)
  apply (rule assms)+
  using assms unfolding act_clock_pre_happ_def by simp


lemma instant_actions_sat_dur_const_specs:
  assumes "a \<in> set actions"
      and "planning_sem.is_instant_action t a"
      and "c (act_to_start_clock a) = 0"
    shows "c \<turnstile> map conv_ac (u_dur a)" "c \<turnstile> map conv_ac (l_dur a)"
  using assms by (auto intro: u_dur_sat_if l_dur_sat_if planning_sem.instant_act_sat_dur_bounds)

lemma ending_actions_sat_mutex_const_specs:
  assumes in_acts: "a \<in> set actions"
    and ending: "planning_sem.is_ending_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_end_clock a t"
              shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_end a)))" 
                "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_end a)))"
  subgoal
    apply (rule mutex_0_constraint_sat)
    using assms(2) planning_sem.is_ending_action_def apply blast
     apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_end b) \<in> planning_sem.plan_happ_seq")
      using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts 
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI)+
    apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts
       apply (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)
      apply (cases "a = b")
      using clocks in_acts rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def by auto
    done
  apply (rule mutex_eps_constraint_sat)
  using assms(2) planning_sem.is_ending_action_dests apply blast
   apply (intro ballI impI)
  subgoal for b
    apply (cases "(t, at_end b) \<in> planning_sem.plan_happ_seq")
    using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts 
    by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI)+
  apply (intro ballI impI)
  subgoal for b
    apply (erule disjE)
    using clocks in_acts
     apply (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)
    apply (cases "a = b")
    using clocks in_acts rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def by auto
  done

lemma instant_action_sat_mutex_start:
  assumes in_acts: "a \<in> set actions"
    and instant: "planning_sem.is_instant_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_start_clock a t"
    and g: " g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_start a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_start a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_end a) \<in> planning_sem.plan_happ_seq" 
          "(t, at_start a) \<in> planning_sem.plan_happ_seq" using instant planning_sem.is_instant_action_def by simp+
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_start b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
  apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts rat_impl.set_impl.at_start_inj_on_acts unfolding inj_on_def
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_end b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_start b) \<in> planning_sem.plan_happ_seq")
      using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_starting_actionI 
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed

lemma instant_action_sat_mutex_end:
  assumes in_acts: "a \<in> set actions"
    and instant: "planning_sem.is_instant_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_end_clock a t"
    and g: "g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_end a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_end a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_end a) \<in> planning_sem.plan_happ_seq" using instant planning_sem.is_instant_action_def by simp
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.plan_happ_seq \<or> at_end a = at_start b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_end b) \<in> planning_sem.plan_happ_seq")
      subgoal using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_ending_actionI by blast
      subgoal using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_not_happening_actionI by blast
      done
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.plan_happ_seq \<or> at_end a = at_end b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
  apply (intro ballI impI)
    subgoal for b
      using clocks in_acts rat_impl.set_impl.at_end_inj_on_acts unfolding inj_on_def
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed

lemma starting_action_sat_mutex_start:
  assumes in_acts: "a \<in> set actions"
    and starting: "planning_sem.is_starting_action t a"
    and clocks: "\<forall>b\<in>set actions. planning_sem.is_ending_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_starting_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "\<forall>b\<in>set actions. planning_sem.is_not_happening_action t b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
                "act_clock_pre_happ c act_to_start_clock a t"
    and g: " g = map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks (at_start a))) \<or> 
            g = map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (net_int_clocks (at_start a)))"
  shows "c \<turnstile> g"
proof -
  have 1: "(t, at_start a) \<in> planning_sem.plan_happ_seq" using starting planning_sem.is_starting_action_def by simp+
  have 2: "\<forall>b\<in>set actions. (t, at_start b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_start b \<longrightarrow> act_clock_pre_happ c act_to_start_clock b t"
  apply (intro ballI impI)
    subgoal for b
      apply (erule disjE)
      using clocks in_acts rat_impl.set_impl.at_start_inj_on_acts unfolding inj_on_def
      by (blast intro: planning_sem.is_ending_actionI planning_sem.is_not_happening_actionI intro: clocks)+
    done
  have 3: "\<forall>b\<in>set actions. (t, at_end b) \<notin> planning_sem.plan_happ_seq \<or> at_start a = at_end b \<longrightarrow> act_clock_pre_happ c act_to_end_clock b t"
    apply (intro ballI impI)
    subgoal for b
      apply (cases "(t, at_start b) \<in> planning_sem.plan_happ_seq")
      using clocks rat_impl.set_impl.end_start_disj_on_acts in_acts planning_sem.is_starting_actionI 
      by (blast intro: planning_sem.is_starting_actionI planning_sem.is_not_happening_actionI)+
    done
  show ?thesis
    using g 1 2 3 mutex_0_constraint_sat mutex_eps_constraint_sat 
    by blast
qed
end
end

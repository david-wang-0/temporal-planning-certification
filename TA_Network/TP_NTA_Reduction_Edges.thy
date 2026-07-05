theory TP_NTA_Reduction_Edges
  imports TP_NTA_Reduction_Prelims
begin
context tp_nta_reduction_correctness
begin

text \<open>Generic Map lemmas restored from Munta's \<open>Simple_Network_Language_Renaming\<close>
  (dropped from the import path by the FPS re-point); used by \<open>init_vars_bounded\<close>
  and \<open>map_of_net_bounds_init_goal\<close>.\<close>
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

primcorec goal_run::"
  (nat list \<times>
    (String.literal \<rightharpoonup> int) \<times>
    (String.literal, real) cval) 
\<Rightarrow> (nat list \<times>
    (String.literal \<rightharpoonup> int) \<times>
    (String.literal, real) cval) stream" where
"goal_run s = s ## (goal_run s)"


lemmas single_step_intro = graph_impl.steps.Cons[OF _ graph_impl.steps.Single]

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

lemma is_upds_set_vars_map: 
  assumes "upds = (map (set_var n) xs)"
      and "v' = (v(xs [\<mapsto>] (map (\<lambda>x. n) xs)))"
    shows "is_upds v upds v'"
  unfolding assms
  by (induction xs arbitrary: v) (auto intro: is_upds.intros simp: is_upd_def check_bexp_simps is_val_simps)

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
  "map_of net_bounds acts_active = Some (0, int (length actions))" unfolding all_vars_def Let_def by simp

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

end
end

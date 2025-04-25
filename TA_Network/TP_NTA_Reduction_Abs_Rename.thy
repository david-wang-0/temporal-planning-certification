theory TP_NTA_Reduction_Abs_Rename
  imports TP_NTA_Reduction_Spec
begin

section \<open>Renumbering the abstract definition\<close>

subsubsection \<open>Some functions for renumbering\<close>

instance rat::time 
  apply standard 
  using dense_order_class.dense apply blast
  using verit_eq_simplify(24) by blast

definition mk_renum::"'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"mk_renum l \<equiv>
  let
    nums = [0..<length l];
    act_nums = zip l nums;
    f = map_of act_nums
  in the o f"

definition mk_snd_ord_renum::"'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat" where
"mk_snd_ord_renum \<equiv> (!) o map mk_renum"

lemma map_of_zip_lemma:
  assumes "x \<in> set as"
  shows "the (map_of (zip as [n..<n + length as]) x) = n + List_Index.index as x"
  using assms
proof (induction as arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a as n)
  show ?case 
  proof (cases "x \<in> set as")
    case True
    show ?thesis
    proof (cases "x = a")
      case xa: True
      hence xa: "x = a" using Cons by simp
      hence "the (map_of (zip (a # as) [n..<n + length (a # as)]) x) = n" by (subst upt_conv_Cons) auto
      then show ?thesis using xa by simp
    next
      case False
      hence "the (map_of (zip (a # as) [n..<n + length (a # as)]) x) = the (map_of (zip as [Suc n..<n + length (a # as)]) x)"
        apply (subst upt_conv_Cons)
         apply simp
        apply (subst zip_Cons_Cons)
        apply (subst map_of_Cons_code(2)) 
        by (metis (full_types))
      also have "... = the (map_of (zip as [Suc n..<Suc n + length as]) x)"
        by simp
      also have "... = Suc n + List_Index.index as x" using Cons.IH[OF True] by blast
      finally show ?thesis using index_Cons False by auto
    qed
  next
    case False
    hence xa: "x = a" using Cons by simp
    hence "the (map_of (zip (a # as) [n..<n + length (a # as)]) x) = n"
      apply (subst upt_conv_Cons)
      by auto
    then show ?thesis 
      using xa by simp
  qed
qed
    

lemma mk_renum_index: 
  assumes "x \<in> set xs"
  shows "mk_renum xs x = List_Index.index xs x"
  unfolding mk_renum_def
  using map_of_zip_lemma[OF assms, of 0]
  by auto
  

lemma mk_renum_inj: "inj_on (mk_renum xs) (set xs)"
proof
  fix x y
  assume x: "x \<in> set xs"
     and y: "y \<in> set xs"
     and rn: "mk_renum xs x = mk_renum xs y"
  from x mk_renum_index
  have "mk_renum xs x = List_Index.index xs x" by metis
  moreover
  from y mk_renum_index
  have "mk_renum xs y = List_Index.index xs y" by metis
  ultimately
  have "List_Index.index xs x = List_Index.index xs y" using rn by simp
  thus "x = y" using inj_on_index unfolding inj_on_def using x y by simp
qed


context tp_nta_reduction_spec
begin

subsection \<open>Automata\<close>

definition "ntas \<equiv> 
let (automata, clocks, vars, formula) = timed_automaton_net_spec 
in automata"                                     

text \<open>The returned automata also contain extra values\<close>
abbreviation "get_actual_auto \<equiv> snd o snd o snd"

subsubsection \<open>Actual automata\<close>

definition actual_autos where
"actual_autos = map get_actual_auto ntas"


lemma in_actual_autosE:
  assumes auto: "auto \<in> set actual_autos"
      and alt:  "\<And>act. auto = (snd o snd) (action_to_automaton_spec act) \<Longrightarrow> act \<in> set actions \<Longrightarrow> thesis"
                "auto = (snd o snd) main_auto_spec \<Longrightarrow> thesis"
   shows thesis
proof -
  from auto 
  have "auto \<in> (\<lambda>a. snd (snd a)) ` (set (map action_to_automaton_spec actions)) \<or> auto = snd (snd main_auto_spec)"
    unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case comp_apply
    set_map 
    apply -
    apply (subst (asm) image_image[symmetric, of _ snd])
    apply (subst (asm) zip_range_id)
    by auto
  then consider
    "\<exists>act \<in> set actions. auto = (snd o snd) (action_to_automaton_spec act)"
  | "auto = (snd o snd) main_auto_spec"
    by force
  thus ?thesis
    apply cases
    using alt by blast+
qed
  
(* definition auto_trans where
"auto_trans auto \<equiv> 
  let
    (committed, urgent, trans, invs) = auto
  in
    trans" *)

subsubsection \<open>Parts of transitions\<close>
abbreviation "trans_resets \<equiv> fst o snd o snd o snd o snd o snd"

abbreviation "trans_guards \<equiv> fst o snd o snd"

subsubsection \<open>Actual transitions\<close>

(* definition get_actual_auto where
"get_actual_auto gen_auto \<equiv> 
  let 
    (name, initial, states, committed, urgent, transitions, invs) = gen_auto 
  in (committed, urgent, transitions, invs)" *)

abbreviation "auto_trans \<equiv> (fst o snd o snd)"

abbreviation "auto_invs \<equiv> (snd o snd o snd)"

definition ta_trans where
"ta_trans = map auto_trans actual_autos"

definition "all_ta_trans \<equiv> fold (\<union>) (map set ta_trans) {}"

definition ta_invs where
"ta_invs = map auto_invs actual_autos"
                                  
subsection \<open>Clocks\<close>

definition "nta_clocks \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in clocks"

definition "urge_clock \<equiv> Urge"

definition "clock_renum \<equiv> mk_renum (urge_clock # nta_clocks)"

subsubsection \<open>Actual clocks\<close>

find_theorems name: "clkp"

definition "trans_clocks t\<equiv>
let (l, b, c, a, u, r, l') = t
in set r \<union> (fst ` collect_clock_pairs c)"

definition "trans_to_clocks trs \<equiv> 
let 
  trans_clocks = map trans_clocks trs
in
  fold (\<union>) trans_clocks {}"

definition "inv_clocks i \<equiv> fst ` (collect_clock_pairs (snd i))"

definition "invs_to_clocks is \<equiv>
let 
  inv_clocks = map inv_clocks is
in
  fold (\<union>) inv_clocks {}"

definition "ta_clocks \<equiv> map trans_to_clocks ta_trans @ map invs_to_clocks ta_invs"

definition "all_ta_clocks \<equiv> fold (\<union>) ta_clocks {}"

lemma fold_union:
  "fold (\<union>) S T =  \<Union> (set S) \<union> T"
  by (induction S arbitrary: T) auto

lemma fold_union':
  "fold (\<union>) S {} =  \<Union> (set S)"
  apply (subst fold_union)
  apply (subst Un_empty_right)
  ..

lemma int_clocks_set: "set (int_clocks_spec d) \<subseteq> set (map ActStart actions) \<union> set (map ActEnd actions)"
  unfolding int_clocks_spec_def by auto

lemma nta_clocks_alt: "set nta_clocks = set (map ActStart actions) \<union> set (map ActEnd actions)"
  unfolding nta_clocks_def Let_def timed_automaton_net_spec_def prod.case by simp


lemma all_ta_clocks_alt: "all_ta_clocks = 
(\<Union>trs\<in>set ta_trans. \<Union> ((set o trans_resets) ` set trs)) \<union> 
(\<Union>trs\<in>set ta_trans. \<Union> (((`) fst o collect_clock_pairs o trans_guards) ` set trs)) \<union> 
(\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
proof -
  have 1: "all_ta_clocks = (\<Union>trs\<in>set ta_trans. \<Union>(l, b, c, a, u, r, l')\<in>set trs. set r \<union> fst ` collect_clock_pairs c) \<union> 
    (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
  unfolding all_ta_clocks_def ta_clocks_def
  apply (subst fold_union')
  unfolding trans_to_clocks_def trans_clocks_def Let_def
  apply (subst fold_union')
  apply (subst set_map)+
  unfolding invs_to_clocks_def ta_invs_def Let_def
  apply (subst fold_union')
  apply (subst map_map)+
  unfolding comp_apply
  by simp
  show ?thesis
  proof (subst 1; rule equalityI; rule subsetI)
    fix x
    assume "x \<in> (\<Union>trs\<in>set ta_trans. \<Union>(l, b, c, a, u, r, l')\<in>set trs. set r \<union> fst ` collect_clock_pairs c)
       \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
    thus "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> ((set \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) snd ` set trs)) 
      \<union> (\<Union>trs\<in>set ta_trans. \<Union> (((`) fst \<circ> collect_clock_pairs \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd) snd ` set trs))
      \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
      by fastforce
  next
    fix x
    assume "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> ((set \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) snd ` set trs)) 
      \<union> (\<Union>trs\<in>set ta_trans. \<Union> (((`) fst \<circ> collect_clock_pairs \<circ>\<circ>\<circ> (\<circ>)) (fst \<circ> snd) snd ` set trs))
      \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
    hence "x \<in> (\<Union>trs\<in>set ta_trans. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x))))))) 
      \<union> (\<Union>trs\<in>set ta_trans. \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))
      \<union> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" unfolding comp_apply .
    hence
      "(\<exists>tr \<in> set ta_trans. x \<in> (\<Union>x\<in>set tr. set (fst (snd (snd (snd (snd (snd x)))))))) \<or>
       (\<exists>tr \<in> set ta_trans. x \<in> (\<Union>x\<in>set tr. fst ` collect_clock_pairs (fst (snd (snd x))))) \<or>
       x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" by auto
    then consider 
      tr where "tr \<in> set ta_trans" "x \<in> (\<Union>x\<in>set tr. set (fst (snd (snd (snd (snd (snd x)))))))"
    | tr where "tr \<in> set ta_trans" "x \<in> (\<Union>x\<in>set tr. fst ` collect_clock_pairs (fst (snd (snd x))))" 
    | "x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" 
      apply -
      apply (elim disjE)
        apply blast
      apply metis
      by blast
    then consider
      tr where "tr \<in> set ta_trans" "x \<in> (\<Union>(l, b, c, a, u, r, l')\<in>set tr. set r)"
    | tr where "tr \<in> set ta_trans" "x \<in> (\<Union>(l, b, c, a, u, r, l')\<in>set tr. fst ` collect_clock_pairs c)" 
    | "x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" 
      apply cases
      by fastforce+
    hence "x \<in> (\<Union>tr\<in>set ta_trans.(\<Union>(l, b, c, a, u, r, l')\<in>set tr. set r))
        \<or> x \<in> (\<Union>tr\<in>set ta_trans.(\<Union>(l, b, c, a, u, r, l')\<in>set tr. fst ` collect_clock_pairs c))
        \<or> x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" 
      apply cases
      apply fast
       apply blast
      by blast
    thus "x \<in> (\<Union>trs\<in>set ta_trans. \<Union>(l, b, c, a, u, r, l')\<in>set trs. set r \<union> fst ` collect_clock_pairs c) \<union> 
          (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))"
      by blast
  qed
qed

lemma all_ta_clocks_correct: "all_ta_clocks \<subseteq> set nta_clocks"
proof -
  have "set nta_clocks = ActStart ` (set actions) \<union> ActEnd ` (set actions)"
    unfolding nta_clocks_def Let_def prod.case timed_automaton_net_spec_def by simp
  moreover
  have "all_ta_clocks \<subseteq> ActStart ` (set actions) \<union> ActEnd ` (set actions)"
  proof
    fix x
    assume "x \<in> all_ta_clocks"
    then consider "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> ((set o trans_resets) ` set trs))"
      | "x \<in> (\<Union>trs\<in>set ta_trans. \<Union> (((`) fst o collect_clock_pairs o trans_guards) ` set trs))"
      | "x \<in> (\<Union>auto\<in>set actual_autos. \<Union> (inv_clocks ` set (auto_invs auto)))" unfolding all_ta_clocks_alt comp_apply by blast
    thus "x \<in> ActStart ` (set actions) \<union> ActEnd ` (set actions)" 
    proof cases
      case 1
      then obtain auto_ts trans where
        at: "auto_ts \<in> set ta_trans"
        and t:"trans \<in> set auto_ts"
        and x: "x \<in> set (trans_resets trans)" by auto
      from at obtain auto where
        auto: "auto \<in> set actual_autos" 
        and at': "auto_ts = auto_trans auto" unfolding ta_trans_def by auto
      consider (act) act where
        "act \<in> set actions"
        "auto = (snd o snd) (action_to_automaton_spec act)"
      | (main) "auto = (snd o snd) main_auto_spec"
        using in_actual_autosE[OF auto] unfolding comp_apply by metis
      then show ?thesis
      proof cases
        case act
        have "trans \<in> set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act]" 
          using t[simplified at' act(2)] unfolding comp_apply action_to_automaton_spec_def Let_def prod.case snd_conv fst_conv .
        with x consider
          "x \<in> set (trans_resets (start_edge_spec act))"|
          "x \<in> set (trans_resets (edge_2_spec act))"|
          "x \<in> set (trans_resets (edge_3_spec act))"|
          "x \<in> set (trans_resets (end_edge_spec act))"|
          "x \<in> set (trans_resets (instant_trans_edge_spec act))" unfolding comp_apply by fastforce
        thus ?thesis 
          apply cases
          subgoal unfolding start_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
          subgoal unfolding edge_2_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          subgoal unfolding edge_3_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
          subgoal unfolding end_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          unfolding instant_trans_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
      next
        case main
        have "trans \<in> set [main_auto_init_edge_spec, main_auto_goal_edge_spec, main_auto_loop_spec]" 
          using t[simplified at' main] unfolding comp_apply main_auto_spec_def Let_def prod.case snd_conv fst_conv .
        with x consider
          "x \<in> set (trans_resets main_auto_init_edge_spec)"|
          "x \<in> set (trans_resets main_auto_goal_edge_spec)"|
          "x \<in> set (trans_resets main_auto_loop_spec)" unfolding comp_apply by auto
        thus ?thesis 
          apply cases
          subgoal unfolding main_auto_init_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          subgoal unfolding main_auto_goal_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          unfolding main_auto_loop_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
      qed
    next
      case 2
      then obtain auto_ts trans g where
        at: "auto_ts \<in> set ta_trans"
        and t: "trans \<in> set auto_ts"
        and g: "g \<in> set (trans_guards trans)"
        and x: "x = fst (constraint_pair g)" unfolding comp_apply collect_clock_pairs_def by blast
      from at obtain auto where
        auto: "auto \<in> set actual_autos" 
        and at': "auto_ts = auto_trans auto" unfolding ta_trans_def by auto
      consider (act) act where
        "act \<in> set actions"
        "auto = (snd o snd) (action_to_automaton_spec act)"
      | (main) "auto = (snd o snd) main_auto_spec"
        using in_actual_autosE[OF auto] unfolding comp_apply by metis
      then show ?thesis 
      proof cases
        case act
        have "trans \<in> set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act]" 
          using t[simplified at' act(2)] unfolding comp_apply action_to_automaton_spec_def Let_def prod.case snd_conv fst_conv .
        with x g consider
          "x \<in> fst ` constraint_pair ` set (trans_guards (start_edge_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (edge_2_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (edge_3_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (end_edge_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (instant_trans_edge_spec act))" unfolding comp_apply by fastforce
        hence "\<exists>act' \<in> set actions. x = ActStart act' \<or> x = ActEnd act'" 
          apply cases
          subgoal unfolding start_edge_spec_def Let_def prod.case comp_apply fst_conv snd_conv int_clocks_spec_def set_map set_append by auto
          subgoal unfolding edge_2_spec_def Let_def prod.case comp_apply fst_conv snd_conv by auto
          subgoal unfolding edge_3_spec_def Let_def prod.case comp_apply fst_conv snd_conv int_clocks_spec_def set_map u_dur_spec_def l_dur_spec_def set_append 
            using act(1) 
            apply (cases "lower act"; cases "upper act")
            subgoal by fastforce
            subgoal for a by (cases a) fastforce+
            subgoal for a by (cases a) fastforce+
            subgoal for a b by (cases a; cases b) fastforce+
            done
          subgoal unfolding end_edge_spec_def Let_def prod.case comp_apply fst_conv snd_conv by auto
          unfolding instant_trans_edge_spec_def Let_def prod.case comp_apply fst_conv snd_conv int_clocks_spec_def set_map u_dur_spec_def l_dur_spec_def set_append 
            using act(1) 
            apply (cases "lower act"; cases "upper act")
            subgoal by fastforce
            subgoal for a by (cases a) fastforce+
            subgoal for a by (cases a) fastforce+
            subgoal for a b by (cases a; cases b) fastforce+
            done
        then show ?thesis by blast
      next
        case main
        have "trans \<in> set [main_auto_init_edge_spec, main_auto_goal_edge_spec, main_auto_loop_spec]" 
          using t[simplified at' main] unfolding comp_apply main_auto_spec_def Let_def prod.case snd_conv fst_conv .
        with x g consider
          "x \<in> fst ` constraint_pair ` set (trans_guards main_auto_init_edge_spec)"|
          "x \<in> fst ` constraint_pair ` set (trans_guards main_auto_goal_edge_spec)"|
          "x \<in> fst ` constraint_pair ` set (trans_guards main_auto_loop_spec)" unfolding comp_apply by auto
        then show ?thesis apply cases
          subgoal unfolding main_auto_init_edge_spec_def Let_def comp_apply fst_conv snd_conv by auto
          subgoal unfolding main_auto_goal_edge_spec_def Let_def comp_apply fst_conv snd_conv by auto
          unfolding main_auto_loop_spec_def Let_def comp_apply fst_conv snd_conv by auto
      qed
    next
      case 3
      then obtain auto invars where
        auto: "auto \<in> set actual_autos"
        and invars: "invars \<in> set (snd (snd (snd auto)))"
        and x: "x \<in> inv_clocks invars" by auto
      consider (act) act where
        "act \<in> set actions"
        "auto = (snd o snd) (action_to_automaton_spec act)"
      | (main) "auto = (snd o snd) main_auto_spec"
        using in_actual_autosE[OF auto] unfolding comp_apply by metis
      then show ?thesis
        apply cases
         unfolding action_to_automaton_spec_def main_auto_spec_def Let_def comp_apply snd_conv using invars x by simp+
    qed
  qed
  ultimately
  show ?thesis by simp
qed 
subsection \<open>Variables\<close>

definition "nta_vars \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in vars"

definition "var_renum \<equiv> mk_renum (map fst nta_vars)"

subsubsection \<open>Actual Variables\<close>


definition "vars_of_update u \<equiv>
let 
  (v, e) = u
in insert v (vars_of_exp e)"

definition "trans_vars t \<equiv> 
let
  (l, c, g, a, u, r, l') = t
in vars_of_bexp c \<union> fold (\<union>) (map vars_of_update u) {}"

definition "trans_to_vars ts \<equiv>
let 
  trans_vars = map trans_vars ts
in fold (\<union>) trans_vars {}"

definition "actual_variables \<equiv> 
let                                  
  ts_vars = map trans_to_vars ta_trans
in fold (\<union>) ts_vars {}"

lemma update_vars_simps: 
  "vars_of_update (set_prop_ab n p) = {PropVar p}"
  "vars_of_update (inc_prop_ab n p) = {PropVar p}"
  "vars_of_update (set_prop_lock_ab n p) = {PropLock p}"
  "vars_of_update (inc_prop_lock_ab n p) = {PropLock p}"
  unfolding vars_of_update_def set_prop_ab_def inc_prop_ab_def set_prop_lock_ab_def inc_prop_lock_ab_def Let_def prod.case by simp+

lemma condition_vars_simps: 
  "vars_of_bexp (is_prop_ab n p) = {PropVar p}"
  "vars_of_bexp (is_prop_lock_ab n p) = {PropLock p}"
  unfolding is_prop_ab_def is_prop_lock_ab_def by simp+

lemma vars_of_bexp_all:
  "vars_of_bexp (bexp_and_all bs) = (\<Union>b \<in> set bs. vars_of_bexp b)"
  by (induction bs; simp)

lemma nta_vars': "nta_vars = all_vars_spec" 
  unfolding nta_vars_def timed_automaton_net_spec_def Let_def prod.case ..

lemma actual_variables_correct: "actual_variables = set (map fst nta_vars)"
proof (rule equalityI; rule subsetI)
  fix x
  assume "x \<in> actual_variables"
  then obtain tr aut where
    aut: "aut \<in> set actual_autos"
    and tr: "tr \<in> set (auto_trans aut)"
    and x: "x \<in> trans_vars tr"
      unfolding actual_variables_def trans_to_vars_def Let_def
      fold_union' comp_apply ta_trans_def by auto 
  from in_actual_autosE[OF aut]
  consider 
    (act) act where "act \<in> set actions"
    "aut = (snd o snd) (action_to_automaton_spec act)"
  | (main) "aut = (snd o snd) main_auto_spec" by metis

  thus "x \<in> set (map fst nta_vars)"
  proof cases
    case act
    with tr
    have "tr \<in> {start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act}" unfolding action_to_automaton_spec_def Let_def comp_apply snd_conv by auto
    with x consider
      "x \<in> trans_vars (start_edge_spec act)" |
      "x \<in> trans_vars (edge_2_spec act)" |
      "x \<in> trans_vars (edge_3_spec act)" |
      "x \<in> trans_vars (end_edge_spec act)" |
      "x \<in> trans_vars (instant_trans_edge_spec act)" by auto
    note act_cases = this
    then show ?thesis 
    proof cases
      case 1
      hence "x \<in> \<Union> (vars_of_bexp ` set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start act))) (dels (at_start act))) @ map (is_prop_ab 1) (pre (at_start act)))) \<union>
       \<Union> (vars_of_update ` set (map (set_prop_ab 1) (adds (at_start act)) @ map (set_prop_ab 0)  (dels (at_start act))))" unfolding trans_vars_def start_edge_spec_def Let_def prod.case fold_union' vars_of_bexp_all set_map .
      hence x: "x \<in> PropLock ` (set (dels (at_start act)) - set (adds (at_start act))) \<or> x \<in> PropVar ` (set (pre (at_start act)) \<union> set (dels (at_start act)) \<union> set (adds (at_start act)))" using update_vars_simps condition_vars_simps by auto
      have s: "set (pre (at_start act)) \<union> set (dels (at_start act)) \<union> set (adds (at_start act)) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply act_ref_fluents_def using act(1) by simp
      have x': "x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x  \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst snap_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 2
      hence "x \<in> \<Union> (vars_of_bexp ` is_prop_ab 1 ` set (over_all act)) \<union> \<Union> (vars_of_update ` inc_prop_lock_ab 1 ` set (over_all act))" 
        unfolding edge_2_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map by blast
      hence x: "x \<in> PropLock ` set (over_all act) \<or> x \<in> PropVar ` set (over_all act)" using update_vars_simps condition_vars_simps by auto
      have s: "set (over_all act) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply using act(1) unfolding act_ref_fluents_def by auto
      have x': "x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x  \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" 
        unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst inv_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 3
      hence "x \<in> vars_of_bexp bexp.true \<union> \<Union> (vars_of_update ` inc_prop_lock_ab (- 1) ` set (over_all act))" unfolding edge_3_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map by simp
      hence x: "x \<in> PropLock ` set (over_all act)" using update_vars_simps condition_vars_simps by auto
      have s: "set (over_all act) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply using act(1) unfolding act_ref_fluents_def by auto
      have x': "x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x  \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" 
        unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst inv_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 4
      hence "x \<in> \<Union> (vars_of_bexp ` set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_end act))) (dels (at_end act))) @ map (is_prop_ab 1) (pre (at_end act)))) \<union>
       \<Union> (vars_of_update ` set (map (set_prop_ab 1) (adds (at_end act)) @ map (set_prop_ab 0) (dels (at_end act))))" unfolding trans_vars_def end_edge_spec_def Let_def prod.case fold_union' vars_of_bexp_all set_map .
      hence x: "x \<in> PropLock ` (set (dels (at_end act)) - set (adds (at_end act))) \<or> x \<in> PropVar ` (set (pre (at_end act)) \<union> set (dels (at_end act)) \<union> set (adds (at_end act)))" using update_vars_simps condition_vars_simps by auto
      have s: "set (pre (at_end act)) \<union> set (dels (at_end act)) \<union> set (adds (at_end act)) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply act_ref_fluents_def using act(1) by simp
      have x': "x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x  \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst (2) snap_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 5
     then show ?thesis unfolding instant_trans_edge_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map by simp 
    qed
  next
    case main
    with tr
    have "tr \<in> {main_auto_init_edge_spec, main_auto_goal_edge_spec, main_auto_loop_spec}" unfolding main_auto_spec_def Let_def comp_apply snd_conv by auto
    with x consider
      "x \<in> trans_vars (main_auto_init_edge_spec)" |
      "x \<in> trans_vars (main_auto_goal_edge_spec)" |
      "x \<in> trans_vars (main_auto_loop_spec)" by blast
    then show ?thesis 
    proof cases
      case 1
      then consider 
        "x = PlanningLock" |
        "x = ActsActive" |
        "x \<in> PropVar ` set init" 
        unfolding main_auto_init_edge_spec_def  Let_def trans_vars_def prod.case fold_union'
         vars_of_bexp_all list.set(2) set_map image_insert Union_insert 
        apply (elim UnE)
        subgoal using update_vars_simps by simp
        subgoal unfolding vars_of_update_def Let_def prod.case by simp
        subgoal unfolding vars_of_update_def Let_def prod.case by simp
        subgoal using update_vars_simps by blast
        done
      then show ?thesis 
      proof cases
        case 1
        then show ?thesis unfolding nta_vars_def timed_automaton_net_spec_def all_vars_spec_def Let_def prod.case by simp
      next
        case 2
        then show ?thesis unfolding nta_vars_def timed_automaton_net_spec_def all_vars_spec_def Let_def prod.case by simp
      next
        case 3
        hence "x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using init_props by auto
        moreover 
        have "(\<lambda>x.  x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> PropVar ` set init \<union> PropVar ` set goal) x" using 3 by blast
        ultimately
        show ?thesis unfolding nta_vars_def timed_automaton_net_spec_def all_vars_spec_def Let_def prod.case set_map by auto
      qed
    next
      case 2
      then consider 
        "x = PlanningLock" |
        "x = ActsActive" |
        "x \<in> PropVar ` set goal" 
        unfolding  main_auto_goal_edge_spec_def Let_def trans_vars_def prod.case fold_union'
         vars_of_bexp_all list.set(2) set_map image_insert Union_insert 
        apply (elim UnE UnionE)
          subgoal
            apply (erule imageE)
            unfolding set_append using condition_vars_simps by auto
          subgoal
            unfolding vars_of_update_def by simp+
          subgoal
            using update_vars_simps by auto
          done
        then show ?thesis 
        proof cases
          case 1
          then show ?thesis unfolding nta_vars_def timed_automaton_net_spec_def all_vars_spec_def Let_def prod.case by simp
        next
          case 2
          then show ?thesis unfolding nta_vars_def timed_automaton_net_spec_def all_vars_spec_def Let_def prod.case by simp
        next
          case 3
        hence "x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using goal_props by auto
        moreover 
        have "(\<lambda>x.  x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> PropVar ` set init \<union> PropVar ` set goal) x" using 3 by blast
        ultimately
        show ?thesis unfolding nta_vars_def timed_automaton_net_spec_def all_vars_spec_def Let_def prod.case set_map by auto
      qed
    next
      case 3
      then show ?thesis unfolding main_auto_loop_spec_def trans_vars_def by simp
    qed
  qed
next
  fix x
  assume "x \<in> set (map fst nta_vars)"
  hence "x = ActsActive 
      \<or> x = PlanningLock 
      \<or> x \<in> fst `
         set (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> PropVar ` set init \<union> PropVar ` set goal)
               (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props))" 
    unfolding nta_vars' all_vars_spec_def Let_def set_map set_append image_Un
    apply -
    apply (erule UnE) 
    by fastforce+
  then consider
    "x = ActsActive"
    | "x = PlanningLock"
    | "x \<in> fst `
         set (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> PropVar ` set init \<union> PropVar ` set goal)
             (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props))" by blast
  thus "x \<in> actual_variables"
  proof cases
    case 1
    then show ?thesis unfolding actual_variables_def ta_trans_def trans_to_vars_def Let_def fold_union' set_map comp_apply actual_autos_def ntas_def timed_automaton_net_spec_def prod.case 
      apply -
      apply (subst (2) image_image[symmetric, of _ snd])
      apply (subst zip_range_id)
       apply simp
      unfolding main_auto_spec_def Let_def 
      apply (subst (2) image_image[symmetric, of _ snd])
      unfolding main_auto_goal_edge_spec_def Let_def
      apply (subst list.set(2))
      apply (subst image_insert)+
      apply (subst Union_iff)
      apply (rule bexI)
       defer
      unfolding fst_conv snd_conv 
       apply (rule insertI1)
      unfolding trans_vars_def 
      by simp
  next
    case 2
    then show ?thesis unfolding actual_variables_def ta_trans_def trans_to_vars_def Let_def fold_union' set_map comp_apply actual_autos_def ntas_def timed_automaton_net_spec_def prod.case 
      apply -
      apply (subst (2) image_image[symmetric, of _ snd])
      apply (subst zip_range_id)
       apply simp
      unfolding main_auto_spec_def Let_def 
      apply (subst (2) image_image[symmetric, of _ snd])
      unfolding main_auto_init_edge_spec_def Let_def
      apply (subst list.set(2))
      apply (subst image_insert)+
      apply (subst Union_iff)
      apply (rule bexI)
       defer
      unfolding fst_conv snd_conv 
       apply (rule insertI1)
      unfolding trans_vars_def 
      by simp
  next
    assume "x \<in> fst `
         set (filter (\<lambda>x. fst x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> PropVar ` set init \<union> PropVar ` set goal)
             (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props))"
    hence "x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> PropVar ` set init \<union> PropVar ` set goal" by auto
    from this[simplified fold_union' set_map]
    consider (act) act where 
      "x \<in> action_vars_spec act"
      "act \<in> set actions"
    | (init) "x \<in> PropVar ` set init"
    | (goal) "x \<in> PropVar ` set goal" by auto
    then show ?thesis 
    proof cases
      case act
      then consider
          "x \<in> inv_vars_spec (over_all act)"
        | "x \<in> snap_vars_spec (at_start act)" 
        | "x \<in> snap_vars_spec (at_end act)"
        apply (subst (asm) action_vars_spec_def)
        unfolding Let_def fold_union'  set_map set_append by blast
      hence x: "x \<in> \<Union> (trans_vars ` set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act])" 
      proof cases
        case 1
        hence "x \<in> trans_vars (edge_2_spec act)" unfolding inv_vars_spec_def Let_def set_append set_map edge_2_spec_def trans_vars_def prod.case vars_of_bexp_all fold_union 
          apply -
          apply (erule UnE)
          subgoal 
            apply (rule UnI2)
            using update_vars_simps by auto
          subgoal 
            apply (rule UnI1)
            using condition_vars_simps by auto
          done
        then show ?thesis by simp
      next
        case 2
        hence "x \<in> trans_vars (start_edge_spec act)" unfolding snap_vars_spec_def Let_def set_append set_map start_edge_spec_def trans_vars_def prod.case vars_of_bexp_all fold_union 
          apply -
          apply (elim UnE)
          subgoal using condition_vars_simps update_vars_simps by fast
          subgoal apply (rule UnI2) using condition_vars_simps update_vars_simps by auto
          subgoal apply (rule UnI1) using condition_vars_simps update_vars_simps by auto
          using condition_vars_simps update_vars_simps by auto
        then show ?thesis by simp
      next
        case 3
        hence "x \<in> trans_vars (end_edge_spec act)" unfolding snap_vars_spec_def Let_def set_append set_map end_edge_spec_def trans_vars_def prod.case vars_of_bexp_all fold_union 
          using condition_vars_simps update_vars_simps by auto
        then show ?thesis by simp
      qed
      show ?thesis unfolding actual_variables_def ta_trans_def Let_def fold_union' comp_apply trans_to_vars_def actual_autos_def ntas_def prod.case set_map timed_automaton_net_spec_def
        apply -
        apply (subst (2) image_image[symmetric, of _ snd])
        apply (subst zip_range_id)
         apply simp
        apply (subst list.set(2))
        apply (subst insert_is_Un)
        apply (subst image_Un)+
        apply (subst Union_Un_distrib)
        apply (rule UnI2)
        unfolding set_map action_to_automaton_spec_def Let_def 
        apply (subst image_image)+
        unfolding fst_conv snd_conv
        using act(2) x by blast
    next
      case init
      then show ?thesis unfolding actual_variables_def ta_trans_def Let_def fold_union' comp_apply trans_to_vars_def actual_autos_def ntas_def prod.case set_map timed_automaton_net_spec_def
        apply -
        apply (subst (2) image_image[symmetric, of _ snd])
        apply (subst zip_range_id)
         apply simp
        unfolding main_auto_spec_def Let_def
        apply (subst list.set(2))
        apply (subst image_insert)+
        apply (subst Union_iff)
        apply (rule bexI)
        defer
         apply (rule insertI1)
        unfolding fst_conv snd_conv 
        unfolding main_auto_init_edge_spec_def Let_def trans_vars_def fold_union' 
        apply (subst Union_iff)
        apply (rule bexI)
         defer
         apply (rule imageI)
         apply (subst list.set(2))
         apply (rule insertI1)
        unfolding prod.case
        apply (rule UnI2)
        unfolding set_map
        unfolding list.set image_insert
        apply (subst insert_is_Un)
        apply (subst (2) insert_is_Un)
        apply (subst Union_Un_distrib)+
        apply (rule UnI2)+
        using update_vars_simps by auto
    next
      case goal
      then show ?thesis unfolding actual_variables_def ta_trans_def Let_def fold_union' comp_apply trans_to_vars_def actual_autos_def ntas_def prod.case set_map timed_automaton_net_spec_def
        apply -
        apply (subst (2) image_image[symmetric, of _ snd])
        apply (subst zip_range_id)
         apply simp
        unfolding main_auto_spec_def Let_def
        apply (subst list.set(2))
        apply (subst image_insert)+
        apply (subst Union_iff)
        apply (rule bexI)
        defer
         apply (rule insertI1)
        unfolding fst_conv snd_conv 
        unfolding main_auto_goal_edge_spec_def Let_def trans_vars_def fold_union' 
        apply (subst Union_iff)
        apply (rule bexI)
         defer
         apply (rule imageI)
         apply (subst list.set(2))
         apply (subst insert_is_Un)
         apply (rule UnI2)
         apply (subst list.set)
         apply (subst insert_is_Un)
        apply (rule UnI1)
        unfolding list.set
        apply simp
        unfolding prod.case
        apply (rule UnI1)
        apply (subst vars_of_bexp.simps)
        apply (subst vars_of_bexp.simps)
        apply (intro UnI2)
        unfolding vars_of_bexp_all 
        using condition_vars_simps by auto
    qed
  qed
qed

subsection \<open>Locations\<close>       
subsubsection \<open>Returned locations for simplicity\<close>
(* Explicitly returned states *)
definition "ta_states \<equiv> (fst o snd o snd)"

definition "individual_ta_states \<equiv> map ta_states ntas"

definition "all_ta_states = fold (@) individual_ta_states []"


lemma set_fold_append: "set (fold (@) xs ys) = fold (\<union>) (map set xs) (set ys)"
  by (induction xs arbitrary: ys) auto

lemma set_fold_append': "set (fold (@) xs []) = fold (\<union>) (map set xs) {}"
  using set_fold_append by force

lemma individual_ta_states_subset_of_all:
  assumes "i < length individual_ta_states"
  shows "set (individual_ta_states ! i) \<subseteq> set all_ta_states"
proof -
  have "individual_ta_states ! i \<in> set individual_ta_states" using assms[THEN nth_mem_mset]
    unfolding in_multiset_in_set by blast
  thus ?thesis unfolding all_ta_states_def unfolding set_fold_append' fold_union' by auto
qed

lemma individual_ta_states_subset_of_all':
  assumes "nta \<in> set ntas"
  shows "set (ta_states nta) \<subseteq> set all_ta_states"
  using assms
  apply (subst all_ta_states_def)
  apply (subst set_fold_append')
  apply (subst fold_union')
  apply (subst individual_ta_states_def)
  by auto

subsubsection \<open>Committed locations\<close>
definition "ta_comm = (fst o snd o snd o snd)"

definition "all_ta_comm \<equiv>
let 
  ind_comm = map ta_comm ntas
in 
  fold (@) ind_comm []"

subsubsection \<open>Urgent locations\<close>
definition "ta_urg = (fst o snd o snd o snd o snd)"

definition "all_ta_urg \<equiv>
let 
  ind_urg = map ta_urg ntas
in
  fold (@) ind_urg []"

subsubsection \<open>Correctness\<close>
abbreviation "ta_comm' \<equiv> fst o snd o snd"

abbreviation "ta_urg' \<equiv> fst o snd o snd o snd"

abbreviation "ta_states' \<equiv> fst o snd"

lemma main_auto_urg_correct:
  "set (ta_urg' main_auto_spec) \<subseteq> set (ta_states' main_auto_spec)"
  unfolding main_auto_spec_def Let_def comp_apply fst_conv snd_conv
  by simp

lemma main_auto_comm_correct:
  "set (ta_comm' main_auto_spec) \<subseteq> set (ta_states' main_auto_spec)"
  unfolding main_auto_spec_def Let_def comp_apply fst_conv snd_conv
  by simp

lemma act_auto_urg_correct: 
  "set (ta_urg' (action_to_automaton_spec act)) \<subseteq> set (ta_states' (action_to_automaton_spec act))"
  unfolding action_to_automaton_spec_def Let_def comp_apply fst_conv snd_conv
  by auto

lemma act_auto_comm_correct: 
  "set (ta_comm' (action_to_automaton_spec act)) \<subseteq> set (ta_states' (action_to_automaton_spec act))"
  unfolding action_to_automaton_spec_def Let_def comp_apply fst_conv snd_conv
  by auto

lemma all_urg_correct: "set all_ta_urg \<subseteq> set all_ta_states"
  unfolding all_ta_urg_def all_ta_states_def
  unfolding Let_def ta_urg_def 
  unfolding individual_ta_states_def
  unfolding ta_states_def set_fold_append' fold_union' 
  unfolding comp_apply set_map
  unfolding ntas_def
  unfolding timed_automaton_net_spec_def
  unfolding Let_def prod.case
  apply (rule subsetI)
  subgoal for x
    apply (subst (asm) image_image[symmetric, of _ snd])
    apply (subst (asm) zip_range_id)
     apply simp
    apply (subst image_image[symmetric, of _ snd])
    apply (subst zip_range_id)
     apply simp
    using act_auto_urg_correct main_auto_urg_correct by auto
  done

lemma all_comm_correct: "set all_ta_comm \<subseteq> set all_ta_states"
  unfolding all_ta_comm_def all_ta_states_def
  unfolding Let_def ta_comm_def 
  unfolding individual_ta_states_def
  unfolding ta_states_def set_fold_append' fold_union' 
  unfolding comp_apply set_map
  unfolding ntas_def
  unfolding timed_automaton_net_spec_def
  unfolding Let_def prod.case
  apply (rule subsetI)
  subgoal for x
    apply (subst (asm) image_image[symmetric, of _ snd])
    apply (subst (asm) zip_range_id)
     apply simp
    apply (subst image_image[symmetric, of _ snd])
    apply (subst zip_range_id)
     apply simp
    using act_auto_comm_correct main_auto_comm_correct by auto
  done

subsubsection \<open>Invariants\<close>

definition "ta_inv_loc = (map fst) o snd o snd o snd o snd o snd o snd"

definition "all_ta_inv_loc \<equiv>
let 
  ind_ta_inv_loc = map ta_inv_loc ntas
in
  fold (@) ind_ta_inv_loc []"

definition "ta_inv_loc' \<equiv> (map fst) o snd o snd o snd o snd o snd"

lemma main_auto_inv_loc_correct:
 "set (ta_inv_loc' main_auto_spec) \<subseteq> set (ta_states' main_auto_spec)"
  unfolding main_auto_spec_def Let_def comp_apply fst_conv snd_conv ta_inv_loc'_def
  by simp

lemma act_auto_inv_loc_correct: 
  "set (ta_inv_loc' (action_to_automaton_spec act)) \<subseteq> set (ta_states' (action_to_automaton_spec act))"
  unfolding action_to_automaton_spec_def Let_def comp_apply fst_conv snd_conv ta_inv_loc'_def
  by auto

lemma all_inv_loc_correct: "set all_ta_inv_loc \<subseteq> set all_ta_states"
  unfolding all_ta_inv_loc_def all_ta_states_def
  unfolding Let_def ta_inv_loc_def 
  unfolding individual_ta_states_def
  unfolding ta_states_def set_fold_append' fold_union' 
  unfolding comp_apply set_map
  unfolding ntas_def
  unfolding timed_automaton_net_spec_def
  unfolding Let_def prod.case
  apply (rule subsetI)
  subgoal for x
    apply (subst (asm) image_image[symmetric, of _ snd])
    apply (subst (asm) zip_range_id)
     apply simp
    apply (subst image_image[symmetric, of _ snd])
    apply (subst zip_range_id)
     apply simp
    unfolding list.set
    apply (subst (asm) insert_is_Un)
    apply (subst insert_is_Un)
    apply (subst (asm) image_Un)
    apply (subst image_Un)
    apply (subst (asm) image_Un)
    apply (subst (asm) Union_Un_distrib)
    apply (erule UnE)
    using main_auto_inv_loc_correct unfolding ta_inv_loc'_def comp_apply apply blast
    using act_auto_inv_loc_correct unfolding ta_inv_loc'_def comp_apply by auto
  done
subsubsection \<open>Actual locations\<close>

definition trans_locs where
"trans_locs tr \<equiv>
  let
    (s, g, c, a, u, r, t) = tr
  in
    {s, t}"

definition trans_to_locs where
"trans_to_locs trs \<equiv> 
  let
    locs = map trans_locs trs
  in 
    fold (\<union>) locs {}"

definition "ta_locs \<equiv> map trans_to_locs ta_trans"

definition actual_locs where
"actual_locs \<equiv> fold (\<union>) ta_locs {}"

lemma some_actual_autos: "0 < length actual_autos"
  unfolding actual_autos_def ntas_def timed_automaton_net_spec_def by simp

lemma actual_autos_alt: "actual_autos = map (snd o snd) (main_auto_spec # map action_to_automaton_spec actions)"
  unfolding actual_autos_def ntas_def Let_def timed_automaton_net_spec_def prod.case
  apply -
  apply (subst map_map[symmetric])
  apply (subst map_snd_zip)
   apply simp
  by simp

lemma actual_autos_alt_set: "set actual_autos = (\<lambda>a. snd (snd a)) ` set (main_auto_spec # map action_to_automaton_spec actions)"
  unfolding actual_autos_def ntas_def Let_def timed_automaton_net_spec_def prod.case comp_apply set_map 
    apply -
    apply (subst image_image[symmetric, of _ snd])
    apply (subst zip_range_id, simp)
  by simp


lemma actual_locs_correct: "set all_ta_states = actual_locs" 
  proof -
    have "\<Union> (set ` (\<lambda>a. fst (snd a)) ` set (main_auto_spec # map action_to_automaton_spec actions)) =
    \<Union> (trans_to_locs ` (\<lambda>x. fst (snd (snd (snd (snd x))))) ` set (main_auto_spec # map action_to_automaton_spec actions))"
    proof (rule equalityI; rule subsetI)
      fix x
      assume "x \<in> \<Union> (set ` (\<lambda>a. fst (snd a)) ` set (main_auto_spec # map action_to_automaton_spec actions))"
      then obtain ls aut where
        x: "x \<in> set ls"
        and ls: "ls = fst (snd aut)"
        and "aut \<in> set (main_auto_spec # map action_to_automaton_spec actions)" by blast
      then consider (act) act where
        "act \<in> set actions"
        "aut = action_to_automaton_spec act"
      | (main) "aut = main_auto_spec" by auto
      thus "x \<in> \<Union> (trans_to_locs ` (\<lambda>x. fst (snd (snd (snd (snd x))))) ` set (main_auto_spec # map action_to_automaton_spec actions))" 
      proof cases
        case act
        obtain trs where
          trs: "trs = (\<lambda>x. fst (snd (snd (snd (snd x))))) (action_to_automaton_spec act)" 
          "trs = [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act]" unfolding action_to_automaton_spec_def Let_def fst_conv snd_conv prod.case Let_def by simp
        have x: "x \<in> {Off act, StartInstant act, Running act, EndInstant act}" using ls x act unfolding action_to_automaton_spec_def Let_def by simp
        then consider "x = Off act" | "x = StartInstant act" | "x = Running act" | "x = EndInstant act" by blast
        hence "x \<in> trans_to_locs trs"
          apply cases
          unfolding trs(2) unfolding trans_to_locs_def Let_def set_map fold_union' trans_locs_def
          subgoal unfolding start_edge_spec_def Let_def list.set by simp
          subgoal unfolding start_edge_spec_def Let_def list.set by simp
          subgoal unfolding edge_3_spec_def Let_def list.set by simp
          subgoal unfolding edge_3_spec_def Let_def list.set by simp
          done
        with trs(1) act
        show ?thesis by auto
      next
        case main
        obtain trs where
          trs: "trs = (\<lambda>x. fst (snd (snd (snd (snd x))))) main_auto_spec" 
          "trs = [main_auto_init_edge_spec, main_auto_goal_edge_spec, main_auto_loop_spec]" unfolding main_auto_spec_def Let_def fst_conv snd_conv prod.case Let_def by simp
        have x: "x \<in> {InitialLocation, Planning, GoalLocation}" using ls x main unfolding main_auto_spec_def Let_def by simp
        then consider "x = InitialLocation" | "x = Planning" | "x = GoalLocation" by blast
        hence "x \<in> trans_to_locs trs"
          apply cases
          unfolding trs(2) unfolding trans_to_locs_def Let_def set_map fold_union' trans_locs_def
          subgoal unfolding main_auto_init_edge_spec_def Let_def list.set by simp
          subgoal unfolding main_auto_init_edge_spec_def Let_def list.set by simp
          subgoal unfolding main_auto_goal_edge_spec_def Let_def list.set by simp
          done
        with trs(1) main
        show ?thesis by simp
      qed
    next
      have act_locs: "set (fst (snd (action_to_automaton_spec act))) =  {Off act, StartInstant act, Running act, EndInstant act}" for act
        unfolding action_to_automaton_spec_def fst_conv snd_conv Let_def prod.case by simp
      fix x
      assume "x \<in> \<Union> (trans_to_locs ` (\<lambda>x. fst (snd (snd (snd (snd x))))) ` set (main_auto_spec # map action_to_automaton_spec actions))"
      hence "x \<in> trans_locs main_auto_init_edge_spec
          \<or> x \<in> trans_locs main_auto_goal_edge_spec
          \<or> x \<in> trans_locs main_auto_loop_spec
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (start_edge_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (edge_2_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (edge_3_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (end_edge_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (instant_trans_edge_spec act))" 
        unfolding main_auto_spec_def action_to_automaton_spec_def Let_def prod.case 
        apply -
        apply (subst (asm) list.set(2))
        apply (subst (asm) image_insert) 
        apply (subst (asm) set_map)
        apply (subst (asm) image_image)
        unfolding snd_conv fst_conv
        apply (subst (asm) image_insert)
        apply (subst (asm) image_image)
        unfolding trans_to_locs_def Let_def fold_union' set_map by auto
      then consider
        "x \<in> trans_locs main_auto_init_edge_spec" |
        "x \<in> trans_locs main_auto_goal_edge_spec" |
        "x \<in> trans_locs main_auto_loop_spec" |
        act where "act \<in> set actions" "x \<in> trans_locs (start_edge_spec act)" |
        act where "act \<in> set actions" "x \<in> trans_locs (edge_2_spec act)" |
        act where "act \<in> set actions" "x \<in> trans_locs (edge_3_spec act)" |
        act where "act \<in> set actions" "x \<in> trans_locs (end_edge_spec act)" |
        act where "act \<in> set actions" "x \<in> trans_locs (instant_trans_edge_spec act)" by auto
      thus "x \<in> \<Union> (set ` (\<lambda>a. fst (snd a)) ` set (main_auto_spec # map action_to_automaton_spec actions))" 
      proof cases
        case 1
        then consider 
          "x = InitialLocation" |
          "x = Planning" unfolding main_auto_init_edge_spec_def trans_locs_def Let_def prod.case by blast
        then show ?thesis 
          apply cases
          unfolding main_auto_spec_def Let_def prod.case
          by simp+
      next
        case 2
        then consider
          "x = Planning" |
          "x = GoalLocation" unfolding main_auto_goal_edge_spec_def trans_locs_def Let_def prod.case by blast
        then show ?thesis 
          apply cases
          unfolding main_auto_spec_def Let_def prod.case 
          by simp+
      next
        case 3
        hence "x = GoalLocation" unfolding main_auto_loop_spec_def trans_locs_def Let_def prod.case by blast
        then show ?thesis 
          apply cases
          unfolding main_auto_spec_def Let_def prod.case 
          by simp+
      next
        case 4
        then show ?thesis unfolding trans_locs_def start_edge_spec_def Let_def prod.case using act_locs by auto
      next
        case 5
        then show ?thesis unfolding trans_locs_def edge_2_spec_def Let_def prod.case using act_locs by auto
      next
        case 6
        then show ?thesis unfolding trans_locs_def edge_3_spec_def Let_def prod.case using act_locs by auto
      next
        case 7
        then show ?thesis unfolding trans_locs_def end_edge_spec_def Let_def prod.case using act_locs by auto
      next
        case 8 
        then show ?thesis unfolding trans_locs_def instant_trans_edge_spec_def Let_def prod.case using act_locs by auto
      qed
    qed
    thus ?thesis
    unfolding all_ta_states_def set_fold_append' fold_union' set_map individual_ta_states_def ntas_def ta_states_def timed_automaton_net_spec_def Let_def prod.case 
      comp_apply
    apply -
    apply (subst image_image[symmetric, of _ snd])
    apply (subst zip_range_id, simp)
    unfolding actual_locs_def fold_union' ta_locs_def set_map  Let_def ta_trans_def comp_apply
    unfolding actual_autos_def ntas_def Let_def timed_automaton_net_spec_def prod.case set_map comp_apply
    apply (subst (3) image_image[symmetric, of _ snd])
    apply (subst zip_range_id, simp)
    by simp
  qed
(* Renumbering states *)
abbreviation "state_renum' \<equiv> mk_snd_ord_renum individual_ta_states"

(* The injective renumbering from every single state *)
definition "inj_state_renum i \<equiv> 
  let renum' = state_renum' i;
      states = individual_ta_states ! i;
      other_states = list_remove_all all_ta_states states;
      renum = extend_domain renum' other_states (length states - 1)
  in renum"

lemma list_remove_all_set:
  "set (list_remove_all xs ys) \<union> set ys = set xs \<union> set ys"
proof (rule equalityI; intro subsetI)
  fix x
  assume "x \<in> set (list_remove_all xs ys) \<union> set ys"
  thus "x \<in> set xs \<union> set ys" 
    apply (rule UnE)
    apply (subst (asm) in_multiset_in_set[symmetric])
     apply (subst (asm) list_remove_all_mset)
     apply (rule UnI1)
    using in_diffD apply fastforce
    by (rule UnI2)
next
  fix x
  assume "x \<in> set xs \<union> set ys" 
  then
  consider "x \<in> set xs - set ys" | "x \<in> set ys" by blast
  thus "x \<in> set (list_remove_all xs ys) \<union> set ys"
    apply (cases)
     apply (rule UnI1)
    apply (subst in_multiset_in_set[symmetric])
     apply (subst list_remove_all_mset)
     apply (metis DiffE count_greater_zero_iff count_mset_0_iff in_diff_count set_mset_mset)
    by blast
qed

lemma extend_domain_not_in_set:
  assumes "x \<notin> set es"
  shows "extend_domain f es n x = f x"
  using assms
  unfolding extend_domain_def
  by (auto split: prod.splits)


lemma extend_domain_fold_lemma:
  assumes "set as \<subseteq> set as'"
  shows "fold (\<lambda>x (i, xs). if x \<in> set as' then (i + 1, (x, i + 1) # xs) else (i, xs)) as (n, bs)
  = (n + length as, rev (zip as [(n+1)..<(n + (length as) + 1)]) @ bs)" (is "fold ?f as (n, bs) = _")
  using assms
proof (induction as arbitrary: n bs)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  hence IH': "\<And>n bs. fold ?f as (n, bs) =
    (n + length as, rev (zip as [n+1..<(n + length as + 1)]) @ bs)"
    by (auto split: prod.split)
  have "a \<in> set as'" using Cons by simp
  hence "fold ?f (a # as) (n, bs)
    = fold ?f as (n + 1, (a, n + 1) # bs)"
    by (auto split: prod.split)
  also have "... = (n + (length (a#as)), rev (zip as [(n + 2)..<(n + length (a#as) + 1)]) @ (a, n + 1) # bs)" 
    by (simp add: IH')
  also have "... = (n + (length (a#as)), (rev ((a, n + 1)#(zip as [(n + 1) + 1..<((n + 1)+ length (a#as))]))) @ bs)" 
    by simp
  also have "... = (n + (length (a#as)), (rev (zip (a#as) [(n + 1)..<(n + length (a#as) + 1)])) @ bs)"
    apply (subst zip_Cons_Cons[symmetric])
    apply (subst Suc_eq_plus1[where n = "n + 1", symmetric])
    apply (subst upt_conv_Cons[symmetric])
    by auto
  finally show ?case by blast
qed

lemma extend_domain_index:
  assumes "x \<in> set es"
  shows "extend_domain f es n x = n + last_index es x + 1"
  using assms
proof (induction es arbitrary: f  n)
  case Nil
  then show ?case by simp
next
  case (Cons e es f n)
  then show ?case 
  proof (cases "x \<in> set es")
    case False
    with Cons
    have xe: "x = e" by simp
    hence 1: "n + last_index (e # es) x + 1 = n + 1" using False
      apply (subst last_index_Cons)
      by simp
    from xe 
    have "extend_domain f (e # es) n x = 
    (
      let 
        (i, xs) = fold 
            (\<lambda>x (i, xs). if x \<in> set (e # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
            (es) (n + 1, [(e, n + 1)]); 
        m' = map_of xs 
      in 
        (\<lambda>x. if x \<in> set (e # es) then the (m' x) else f x)) x" 
      unfolding extend_domain_def fold_Cons by (auto split: prod.splits)
    also have "... = 
      (let 
        (i, xs) = fold 
            (\<lambda>x (i, xs). if x \<in> set (e # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
            (es) (n + 1, [(e, n + 1)]); 
        m' = map_of xs
      in 
       the (m' x))" using xe by (auto split: prod.splits)
    also have "... = n + 1" using False  
      apply (subst Let_def)
      apply (subst extend_domain_fold_lemma[where as' = "e#es" and as = es and n = "n + 1" and bs = "[(e, n + 1)]"])
       apply auto[1]
      apply (subst prod.case)
      apply (subst Let_def)
      apply (subst xe, subst (asm) xe)
      apply (subst map_of_distinct_lookup)
        apply (subst zip_rev[symmetric])
         apply (subst length_upt)
         apply simp
        apply (subst map_fst_zip)
         apply (subst length_rev)+
         apply (subst length_upt)
      by simp+
    finally
    show ?thesis using 1 by simp
  next
    case True 
    {fix f n
      have "n + last_index es x + 1 = extend_domain f es n x" using Cons True by auto
      also have "... = the (map_of (rev (zip es [n + 1..<(n + (length es) + 1)])) x)" 
        apply (subst extend_domain_def) 
        apply (subst extend_domain_fold_lemma)
         apply simp
        apply (subst Let_def)
        apply (subst prod.case)
        apply (subst Let_def)
        using True by auto
      finally have "the (map_of (rev (zip es [n + 1..<n + length es + 1])) x) = n + last_index es x + 1" by simp
    } note IH' = this

    have 1: "x \<in> dom (map_of (rev (zip es [n + 1 + 1..<n + 1 + length es + 1])))" 
      using True
      apply (subst zip_rev[symmetric])
       apply (subst length_upt)
       apply simp
      apply (subst dom_map_of_zip)
       apply (subst length_rev)+
       apply (subst length_upt)
      by simp+
      
    have "extend_domain f (e # es) n x = 
      (
        let 
          (i, xs) = fold 
              (\<lambda>x (i, xs). if x \<in> set (e # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
              (es) (n + 1, [(e, n + 1)]); 
          m' = map_of xs 
        in 
          (\<lambda>x. if x \<in> set (e # es) then the (m' x) else f x)) x" 
        unfolding extend_domain_def fold_Cons by (auto split: prod.splits)
    also have "... = 
        (let 
          (i, xs) = fold 
              (\<lambda>x (i, xs). if x \<in> set (e # es) then (i + 1, (x, i + 1) # xs) else (i, xs)) 
              (es) (n + 1, [(e, n + 1)]); 
          m' = map_of xs
        in 
       the (m' x))" using True by (auto split: prod.splits)
    also have "... = n + 1 + last_index es x + 1" apply (subst Let_def)
      apply (subst extend_domain_fold_lemma[where as' = "e#es" and as = es and n = "n + 1" and bs = "[(e, n + 1)]"])
       apply auto[1]
      apply (subst prod.case)
        apply (subst Let_def)
        apply (subst map_of_append)
        apply (subst map_add_dom_app_simps(1))
         apply (rule 1)
        find_theorems "map_of (?xs @ ?ys)"
        apply (subst IH')
        ..
      finally show ?thesis using True 
        apply (subst last_index_Cons)
        by simp
  qed
qed

find_theorems name: "last_index"

lemma extend_domain_inj_new:
  "inj_on (extend_domain f es (n::nat)) (set es)"
  apply (rule inj_onI)
  subgoal for x y
    using extend_domain_index[of x] extend_domain_index[of y]
    by simp
  done


lemma extend_domain_inj:
  assumes inj_on_f: "inj_on f (set d)"
      and f_ran: "\<forall>x \<in> set d. f x \<le> n"
      and n: "n = length d - 1"
    shows "inj_on (extend_domain f e n) (set d \<union> set e)"
  find_theorems "inj_on ?f (?s \<union> ?t)"
proof (subst inj_on_Un; intro conjI)
  show "inj_on (extend_domain f e n) (set e)" using extend_domain_inj_new by blast
  show "inj_on (extend_domain f e n) (set d)"
  proof (rule inj_onI)
    fix x y 
    assume x: "x \<in> set d" 
       and y: "y \<in> set d" 
       and e: "extend_domain f e n x = extend_domain f e n y"
    show "x = y"
    proof (cases "x \<in> set e"; cases "y \<in> set e") 
      assume a: "x \<notin> set e" "y \<notin> set e"
      hence "f x = f y" using extend_domain_not_in_set[of _ e f n] e by auto
      with x y
      show "x = y" using inj_on_f[simplified inj_on_def] by blast
    next
      assume a: "x \<notin> set e" "y \<in> set e"
      hence "extend_domain f e n x = f x" using extend_domain_not_in_set[of x e f n] by blast
      hence "extend_domain f e n x \<le> n" using f_ran x by auto
      moreover
      have "extend_domain f e n y = n + last_index e y + 1" using a extend_domain_index by auto
      ultimately 
      have "False" using e by auto
      thus ?thesis by simp
    next
      assume a: "x \<in> set e" "y \<notin> set e"
      hence "extend_domain f e n y = f y" using extend_domain_not_in_set by metis
      hence "extend_domain f e n y \<le> n" using f_ran y by auto
      moreover
      have "extend_domain f e n x = n + last_index e x + 1" using a extend_domain_index by auto
      ultimately 
      have "False" using e by auto
      thus ?thesis by simp
    next
      assume a: "x \<in> set e" "y \<in> set e"
      have "extend_domain f e n x = n + last_index e x + 1" using extend_domain_index a by auto
      moreover
      have "extend_domain f e n y = n + last_index e y + 1" using extend_domain_index a by auto
      ultimately
      have "last_index e x = last_index e y" using e by auto
      with a
      show "x = y" by auto
    qed
  qed
  
  show "extend_domain f e n ` (set d - set e) \<inter> extend_domain f e n ` (set e - set d) = {}"
  proof -
    { fix x y
      assume x: "x \<in> (set d - set e)"
         and y: "y \<in> (set e - set d)"
      have "extend_domain f e n x \<le> n" using f_ran extend_domain_not_in_set[of x e f n] x by auto
      moreover
      have "extend_domain f e n y = n + last_index e y + 1" using extend_domain_index y by fast
      ultimately
      have "extend_domain f e n x \<noteq> extend_domain f e n y" by force
    }
    thus ?thesis by blast
  qed
qed

lemma map_of_zip_fst:
  assumes "x \<in> set as"
     and "length as = length bs"
   shows "map_of (zip as bs) x = Some (bs ! (List_Index.index as x))"
  using assms
proof (induction as arbitrary: bs)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then obtain c cs where
    bs[simp]: "bs =c#cs" by (cases bs, auto)
  show ?case 
  proof (cases "x = a")
    case [simp]: True
    hence "List_Index.index (a # as) x = 0" by auto
    hence "bs ! (List_Index.index (a # as) x) = c" using nth_Cons_0 by simp
    moreover
    have "map_of (zip (a # as) bs) x = Some c" by auto
    ultimately
    show ?thesis by simp
  next
    case False
    show ?thesis 
      apply (subst bs)+
      apply (subst zip_Cons_Cons)
      apply (subst map_of_Cons_code(2))
      using False Cons
      by simp
  qed
qed

(* lemma map_of_zip_ran_distinct_inj:
  assumes dist: "distinct bs"
      and l: "length as = length bs"
    shows "inj_on (map_of (zip as bs)) (set as)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> set as"
     and y: "y \<in> set as"
     and mz: "map_of (zip as bs) x = map_of (zip as bs) y"
  
qed *)

    

lemma individual_ta_states_inj:
  assumes i_ran: "i < length individual_ta_states"
  shows "inj_on (state_renum' i) (set (individual_ta_states ! i))"
  using assms
  apply (subst mk_snd_ord_renum_def)
  apply (subst comp_apply)
  using mk_renum_inj 
  apply (subst nth_map)
  by blast+

lemma state_renum'_ran:
  assumes i: "i < length individual_ta_states"
      and x: "x \<in> set (individual_ta_states ! i)" 
    shows "state_renum' i x \<le> (length (individual_ta_states ! i) - 1)"
  unfolding mk_snd_ord_renum_def comp_apply mk_renum_def Let_def
  apply (subst nth_map[OF i])
  apply (subst map_of_zip_fst[OF x])
   apply simp
  apply (subst option.sel)
  using x[simplified index_less_size_conv[symmetric]]
  by simp

lemma state_renum'_inj: 
  assumes i_ran: "i < length individual_ta_states"
      and x: "x \<in> set all_ta_states"
      and y: "y \<in> set all_ta_states"
      and e: "inj_state_renum i x = inj_state_renum i y"
    shows "x = y"
proof -
  have a: "inj_state_renum i = 
  extend_domain (state_renum' i) (list_remove_all all_ta_states (individual_ta_states ! i)) (length (individual_ta_states ! i) - 1)" 
    apply (subst inj_state_renum_def)
    apply (subst Let_def)+
    by blast
  
  have 1: "inj_on (state_renum' i) (set (individual_ta_states ! i))" using individual_ta_states_inj[OF i_ran] .
  have 2: " \<forall>x\<in>set (individual_ta_states ! i). state_renum' i x \<le> length (individual_ta_states ! i) - 1"
    using state_renum'_ran i_ran by blast
  
  have "inj_on (extend_domain (state_renum' i)  (list_remove_all all_ta_states (individual_ta_states ! i)) (length (individual_ta_states ! i) - Suc 0)) (set (individual_ta_states ! i) \<union> set (list_remove_all all_ta_states (individual_ta_states ! i)))" 
    using extend_domain_inj[OF 1 2, simplified]
    by blast
  hence "inj_on (extend_domain (state_renum' i) (list_remove_all all_ta_states (individual_ta_states ! i)) (length (individual_ta_states ! i) - Suc 0))
   (set all_ta_states)" 
    apply -
    apply (subst (asm) Un_commute)
    apply (subst (asm) list_remove_all_set)
    apply (subst (asm) Un_commute)
    apply (subst (asm) individual_ta_states_subset_of_all[OF i_ran, simplified subset_Un_eq])
    by assumption
  hence "inj_on (inj_state_renum i) (set all_ta_states)" using a by auto
  thus ?thesis using e x y unfolding inj_on_def by blast
qed

definition "nta_init \<equiv> fst o snd"

definition "ntas_inits \<equiv> map nta_init ntas"


lemma ntas_inits_alt: "ntas_inits = InitialLocation # map Off actions" unfolding ntas_inits_def nta_init_def ntas_def timed_automaton_net_spec_def Let_def prod.case
  apply (subst map_map[symmetric])
  apply (subst map_snd_zip)
   apply simp
  unfolding main_auto_spec_def action_to_automaton_spec_def Let_def
  apply (subst list.map)
  apply (subst map_map)
  unfolding fst_conv comp_apply ..

subsection \<open>Actions\<close>
(* This needs to be lifted out of the locale *)
definition "broadcast \<equiv> []::String.literal list"

(* There is one action *)
definition "nta_actions \<equiv> [STR '''']::String.literal list"

find_consts name: "mk_renaming"

abbreviation "act_renum \<equiv> mk_renum (broadcast @ nta_actions)"

definition "init_vars \<equiv> map (\<lambda>x. (fst x, 0::int)) nta_vars"

definition trans_acts::"
  'action location \<times>
  ('proposition variable, int) Simple_Expressions.bexp \<times>
  ('action clock, int) acconstraint list \<times> 
  String.literal act \<times> 
  ('proposition variable \<times> ('proposition variable, int) exp) list \<times> 
  'action clock list \<times> 
  'action location \<Rightarrow> String.literal set" where
"trans_acts \<equiv> (act.set_act o fst o snd o snd o snd)"

definition trans_to_acts where
"trans_to_acts t \<equiv> 
let
  trans_vars = map trans_acts t
in fold (\<union>) trans_vars {}"

definition "actual_acts \<equiv> 
let
  trans_vars = map trans_to_acts ta_trans
in fold (\<union>) trans_vars {}"

find_theorems name: "zip" "snd ` (set  (zip ?xs ?ys))"

find_theorems " ?f ` ?g ` ?S = (\<lambda>x. ?f (?g x)) ` ?S"

lemma actual_acts_correct: "actual_acts \<subseteq> set nta_actions"
  unfolding actual_acts_def fold_union' Let_def ta_trans_def trans_to_acts_def trans_acts_def set_map comp_apply 
    actual_autos_def nta_actions_def ntas_def prod.case timed_automaton_net_spec_def main_auto_spec_def action_to_automaton_spec_def
  apply (rule subsetI)
  subgoal for x
  apply (subst (asm) Union_iff)
    apply (erule bexE)
    subgoal for tr
      apply (erule imageE)
      subgoal for trs
        apply (erule imageE)
        subgoal 
          apply (subst (asm) image_image[symmetric, of snd])
          apply (subst (asm) (3) image_image[symmetric, of _ snd])
          apply (subst (asm) zip_range_id)
           apply simp
          apply (elim imageE)
          subgoal for _ auto
            unfolding main_auto_init_edge_spec_def main_auto_goal_edge_spec_def main_auto_loop_spec_def Let_def start_edge_spec_def end_edge_spec_def edge_2_spec_def edge_3_spec_def instant_trans_edge_spec_def
            by auto
          done
        done
      done
    done
  done

definition "form \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in formula"

lemma nta_length[simp]: "length individual_ta_states = length ntas"
  unfolding individual_ta_states_def
  using length_map .

interpretation abs_renum: Simple_Network_Rename_Formula
    broadcast 
    nta_vars 
    act_renum 
    var_renum 
    clock_renum
    inj_state_renum
    urge_clock
    init_vars
    ntas_inits
    actual_autos
    form
proof
  have auto_alt: "{(Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) 
            |p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} 
            = automaton_of ` (set actual_autos)"
    unfolding Simple_Network_Language.Prod_TA_Defs.N_def Simple_Network_Language.Prod_TA_Defs.n_ps_def
    apply (subst set_map[symmetric])
    apply (subst (3) set_conv_nth)
    unfolding fst_conv snd_conv by blast

  have trans_alt':  "map (trans o automaton_of) actual_autos = map set ta_trans"
    unfolding actual_autos_def ta_trans_def automaton_of_def Simple_Network_Language.trans_def
    by auto

  have trans_alt: "\<Union> (trans ` automaton_of ` (set actual_autos)) = all_ta_trans"
    unfolding all_ta_trans_def 
    unfolding set_map[symmetric]
    apply (subst map_map)
    using trans_alt' 
    unfolding fold_union'
    by simp

  have loc_set_alt: "set (all_ta_states) = Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
  proof -
    have "Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)
      = fst ` (\<Union> (trans ` automaton_of ` (set actual_autos)))
      \<union> (snd o snd o snd o snd o snd o snd) ` (\<Union> (trans ` automaton_of ` (set actual_autos)))" unfolding Prod_TA_Defs.loc_set_def auto_alt[symmetric] by blast
    also have "... = fst ` all_ta_trans \<union> (snd o snd o snd o snd o snd o snd) ` all_ta_trans" using trans_alt by simp
    also have "... = set all_ta_states" unfolding actual_locs_correct actual_locs_def fold_union' 
        ta_locs_def trans_to_locs_def Let_def trans_locs_def set_map all_ta_trans_def 
      apply (rule equalityI; rule subsetI)
      subgoal for x
        apply (erule UnE)
        subgoal
          apply (erule imageE)
          apply (erule UnionE)
          apply (erule imageE)
          subgoal for tr trs alltrs
            apply (rule UnionI)
             apply (rule imageI)
             apply assumption
            apply (rule UnionI)
            by auto
          done
        apply (erule imageE)
        apply (erule UnionE)
        apply (erule imageE)
        subgoal for tr trs alltrs
          apply (rule UnionI)
           apply (rule imageI)
           apply assumption
          apply (rule UnionI)
          by auto
        done
      subgoal for x
        apply (erule UnionE)
        apply (erule imageE)
        subgoal for tls trs
          apply (drule subst[of tls])
           apply assumption
          apply (erule UnionE)
          apply (erule imageE)
          subgoal for tls tr
            apply (induction tr)
            subgoal for s _ _ _ _ _ t
              unfolding prod.case
              apply (subst (asm) insert_is_Un)
              apply (drule subst[of tls])
               apply rotate_tac
               apply rotate_tac
               apply assumption
              apply (erule UnE)
               apply blast
              apply (rule UnI2)
              by force
            done
          done
        done
      done
    finally show ?thesis by auto
  qed

  have clk_set'_alt: "Simple_Network_Impl.clk_set' actual_autos = all_ta_clocks"
  proof -
    have 1: "(\<Union>A\<in>set actual_autos. \<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r) 
      = (\<Union>trs\<in>set ta_trans. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))"
      unfolding ta_trans_def comp_apply set_map
    proof (rule equalityI; rule subsetI)
      fix x
      assume "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r)"
      then obtain A where
       A: "A \<in> set actual_autos"
        "x \<in> (\<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r)" by blast
      then obtain r where
        "\<exists>a b c d e f. (a, b, c, d, e, r, f) \<in> set (fst (snd (snd A)))" 
        "x \<in> set r" by blast
      hence "\<exists>tr. tr \<in> set (fst (snd (snd A))) \<and> x \<in> set (fst (snd (snd (snd (snd (snd tr))))))" by fastforce
      with A(1)
      show "x \<in> (\<Union>trs\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))" by blast
    next
      fix x
      assume "x \<in> (\<Union>trs\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))"
      then obtain trs where
        "trs \<in> (fst o snd o snd) ` set actual_autos"
        "x \<in> (\<Union>x\<in>set trs. set (fst (snd (snd (snd (snd (snd x)))))))" by auto
      then obtain A tr where
        Atr: "A \<in> set actual_autos"
        "trs = fst (snd (snd A))"
        "tr \<in> set trs"
        "x \<in> set (fst (snd (snd (snd (snd (snd tr))))))" by auto
      then obtain r where
        "\<exists>a b c d e f. (a, b, c, d, e, r, f) = tr" apply (cases tr) by auto
      with Atr
      show "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(_, _, _, _, _, r, _)\<in>set (fst (snd (snd A))). set r)" by fastforce
    qed
    have 2: "\<And>A B C. B = C \<Longrightarrow> A \<union> B = A \<union> C" by blast

    have invr_clocks: "(\<Union>A\<in>set actual_autos. \<Union>g\<in>set (snd (snd (snd A))). fst ` (collect_clock_pairs (snd g))) = 
      (\<Union>auto\<in>set actual_autos. \<Union>i\<in>set (snd (snd (snd auto))). fst ` collect_clock_pairs (snd i))" by simp

    have guard_clocks: " (\<Union>A\<in>set actual_autos. \<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g)) 
        = (\<Union>trs\<in>set (map (\<lambda>x. fst (snd (snd x))) actual_autos). \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))"
    proof (rule equalityI; rule subsetI)
      fix x 
      assume "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g))"
      then obtain A where
        A: "A \<in> set actual_autos"
        "x \<in> (\<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g))" by blast
      then obtain trans where
        "trans \<in> set (fst (snd (snd A)))"
        "x \<in> fst ` collect_clock_pairs (fst (snd (snd trans)))"
        apply -
        apply (subst (asm) Union_iff)
        apply (erule bexE)
        subgoal for trs
          apply (erule imageE)
          subgoal for trs'
            apply (induction trs')
            subgoal for l b g
              apply (subst (asm) prod.case)+
              by simp
            done
          done
        done
      with A
      show "x \<in> (\<Union>trs\<in>set (map (\<lambda>x. fst (snd (snd x))) actual_autos). \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))" by auto
    next
      fix x
      assume "x \<in> (\<Union>trs\<in>set (map (\<lambda>x. fst (snd (snd x))) actual_autos). \<Union>x\<in>set trs. fst ` collect_clock_pairs (fst (snd (snd x))))" 
      then obtain A tr where
        A: "A \<in> set actual_autos"
        "tr \<in> set (fst (snd (snd A)))"
        "x \<in> fst ` collect_clock_pairs (fst (snd (snd tr)))" 
        apply -
        apply (subst (asm) Union_iff)
        apply (erule bexE)
        subgoal for tr
          apply (subst (asm) set_map)
          apply (erule imageE)
          subgoal for trs
            by blast
          done
        done
      then obtain l c g a b d e where
        g: "tr = (l, c, g, a, b, d, e)" apply (cases tr) by auto
      show "x \<in> (\<Union>A\<in>set actual_autos. \<Union>(l, b, g, _)\<in>set (fst (snd (snd A))). fst ` (collect_clock_pairs g))" 
        using A unfolding g
        apply -
        apply (subst (asm) snd_conv | subst (asm) fst_conv)+
        by blast
    qed

    show ?thesis
      apply (subst Simple_Network_Impl.clk_set'_def)
      apply (subst all_ta_clocks_alt)
      apply (subst 1)
      unfolding comp_apply
      apply (subst Un_commute)
      apply (subst Un_assoc)
      apply (rule 2)
      unfolding Simple_Network_Impl.clkp_set'_def
      unfolding ta_trans_def comp_apply inv_clocks_def
      apply (subst (2) Un_commute) 
      apply (subst invr_clocks[symmetric])
      apply (subst guard_clocks[symmetric])
      by blast
  qed

  have var_set_alt: "Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars) = actual_variables"
  proof (rule equalityI; rule subsetI)
    fix x 
    assume "x \<in> Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
    hence "x \<in> (\<Union>S\<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
          p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
         \<Union> (vars_of_bexp ` S)) \<union>
     (\<Union>S\<in>{(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) `
           Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |
           p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
         \<Union>f\<in>S. \<Union>(x, e)\<in>set f. {x} \<union> vars_of_exp e)"  unfolding Prod_TA_Defs.var_set_def .
    then consider "x \<in> (\<Union>S\<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
          p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
         \<Union> (vars_of_bexp ` S))" |
     "x \<in> (\<Union>S\<in>{(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) `
           Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |
           p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
         \<Union>f\<in>S. \<Union>(x, e)\<in>set f. {x} \<union> vars_of_exp e)" by blast
    then have
      "(\<exists>auto trans cond. x \<in> vars_of_bexp cond 
      \<and> cond = fst (snd trans)
      \<and> trans \<in> Simple_Network_Language.trans auto
      \<and> auto \<in> set (map automaton_of actual_autos)) \<or> 
    (\<exists>auto trans v e. x \<in> insert v (vars_of_exp e) 
      \<and> (v, e) \<in> set ((fst o snd o snd o snd o snd) trans) 
      \<and> trans \<in> Simple_Network_Language.trans auto 
      \<and> auto \<in> set (map automaton_of actual_autos))" unfolding Prod_TA_Defs.n_ps_def Prod_TA_Defs.N_def
      apply cases
      unfolding comp_apply
       apply (rule disjI1)
      unfolding fst_conv snd_conv
       apply (subst (asm) Union_iff)
       apply (erule bexE)
      subgoal for cvs
        apply (erule imageE)
        subgoal for conds
          apply (erule CollectE)
          apply (erule exE)
          subgoal for n
            apply (erule conjE)
            apply (drule nth_mem)
            by blast
          done
        done
      apply (rule disjI2)
      apply (subst (asm) Union_iff)
      apply (erule bexE)
      subgoal for upd_vs
        apply (erule imageE)
        subgoal for upds
          apply (erule CollectE)
          apply (erule exE)
          subgoal for n
            apply (erule conjE)
            apply (drule nth_mem)
            by blast
          done
        done
      done
    then consider 
      (conds) auto trans cond where
      "x \<in> vars_of_bexp cond"
      "cond = fst (snd trans)"
      "trans \<in> Simple_Network_Language.trans auto"
      "auto \<in> set (map automaton_of actual_autos)" |
      (upds) auto trans v e where
      "x \<in> insert v (vars_of_exp e)"
      "(v, e) \<in> set ((fst o snd o snd o snd o snd) trans)"
      "trans \<in> Simple_Network_Language.trans auto"
      "auto \<in> set (map automaton_of actual_autos)"
      by blast
    thus "x \<in> actual_variables" 
    proof cases
      case conds
      hence "x \<in> (\<Union>ts\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>(l, c, g, a, u, r, l')\<in>set ts. vars_of_bexp c)"
        unfolding Simple_Network_Language.trans_def  Let_def fold_union' comp_apply set_map 
        automaton_of_def 
        apply -
        apply (erule imageE)
        subgoal for a'
          apply (induction a')
          subgoal for _ _ tr
            apply (subst (asm) prod.case)+
            apply simp
            apply (rule bexI)
             apply (rule bexI[of _ trans])
            by auto
          done
        done
      then show ?thesis unfolding actual_variables_def ta_trans_def trans_vars_def trans_to_vars_def Let_def comp_apply fold_union' set_map by blast
    next
      case upds
      hence "x \<in> (\<Union>ts\<in>(\<lambda>x. fst (snd (snd x))) ` set actual_autos. \<Union>(l, c, g, a, u, r, l')\<in>set ts. \<Union> (vars_of_update ` set u))"
        unfolding Simple_Network_Language.trans_def comp_apply vars_of_update_def Let_def set_map
        apply -
        apply (erule imageE)
        subgoal for a'
          apply (induction a')
          subgoal for a b tr d
            apply simp
            unfolding automaton_of_def prod.case
            snd_conv fst_conv
            apply (rule bexI[of _ "(a, b, tr, d)"])
             apply (rule bexI[of _ trans])
              apply (induction trans)
            subgoal unfolding prod.case
              by auto
             apply simp
            by simp
          done
        done
        then show ?thesis unfolding actual_variables_def ta_trans_def trans_vars_def trans_to_vars_def Let_def comp_apply fold_union' set_map by blast
    qed
  next
    fix x
    assume "x \<in> actual_variables"
    then obtain tran aut l c g a u r l' where
      trans: "aut \<in> set actual_autos"
          "tran \<in> (set o fst o snd o snd) aut"        
          "tran = (l, c, g, a, u, r, l')"
      and "x \<in> vars_of_bexp c \<or> x \<in> \<Union> (vars_of_update ` set u)"
      unfolding actual_variables_def Let_def fold_union' set_map trans_to_vars_def trans_vars_def ta_trans_def comp_apply by blast
    then consider "x \<in> vars_of_bexp c" | "x \<in> \<Union> (vars_of_update ` set u)" by blast
    thus "x \<in> Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" 
    proof cases
      case 1
      obtain aut' where
        aut': "aut' = automaton_of aut" by simp
      moreover
      from 1 trans obtain trs where
        "trs = set (fst (snd (snd aut)))" by auto
      ultimately
      have trs: "trs = fst (snd (snd aut'))" unfolding automaton_of_def apply (cases aut) by auto
      with aut' trans
      have "tran \<in> trs" unfolding automaton_of_def comp_apply apply (cases aut) by auto
      with 1 trans aut' trs
      have "x \<in> vars_of_bexp c \<and> c = fst (snd tran) \<and> tran \<in> trs \<and> trs = fst (snd (snd aut')) \<and> aut' \<in> automaton_of ` set actual_autos" by auto
      hence "\<exists>c tr trs aut. c = fst (snd tr) \<and> tr \<in> trs \<and> trs = Simple_Network_Language.trans aut \<and> aut \<in> automaton_of ` set actual_autos \<and> x \<in> vars_of_bexp c"
        using trans unfolding Simple_Network_Language.trans_def automaton_of_def by blast
      hence "\<exists>c tr trs aut. (c = fst (snd tr)) \<and> tr \<in> trs \<and> trs = Simple_Network_Language.trans aut \<and> aut \<in> {Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> vars_of_bexp c" using auto_alt by presburger
      hence "\<exists>c tr trs. (c = fst (snd tr)) \<and> tr \<in> trs \<and> trs \<in> {Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> vars_of_bexp c" by blast
      hence "\<exists>c trans. (c \<in> (fst o snd) ` trans) \<and> trans \<in> {Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> vars_of_bexp c" unfolding comp_apply by fastforce
      hence "\<exists>c. c \<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)} \<and> x \<in> \<Union>(vars_of_bexp ` c)" by auto
      hence "x \<in> (\<Union>S\<in>{(fst \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
            p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
           \<Union> (vars_of_bexp ` S))" by blast
      then show ?thesis unfolding Prod_TA_Defs.var_set_def by blast
    next
      case 2
      with trans
      obtain v e where
        ve: "(v, e) \<in> set u"
        "x \<in> {v} \<union> vars_of_exp e" unfolding vars_of_update_def by auto
      obtain aut' where aut': "aut' = automaton_of aut" by simp
      moreover
      obtain trs where trs: "trs = Simple_Network_Language.trans aut'" by simp
      ultimately
      have "tran \<in> trs" unfolding Simple_Network_Language.trans_def automaton_of_def using trans unfolding comp_apply apply (cases aut) by auto
      then
      obtain re res where
        "re \<in> res \<and> res = (fst o snd o snd o snd o snd) ` trs \<and> trs = Simple_Network_Language.trans aut'
          \<and> aut' \<in> automaton_of ` (set actual_autos)
            \<and> x \<in> (\<Union>(x, e)\<in>set re. {x} \<union> vars_of_exp e)" using trans ve trs aut' by fastforce
      hence "re \<in> res \<and> res = (fst o snd o snd o snd o snd) ` trs \<and> trs = Simple_Network_Language.trans aut'
          \<and> aut' \<in> {Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p |p.
             p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}
            \<and> x \<in> (\<Union>(x, e)\<in>set re. {x} \<union> vars_of_exp e)" using auto_alt by blast
      hence "re \<in> res \<and> res = (fst o snd o snd o snd o snd) ` trs 
          \<and> trs \<in> {Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
             p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}
            \<and> x \<in> (\<Union>(x, e)\<in>set re. {x} \<union> vars_of_exp e)" by blast
      hence "res \<in> {(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
             p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}
            \<and> x \<in> (\<Union>f\<in>res. \<Union>(x, e)\<in>set f. {x} \<union> vars_of_exp e)" by blast
      hence "x \<in> (\<Union>S\<in>{(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p) |p.
             p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
           \<Union>f\<in>S. \<Union>(x, e)\<in>set f. {x} \<union> vars_of_exp e)" by blast
      then show ?thesis unfolding Prod_TA_Defs.var_set_def by blast
    qed
  qed

  show "\<forall>i<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars).
       \<forall>x\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars).
          \<forall>y\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars). 
            inj_state_renum i x = inj_state_renum i y \<longrightarrow> x = y"
  proof (intro allI impI)
    fix i
    assume "i < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
    hence "i < length individual_ta_states" unfolding Prod_TA_Defs.n_ps_def fst_conv snd_conv actual_autos_def individual_ta_states_def by simp
    from state_renum'_inj[OF this, simplified loc_set_alt]
    show "(\<forall>x\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars). \<forall>y\<in>Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars). inj_state_renum i x = inj_state_renum i y \<longrightarrow> x = y)" by simp
  qed

  show "inj_on clock_renum (insert urge_clock (Simple_Network_Impl.clk_set' actual_autos))"
  proof -
      
    have ins: "insert urge_clock all_ta_clocks \<subseteq> set (urge_clock # nta_clocks)"
      using all_ta_clocks_correct by auto

    show "inj_on clock_renum (insert urge_clock (Simple_Network_Impl.clk_set' actual_autos))"
      apply (subst clk_set'_alt)
      apply (rule inj_on_subset[OF _ ins])
      unfolding clock_renum_def 
      using mk_renum_inj by blast
  qed

  show "inj_on var_renum (Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars))" 
  proof -                                                                                          
    
    have "inj_on var_renum (set (map fst nta_vars))" unfolding var_renum_def using mk_renum_inj by blast
    thus ?thesis using inj_on_subset actual_variables_correct var_set_alt by blast
  qed

  show "inj_on (mk_renum (broadcast @ nta_actions)) (Prod_TA_Defs.act_set (set broadcast, map automaton_of actual_autos, map_of nta_vars))" 
  proof -
    have 1: "Prod_TA_Defs.act_set (set broadcast, map automaton_of actual_autos, map_of nta_vars) = set broadcast \<union> actual_acts"
      unfolding Prod_TA_Defs.act_set_def auto_alt
    proof -
      have "(\<Union>p\<in>{0..<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
        \<Union>(l, e, g, a, _)\<in>Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p). set_act a) = actual_acts"
      proof -
        have "(\<Union>p\<in>{0..<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
        \<Union>(l, e, g, a, _)\<in>Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p). set_act a) = 
        (\<Union>act\<in>{Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p|p. p < Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}. 
        \<Union>(l, e, g, a, _)\<in>Simple_Network_Language.trans act. set_act a)" 
          apply (rule equalityI; rule subsetI)
          by fastforce+
        also have "... = (\<Union>act\<in>automaton_of ` set actual_autos. \<Union>(l, e, g, a, _)\<in>Simple_Network_Language.trans act. set_act a)" using auto_alt by simp
        also have "... = actual_acts"
          unfolding actual_acts_def trans_to_acts_def ta_trans_def automaton_of_def comp_apply fold_union' Let_def set_map trans_acts_def Simple_Network_Language.trans_def
          apply (rule equalityI; rule subsetI)
          subgoal for x 
            apply (subst (asm) Union_iff)
            apply (erule bexE)
            subgoal for tr
              apply (erule imageE)
              subgoal for auto'
                apply (erule imageE)
                subgoal for auto
                  apply (induction auto)
                  subgoal for _ _ trs
                  unfolding prod.case
                    apply (rule UnionI)
                    apply (rule imageI)
                   apply (rule imageI)
                   apply assumption
                  by fastforce
                done
              done
            done
          done
        subgoal for x
          apply (subst (asm) Union_eq)
          apply (erule CollectE)
          apply (erule bexE)
          subgoal for act'
            apply (erule imageE)
            subgoal for tr
              apply (erule imageE)
              subgoal for auto
                apply (subst (asm) Union_eq)
                apply (frule subst[of act'])
                apply assumption
                apply (erule CollectE)
                apply (erule bexE)
                subgoal for act''
                  apply (rule UnionI)
                   apply (rule imageI)
                   apply (rule imageI)
                  apply assumption
                  apply (cases auto)
                  by fastforce
                done
              done
            done
          done
        done
        finally
        show ?thesis .
      qed
      thus "(\<Union>p\<in>{0..<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}.
            \<Union>(l, e, g, a, _)\<in>Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) p). set_act a) \<union>
             Prod_TA_Defs.broadcast (set broadcast, map automaton_of actual_autos, map_of nta_vars)
          = set broadcast \<union> actual_acts" unfolding Prod_TA_Defs.broadcast_def by auto
    qed 
    moreover
    have "inj_on (mk_renum (broadcast @ nta_actions)) (set (broadcast @ nta_actions))" using mk_renum_inj by blast
    ultimately
    show ?thesis unfolding 1
      apply -
      apply (rule inj_on_subset)
       apply assumption
      using actual_acts_correct by auto
  qed
  show "infinite (UNIV::'action clock set)"
    using infinite_actions infinite_clock by blast
  show "infinite (UNIV::'proposition variable set)"
    using infinite_propositions infinite_variable by blast
  show "infinite (UNIV::'action location set)"
    using infinite_actions infinite_location by blast
  show "infinite (UNIV::String.literal set)" using infinite_literal .
  show "fst ` set nta_vars = Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" using var_set_alt actual_variables_correct by auto
  show "(\<Union>g\<in>set (map (snd \<circ> snd \<circ> snd) actual_autos). fst ` set g) \<subseteq> Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" 
    unfolding loc_set_alt[symmetric] unfolding actual_autos_def using all_inv_loc_correct unfolding all_ta_inv_loc_def Let_def set_fold_append' fold_union' set_map image_image comp_apply ta_inv_loc_def by blast
  show "\<Union> ((set \<circ>\<circ>\<circ> (\<circ>)) fst snd ` set actual_autos) \<subseteq> Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
    unfolding loc_set_alt[symmetric] unfolding actual_autos_def using all_urg_correct unfolding all_ta_urg_def Let_def ta_urg_def set_fold_append' fold_union' set_map image_image comp_apply by simp
  show "\<Union> ((set \<circ> fst) ` set actual_autos) \<subseteq> Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
    unfolding loc_set_alt[symmetric] unfolding actual_autos_def using all_comm_correct unfolding all_ta_comm_def Let_def ta_comm_def set_fold_append' fold_union' set_map image_image comp_apply by simp
  show "urge_clock \<notin> Simple_Network_Impl.clk_set' actual_autos" 
    apply (subst clk_set'_alt)
    unfolding urge_clock_def using all_ta_clocks_correct unfolding nta_clocks_def Let_def timed_automaton_net_spec_def prod.case by auto

  show "ntas_inits \<in> Prod_TA_Defs.states (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
  proof -

    have x: "(InitialLocation # map Off actions) ! i \<in> \<Union>(trans_locs ` ((map set ta_trans) ! i))" if "i < length actions + 1" for i
      unfolding ta_trans_def actual_autos_def ntas_def timed_automaton_net_spec_def main_auto_spec_def action_to_automaton_spec_def
      unfolding Let_def  prod.case
      apply (subst (2) map_map[symmetric, where g = snd])
      apply (subst map_snd_zip)
       apply simp
      unfolding comp_apply map_map 
      apply (subst list.map)
      apply (subst map_map)
      apply (subst comp_def)
      unfolding fst_conv snd_conv
      using that
      apply (induction i)
        subgoal
        unfolding main_auto_init_edge_spec_def
        unfolding Let_def
        unfolding trans_locs_def
        by simp
      subgoal for i
        unfolding start_edge_spec_def Let_def trans_locs_def by simp
      done
 
    have l: "Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars) = length actions + 1"
      unfolding Prod_TA_Defs.n_ps_def actual_autos_def ntas_def timed_automaton_net_spec_def Let_def comp_apply prod.case fst_conv snd_conv by auto
    
    have 1: "\<forall>i<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars).
       (InitialLocation # map Off actions) ! i \<in> (\<Union>(l, e, g, a, r, u, l')\<in>Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of actual_autos, map_of nta_vars) i). {l, l'})"
      apply (rule allI; rule impI)
      subgoal for i
        apply (subst (asm) l)
        apply (frule x)
        unfolding Prod_TA_Defs.N_def fst_conv snd_conv
        apply (erule UnionE)
        subgoal for loc
          unfolding trans_locs_def
          apply (erule imageE)
          subgoal for tr
            apply (subst (asm) trans_alt'[symmetric])
            apply (cases tr)
            subgoal for l _ _ _ _ _ l'
              apply (rule UnionI)
               apply (rule imageI)
               apply (subst nth_map)
              subgoal unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case comp_apply by auto
               apply (subst (asm) nth_map)
              subgoal unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case comp_apply by auto
               apply simp
              unfolding prod.case
              by simp
            done
          done
        done
      done
    
    have "InitialLocation # map Off actions \<in> Prod_TA_Defs.states (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
      unfolding Prod_TA_Defs.states_def
      apply (rule CollectI)
      apply (rule conjI)
      subgoal
        unfolding Prod_TA_Defs.n_ps_def fst_conv snd_conv actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case 
        apply (subst map_map[symmetric])
        apply (subst map_snd_zip)
        apply simp
        by simp
      using 1 by simp
    thus ?thesis using ntas_inits_alt by simp
  qed 

  (* initial assignment assigns values to actual variables *)
  show "fst ` set init_vars = Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)" 
    unfolding var_set_alt actual_variables_correct
    unfolding init_vars_def set_map by auto
  show "distinct (map fst init_vars)" 
    unfolding init_vars_def nta_vars_def 
    unfolding timed_automaton_net_spec_def Let_def prod.case
    unfolding all_vars_spec_def Let_def fold_union'
    apply (subst map_map)
    apply (subst comp_def)
    apply (subst fst_conv)
    apply (subst map_append)
    apply (subst list.map)+
    unfolding fst_conv
    apply (subst distinct_append)
    apply (intro conjI)
      apply simp
     defer 
    apply (subst list.set)+
     apply (subst set_map)+
     apply fastforce
    apply (subst filter_append)
    apply (subst filter_map)+
    unfolding map_map fst_conv comp_apply set_map map_append
    apply (subst distinct_append)
    apply (intro conjI)
      apply (rule distinct_inj_map)
       apply (rule distinct_filter)
       apply (rule distinct_props)
      apply (rule injI)
    using variable.inject(2)
    apply simp
      apply (rule distinct_inj_map)
       apply (rule distinct_filter)
       apply (rule distinct_props)
      apply (rule injI)
    using variable.inject(2)
     apply simp
    by auto
  (* locations exist in some automata *)
  show "set2_formula form \<subseteq> Prod_TA_Defs.loc_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
    apply (subst loc_set_alt[symmetric])
    unfolding form_def timed_automaton_net_spec_def Let_def prod.case
    unfolding all_ta_states_def individual_ta_states_def ntas_def timed_automaton_net_spec_def 
    unfolding Let_def prod.case 
    unfolding ta_states_def
    apply (subst map_map[symmetric])
    apply (subst map_snd_zip)
     apply simp
    apply (subst list.map)
    apply (rule subsetI)
    apply (subst set_fold_append')
    apply (subst fold_union')
    apply (subst set_map)
    apply (subst list.set)
    apply (subst insert_is_Un)
    apply (rule UnionI)
     apply (rule imageI)
     apply (rule UnI1)
    unfolding main_auto_spec_def
    unfolding Let_def comp_apply prod.case fst_conv snd_conv
     apply blast
    by fastforce
  (* automaton is in the list of automata *)
  show "locs_of_formula form \<subseteq> {0..<Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars)}"
    unfolding Prod_TA_Defs.n_ps_def fst_conv snd_conv
    unfolding form_def timed_automaton_net_spec_def Let_def prod.case 
    apply (subst locs_of_formula.simps)
    apply (subst locs_of_sexp.simps)
    unfolding actual_autos_def ntas_def Let_def timed_automaton_net_spec_def prod.case by simp
  show "vars_of_formula form \<subseteq> Prod_TA_Defs.var_set (set broadcast, map automaton_of actual_autos, map_of nta_vars)"
    unfolding var_set_alt actual_variables_correct
    unfolding form_def timed_automaton_net_spec_def Let_def prod.case vars_of_formula.simps vars_of_sexp.simps ..
qed

find_theorems name: "abs_renum.urge_bisim"
             
(* lemma "abs_renum.sem, abs_renum.a\<^sub>0 \<Turnstile> form"
  sorry *)
(* To do: Don't actually prove this correct. Just provide the necessary assumptions to instantiate this *)
section \<open>Equivalence to temporal planning semantics\<close>


term "map_option (map_lower_bound Rat.of_int)"

definition lower_sem where
"lower_sem \<equiv> (map_option (map_lower_bound Rat.of_int)) o lower"

definition upper_sem where
"upper_sem \<equiv> (map_option (map_upper_bound Rat.of_int)) o upper"

lemma form_alt: "form \<equiv> Simple_Network_Language_Model_Checking.formula.EX (sexp.loc 0 GoalLocation)"
  unfolding form_def Let_def timed_automaton_net_spec_def prod.case .

context 
  fixes \<pi>
  assumes vp: "valid_plan \<pi> (set init) (set goal) at_start at_end (set \<circ> over_all) lower_sem upper_sem (set \<circ> pre) (set \<circ> adds) (set \<circ> dels) (Rat.of_int \<epsilon>)"
      and pap: "plan_actions_in_problem \<pi> (set actions)"
      and nso: "no_self_overlap \<pi>"
begin
interpretation planning_sem: nta_temp_planning 
  "set init" "set goal" 
  at_start at_end 
  "set o over_all" 
  lower_sem upper_sem 
  "set o pre" "set o adds" "set o dels"
  "Rat.of_int \<epsilon>"
  "set props"
  "set actions"
  \<pi> 
  1
  apply standard 
  subgoal using some_propositions unfolding List.card_set apply (induction props) by auto
  subgoal using some_actions unfolding List.card_set apply (induction actions) by auto
  subgoal by simp
  subgoal by simp
  subgoal using eps_range unfolding Rat.of_int_def by auto
  subgoal using domain_ref_fluents using fluent_imp_const_valid_dom by blast
  using domain_ref_fluents init_props goal_props at_start_inj at_end_inj snaps_disj vp pap nso by simp+

(* Invariants of actions whose index is lower than n and are scheduled at t 
    have been deactivated. In other words, the parts of their end snap-actions that
    deactivate invariants have been executed *)                         
definition "partially_updated_locked_before t p n \<equiv> planning_sem.locked_before t p 
-  sum_list (map 
      (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0)) 
      (filter 
        (\<lambda>a. p \<in> set (over_all a)) 
        (map (\<lambda>n. actions ! n) [0..<n])))"

lemma sum_list_eq:
  assumes "distinct xs" "distinct ys" "set xs = set ys" 
  shows "sum_list ((map f xs)::nat list) = sum_list (map f ys)"
proof -
  have "mset xs = mset ys" using assms set_eq_iff_mset_eq_distinct by blast
  hence "mset (map f xs) = mset (map f ys)" by simp
  hence "fold (+) (map f xs) 0 = fold (+) (map f ys) 0"
    apply -
    apply (rule fold_permuted_eq[where P = "\<lambda>_. True"])
       apply simp
      apply simp
     apply simp
    by simp
  moreover
  have "foldr (+) (map f xs) 0 = fold (+) (map f xs) 0"
    apply (subst foldr_fold)
    by auto
  moreover
  have "foldr (+) (map f ys) 0 = fold (+) (map f ys) 0"
    apply (subst foldr_fold)
    by auto
  ultimately
  show ?thesis unfolding sum_list.eq_foldr by argo
qed

lemma partially_updated_locked_before_by_all_actions_is_locked_during: 
  "partially_updated_locked_before t p (length actions) = planning_sem.locked_during t p"
proof -
  have d1: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) actions)" using distinct_actions by auto
  have d2: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.distinct_action_list by simp
  have s: "set (filter (\<lambda>a. p \<in> set (over_all a)) actions) = set (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.set_action_list by auto
  
  show ?thesis
  unfolding partially_updated_locked_before_def planning_sem.locked_during_and_before
  apply (subst planning_sem.locked_by_def)
  apply (subst comp_apply)
  apply (subst List.map_nth)
  using sum_list_eq[OF d1 d2 s]
  by auto
qed

lemma partially_updated_locked_before_inv_mono: "partially_updated_locked_before t p n \<ge> partially_updated_locked_before t p (Suc n)"
  unfolding partially_updated_locked_before_def by simp


lemma partially_updated_locked_before_inv_mono': assumes "n \<le> m"
  shows "partially_updated_locked_before t p n \<ge> partially_updated_locked_before t p m"
  using assms
  apply (induction m arbitrary: n)
  subgoal for n
   apply (induction n)
    using partially_updated_locked_before_inv_mono apply blast
    using partially_updated_locked_before_inv_mono order_trans by blast
  subgoal for m n
    apply (subst (asm) le_Suc_eq)
    apply (erule disjE)
    apply (rule partially_updated_locked_before_inv_mono[THEN order_trans])
     apply blast
    by blast
  done

lemma partially_updated_locked_before_by_none_is_locked_before:
  "partially_updated_locked_before t p 0 = planning_sem.locked_before t p"
  unfolding partially_updated_locked_before_def
  by simp

lemma partially_updated_locked_before_ran: "partially_updated_locked_before t p n \<le> length actions" 
  using planning_sem.locked_before_ran unfolding distinct_card[OF distinct_actions]
  using partially_updated_locked_before_inv_mono'[of 0 n] unfolding partially_updated_locked_before_by_none_is_locked_before 
  using order_trans by blast

lemma foldr_assoc: "foldr (+) xs (n + 0::nat) = (foldr (+) xs 0) + n"
  apply (induction xs)
   apply simp
  subgoal for x xs
    by auto
  done

lemma partially_updated_locked_before_alt: assumes "n < length actions"
  shows "partially_updated_locked_before t p n = planning_sem.locked_during t p 
+ sum_list (map 
      (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)) 
      (filter 
        (\<lambda>a. p \<in> set (over_all a)) 
        (map (\<lambda>n. actions ! n) [n..<length actions])))"
proof -
  have 1: "foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n]))) 0 +
  foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0 =
  foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n])))
   (foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0)"
    using foldr_assoc[symmetric, where xs = "(map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n])))" and n = "foldr (+) (map (\<lambda>a. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) (filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]))) 0"]
    by simp
  have d1: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) actions)" using distinct_actions by auto
  have d2: "distinct (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.distinct_action_list by simp
  have s: "set (filter (\<lambda>a. p \<in> set (over_all a)) actions) = set (filter (\<lambda>a. p \<in> set (over_all a)) planning_sem.action_list)" using planning_sem.set_action_list by auto


  have "(\<Sum>a\<leftarrow>planning_sem.locked_by p. if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0) 
      = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [0..<n]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0) 
      + (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then 1 else 0)"
    apply (subst (2) sum_list.eq_foldr)+
    apply (subst 1)
    apply (subst foldr_append[symmetric])
    apply (subst map_append[symmetric])
    apply (subst filter_append[symmetric])
    apply (subst map_append[symmetric])
    apply (subst upt_append)
    using assms
     apply simp
    apply (subst sum_list.eq_foldr[symmetric])
    apply (subst List.map_nth)
    apply (subst sum_list_eq[OF d1 d2 s])
    using planning_sem.locked_by_def unfolding comp_def
    by simp
  thus ?thesis 
    apply (subst partially_updated_locked_before_def)  
    apply (subst planning_sem.locked_before_and_during)
    by linarith
qed

(* A is Graph_Defs for the Bisimulation_Invariant of parts of the transition relation.
A is the original graph combined with semantics. *)

term "\<lambda>(L, s, u) (L', s', u'). step_u' abs_renum.sem L s u L' s' u'"

value "shd (shift [1::nat] x)"

term "planning_sem.happ_seq"

definition to_var_asmt::"'proposition set \<Rightarrow> 'proposition set \<Rightarrow> 'proposition variable \<Rightarrow> int option" where
"to_var_asmt ps iv vr \<equiv> (
  case vr of
    PropVar p \<Rightarrow> if (p \<in> ps) then 1 else 0
  | PropLock p \<Rightarrow> if (p \<in> iv) then 1 else 0
) |> Some
"


(* The main automaton is the first automaton, so the index must be incremented *)
definition enter_start_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"enter_start_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := StartInstant act];

  ds = dels (at_start act) |> map PropVar;
  as = adds (at_start act) |> map PropVar;
  var_asmt' = var_asmt(ds [\<mapsto>] (list_of (0::int) (length ds)));
  var_asmt'' = var_asmt'(as [\<mapsto>] (list_of (0::int) (length as)));

  clock_asmt' = clock_asmt(ActStart act := 0)
in (act_locs', var_asmt'', clock_asmt')
"

definition enter_start_instants::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"enter_start_instants ns s \<equiv>
  seq_apply (map enter_start_instant ns) s
"


(* It is valid to assume that variables have an assignment. Hidden assumption (at this level)

The initial variable assignment has a domain equal to the set of actually occurring variables and
in no step is a variable unassigned *)
definition leave_start_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"leave_start_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := Running act];
  locks = over_all act |> map PropLock;
  cur_asmt = map (get_default 0 var_asmt) locks;
  next_asmt = map (\<lambda>x. x + 1) cur_asmt;
  var_asmt' = var_asmt(locks [\<mapsto>] next_asmt)
in (act_locs', var_asmt', clock_asmt)
"

definition leave_start_instants::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval) list" where
"leave_start_instants ns s \<equiv>
  seq_apply (map leave_start_instant ns) s
"

text \<open>Applying the end happenings first\<close>
definition enter_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"enter_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := EndInstant act];

  locks = over_all act |> map PropLock;
  cur_asmt = map (the o var_asmt) locks;
  next_asmt = map (\<lambda>x. x - 1) cur_asmt;
  var_asmt' = var_asmt(locks [\<mapsto>] next_asmt);
  clock_asmt' = clock_asmt(ActEnd act := 0)
in (act_locs', var_asmt', clock_asmt')
"

definition "enter_end_instants ns s \<equiv> seq_apply (map enter_end_instant ns) s"

definition leave_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"leave_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := Off act];

  
  ds = dels (at_end act) |> map PropVar;
  as = adds (at_end act) |> map PropVar;
  var_asmt' = var_asmt(ds [\<mapsto>] (list_of (0::int) (length ds)));
  var_asmt'' = var_asmt'(as [\<mapsto>] (list_of (0::int) (length as)))
in (act_locs', var_asmt'', clock_asmt)
"

definition "leave_end_instants ns s \<equiv> seq_apply (map leave_end_instant ns) s"

definition apply_snap_action::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"apply_snap_action n s \<equiv>
seq_apply [enter_start_instant n, enter_end_instant n, leave_end_instant n] s
"

definition "apply_instant_actions ns s \<equiv> seq_apply'' (map apply_snap_action ns) s" 

(* apply all snap actions of the nth happening in the plan *)
definition apply_nth_happening::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"apply_nth_happening n s \<equiv>
let
  h = happ_at planning_sem.happ_seq (time_index \<pi> n);
  act_indices = [0..<length actions];
  start_indices = filter (\<lambda>n. at_start (actions ! n) \<in> h \<and> at_end (actions ! n) \<notin> h) act_indices;
  end_indices = filter (\<lambda>n. at_start (actions ! n) \<notin> h \<and> at_end (actions ! n) \<in> h) act_indices;
  both = filter (\<lambda>n. at_start (actions ! n) \<in> h \<and> at_end (actions ! n) \<in> h) act_indices
in 
  s 
  |> enter_end_instants end_indices
  |> (\<lambda>s. ext_seq' s (enter_start_instants start_indices))
  |> (\<lambda>s. ext_seq' s (apply_instant_actions both))
  |> (\<lambda>s. ext_seq' s (leave_end_instants end_indices))
  |> (\<lambda>s. ext_seq' s (leave_start_instants start_indices))
"

definition delay::"
real
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval)" where
"delay t s \<equiv> map_prod id (map_prod id (\<lambda>clock_asmt. clock_asmt \<oplus> t)) s"


find_theorems name: "real*of"

definition get_delay::"nat \<Rightarrow> real" where
"get_delay i \<equiv>
  if (i = 0) 
  then \<epsilon> + 1
  else real_of_rat (htpl \<pi> ! i - htpl \<pi> ! (i - 1)) 
"


definition delay_and_apply::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"delay_and_apply i s \<equiv>
let
  d = get_delay i
in
  s 
  |> delay d
  |> apply_nth_happening i
"

definition start_planning::"
('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"start_planning s \<equiv>
let 
  (locs, var_asmt, clock_asmt) = s;
  main_auto_index = 0;

  locs' = locs[main_auto_index := Planning];
  
  init_props = map PropVar init;
  var_asmt' = var_asmt(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0);
  var_asmt'' = var_asmt'(init_props [\<mapsto>] (list_of (1::int) (length init)))
in (locs', var_asmt'', clock_asmt)"

definition end_planning::"
('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"end_planning s \<equiv>
let
  (locs, var_asmt, clock_asmt) = s;
  main_auto_index = 0;

  locs' = locs[main_auto_index := GoalLocation];
  
  init_props = map PropLock init;
  var_asmt' = var_asmt(PlanningLock \<mapsto> 2)
in (locs', var_asmt', clock_asmt)"


primcorec goal_run::"
  ('action location list \<times>
    ('proposition variable \<rightharpoonup> int) \<times>
    ('action clock, real) cval) 
\<Rightarrow> ('action location list \<times>
    ('proposition variable \<rightharpoonup> int) \<times>
    ('action clock, real) cval) stream" where
"goal_run s = s ## (goal_run s)"

(* Just for testing *)
definition "goal_state \<equiv> (GoalLocation # map Off actions, map_of (zip (map fst nta_vars) (map (fst o snd) nta_vars)), (\<lambda>x. 0))"

definition plan_steps::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) list" where
"plan_steps \<equiv>
let 
  htp_indices = [0..<length (htpl \<pi>)];
  apply_happs = map delay_and_apply htp_indices;
  seq = [abs_renum.a\<^sub>0] 
        |> (\<lambda>s. ext_seq s [start_planning]) 
        |> (\<lambda>s. ext_seq'' s apply_happs)
        |> (\<lambda>s. ext_seq s [end_planning])
in seq"

definition plan_state_sequence::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) stream" where
"plan_state_sequence \<equiv> plan_steps @- (goal_run (last plan_steps))"



subsection \<open>General properties of the problem\<close>
lemma action_variables: 
  assumes "a \<in> set actions"
  shows "action_vars_spec a \<subseteq> PropLock ` (set props) \<union> PropVar ` (set props)"
  unfolding action_vars_spec_def Let_def inv_vars_spec_def set_map set_append snap_vars_spec_def 
  using domain_ref_fluents[simplified fluent_domain_def, THEN bspec, OF assms] 
  unfolding act_ref_fluents_def by auto

lemma init_variables:
  "PropVar ` (set init) \<union> PropVar ` (set goal) \<subseteq> PropVar ` (set props)"
  using init_props goal_props by auto

lemma all_vars_spec_exact: "all_vars_spec = [(ActsActive, 0, (length actions)), (PlanningLock, 0, 2)] @ map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props) @
    map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" 
proof -
  have 1: "filter (\<lambda>x. fst x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props) = 
    map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props) @
    map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)"
    apply (subst filter_append)
    apply (subst filter_map)+
    apply (subst comp_def)+
    apply (subst fst_conv)+ by simp
  
  have 2: "map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)
      = map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props)" apply (induction props) by auto
  
  show "all_vars_spec = [(ActsActive, 0, (length actions)), (PlanningLock, 0, 2)] @ map (\<lambda>p. (PropLock p, 0, (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props) @
    map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" 
    unfolding all_vars_spec_def Let_def fold_union' apply (subst 1)
    apply (subst 2)
    by simp
qed



lemma all_vars_spec_exact_set: "set (map fst all_vars_spec) = {ActsActive, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)"
proof -
  have 1: "set (map fst (filter (\<lambda>x. fst x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props))) 
    = \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)"
    apply (subst filter_append)
    unfolding filter_map comp_def
    unfolding set_append fst_conv map_append
    unfolding map_map comp_def fst_conv
    apply (subst (3) comp_def[of _ PropLock, symmetric])
    apply (subst filter_map[symmetric])
    apply (subst (4) comp_def[of _ PropVar, symmetric])
    apply (subst filter_map[symmetric])
    using action_variables init_variables 
    by auto
  show ?thesis 
    unfolding all_vars_spec_def Let_def prod.case fold_union'
    unfolding map_append
    unfolding set_append
    apply (subst list.map)+
    apply (subst fst_conv)+
    apply (subst list.set)+
    apply (subst 1)
    unfolding set_map ..
qed

subsection \<open>General properties of the automaton\<close>

lemma conv_trans:
assumes "p < length (map (automaton_of o conv_automaton) actual_autos)"
shows "Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) ` (trans (automaton_of  (actual_autos ! p)))"
  apply (subst nth_map)
  using assms apply simp
  apply (subst comp_def)
  apply (cases "actual_autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "actual_autos ! p"])
     apply assumption
    unfolding conv_automaton_def prod.case
    unfolding automaton_of_def prod.case
    unfolding trans_def fst_conv snd_conv
    unfolding set_map by blast
  done

lemma conv_committed: 
  assumes "p < length (map (automaton_of o conv_automaton) actual_autos)"
  shows "committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = committed (map automaton_of actual_autos ! p)"
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "actual_autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "actual_autos ! p"])
     apply simp
    unfolding comp_apply
    unfolding conv_automaton_def automaton_of_def committed_def prod.case fst_conv ..
  done

lemma no_committed: 
  assumes "p < length actual_autos"
  shows "committed (map automaton_of actual_autos ! p) = {}"
  using assms
  unfolding actual_autos_alt automaton_of_def committed_def main_auto_spec_def Let_def action_to_automaton_spec_def
  apply (cases p)
  by simp+

lemma conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) actual_autos)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of actual_autos ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "actual_autos ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(actual_autos ! p)"])
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

lemma no_invs': assumes "p < length actual_autos"
  shows "inv (automaton_of (actual_autos ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case 
    by simp+
  show ?thesis
  unfolding actual_autos_def  ntas_def timed_automaton_net_spec_def Let_def prod.case
  apply (subst map_map[symmetric])
  apply (subst map_snd_zip)
   apply simp
  unfolding main_auto_spec_def Let_def action_to_automaton_spec_def
  unfolding comp_apply
  apply (subst list.map)
  apply (subst map_map)
  unfolding snd_conv comp_def inv_def
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

lemma no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) actual_autos)"
  shows "inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>x. [])"
  apply (subst conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using no_invs'
  apply (subst no_invs')
  using assms by auto

lemma cval_add_0: "z\<oplus>(0::real) = z" unfolding cval_add_def 
  by simp

lemma step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of nta_vars) y"
  shows "abs_renum.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding abs_renum.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using no_invs by simp
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by simp
  done

lemmas single_step_intro = abs_renum.urge_bisim.A.steps.Cons[OF _ abs_renum.urge_bisim.A.steps.Single]
lemmas non_t_step_intro = step_t_possible[THEN step_u'.intros, rotated, rotated]

subsection \<open>Proofs\<close>

definition exec_state_to_loc_list::"'action set \<Rightarrow> 'action location list" where
"exec_state_to_loc_list S \<equiv> 
let es_to_loc = (\<lambda>a. if a \<in> S then Running a else Off a)
in (Planning # map es_to_loc actions)"

definition prop_state_to_var_asmt::"'proposition set \<Rightarrow> ('proposition \<Rightarrow> nat) \<Rightarrow> 'proposition variable \<Rightarrow> int option" where
"prop_state_to_var_asmt P PI p \<equiv> case p of
  PropVar p \<Rightarrow> if (p \<in> P) then Some 1 else Some 0
| PropLock p \<Rightarrow> Some (PI p)"

fun act_clock_spec::"rat \<Rightarrow> 'action clock \<Rightarrow> real" where
"act_clock_spec t (ActStart a) = real_of_rat (planning_sem.last_snap_exec (at_start a) t)" |
"act_clock_spec t (ActEnd a) = real_of_rat (planning_sem.last_snap_exec (at_end a) t)"


lemma "abs_renum.urge_bisim.A.steps ((undefined, undefined, undefined) # (undefined, undefined, undefined) # undefined)"
  apply (rule abs_renum.urge_bisim.A.steps.intros)
   apply (subst prod.case)+
  apply (rule non_t_step_intro)
  sorry

lemma a\<^sub>0_alt: "abs_renum.a\<^sub>0 = (InitialLocation # map Off actions, map_of (map (\<lambda>x. (fst x, 0)) nta_vars), \<lambda>_. 0)"
  unfolding abs_renum.a\<^sub>0_def
  unfolding ntas_inits_alt
  unfolding init_vars_def
  ..

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

lemma planning_start_state_char: 
  assumes "start_planning abs_renum.a\<^sub>0 = (l1, v1, c1)"
  shows "l1 = Planning # map Off actions 
    \<and> v1 PlanningLock = Some 1 
    \<and> v1 ActsActive = Some 0 
    \<and> (\<forall>p \<in> set init. v1 (PropVar p) = Some 1)
    \<and> (\<forall>v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0) 
    \<and> (\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None) 
    \<and> c1 = (\<lambda>_. 0)"
proof (intro conjI)
  have "l1 = Planning # map Off actions"
       "c1 = (\<lambda>_. 0)"
       and v1: "v1 = (map_of (map (\<lambda>x. (fst x, 0)) nta_vars))(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] list_of 1 (length init))"
    using assms unfolding a\<^sub>0_alt start_planning_def Let_def prod.case by simp+
  thus "l1 = Planning # map Off actions" "c1 = (\<lambda>_. 0)" by simp+
  show "v1 PlanningLock = Some 1" unfolding v1
    apply (subst Map.map_upds_apply_nontin) by auto
  show "v1 ActsActive = Some 0" unfolding v1
    apply (subst Map.map_upds_apply_nontin) by auto
  show "\<forall>p\<in>set init. v1 (PropVar p) = Some 1"
  proof (rule ballI)
    fix p
    assume a: "p \<in> set init"
    hence l: "0 < length init" by auto
    hence s: "set (list_of 1 (length init)) = {1}"
      apply (rule set_list_of) .
      
    have "map_of (zip (rev (map PropVar init)) (rev (list_of 1 (length init)))) (PropVar p) = Some 1" 
      using map_of_zip_dom_to_range'[of "PropVar p" "(rev (map PropVar init))", simplified, of "rev (list_of 1 (length init))", simplified length_list_of length_rev set_rev s]
      a by auto
    hence "map_of (rev (zip (map PropVar init) (list_of 1 (length init)))) (PropVar p) = Some 1" 
      apply -
      apply (subst zip_rev[symmetric])
       apply (subst length_list_of)
      by simp+
    thus "v1 (PropVar p) = Some 1" unfolding v1
      apply (subst map_upds_def)
      apply (subst map_add_Some_iff)
      by auto
  qed
  show "\<forall>v\<in>actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0" 
  proof (rule ballI)
    fix v
    assume a: "v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init)"
    hence b: "v \<in> actual_variables" by simp
    have "map_of (rev (zip (map PropVar init) (list_of 1 (length init)))) v = None"
      apply (subst zip_rev[symmetric])
      unfolding length_list_of
       apply simp
      apply (subst map_of_zip_is_None)
      unfolding length_list_of length_rev
       apply simp
      using a by simp
    moreover
    have 1: "(map (\<lambda>x. (fst x, 0)) nta_vars) = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" by auto
    have "((map_of (map (\<lambda>x. (fst x, 0)) nta_vars))(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0)) v = Some 0"
      apply (subst fun_upd_other)
      using a apply simp
      apply (subst fun_upd_other)
      using a apply simp
      using b unfolding actual_variables_correct
      apply (subst 1)
      apply (subst map_of_map)
      apply (subst comp_apply)
      apply (subst (asm) set_map)
      apply (erule imageE)
      subgoal for x
        apply (cases x)
        subgoal for y z
          using weak_map_of_SomeI by fastforce
        done
      done
    ultimately
    show "v1 v = Some 0" 
      unfolding v1
      apply (subst map_upds_def)
      apply (subst map_add_Some_iff)
      apply (rule disjI2)
      by simp
  qed
  show "\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None"
  proof (intro allI impI)
    fix v
    assume "v \<notin> actual_variables"
    with actual_variables_correct
    have 1: "v \<notin> set (map fst nta_vars)" by argo
    with all_vars_spec_exact_set nta_vars'
    have 2: "v \<notin> {ActsActive, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)" by simp
    
    have 3: "(map (\<lambda>x. (fst x, 0)) nta_vars) = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" by auto
    show "v1 v = None"
      unfolding v1
      apply (subst map_upds_apply_nontin)
      using 2 apply simp
      apply (subst fun_upd_other)
      using 2 apply simp
      apply (subst fun_upd_other)
      using 2 apply simp
      apply (subst 3)
      apply (subst map_of_map)
      apply (subst comp_def)
      using 1 
      unfolding set_map map_of_eq_None_iff[symmetric]
      by simp
  qed
qed

lemma init_vars_alt: "init_vars = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" unfolding init_vars_def by auto


lemma init_vars_bounded: "bounded (map_of nta_vars) (map_of init_vars)"
  unfolding bounded_def
proof (intro conjI ballI)
  show 1: "dom (map_of init_vars) = dom (map_of nta_vars)" unfolding init_vars_alt apply (subst dom_map_of_map) apply (subst dom_map_of_conv_image_fst) by blast
  { fix x
    assume "x \<in> dom (map_of init_vars)" 
    then obtain y where
      y: "map_of nta_vars x = Some y" using 1 by auto
    hence "fst y = 0" unfolding nta_vars' unfolding all_vars_spec_def Let_def
      apply -
      apply (drule map_of_SomeD)
      by auto
    thus "fst (the (map_of nta_vars x)) \<le> the (map_of init_vars x)" unfolding init_vars_alt map_of_map comp_apply
      using y by simp
      
  }
  { fix x
    assume "x \<in> dom (map_of init_vars)"then obtain y where
      y: "map_of nta_vars x = Some y" using 1 by auto
    hence "snd y \<ge> 0" unfolding nta_vars' unfolding all_vars_spec_def Let_def
      apply -
      apply (drule map_of_SomeD)
      unfolding set_append
      apply (induction y)
      by auto
    thus "the (map_of init_vars x) \<le> snd (the (map_of nta_vars x))" unfolding init_vars_alt map_of_map comp_apply
      using y by simp
  }
qed
      
lemma main_auto_init_edge_spec_simp: "main_auto_init_edge_spec = (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning)"
  unfolding main_auto_init_edge_spec_def Let_def ..
(* 
lemma step_int_simp: "x = (l, b, g, Sil a, f, r, l') \<Longrightarrow>
  TRANS ''silent'' \<bar> (l, b, g, Sil a, f, r, l') \<in> Simple_Network_Language.trans (N ! p) \<Longrightarrow>
  ''committed'' \<bar> l \<in> committed (N ! p) \<or> (\<forall>p<length N. L ! p \<notin> committed (N ! p)) \<Longrightarrow>
  ''bexp'' \<bar> Simple_Expressions.check_bexp s b True \<Longrightarrow>
  ''guard'' \<bar> u \<turnstile> g \<Longrightarrow>
  ''target invariant'' \<bar> \<forall>p<length N. u' \<turnstile> Simple_Network_Language.inv (N ! p) (L' ! p) \<Longrightarrow>
  ''loc'' \<bar> L ! p = l \<Longrightarrow>
  ''range'' \<bar> p < length L \<Longrightarrow> ''new loc'' \<bar> L' = L[p := l'] \<Longrightarrow>
  ''new valuation'' \<bar> u' = [r\<rightarrow>0]u \<Longrightarrow> ''is_upd'' \<bar> is_upds s f s' \<Longrightarrow>
  ''bounded'' \<bar> Simple_Network_Language.bounded B s' \<Longrightarrow> 
  (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>" apply (rule step_int) *)

lemma "x \<in> dom v \<Longrightarrow> \<exists>y. v x = Some y" by auto

lemma is_upds_set_vars_list_of: "is_upds v (map (set_var n) xs) (v(xs [\<mapsto>] (list_of n (length xs))))"
  apply (induction xs arbitrary: v)
  subgoal 
    apply (subst list_of_def)
    apply simp
    by (rule is_upds.intros)
  subgoal for x xs v
    apply (subst length_nth_simps)
    apply (subst list_of_Suc)
    apply (subst list.map)
    apply (subst map_upds_Cons)
    apply (rule is_upds.intros)
    unfolding is_upd_def
    apply (intro exI conjI)
      apply (rule HOL.refl)
      apply (rule check_bexp_is_val.intros)
     apply (rule HOL.refl)
    by simp
  done

lemma is_upds_inc_vars: 
  assumes "set xs \<subseteq> dom v"
      and "distinct xs"
  shows "is_upds v (map (\<lambda>v. (v, binop plus_int (var v) (exp.const (- 1)))) xs) (v(xs [\<mapsto>] map (\<lambda>x. x - 1) (map (the o v) xs)))"
  using assms
proof (induction xs arbitrary: v)
  case Nil
  then show ?case 
    apply simp
    by (rule is_upds.intros)
next
  case (Cons x xs v)
  have 1: "is_upd v (x, binop plus_int (var x) (exp.const (- 1))) (v(x \<mapsto> the (v x) - 1))" (is "is_upd v ?upd ?v'")
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

   have "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const (- 1)))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x - 1) (map (the \<circ> ?v') xs)))"
     apply (rule Cons.IH)
     using Cons(2,3) by auto
   hence 3: "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const (- 1)))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x - 1) (map (the \<circ> v) xs)))"
     apply (subst 2) by simp
   show ?case 
    apply (subst list.map)+
    apply (subst map_upds_Cons)
     apply (rule is_upds.intros(2)[OF 1])
     using 3 unfolding comp_apply by simp
qed

schematic_goal nta_vars_exact: "nta_vars = ?x"
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact)
  ..

schematic_goal map_of_nta_vars_exact: "map_of nta_vars = ?x"
  apply (subst nta_vars_exact)
  apply (subst map_of_map)
  unfolding comp_def map_of_append
  ..

schematic_goal dom_map_of_nta_vars: "dom (map_of nta_vars) = ?d"
  apply (subst dom_map_of_conv_image_fst)
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact_set[simplified set_map])
  ..

lemma map_of_nta_vars_ActsActive: 
  "map_of nta_vars ActsActive = Some (0, length actions)" using nta_vars_exact by simp

lemma map_of_nta_vars_PlanningLock:
  "map_of nta_vars PlanningLock = Some (0, 2)" using nta_vars_exact by simp

lemma map_prop_var_simp: "map (\<lambda>p. (PropVar p, 0, 1)) xs = map (\<lambda>(v, b). (v, id b)) (map (\<lambda>v. (v, 0, 1)) (map PropVar xs))"
  by simp

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
      unfolding v'
      apply (subst (asm) dom_map_upds)
      apply (subst (asm) assms(2)[symmetric])
      apply (subst (asm) take_all, simp)
      apply (erule UnE)
      subgoal using bounds by blast
      subgoal using previous unfolding bounded_def by argo
      done
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

find_theorems name: "upd*Some"

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

  
text \<open>The bounds of nta_vars\<close>
lemma map_of_nta_vars_init_goal:
  assumes "v \<in> set (map PropVar init) \<union> set (map PropVar goal)"
  shows "map_of nta_vars v = Some (0, 1)"
proof-
  from assms init_props goal_props
  obtain p where
    p: "p \<in> set init \<union> set goal"
    "p \<in> set props"
    "v = PropVar p" by auto

  hence 1: "p \<in> set (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" by auto
  have distinct: "distinct (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)" using distinct_props by simp
  have 2:"(map_of (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)) p) = Some (0, 1)"
    apply (rule map_of_is_SomeI)
    using distinct
     apply (subst map_map)
     apply (subst comp_def)
     apply (subst fst_conv)
     apply simp
    using 1 by simp
  have 3: "map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props) = 
    map (\<lambda>(p, v). (PropVar p, v)) (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props))"
    by simp
  have 4: "map_of (map (\<lambda>p. (PropVar p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)) (PropVar p) 
    = (map_of (map (\<lambda>p. (p, 0, 1)) (filter (\<lambda>x. PropVar x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) props)) p)" 
    apply (subst 3)
    apply (subst map_of_map_inj_fst)
     apply (subst inj_def)
    by simp+

  show ?thesis
    apply (subst map_of_nta_vars_exact)
    apply (subst p)
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_left)
     apply (rule map_of_NoneI)
     apply (subst set_map)
     apply (subst image_image)
     apply (subst fst_conv)
     apply (rule notI)
     apply (rule imageE)
      apply simp
     apply simp
      apply (subst 4)
      apply (subst 2)
      by simp
qed


lemma map_of_nta_vars_action_inv:
  assumes "a \<in> set actions"
    "v \<in> set (map PropLock (over_all a))"
  shows "map_of nta_vars v = Some (0, length actions)"
proof -
  from assms local.planning_sem.finite_props_domain
  obtain p where
    p: "p \<in> set (over_all a)"
    "p \<in> set props"
    "v = PropLock p" unfolding fluent_domain_def act_ref_fluents_def by auto
  hence 1: "p \<in> set (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props)" 
    unfolding action_vars_spec_def Let_def inv_vars_spec_def set_map using assms
    by auto

  have 2: "map_of (map (\<lambda>p. (PropLock p, y)) (filter (\<lambda>x. PropLock x \<in> S) props)) (PropLock p) 
    = (map_of (map (\<lambda>p. (p, y)) (filter (\<lambda>x. PropLock x \<in> S) props)) p)" for S y 
    apply (subst (2) map_of_map_inj_fst[symmetric, where f = PropLock])
    unfolding inj_def apply simp
    apply (subst map_map)
    apply (subst comp_def)
    unfolding prod.case
    by blast


  show ?thesis
    apply (subst map_of_nta_vars_exact)
    apply (subst p)
    apply (subst map_add_find_left)
     apply simp
    apply (subst map_add_find_right)
     apply (subst 2)
     apply (rule map_of_is_SomeI)
    using distinct_props unfolding map_map comp_apply apply simp
    using 1 apply fastforce
    by simp

qed


lemma initial_steps_are_steps: "abs_renum.urge_bisim.A.steps ([abs_renum.a\<^sub>0] |> (\<lambda>s. ext_seq s [start_planning]))"
proof -
  have "abs_renum.urge_bisim.A.steps [abs_renum.a\<^sub>0, start_planning abs_renum.a\<^sub>0]" 
  proof (rule abs_renum.urge_bisim.A.steps.intros)
    show "(case abs_renum.a\<^sub>0 of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (start_planning abs_renum.a\<^sub>0)"
    proof -
      obtain l1 v1 c1 where
        sp: "start_planning abs_renum.a\<^sub>0 = (l1, v1, c1)"
        and l1: "l1 = Planning # map Off actions"
        and "v1 PlanningLock = Some 1"
        and v1: "v1 ActsActive = Some 0"
        "\<forall>p \<in> set init. v1 (PropVar p) = Some 1"
        "\<forall>v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0" 
        "\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None"
        and c1: "c1 = (\<lambda>_. 0)" using planning_start_state_char apply (cases "start_planning abs_renum.a\<^sub>0") by blast
      (* To do: clean up? *)

      obtain l v and c::"'action clock \<Rightarrow> real" where
        arc: "(l, v, c) = abs_renum.a\<^sub>0" apply (cases "abs_renum.a\<^sub>0::('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))") by simp
      hence l: "l = ntas_inits" 
        and v: "v = map_of init_vars"
        and c: "c = (\<lambda>_. 0)" unfolding abs_renum.a\<^sub>0_def by simp+
      from sp
      have v1': "v1 = v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] list_of 1 (length init))" unfolding start_planning_def Let_def arc[symmetric] prod.case by simp

      have "abs_renum.sem \<turnstile> \<langle>l, v, c\<rangle> \<rightarrow> \<langle>l1, v1, c1\<rangle>"
      proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
        show "abs_renum.sem \<turnstile> \<langle>l, v, c\<rangle> \<rightarrow>\<^bsub>Internal (STR '''')\<^esub> \<langle>l1, v1, c1\<rangle>"
          unfolding abs_renum.sem_def
        proof (rule step_u.step_int)
          show "TRANS ''silent'' \<bar> (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning) \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! 0)" 
            apply (subst TAG_def)
            apply (subst nth_map)
             apply (subst actual_autos_def)
             apply (subst ntas_def)
            apply (subst timed_automaton_net_spec_def)
            unfolding Let_def prod.case
             apply simp
             apply (subst actual_autos_def)
             apply (subst ntas_def)
            apply (subst timed_automaton_net_spec_def)
            unfolding Let_def prod.case
            apply (subst nth_map)
             apply simp
            apply (subst upt_conv_Cons)
             apply simp
            apply (subst nth_zip)
              apply simp
             apply simp
            apply (subst nth_Cons_0)+
            unfolding main_auto_spec_def Let_def prod.case comp_apply snd_conv
            unfolding conv_automaton_def prod.case
            unfolding automaton_of_def prod.case
            unfolding Simple_Network_Language.trans_def fst_conv snd_conv
            unfolding set_map
            apply (subst list.set)
            apply (subst image_insert)
            apply (subst main_auto_init_edge_spec_def)
            unfolding Let_def prod.case
            by simp
            
          show "''committed'' \<bar> InitialLocation \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! 0) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). l ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
            apply (subst TAG_def)
            apply (subst conv_committed)
            using some_actual_autos apply simp
            apply (rule disjI2)
            apply (intro allI impI)
            subgoal for p
            apply (subst conv_committed)
            using some_actual_autos apply simp
            apply (subst nth_map)
            using some_actual_autos apply simp
            apply (subst (asm) length_map)
            apply (frule no_committed)
            apply (subst (asm) nth_map)
            by simp+
          done
          show "''bexp'' \<bar> Simple_Expressions.check_bexp v (Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0)) True"
          proof -
            have "is_val v (var PlanningLock) 0"
              unfolding v init_vars_def 
              apply (rule check_bexp_is_val.intros)
              apply (subst nta_vars')
              unfolding all_vars_spec_def Let_def 
              by simp
            moreover
            have "is_val v (exp.const 0) 0"
              by (rule check_bexp_is_val.intros)
            ultimately
            show ?thesis 
              apply -
              apply (drule check_bexp_is_val.intros)
               apply assumption
              apply (subst TAG_def)
              by simp
          qed
          show "''guard'' \<bar> c \<turnstile> []" apply (subst TAG_def) by simp
          show "''target invariant'' \<bar> \<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c1 \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (l1 ! p)"
            apply (subst TAG_def)
            apply (intro allI impI)
            apply (subst no_invs)
            by simp+
          show "''loc'' \<bar> l ! 0 = InitialLocation"
            apply (subst TAG_def)
            apply (subst l)
            apply (subst ntas_inits_alt)
            by simp
          show "''range'' \<bar> 0 < length l"
            by (simp add: TAG_def l ntas_inits_alt)
          show "''new loc'' \<bar> l1 = l[0 := Planning]"
            apply (subst TAG_def)
            apply (subst l)
            apply (subst ntas_inits_alt)
            apply (subst l1)
            by simp
          show "''new valuation'' \<bar> c1 = [[]\<rightarrow>0]c"
            apply (subst TAG_def)
            unfolding c c1 by simp
          show "''is_upd'' \<bar> is_upds v ((PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init) v1"
          proof -
            have 1: "map (set_prop_ab 1) xs = map (set_var 1) (map PropVar xs)" for xs unfolding set_prop_ab_def by simp
            show ?thesis
            apply (subst TAG_def)
            apply (rule is_upds.intros)
             apply (subst is_upd_def)
             apply (intro exI conjI)
               apply (rule HOL.refl)
              apply (rule check_bexp_is_val.intros)
             apply (rule HOL.refl)
            apply (rule is_upds.intros)
            apply (subst is_upd_def)
             apply (intro exI conjI)
               apply (rule HOL.refl)
              apply (rule check_bexp_is_val.intros)
               apply (rule HOL.refl)
              unfolding v1'
              apply (subst 1)
              using is_upds_set_vars_list_of[where v = "v(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0)" and n = 1 and xs = "(map PropVar init)"] 
              by simp
          qed
          show "''bounded'' \<bar> Simple_Network_Language.bounded (map_of nta_vars) v1"
          proof (subst TAG_def)
            have "bounded (map_of nta_vars) (v(PlanningLock # ActsActive # map PropVar init [\<mapsto>] (1 # 0 # list_of 1 (length init))))"
            proof (rule upds_bounded)
              show "bounded (map_of nta_vars) v"
                using arc unfolding abs_renum.a\<^sub>0_def
                using init_vars_bounded by simp
              show "length (PlanningLock # ActsActive # map PropVar init) = length (1 # 0 # list_of 1 (length init))" 
                apply (subst length_Cons)+
                apply (subst length_list_of)
                by auto
              show "\<forall>n<length (PlanningLock # ActsActive # map PropVar init). \<exists>l u. map_of nta_vars ((PlanningLock # ActsActive # map PropVar init) ! n) = Some (l, u) \<and> l \<le> (1 # 0 # list_of 1 (length init)) ! n \<and> (1 # 0 # list_of 1 (length init)) ! n \<le> u"
              proof (intro allI impI)
                fix n
                assume a: "n < length (PlanningLock # ActsActive # map PropVar init)"
                show "\<exists>l u. map_of nta_vars ((PlanningLock # ActsActive # map PropVar init) ! n) = Some (l, u) \<and> l \<le> (1 # 0 # list_of 1 (length init)) ! n \<and> (1 # 0 # list_of 1 (length init)) ! n \<le> u"
                proof (cases n)
                  case 0
                  then show ?thesis
                  using map_of_nta_vars_PlanningLock by simp
                next
                  case n': (Suc n')
                  then show ?thesis 
                  proof (cases n')
                    case 0
                    then show ?thesis 
                    using map_of_nta_vars_ActsActive n' by simp
                  next
                    case n'': (Suc n'')
                    have "n'' < length init" using a n' n'' by simp
                    hence "\<exists>l u. map_of nta_vars (map PropVar init ! n'') = Some (l, u) \<and> l \<le> (list_of 1 (length init)) ! n'' \<and> (list_of 1 (length init)) ! n'' \<le> u" 
                      apply (subst nth_list_of, assumption)+
                      using map_of_nta_vars_init_goal by simp
                    then show "\<exists>l u. map_of nta_vars ((PlanningLock # ActsActive # map PropVar init) ! n) = Some (l, u) \<and> l \<le> (1 # 0 # list_of 1 (length init)) ! n \<and> (1 # 0 # list_of 1 (length init)) ! n \<le> u" 
                      unfolding n'' n' by simp
                  qed
                qed
              qed
            qed
            thus "bounded (map_of nta_vars) v1"
              unfolding v1' by simp
          qed
        qed
        show "Simple_Network_Language.bounded (map_of nta_vars) v"
          using arc unfolding abs_renum.a\<^sub>0_def
          using init_vars_bounded by simp
      qed
      thus ?thesis using arc[symmetric] sp by simp
    qed
    show "abs_renum.urge_bisim.A.steps [start_planning abs_renum.a\<^sub>0]" by (rule abs_renum.urge_bisim.A.steps.intros)
  qed
  thus ?thesis by simp
qed

lemma steps_extend: "abs_renum.urge_bisim.A.steps xs \<Longrightarrow> abs_renum.urge_bisim.A.steps (last xs # seq_apply fs (last xs)) \<Longrightarrow> abs_renum.urge_bisim.A.steps (ext_seq xs fs)"
  apply (frule abs_renum.urge_bisim.A.steps_append'[where bs = "last xs # seq_apply fs (last xs)"])
     apply simp
    apply simp
   apply (subst List.tl_def)
   apply simp
  apply (subst (asm) ext_seq_alt[symmetric])
   apply (erule abs_renum.urge_bisim.A.steps.cases)
  subgoal for x by blast
  subgoal for x xs by auto
  by simp

lemma length_seq_apply[simp]: "length (seq_apply fs s) = length fs"
  apply (induction fs arbitrary: s)
  by auto

lemma steps_extend_induct:
  assumes "\<forall>i < length xs. abs_renum.urge_bisim.A.steps [xs!i, xs!Suc i]"
      and "0 < length xs"
  shows "abs_renum.urge_bisim.A.steps xs"
proof -
  have "abs_renum.urge_bisim.A.steps (take n xs @ [xs ! n])" if "n < length xs" "0 < length xs" for n
    using that
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    have 1: "abs_renum.urge_bisim.A.steps (take n xs @ [xs ! n])" using Suc by simp
    have 2: "abs_renum.urge_bisim.A.steps ([xs ! n, xs ! Suc n])" using assms Suc by simp
    
    have "abs_renum.urge_bisim.A.steps (take n xs @ [xs ! n] @ [xs ! Suc n])" using abs_renum.urge_bisim.A.steps_append[OF 1 2] by force
    thus ?case 
        apply (subst take_Suc_conv_app_nth)
      using Suc by auto
  qed
  from this[of "length xs - 1", OF _ assms(2)]
  show ?thesis using take_Suc_conv_app_nth[of "length xs - 1" xs] take_all[of xs "length xs"] assms(2) by auto
qed

lemma seq_apply_steps_induct:
  assumes "\<forall>i < length (s#seq_apply fs s). abs_renum.urge_bisim.A.steps [(s#seq_apply fs s) ! i, (s#seq_apply fs s) ! Suc i]"
  shows "abs_renum.urge_bisim.A.steps (s # seq_apply fs s)" using assms steps_extend_induct by blast

schematic_goal nth_auto_trans:
  assumes "n < length actions"
  shows "trans (automaton_of (actual_autos ! Suc n)) = ?x"
  apply (subst actual_autos_alt)
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_Cons_Suc)
  apply (subst nth_map)
  apply (rule assms)
  unfolding action_to_automaton_spec_def Let_def comp_def snd_conv trans_def automaton_of_def prod.case fst_conv list.set ..
  

schematic_goal nth_auto_trans':
  assumes "n < length actions"
  shows "trans (automaton_of ((snd \<circ> snd) (action_to_automaton_spec (actions ! n)))) = ?x"
  unfolding action_to_automaton_spec_def Let_def comp_def snd_conv trans_def automaton_of_def prod.case fst_conv list.set ..

(* Indices of locations and automata are offset by 1 w.r.t. actions' indices *)

schematic_goal int_clocks_spec_alt:
  shows "set (int_clocks_spec h) = ?x"
  unfolding int_clocks_spec_def Let_def filter_append set_append set_map set_filter ..

lemma mutex_0_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> h = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> h = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap h b \<Longrightarrow> 0 < planning_sem.exec_time b t" for b by blast

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_start act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_start act) t" by simp
    moreover
    have "(t, at_start act) \<notin> planning_sem.happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (ActStart act)" using s_corr a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (ActStart act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map ActStart (filter (\<lambda>a. mutex_effects_spec h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_end act)"
    from mutex_time[OF a(2)]
    have "0 < planning_sem.exec_time (at_end act) t" by simp
    moreover
    have "(t, at_end act) \<notin> planning_sem.happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    ultimately
    have "0 < c (ActEnd act)" using e_corr a(1) by simp
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GT (ActEnd act) 0)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GT x 0)) (map ActEnd (filter (\<lambda>a. mutex_effects_spec h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  ultimately
  show ?thesis 
    unfolding int_clocks_spec_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed

lemma mutex_eps_constraint_sat:
  assumes h_at_t: "(t, h) \<in> planning_sem.happ_seq"
      and s_corr: "\<forall>a \<in> set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> h = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
      and e_corr: "\<forall>a \<in> set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> h = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
    shows "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec h))"
proof -
  from planning_sem.exec_time_and_separation[OF h_at_t]
  have mutex_time: "planning_sem.mutex_snap h b \<Longrightarrow> rat_of_int \<epsilon> \<le> planning_sem.exec_time b t" for b 
    unfolding Rat.of_int_def by simp

  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_start act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_start act) t" by simp
    have c: "(t, at_start act) \<notin> planning_sem.happ_seq \<or> h = at_start act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (ActStart act)"
      apply (subst s_corr[THEN bspec, OF a(1), THEN mp, OF c])
      using x of_rat_less_eq by blast
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (ActStart act) \<epsilon>)"
      apply simp
      by (erule clock_val_a.intros)
  } note 1 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map ActStart (filter (\<lambda>a. mutex_effects_spec h (at_start a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 1)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  moreover
  { fix act
    assume a: "act \<in> set actions" "planning_sem.mutex_snap h (at_end act)"
    from mutex_time[OF a(2)]
    have x: "rat_of_int \<epsilon> \<le> planning_sem.exec_time (at_end act) t" by simp
    have c: "(t, at_end act) \<notin> planning_sem.happ_seq \<or> h = at_end act" using a(2) h_at_t planning_sem.mutex_same_instant_is_same by blast
    have "real_of_rat (rat_of_int \<epsilon>) \<le> c (ActEnd act)"
      apply (subst e_corr[THEN bspec, OF a(1), THEN mp, OF c])
      using x of_rat_less_eq by blast
    hence "c \<turnstile>\<^sub>a conv_ac (acconstraint.GE (ActEnd act) \<epsilon>)"
      apply simp
      by (erule clock_val_a.intros)
  } note 2 = this
  have "c \<turnstile> map (conv_ac \<circ> (\<lambda>x. acconstraint.GE x \<epsilon>)) (map ActEnd (filter (\<lambda>a. mutex_effects_spec h (at_end a)) actions))" 
    unfolding clock_val_def list_all_iff map_map comp_def set_map
    apply (rule ballI)
    apply (subst (asm) set_filter)
    apply (erule imageE)
    subgoal for x act
      apply (erule ssubst[of x])
      apply (rule 2)
      apply simp
      unfolding planning_sem.mutex_snap_def comp_apply by simp
    done
  ultimately
  show ?thesis 
    unfolding int_clocks_spec_def clock_val_def Let_def
      comp_def map_map map_append list_all_append 
    by auto
qed 

context 
  fixes n t L v c L' v' c'
 assumes n: "n < length actions"
      and end_scheduled: "(t, at_end (actions ! n)) \<in> planning_sem.happ_seq"
      and start_not_scheduled: "(t, at_start (actions ! n)) \<notin> planning_sem.happ_seq"

      and locked_before: "\<forall>p. PropLock p \<in> dom (map_of nta_vars) \<longrightarrow> v (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))"

      and v_bounded: "bounded (map_of nta_vars) v"

      and planning_state: "v PlanningLock = Some 1"

      and ending_executed_clock: 
          "\<forall>i < n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
            \<longrightarrow> c (ActEnd (actions ! i)) = (0::real)"
      and ending_not_executed_clock: 
          "\<forall>i < length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq
            \<longrightarrow> c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
      and start_snap_time: "\<forall>i < length actions. c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"

      and ending_executed_loc: "\<forall>i < n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
              \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (EndInstant (actions ! i))"
      and ending_not_executed_loc: "\<forall>i < length actions. n \<le> i 
              \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
              \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L ! Suc i = (Running (actions ! i))"
      and L_len: "length L = Suc (length actions)"
      and s': "enter_end_instant n (L, v, c) = (L', v', c')"
begin

text \<open>Properties of current state\<close>
lemma partially_updated_locked_before_lower: 
  assumes "p \<in> set (over_all (actions ! n))"
  shows "0 < partially_updated_locked_before t p n" 
proof -
  have "0 < (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)"
  proof -
    { assume "0 = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)"
      hence "\<forall>n \<in> set (map 
        (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)) 
        (filter 
          (\<lambda>a. p \<in> set (over_all a)) 
          (map (\<lambda>n. actions ! n) [n..<length actions]))). n = 0"  apply (subst sum_list_eq_0_iff[symmetric])
        by metis
      moreover
      {
        have "(if (t, at_start (actions ! n)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! n)) \<in> planning_sem.happ_seq then (1::nat) else 0) = 1" using start_not_scheduled end_scheduled by simp
        moreover
        have "n \<in> set [n..<length actions]" using n by simp
        ultimately
        have "\<exists>n \<in> set (map 
          (\<lambda>a. (if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)) 
          (filter 
            (\<lambda>a. p \<in> set (over_all a)) 
            (map (\<lambda>n. actions ! n) [n..<length actions]))). n > 0" using assms n end_scheduled start_not_scheduled
          apply -
          apply (rule bexI)
          defer
           apply (subst set_map)
           apply (rule imageI[of "actions ! n"])
          using assms apply simp
          by simp
      }
      ultimately
      have False by fast
    }
    thus ?thesis 
      apply (cases "0 = (\<Sum>a\<leftarrow>filter (\<lambda>a. p \<in> set (over_all a)) (map ((!) actions) [n..<length actions]). if (t, at_start a) \<notin> planning_sem.happ_seq \<and> (t, at_end a) \<in> planning_sem.happ_seq then (1::nat) else 0)")
       apply blast
      by linarith
  qed
  thus ?thesis using partially_updated_locked_before_alt[OF n] by presburger
qed

text \<open>Definition and properties of next state\<close>

lemma L': "L' = L[Suc n := EndInstant (actions ! n)]" 
  and v': "v' = v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. x - 1) (map (the o v) (map PropLock (over_all (actions ! n)))))" 
  and c': "c' = c(ActEnd (actions ! n) := 0)"
  apply (cases "enter_end_instant n (L, v, c)") using s' unfolding enter_end_instant_def Let_def prod.case by blast+


lemma variables_locked_after:
  assumes p_has_lock: "PropLock p \<in> dom (map_of nta_vars)" 
    shows "v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p (Suc n)))"
proof (cases "p \<in> set (over_all (actions ! n))")
  case True
  have 1: "v' (PropLock p) = Some (the (v (PropLock p)) - 1)"
    unfolding v' 
    apply (subst map_map)
    apply (subst distinct_map_upds)
    using True n apply simp
    apply (rule distinct_inj_map)
    using over_all_distinct[THEN bspec[of _ _ "actions ! n"]] n apply simp
    unfolding inj_def apply simp
    unfolding comp_def by simp
  
  have 2: "partially_updated_locked_before t p (Suc n) = partially_updated_locked_before t p n - 1"
    unfolding partially_updated_locked_before_def 
    apply (subst sum_list.eq_foldr)
    apply (subst upt_Suc_append, simp)
    apply (subst map_append)
    apply (subst filter_append)
    apply (subst map_append)
    apply (subst foldr_append)
    apply (subst list.map)+
    apply (subst filter.simps)
    apply (subst (3) if_P)
     apply (rule True)
    apply (subst filter.simps)
    apply (subst list.map)+
    apply (subst foldr.simps)
    unfolding comp_def
    apply (subst foldr.simps)
    apply (subst (2) if_P)
    using start_not_scheduled end_scheduled
     apply simp
    apply (subst id_def)
    apply (subst sum_list.eq_foldr)
    apply (subst foldr_assoc)
    by linarith

  show ?thesis 
    apply (subst 1)
    apply (subst locked_before[THEN spec, THEN mp, OF assms])
    apply (subst 2)
    apply simp
    using partially_updated_locked_before_lower[OF True] 
    unfolding int_of_nat_def by simp
next
  case False
  have "partially_updated_locked_before t p (Suc n) = partially_updated_locked_before t p n" 
    unfolding partially_updated_locked_before_def using False by simp
  moreover
  have "v' (PropLock p) = v (PropLock p)"
    unfolding v' 
    apply (subst map_upds_apply_nontin)
    using n False by auto
  ultimately
  show ?thesis using locked_before assms by simp
qed

lemma variables_same_after:
  assumes "x \<notin> set (map PropLock (over_all (actions ! n)))"
  shows "v' x = v x"
  unfolding v' using assms map_upds_apply_nontin by simp

lemma ending_executed_clock':
  assumes "i \<le> n" 
    "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq" 
    "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq" 
    shows "c' (ActEnd (actions ! i)) = (0::real)"
  apply (cases "i = n")
  subgoal unfolding c' by simp
  using assms ending_executed_clock unfolding c' by auto

lemma ending_not_executed_clock': 
  assumes "n < i"
    "i < length actions"
    "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq" 
    "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq" 
  shows "c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
  unfolding c'
  apply (subst fun_upd_other)
  using assms(1,2) distinct_actions distinct_conv_nth apply fastforce
  using ending_not_executed_clock assms by simp

lemma clocks_same_after:
  assumes "x \<noteq> ActEnd (actions ! n)"
  shows "c' x = c x"
  unfolding c' using fun_upd_other assms by simp

lemma ending_executed_loc':
  assumes "i \<le> n" "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq" "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq"
    shows "L' ! Suc i = (EndInstant (actions ! i))"
  apply (cases "i = n")
  subgoal unfolding L' using n nth_list_update_eq L_len by auto
  unfolding L' using nth_list_update_neq assms ending_executed_loc L_len n by simp

lemma ending_not_executed_loc':
  assumes "i < length actions" 
    "n < i"
    "(t, at_start (actions ! i)) \<notin> planning_sem.happ_seq"
    "(t, at_end (actions ! i)) \<in> planning_sem.happ_seq"
  shows "L' ! Suc i = (Running (actions ! i))"
  unfolding L' using assms ending_not_executed_loc nth_list_update_neq by auto

lemma locs_same_after:
  assumes "i < length actions"
      and "i \<noteq> Suc n"
    shows "L' ! i = L ! i"
  using assms unfolding L' using nth_list_update_neq by simp

lemma enter_end_instant_okay:
    shows "abs_renum.urge_bisim.A.steps [(L, v, c), enter_end_instant n (L, v, c)]"
proof (rule single_step_intro)

  obtain l b g a f r l' where
    t: "(l, b, g, a, f, r, l') = (\<lambda>(l, b, g, a, f, r, l'). (l, b, map conv_ac g, a, f, r, l')) (edge_3_spec (actions ! n))" 
 and t': "l = Running (actions ! n)"
     "b = bexp.true"
     "g = map conv_ac (l_dur_spec (actions ! n) @ u_dur_spec (actions ! n) @ map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))) @ map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))"
     "a = Sil STR ''''"
     "f = map (inc_prop_lock_ab (-1)) (over_all (actions ! n))"
     "r = [ActEnd (actions ! n)]"
     "l' = EndInstant (actions ! n)"
    unfolding edge_3_spec_def Let_def prod.case by simp
    
  show "(case (L, v, c) of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). abs_renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (enter_end_instant n (L, v, c))"
    unfolding s' prod.case
  proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
    show "bounded (map_of nta_vars) v" using v_bounded .
    show "abs_renum.sem \<turnstile> \<langle>L, v, c\<rangle> \<rightarrow>\<^bsub>Internal STR ''''\<^esub> \<langle>L', v', c'\<rangle>"
      unfolding abs_renum.sem_def
    proof (rule step_int)
      show "TRANS ''silent'' \<bar> (l, b, g, Sil STR '''', f, r, l') \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! (Suc n))"
        apply (subst TAG_def)
        apply (subst t'(4)[symmetric])
        apply (subst conv_trans)
        using n actual_autos_alt apply simp
        apply (subst nth_auto_trans)
        using n t by fast+
      show "''committed'' \<bar> l \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! Suc n) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). L ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
        apply (subst TAG_def)
        apply (rule disjI2)
        apply (intro allI impI)
        subgoal for p
          apply (subst conv_committed)
           apply simp
          using no_committed
          by simp
        done
      show "''bexp'' \<bar> Simple_Expressions.check_bexp v b True"
        unfolding t'
        apply (subst TAG_def)
        by (rule check_bexp_is_val.intros)
      show "''guard'' \<bar> c \<turnstile> g"
      proof -
        (* The exec time satisfies the duration bounds *)
        (* There will be a similar, repetitive proof. Repetition is necessary, because the other case has 
            actions with a duration of 0 and therefore the duration bounds will be satisfied for other reasons. *)
        from planning_sem.exec_time_sat_dur_const[OF _ end_scheduled start_not_scheduled]
        have sat_dur_bounds: "satisfies_duration_bounds lower_sem upper_sem (actions ! n) (planning_sem.exec_time (at_start (actions ! n)) t)" using n by simp
        from this
        have "c \<turnstile> map conv_ac (l_dur_spec (actions ! n))"
          apply (subst clock_val_def)
          apply (subst l_dur_spec_def)
          apply (cases "lower (actions ! n)")
           apply simp
          subgoal for b
            apply (cases b)
            subgoal
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct1)
              unfolding lower_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n]) 
              by (metis Rat.of_int_def of_rat_less of_rat_of_int_eq)
            subgoal 
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct1)
              unfolding lower_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n])
              by (metis Rat.of_int_def of_rat_less_eq of_rat_of_int_eq)
            done
          done
        moreover
        from sat_dur_bounds
        have "c \<turnstile> map conv_ac (u_dur_spec (actions ! n))"
          apply (subst clock_val_def)
          apply (subst u_dur_spec_def)
          apply (cases "upper (actions ! n)")
           apply simp
          subgoal for b
            apply (cases b)
            subgoal
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct2)
              unfolding upper_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n]) 
              by (metis Rat.of_int_def of_rat_less of_rat_of_int_eq)
            subgoal 
              unfolding satisfies_duration_bounds_def
                Let_def apply (drule conjunct2)
              unfolding upper_sem_def apply simp
              apply (rule clock_val_a.intros)
              apply (subst start_snap_time[THEN spec, THEN mp, OF n])
              by (metis Rat.of_int_def of_rat_less_eq of_rat_of_int_eq)
            done
          done
        moreover
        have s_corr: "\<forall>a\<in>set actions. (t, at_start a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_start a \<longrightarrow> c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)"
        proof (intro ballI impI)
          fix a
          assume a: "a \<in> set actions" "(t, at_start a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_start a"
          then obtain i where
            "a = actions ! i"
            "i < length actions" 
            apply -
            apply (subst (asm) set_conv_nth)
            by auto
          thus "c (ActStart a) = real_of_rat (planning_sem.exec_time (at_start a) t)" using start_snap_time[THEN spec] by blast
        qed
        have e_corr: "\<forall>a\<in>set actions. (t, at_end a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_end a \<longrightarrow> c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)"
        proof (intro ballI impI)
          fix a
          assume a: "a \<in> set actions" "(t, at_end a) \<notin> planning_sem.happ_seq \<or> at_end (actions ! n) = at_end a"
          then obtain i where
            i: "a = actions ! i"
            "i < length actions"
            apply -
            apply (subst (asm) set_conv_nth)
            apply (erule CollectE)
            by blast
          show "c (ActEnd a) = real_of_rat (planning_sem.exec_time (at_end a) t)" 
            unfolding i(1)
          proof (rule ending_not_executed_clock[THEN spec, THEN mp, OF i(2), THEN mp]) 
            from a(2)
            consider "(t, at_end a) \<notin> planning_sem.happ_seq" | "at_end (actions ! n) = at_end a" by auto
            thus "n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq"
            proof cases
              case 1
              then show ?thesis using i(1) by auto
            next
              assume "at_end (actions ! n) = at_end a" 
              hence "at_end (actions ! n) = at_end (actions ! i)" using i by blast
              moreover
              from i(2) n
              have "actions ! n \<in> set actions" "actions ! i \<in> set actions" by simp+
              ultimately
              have "actions ! n = actions ! i" using at_end_inj unfolding inj_on_def by blast
              with i n
              have "n = i" using distinct_actions using distinct_conv_nth by auto
              then show ?thesis by simp
            qed
          qed
        qed
        have "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec (at_end (actions ! n))))"
          using mutex_0_constraint_sat end_scheduled s_corr e_corr by blast
        moreover
        have "c \<turnstile> map conv_ac (map (\<lambda>x. acconstraint.GE x \<epsilon>) (int_clocks_spec (at_end (actions ! n))))"
          using  mutex_eps_constraint_sat end_scheduled s_corr e_corr by blast
        ultimately
        show ?thesis unfolding t' TAG_def
          unfolding map_append
          by (auto intro: guard_append)
      qed
      show "''target invariant'' \<bar> \<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). c' \<turnstile> Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) (L' ! p)"
        unfolding TAG_def 
        apply (intro allI impI)
        apply (subst no_invs)
        by simp+
      show "''loc'' \<bar> L ! Suc n = l" unfolding TAG_def t' using ending_not_executed_loc[THEN spec, THEN mp, OF n] using start_not_scheduled end_scheduled by blast
      show "''range'' \<bar> Suc n < length L" unfolding TAG_def using n L_len by simp
      show "''new loc'' \<bar> L' = L[Suc n := l']" unfolding TAG_def t' using L' by simp
      show "''new valuation'' \<bar> c' = [r\<rightarrow>0]c" unfolding TAG_def t' using c' by simp

      have locks_in_dom: "set (map PropLock (over_all (actions ! n))) \<subseteq> dom (map_of nta_vars)" 
          unfolding dom_map_of_nta_vars set_map action_vars_spec_def Let_def inv_vars_spec_def
          apply -
          apply (rule subsetI)
          apply (rule UnI2)
          apply (rule UnI1)+ 
          using n
          by auto

      show "''is_upd'' \<bar> is_upds v f v'" 
      proof (subst TAG_def)
        have v': "v' = v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. x - 1) (map (the o v) (map PropLock (over_all (actions ! n)))))" using v' by simp
        have x: "map (\<lambda>prop. (PropLock prop, binop plus_int (var (PropLock prop)) (exp.const (- 1)))) xs = map (inc_var (-1)) (map PropLock xs)" for xs unfolding comp_apply map_map by simp
        show "is_upds v f v'" unfolding v' t'
          unfolding inc_prop_lock_ab_def x
        proof (rule is_upds_inc_vars)
          show "set (map PropLock (over_all (actions ! n))) \<subseteq> dom v"
            using locks_in_dom v_bounded bounded_def by metis
          show "distinct (map PropLock (over_all (actions ! n)))" using n over_all_distinct
            unfolding distinct_map
            unfolding inj_on_def by simp
        qed
      qed
      show "''bounded'' \<bar> Simple_Network_Language.bounded (map_of nta_vars) v'" unfolding TAG_def
      proof -
        have v': "v' = v(map PropLock (over_all (actions ! n)) [\<mapsto>] map (\<lambda>x. x - 1) (map (the \<circ> v) (map PropLock (over_all (actions ! n)))))" using L' v' c' by simp
        have invs_in_props: "set (over_all a) \<subseteq> set props" if "a \<in> set actions" for a using that planning_sem.finite_props_domain unfolding fluent_domain_def act_ref_fluents_def by simp

        show "Simple_Network_Language.bounded (map_of nta_vars) v'"
        proof (rule updated_bounded[OF v_bounded _ v'])
          show "length (map PropLock (over_all (actions ! n))) = length (map (\<lambda>x. x - 1) (map (the \<circ> v) (map PropLock (over_all (actions ! n)))))" by simp
          show "\<forall>x\<in>set (map PropLock (over_all (actions ! n))). \<exists>l u. map_of nta_vars x = Some (l, u) \<and> l \<le> the (v' x) \<and> the (v' x) \<le> u"
            apply (rule ballI)
            subgoal for x
              unfolding set_map
              apply (erule imageE)
              subgoal for p
                apply (intro exI conjI)
                  apply (subst map_of_nta_vars_action_inv[of "actions ! n"])
                using n
                    apply simp
                   apply simp
                  apply simp
                 apply (erule ssubst[of x])
                 apply (subst variables_locked_after)
                using locks_in_dom apply auto[1]
                 apply (subst option.the_def)
                apply (subst int_of_nat_def)
                 apply simp
                 apply (erule ssubst[of x])
                 apply (subst variables_locked_after)
                using locks_in_dom apply auto[1]
                 apply (subst option.the_def)
                apply (subst int_of_nat_def)
                using partially_updated_locked_before_ran by simp
              done
            done
          qed
      qed
    qed
  qed
qed
end 
thm ending_not_executed_loc'
(* Context to apply every snap action placed at a timepoint *)
context
  fixes M t
    end_indices
    L v c
  assumes l: "l < length (htpl \<pi>)"
      and p_locked_before: "\<forall>p. PropLock p \<in> set (map fst nta_vars) \<longrightarrow>  v (PropLock p) = Some (planning_sem.locked_before t p)"
      and v_bounded: "bounded (map_of nta_vars) v"
      and planning_state: "v PlanningLock = Some 1"
      and ending_clock: "\<forall>i < length actions. c (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
      and starting_clock: "\<forall>i < length actions. c (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      and ending_loc: "\<forall>i < length actions. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L' ! Suc i = (Running (actions ! i))"
  defines "M \<equiv> planning_sem.plan_state_seq"
      and "t \<equiv> time_index \<pi> l"
      and "end_indices \<equiv> filter (\<lambda>n. (t, at_end (actions ! n)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! n)) \<notin> planning_sem.happ_seq) [0..<length actions]"
begin 

lemma enter_end_instants_take_n_pre:
  fixes L' v' c' i
  assumes "l < length (htpl \<pi>)"
      and "i \<le> length end_indices"
      and "n = end_indices ! i"
      and "(s#enter_end_instants end_indices s) ! i = (L', v', c')"
    shows "\<forall>p. PropLock p \<in> dom (map_of nta_vars) 
            \<longrightarrow> v' (PropLock p) = Some (int_of_nat (partially_updated_locked_before t p n))"
      "bounded (map_of nta_vars) v'"
     "v' PlanningLock = Some 1"
      "\<forall>i < n. (t, at_end (actions ! i)) \<in> planning_sem.happ_seq \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
            \<longrightarrow> c' (ActEnd (actions ! i)) = (0::real)"
      "\<forall>i < length actions. n \<le> i \<or> (t, at_start (actions ! i)) \<in> planning_sem.happ_seq \<or> (t, at_end (actions ! i)) \<notin> planning_sem.happ_seq
            \<longrightarrow> c' (ActEnd (actions ! i)) = real_of_rat (planning_sem.exec_time (at_end (actions ! i)) t)"
      "\<forall>i < length actions. c' (ActStart (actions ! i)) = real_of_rat (planning_sem.exec_time (at_start (actions ! i)) t)"
      "\<forall>i < n. (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
              \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L' ! Suc i = (EndInstant (actions ! i))"
     "\<forall>i < length actions. n \<le> i 
              \<and> (t, at_start (actions ! i)) \<notin> planning_sem.happ_seq 
              \<and> (t, at_end (actions ! i)) \<in> planning_sem.happ_seq
          \<longrightarrow> L' ! Suc i = (Running (actions ! i))"
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  done
(* proof -
  show ?thesis sorry
qed
 *)
lemma enter_end_instants_okay:
  assumes "l < length (htpl \<pi>)"
      and "M = planning_sem.plan_state_seq"
      and "s = (L, v, c)"
      and "\<forall>p. PropVar p \<in> set (map fst nta_vars) \<and> p \<in> M l \<longrightarrow> v (PropVar p) = Some 1"
      and "\<forall>p. PropVar p \<in> set (map fst nta_vars) \<and> p \<notin> M l \<longrightarrow> v (PropVar p) = Some 0"
      and "\<forall>p. PropLock p \<in> set (map fst nta_vars) \<longrightarrow>  v (PropLock p) = Some (planning_sem.locked_before t p)"
    shows "abs_renum.urge_bisim.A.steps (s # enter_end_instants end_indices s)"
proof -
  show ?thesis unfolding enter_end_instants_def
  proof (intro seq_apply_steps_induct allI impI)
    fix i
    assume "i < length (s # seq_apply (map enter_end_instant end_indices) s)"
    
    show "abs_renum.urge_bisim.A.steps [(s # seq_apply (map enter_end_instant end_indices) s) ! i, (s # seq_apply (map enter_end_instant end_indices) s) ! Suc i]"
    proof (rule single_step_intro)
      show ?thesis sorry
    qed
  qed
qed

end


lemma apply_happening:
  assumes "n < length (htpl \<pi>)"
      and "P s"
    shows "abs_renum.urge_bisim.A.steps (s # apply_nth_happening n s)"
  sorry

lemma apply_happenings:
  assumes "n < length (htpl \<pi>)"
      and "P s"
    shows "abs_renum.urge_bisim.A.steps (s # delay_and_apply n s)"
  sorry


thm plan_steps_def[simplified Let_def ext_seq''_alt]

lemma plan_steps_are_steps: "abs_renum.urge_bisim.A.steps plan_steps"
  unfolding plan_steps_def Let_def
  sorry


lemma end_of_steps_is_run: "abs_renum.urge_bisim.A.run (goal_run (last plan_steps))" sorry

lemma "abs_renum.urge_bisim.A.run (goal_run goal_state)" sorry


lemma "abs_renum.urge_bisim.A.steps (undefined # undefined # undefined)"
  find_theorems intro name: "steps"
  apply (rule abs_renum.urge_bisim.A.stepsI)
  using abs_renum.urge_bisim.A.steps.intros
  sorry

lemma state_seq_sat_goal: "ev (holds (\<lambda>(L, s, _). check_sexp (sexp.loc 0 GoalLocation) L (the \<circ> s))) plan_state_sequence"
  find_theorems intro name: "ev" sorry

find_theorems name: "abs_renum*steps"

lemma state_seq_is_run: "abs_renum.urge_bisim.A.run plan_state_sequence"
  find_theorems name: "run*con"
  apply (rule abs_renum.urge_bisim.A.extend_run'[where zs = plan_state_sequence])
  unfolding plan_state_sequence_def
  sorry

find_theorems name: "Simple_Network_Language_Model_Checking.step_u'.intros"

lemma "abs_renum.sem, abs_renum.a\<^sub>0 \<Turnstile> form"
proof -
  show "?thesis" unfolding form_alt 
    unfolding models_def 
    unfolding formula.case
    find_theorems name: "abs_renumEx_ev"
    apply (subst abs_renum.urge_bisim.A.Ex_ev_def)
    find_theorems (200) name: "abs_renum*run"
    find_theorems name: deadlock
    apply (rule exI)
    apply (rule conjI)
     apply (coinduction rule: abs_renum.urge_bisim.A.run.coinduct) sorry
  qed

(* Functions from actions to locations and clocks, and from propositions to variables must be fixed
  later. Renamings like in Munta. *)

(* Lists are used to implement sets. Lift this to a higher level. *)

(* Do the conversion to strings later, as renamings *)
(* Right now, do the conversion using the actual types as placeholders.
Propositions and actions are not renamed in variables  *)

end
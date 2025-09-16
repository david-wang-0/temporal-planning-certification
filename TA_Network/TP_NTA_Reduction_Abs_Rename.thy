theory TP_NTA_Reduction_Abs_Rename
  imports TP_NTA_Reduction_Spec
begin

section \<open>Renumbering the abstract definition\<close>

subsubsection \<open>Some functions for renumbering\<close>


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


lemma some_actual_autos: "0 < length actual_autos"
  unfolding actual_autos_def ntas_def timed_automaton_net_spec_def by simp

lemma actual_autos_alt: "actual_autos = map (snd o snd) (main_auto_spec # map action_to_automaton_spec actions)"
  unfolding actual_autos_def ntas_def Let_def timed_automaton_net_spec_def prod.case
  apply -
  apply (subst map_map[symmetric])
  apply (subst map_snd_zip)
   apply simp
  by simp

lemma length_actual_autos: "length actual_autos = Suc (length actions)" using actual_autos_alt by simp

lemma actual_autos_alt_set: "set actual_autos = (\<lambda>a. snd (snd a)) ` set (main_auto_spec # map action_to_automaton_spec actions)"
  unfolding actual_autos_def ntas_def Let_def timed_automaton_net_spec_def prod.case comp_apply set_map 
    apply -
    apply (subst image_image[symmetric, of _ snd])
    apply (subst zip_range_id, simp)
  by simp

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
        have "trans \<in> set [start_edge_spec act, edge_2_spec act, edge_3_spec act, 
              end_edge_spec act, instant_trans_edge_spec act, leave_start_edge_spec act]" 
          using t[simplified at' act(2)] unfolding comp_apply action_to_automaton_spec_def Let_def prod.case snd_conv fst_conv .
        with x consider
          "x \<in> set (trans_resets (start_edge_spec act))"|
          "x \<in> set (trans_resets (edge_2_spec act))"|
          "x \<in> set (trans_resets (edge_3_spec act))"|
          "x \<in> set (trans_resets (end_edge_spec act))"|
          "x \<in> set (trans_resets (instant_trans_edge_spec act))"|
          "x \<in> set (trans_resets (leave_start_edge_spec act))" unfolding comp_apply by fastforce
        thus ?thesis 
          apply cases
          subgoal unfolding start_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
          subgoal unfolding edge_2_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          subgoal unfolding edge_3_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp
          subgoal unfolding end_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv by simp
          unfolding instant_trans_edge_spec_def leave_start_edge_spec_def comp_apply Let_def prod.case snd_conv fst_conv using act(1) by simp+
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
        have "trans \<in> set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act, leave_start_edge_spec act]" 
          using t[simplified at' act(2)] unfolding comp_apply action_to_automaton_spec_def Let_def prod.case snd_conv fst_conv .
        with x g consider
          "x \<in> fst ` constraint_pair ` set (trans_guards (start_edge_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (edge_2_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (edge_3_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (end_edge_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (instant_trans_edge_spec act))"|
          "x \<in> fst ` constraint_pair ` set (trans_guards (leave_start_edge_spec act))" unfolding comp_apply by fastforce
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
          unfolding instant_trans_edge_spec_def leave_start_edge_spec_def Let_def prod.case comp_apply fst_conv snd_conv int_clocks_spec_def set_map u_dur_spec_def l_dur_spec_def set_append 
            using act(1) 
            apply (cases "lower act"; cases "upper act")
            subgoal by fastforce
            subgoal for a by (cases a) fastforce+
            subgoal for a by (cases a) fastforce+
            subgoal for a b by (cases a; cases b) fastforce+
            subgoal by simp
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

subsection \<open>General properties of the problem\<close>
lemma action_variables: 
  assumes "a \<in> set actions"
  shows "action_vars_spec a \<subseteq> PropLock ` (set props) \<union> PropVar ` (set props)"
  unfolding action_vars_spec_def Let_def inv_vars_spec_def set_map set_append snap_vars_spec_def 
  using acts_ref_props unfolding rat_impl.set_impl.act_ref_props_def
  unfolding rat_impl.set_impl.snap_ref_props_def comp_def
  unfolding action_and_prop_set.snap_ref_props_def using assms
  apply -
  apply (drule bspec, assumption)
  by auto

lemma init_variables:
  "PropVar ` (set init) \<union> PropVar ` (set goal) \<subseteq> PropVar ` (set props)"
  using init_in_props goal_in_props by auto

lemma all_vars_spec_exact: "all_vars_spec = [(ActsActive, 0, int (length actions)), (Effecting, 0, int (length actions)), (PlanningLock, 0, 2)] @ map (\<lambda>p. (PropLock p, 0, int (length actions))) (filter (\<lambda>x. PropLock x \<in> \<Union> (set (map action_vars_spec actions))) props) @
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
  
  show ?thesis
    unfolding all_vars_spec_def Let_def fold_union' apply (subst 1)
    apply (subst 2)
    by simp
qed


lemma all_vars_spec_exact_set: "set (map fst all_vars_spec) = {ActsActive, Effecting, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)"
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

lemma nta_vars': "nta_vars = all_vars_spec" 
  unfolding nta_vars_def timed_automaton_net_spec_def Let_def prod.case ..

schematic_goal nta_vars_exact: "nta_vars = ?x"
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact)
  ..

schematic_goal map_of_nta_vars_exact: "map_of nta_vars = ?x"
  apply (subst nta_vars_exact)
  unfolding map_of_map comp_def map_of_append set_map
  ..

schematic_goal dom_map_of_nta_vars: "dom (map_of nta_vars) = ?d"
  apply (subst dom_map_of_conv_image_fst)
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact_set[simplified set_map])
  ..

schematic_goal fst_nta_vars: "set (map fst nta_vars) = ?x"
  apply (subst nta_vars')
  apply (subst all_vars_spec_exact_set)
  ..

schematic_goal action_vars_spec_exact: "action_vars_spec = ?x"
  unfolding action_vars_spec_def Let_def inv_vars_spec_def snap_vars_spec_def set_map map_append set_append set_filter image_Collect
  ..


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
  "vars_of_update (inc_var n v) = {v}"
  unfolding vars_of_update_def set_prop_ab_def inc_prop_ab_def set_prop_lock_ab_def inc_prop_lock_ab_def Let_def prod.case by simp+

lemma condition_vars_simps: 
  "vars_of_bexp (is_prop_ab n p) = {PropVar p}"
  "vars_of_bexp (is_prop_lock_ab n p) = {PropLock p}"
  "vars_of_bexp (var_is n v) = {v}"
  unfolding is_prop_ab_def is_prop_lock_ab_def by simp+

lemma vars_of_bexp_all:
  "vars_of_bexp (bexp_and_all bs) = (\<Union>b \<in> set bs. vars_of_bexp b)"
  by (induction bs; simp)

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
    have "tr \<in> {start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act, leave_start_edge_spec act}" 
      unfolding action_to_automaton_spec_def Let_def comp_apply snd_conv by auto
    with x consider
      "x \<in> trans_vars (start_edge_spec act)" |
      "x \<in> trans_vars (edge_2_spec act)" |
      "x \<in> trans_vars (edge_3_spec act)" |
      "x \<in> trans_vars (end_edge_spec act)" |
      "x \<in> trans_vars (instant_trans_edge_spec act)" |
      "x \<in> trans_vars (leave_start_edge_spec act)"by auto
    note act_cases = this
    then show ?thesis 
    proof cases
      case 1
      hence "x \<in> \<Union> (vars_of_bexp ` set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_start act))) (dels (at_start act))) @ map (is_prop_ab 1) (pre (at_start act)))) \<union>
       \<Union> (vars_of_update ` set ((inc_var 1 ActsActive) # (inc_var 1 Effecting) # map (set_prop_ab 0) (dels (at_start act)) @ map (set_prop_ab 1) (adds (at_start act))))" 
        unfolding trans_vars_def start_edge_spec_def Let_def prod.case fold_union' vars_of_bexp_all set_map by blast
      hence x: "x \<in> {ActsActive, Effecting} \<union> PropLock ` (set (dels (at_start act)) - set (adds (at_start act))) \<or> x \<in> PropVar ` (set (pre (at_start act)) \<union> set (dels (at_start act)) \<union> set (adds (at_start act)))"
        apply (subst (asm) list.set)
        apply (subst (asm) list.set)
        apply (subst (asm) Union_image_insert)
        apply (subst (asm) Union_image_insert)
        apply (subst (asm) update_vars_simps)+
         using update_vars_simps condition_vars_simps by auto
      have s: "set (pre (at_start act)) \<union> set (dels (at_start act)) \<union> set (adds (at_start act)) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply act_ref_fluents_def using act(1) by simp
      have x': "x \<in> {ActsActive, Effecting} \<union> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x \<in> {ActsActive, Effecting} \<union>  fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst snap_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 2
      hence "x \<in> {Effecting} \<union> \<Union> (vars_of_bexp ` is_prop_ab 1 ` set (over_all act)) \<union> \<Union> (vars_of_update ` inc_prop_lock_ab 1 ` set (over_all act))" 
        unfolding edge_2_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map 
        apply -
        apply (subst (asm) list.set)
        apply (subst (asm) Union_image_insert)
        apply (subst (asm) update_vars_simps)
        by auto
      hence x: "x = Effecting \<or> x \<in> PropLock ` set (over_all act) \<or> x \<in> PropVar ` set (over_all act)" using update_vars_simps condition_vars_simps by auto
      have s: "set (over_all act) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply using act(1) unfolding act_ref_fluents_def by auto
      have x': "x = Effecting \<or> x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x = Effecting \<or> x  \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" 
        unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst inv_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 3
      hence "x \<in> vars_of_bexp bexp.true \<union> \<Union> (vars_of_update ` set ((inc_var 1 Effecting) # map (inc_prop_lock_ab (- 1)) (over_all act)))" 
        unfolding edge_3_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map by simp
      hence x: "x = Effecting \<or> x \<in> PropLock ` set (over_all act)"
        apply (subst (asm) list.set)
        apply (subst (asm) Union_image_insert)
        apply (subst (asm) update_vars_simps)
        using update_vars_simps condition_vars_simps by auto
      have s: "set (over_all act) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply using act(1) unfolding act_ref_fluents_def by auto
      have x': "x = Effecting \<or> x \<in> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x = Effecting \<or> x \<in> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" 
        unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst inv_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 4
      hence "x \<in> \<Union> (vars_of_bexp ` set (map (is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (adds (at_end act))) (dels (at_end act))) @ map (is_prop_ab 1) (pre (at_end act)))) \<union>
       \<Union> (vars_of_update ` set ((inc_var (-1) ActsActive) # (inc_var (-1) Effecting) # map (set_prop_ab 0) (dels (at_end act)) @ map (set_prop_ab 1) (adds (at_end act))))" 
        unfolding trans_vars_def end_edge_spec_def Let_def prod.case fold_union' vars_of_bexp_all set_map by blast
      hence x: "x = ActsActive \<or> x = Effecting \<or> x \<in> PropLock ` (set (dels (at_end act)) - set (adds (at_end act))) \<or> x \<in> PropVar ` (set (pre (at_end act)) \<union> set (dels (at_end act)) \<union> set (adds (at_end act)))"
        apply (subst (asm) list.set)
        apply (subst (asm) Union_image_insert)
        apply (subst (asm) update_vars_simps)
        apply (subst (asm) list.set)
        apply (subst (asm) Union_image_insert)
        apply (subst (asm) update_vars_simps)
        using update_vars_simps condition_vars_simps by auto
      have s: "set (pre (at_end act)) \<union> set (dels (at_end act)) \<union> set (adds (at_end act)) \<subseteq> set props" using domain_ref_fluents unfolding fluent_domain_def comp_apply act_ref_fluents_def using act(1) by simp
      have x': "x \<in> {ActsActive, Effecting} \<union> fst ` set (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props)" using x s 
        unfolding set_map set_append by blast
      have x'': "x  \<in> {ActsActive, Effecting} \<union> fold (\<union>) (map action_vars_spec actions) {} \<union> set (map PropVar init) \<union> set (map PropVar goal)" unfolding action_vars_spec_def using act(1) unfolding fold_union' Let_def using x 
        apply -
        apply (subst (2) snap_vars_spec_def)
        unfolding Let_def map_append set_map 
        by auto
      show ?thesis unfolding nta_vars' all_vars_spec_def Let_def prod.case Let_def set_map using x' x'' by auto
    next
      case 5
      then show ?thesis unfolding instant_trans_edge_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map by simp 
    next
      case 6
      hence "x \<in> vars_of_exp (var Effecting)  \<union> \<Union> (vars_of_bexp ` is_prop_ab 1 ` set (over_all act))"
        unfolding leave_start_edge_spec_def trans_vars_def Let_def prod.case fold_union' vars_of_bexp_all set_map vars_of_bexp.simps by simp
      hence x: "x = Effecting \<or> x \<in> PropVar ` set (over_all act)"
        using update_vars_simps condition_vars_simps by auto
      thus ?thesis unfolding fst_nta_vars action_vars_spec_exact using \<open>act \<in> set actions\<close> by fast
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
      \<or> x = Effecting
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
    | "x = Effecting"
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
    case 3
    obtain act where act: "act \<in> set actions" using some_actions by blast
    have "x \<in> trans_vars (edge_2_spec act)" unfolding trans_vars_def edge_2_spec_def Let_def prod.case fold_union' set_map vars_of_update_def using 3 by simp
    hence "x \<in> (trans_to_vars o (\<lambda>x. fst (snd (snd x))) o (\<lambda>x. snd (snd x))) (action_to_automaton_spec act)" unfolding action_to_automaton_spec_def Let_def trans_to_vars_def fold_union' by auto
    thus ?thesis unfolding actual_variables_def ta_trans_def Let_def actual_autos_alt fold_union' set_map using act by auto
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
      hence x: "x \<in> \<Union> (trans_vars ` set [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act, leave_start_edge_spec act])" 
      proof cases
        case 1
        then consider "x \<in> PropLock ` set (over_all act)" |
          "x \<in> PropVar ` set (over_all act)" unfolding inv_vars_spec_def Let_def set_append set_map  trans_vars_def prod.case vars_of_bexp_all fold_union by auto
        then show ?thesis
        proof (cases)
          case 1
          hence "x \<in> trans_vars (edge_2_spec act)" 
            unfolding edge_2_spec_def Let_def set_append set_map  trans_vars_def prod.case vars_of_bexp_all fold_union 
            using update_vars_simps by auto
          then show ?thesis by simp
        next
          case 2
          hence "x \<in> trans_vars (leave_start_edge_spec act)" 
            unfolding leave_start_edge_spec_def Let_def set_append set_map  trans_vars_def prod.case vars_of_bexp_all fold_union 
            apply (subst vars_of_bexp.simps)
            apply (rule UnI1)
            apply (rule UnI2)
            apply (subst vars_of_bexp_all)
            using is_prop_ab_def by auto
          then show ?thesis by simp
        qed
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

schematic_goal actual_variables_exact: "actual_variables = ?x"
  unfolding actual_variables_correct
  unfolding nta_vars_exact
  unfolding map_map comp_apply prod.case map_append list.map
  unfolding fst_conv
  unfolding set_append list.set set_map set_filter 
  unfolding image_Collect
  unfolding Union_Un_distrib
  ..

schematic_goal in_actual_variablesI:
  "?c \<Longrightarrow> x \<in> actual_variables"
  unfolding actual_variables_exact
  by assumption

subsection \<open>Locations\<close>       
subsubsection \<open>Locations for simplicity\<close>
(* Explicitly returned (by functions) states *)
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

schematic_goal all_ta_urg_conv_prod: "all_ta_urg = ?x"
   unfolding all_ta_urg_def Let_def   ta_urg_def timed_automaton_net_spec_def 
    ntas_def prod.case
  apply (subst map_map[symmetric, of _ snd])
  apply (subst map_snd_zip)
    apply simp
   ..

schematic_goal set_all_ta_urg_conv_prod: "set all_ta_urg = ?x"
  unfolding all_ta_urg_conv_prod
  unfolding set_fold_append' fold_union set_map list.set
  ..


schematic_goal all_ta_urg_alt: "all_ta_urg = ?x"
  unfolding all_ta_urg_conv_prod main_auto_spec_def main_auto_spec_def Let_def comp_def fst_conv snd_conv action_to_automaton_spec_def list.map map_map ..

schematic_goal set_all_ta_urg_alt: "set all_ta_urg = ?x"
  unfolding all_ta_urg_alt set_fold_append' fold_union'
  ..

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
          "trs = [start_edge_spec act, edge_2_spec act, edge_3_spec act, end_edge_spec act, instant_trans_edge_spec act, leave_start_edge_spec act]" unfolding action_to_automaton_spec_def Let_def fst_conv snd_conv prod.case Let_def by simp
        have x: "x \<in> {Off act, StartInstant act, Running act, EndInstant act, PostStart act}" using ls x act unfolding action_to_automaton_spec_def Let_def by simp
        then consider "x = Off act" | "x = StartInstant act" | "x = Running act" | "x = EndInstant act" | "x = PostStart act" by blast
        hence "x \<in> trans_to_locs trs"
          apply cases
          unfolding trs(2) unfolding trans_to_locs_def Let_def set_map fold_union' trans_locs_def
          subgoal unfolding start_edge_spec_def Let_def list.set by simp
          subgoal unfolding start_edge_spec_def Let_def list.set by simp
          subgoal unfolding edge_3_spec_def Let_def list.set by simp
          subgoal unfolding edge_3_spec_def Let_def list.set by simp
          subgoal unfolding leave_start_edge_spec_def by simp
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
      have act_locs: "set (fst (snd (action_to_automaton_spec act))) =  {Off act, StartInstant act, Running act, EndInstant act, PostStart act}" for act
        unfolding action_to_automaton_spec_def fst_conv snd_conv Let_def prod.case by auto
      fix x
      assume "x \<in> \<Union> (trans_to_locs ` (\<lambda>x. fst (snd (snd (snd (snd x))))) ` set (main_auto_spec # map action_to_automaton_spec actions))"
      hence "x \<in> trans_locs main_auto_init_edge_spec
          \<or> x \<in> trans_locs main_auto_goal_edge_spec
          \<or> x \<in> trans_locs main_auto_loop_spec
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (start_edge_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (edge_2_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (edge_3_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (end_edge_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (instant_trans_edge_spec act))
          \<or> (\<exists>act \<in> set actions. x \<in> trans_locs (leave_start_edge_spec act))" 
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
        act where "act \<in> set actions" "x \<in> trans_locs (instant_trans_edge_spec act)" |
        act where "act \<in> set actions" "x \<in> trans_locs (leave_start_edge_spec act)" by auto
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
      next
        case 9
        then show ?thesis unfolding trans_locs_def leave_start_edge_spec_def Let_def prod.case using act_locs by auto
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
            unfolding main_auto_init_edge_spec_def main_auto_goal_edge_spec_def main_auto_loop_spec_def Let_def start_edge_spec_def end_edge_spec_def edge_2_spec_def edge_3_spec_def instant_trans_edge_spec_def leave_start_edge_spec_def
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

lemma n_ps_conv_Suc_length_actions: "Prod_TA_Defs.n_ps (set broadcast, map automaton_of actual_autos, map_of nta_vars) = Suc (length actions)"
  unfolding Prod_TA_Defs.n_ps_def fst_conv snd_conv actual_autos_alt by simp

schematic_goal sem_alt_def: "Simple_Network_Impl.sem actual_autos broadcast nta_vars = ?y"
  apply (subst Simple_Network_Impl.sem_def)
  apply (subst actual_autos_alt)
  apply (subst map_map)
  apply (subst comp_assoc[symmetric])
  ..

typ "(String.literal, 'action location,'action clock, int, 'proposition variable, int) transition"

sublocale abs_renum: Simple_Network_Rename_Formula
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
    unfolding loc_set_alt[symmetric] unfolding actual_autos_def 
    unfolding set_map image_image comp_def
    using all_urg_correct 
    unfolding all_ta_urg_def Let_def ta_urg_def set_fold_append' fold_union' set_map image_image comp_apply by simp
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
end

end
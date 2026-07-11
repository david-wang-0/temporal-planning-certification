theory Ground_PDDL_NTA_Reduction_Impl
  imports Ground_PDDL_NTA_Reduction_Correctness
    "Temporal_Planning.Temporal_PDDL_Checker_Explicit"
begin


lemmas return_iff = return_iff check_all_list_return_iff check_wf_problem_return_iff


lemma context_bind_return_iff[return_iff]:
  "(m \<bind> f = Inr y) = (\<exists>x. m = Inr x \<and> (m = Inr x \<longrightarrow> f x = Inr y))"
  apply (subst return_iff)
  by auto

lemma context_bind_return_iff'[return_iff]:
  "(m \<bind> f = Inr y) = (\<exists>x P. m = Inr x \<and> (m = Inr x \<longleftrightarrow> P) \<and> (P \<longrightarrow> f x = Inr y))"
  apply (subst context_bind_return_iff)
  by simp

lemma mapM_return_iff[return_iff]: "mapM f xs = Inr ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = Inr y) xs ys"
proof (rule iffI)
  assume a: "mapM f xs = Inr ys"
  have len: "length xs = length ys" using a mapM_return by fastforce
  show "list_all2 (\<lambda>x y. f x = Inr y) xs ys"
  proof (rule list_all2_all_nthI[OF len])
    fix n
    assume n: "n < length xs" 
    have ys: "ys = map (projr \<circ> f) xs" 
      and xs_r: "(\<forall>x\<in>set xs. \<forall>e. f x \<noteq> Inl e)" using a[THEN mapM_return] by blast+
    obtain r where
        xs_n_inr: "f (xs ! n) = Inr r" using xs_r n apply (cases "f (xs ! n)") by auto
    have "ys ! n = r" using xs_n_inr ys unfolding comp_def using n by simp
    thus "f (xs ! n) = Inr (ys ! n)" using xs_n_inr by simp
  qed
next
  assume a: "list_all2 (\<lambda>x y. f x = Inr y) xs ys"
  thus "mapM f xs = Inr ys"
    by (induction rule: list_all2_induct) auto
qed


lemma list_all2_return_if:
  assumes "list_all P xs"
      and "\<And>x y. P x \<Longrightarrow> fM x = Inr y \<longleftrightarrow> f x = y"
    shows "list_all2 (\<lambda>x y. fM x = Inr y) xs ys = (ys = map f xs)"
  unfolding list_all2_conv_all_nth
proof (intro iffI strip conjI; (elim conjE)?)
  assume len: "length xs = length ys" 
    and i: "\<forall>i<length xs. fM (xs ! i) = Inr (ys ! i)"
  have nth_eq: "\<forall>i < length xs. ys ! i = f (xs ! i)" using i assms unfolding list_all_iff by simp
  show "ys = map f xs" apply (subst list_eq_iff_nth_eq)
    using len nth_eq by auto 
next
  show "ys = map f xs \<Longrightarrow> length xs = length ys" by simp
next
  fix i
  assume ys: "ys = map f xs"
    and i: "i < length xs"
  show "fM (xs ! i) = Inr (ys ! i)"
    using assms ys i unfolding list_all_iff by auto
qed

text \<open>We need to refine some datatypes\<close>

text \<open>WP-D ISOLATION: the code-generation-only typeclass block that used to live here
  (card_UNIV / proper_interval / cproper_interval / ceq / ccompare / set_impl instances
  and derive commands for String.literal / predicate / ast_action_schema) was removed to
  reach green through model_checking_problem_refine.  It is broken by the
  Formal-PDDL-Semantics re-point on two counts: (a) list_less_one_correct relied on the OLD
  literal.Abs_literal internal representation, and (b) the derive commands reference the
  removed 'ast_action_schema' type.  None of it feeds the net-constructor definitions, the
  *_refine lemmas, or model_checking_problem_refine (verified: nothing after this point uses
  those names, and there is no export_code in this file).  To be repaired / re-derived under
  WP-D (code export).  The removed block is preserved in git history (commit 31a9e17).\<close>

text \<open>WP-D ISOLATION: the executable problem-checker scaffolding that used to live here
  (example_domain / example_problem / a check_wf_problem value, and the check_ground_problem
  definition + check_ground_problem_return_iff correctness lemma) was removed to reach green
  through model_checking_problem_refine.  It is broken by the Formal-PDDL-Semantics re-point:
  the checker used the old ast_domain.STG / ast_domain.mp_constT / ast_problem.mp_objT
  accessors and the ast_problem locale, and the correctness proof used the removed
  wf_ast_problem_def / wf_problem'_correct facts -- all of which moved to the ast_cont_*
  namespace (ast_cont_domain.STG, wf_cont_problem', ...).  None of it feeds
  model_checking_problem_refine or the reduction *_refine chain (verified: nothing between
  here and model_checking_problem_refine uses check_ground_problem / check_wf_problem /
  example_*).  This is the "retire check_ground_problem" WP-D item.  The removed block is
  preserved in git history (commit 31a9e17).\<close>


definition "prop_to_var_impl prop_to_name p \<equiv> STR ''var_'' + prop_to_name p"
definition "prop_to_lock_impl prop_to_name p \<equiv> STR ''lock_'' + prop_to_name p"
definition "acts_active_impl \<equiv> STR ''acts_active''"
definition "planning_lock_impl \<equiv> STR ''planning_lock''"

definition "act_to_start_clock_impl act_to_name a \<equiv> STR ''start_'' + act_to_name a"
definition "act_to_end_clock_impl act_to_name a \<equiv> STR ''end_'' + act_to_name a"

definition "off_loc_impl \<equiv> 0::nat"
definition "starting_loc_impl \<equiv> 1::nat"
definition "running_loc_impl \<equiv> 2::nat"
definition "ending_loc_impl \<equiv> 3::nat"

definition "init_loc_impl \<equiv> 0::nat"
definition "planning_loc_impl \<equiv> 1::nat"
definition "goal_loc_impl \<equiv> 2::nat"

abbreviation "var_is n v \<equiv> bexp.eq (exp.var v) (exp.const n)"
abbreviation "inc_var n v \<equiv> (v, exp.binop (+) (exp.var v) (exp.const n))"
abbreviation "set_var n v \<equiv> (v, exp.const n)"


fun lower_spec_impl::"ast_temporal_action_schema \<Rightarrow> _" where
"lower_spec_impl (SimpleActionSchema h b) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec_impl (DurativeActionSchema h (DurativeActionBody dc cond deff)) = map_option (map_lower_bound floor) (dc_list_lower (map snd dc))"

fun upper_spec_impl::"ast_temporal_action_schema \<Rightarrow> _" where
"upper_spec_impl (SimpleActionSchema h b) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec_impl (DurativeActionSchema h (DurativeActionBody dc cond deff)) = map_option (map_upper_bound floor) (dc_list_upper (map snd dc))"

definition "l_dur_impl a \<equiv> (case lower_spec_impl a of 
  None \<Rightarrow> [] | Some (lower_bound.GT n) \<Rightarrow> 
    [acconstraint.GT (act_to_start_clock_impl ast_temporal_action_schema_name a) n]
| Some (lower_bound.GE n) \<Rightarrow> 
    [acconstraint.GE (act_to_start_clock_impl ast_temporal_action_schema_name a) n])"


definition "u_dur_impl a \<equiv> (case upper_spec_impl a of 
  None \<Rightarrow> [] | Some (upper_bound.LT n) \<Rightarrow> 
    [acconstraint.LT (act_to_start_clock_impl ast_temporal_action_schema_name a) n]
| Some (upper_bound.LE n) \<Rightarrow> 
    [acconstraint.LE (act_to_start_clock_impl ast_temporal_action_schema_name a) n])"

definition main_auto_loop_impl::"(nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)" where
"main_auto_loop_impl \<equiv> (goal_loc_impl, bexp.true, [], Sil STR '''', [], [], goal_loc_impl)"


context ground_ast_problem_defs
begin

text \<open>We define the code that generates the automata\<close>

definition "mutex_snap_action' a b = 
  action_defs.mutex_snap_action (\<lambda>a. set (imp_defs.rat_impl.pre_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.add_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.del_imp_list a)) a b"

definition "net_int_clocks' a =
    map (act_to_start_clock_impl ast_temporal_action_schema_name) (filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec) 
  @ map (act_to_end_clock_impl ast_temporal_action_schema_name) (filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec)"

definition "start_edge' a = 
(let start_snap = AtStart a; guard = map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks' start_snap) @ map (\<lambda>x. acconstraint.GE x 0) (net_int_clocks' start_snap);
  not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list start_snap)) (imp_defs.rat_impl.del_imp_list start_snap)); 
  pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list start_snap);
  var_check = bexp_and_all (var_is 1 planning_lock_impl # not_locked_check @ pre_check); 
  add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list start_snap); 
  del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list start_snap);
  upds = (inc_var 1 acts_active_impl) # del_upds @ add_upds; 
  resets = [act_to_start_clock_impl ast_temporal_action_schema_name a]
 in (off_loc_impl, var_check, guard, Sil STR '''', upds, resets, starting_loc_impl))"

definition "edge_2' a =
(let 
  check_invs = bexp_and_all (var_is 1 planning_lock_impl # map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (over_all_spec a));
  upds = map ((inc_var 1 \<circ>\<circ> prop_to_lock_impl) predicate.name) (over_all_spec a)
in (starting_loc_impl, check_invs, [], Sil STR '''', upds, [], running_loc_impl))"

definition "edge_3' a =
(let 
  end_snap = AtEnd a; 
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (net_int_clocks' end_snap); 
  guard = l_dur_impl a @ u_dur_impl a @ int_clocks;
  upds = map ((inc_var (- 1) \<circ>\<circ> prop_to_lock_impl) predicate.name) (over_all_spec a); 
  resets = [act_to_end_clock_impl ast_temporal_action_schema_name a]
in (running_loc_impl, var_is 1 planning_lock_impl, guard, Sil STR '''', upds, resets, ending_loc_impl))"

definition "end_edge' a =
(let 
  end_instant = ending_loc_impl; 
  off = off_loc_impl; 
  end_snap = AtEnd a; 
  not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list end_snap)) (imp_defs.rat_impl.del_imp_list end_snap));
  pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list end_snap); 
  check = bexp_and_all (var_is 1 planning_lock_impl # not_locked_check @ pre_check);
  add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list end_snap); 
  del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list end_snap);
  upds = inc_var (- 1) acts_active_impl # del_upds @ add_upds
in (end_instant, check, [], Sil STR '''', upds, [], off))"


definition "instant_trans_edge' a =
(let 
  end_snap = AtEnd a; 
  start_snap = AtStart a; 
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (net_int_clocks' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (net_int_clocks' end_snap); 
  guard = l_dur_impl a @ u_dur_impl a @ int_clocks;
 resets = [act_to_end_clock_impl ast_temporal_action_schema_name a]
in (starting_loc_impl, var_is 1 planning_lock_impl, guard, Sil STR '''', [], resets, ending_loc_impl))"


definition "action_to_automaton' a =
(let committed_locs = []; 
  urgent_locs = [starting_loc_impl, ending_loc_impl]; 
  edges = [start_edge' a, edge_2' a, edge_3' a, end_edge' a, instant_trans_edge' a];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

text \<open>We do the same for the main automaton\<close>

definition "init_spec' = (map to_predicate (filter is_predAtom (init P)))"

definition "main_auto_init_edge' \<equiv>
(let can_start = var_is 0 planning_lock_impl;
  permit_planning = set_var 1 planning_lock_impl; 
  set_active = set_var 0 acts_active_impl;
  set_props = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) init_spec'; 
  upds = permit_planning # set_active # set_props
in (init_loc_impl, can_start, [], Sil STR '''', upds, [], planning_loc_impl))
"

definition main_auto_goal_edge'::"nat \<times>
   (String.literal, int) Simple_Expressions.bexp \<times>
   (String.literal, int) acconstraint list \<times>
   String.literal act \<times>
   (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_goal_edge' \<equiv>
(let 
  can_end = [var_is 1 planning_lock_impl, var_is 0 acts_active_impl]; 
  goal_sat = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) goal_spec;
  cond = bexp_and_all (can_end @ goal_sat); 
  lock_plan = (planning_lock_impl, exp.const 2)
in (planning_loc_impl, cond, [], Sil STR '''', [lock_plan], [], goal_loc_impl))
"

definition main_auto'::"nat list \<times>
   nat list \<times>
   (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat) list \<times>
   (nat \<times> (String.literal, int) acconstraint list) list" where
"main_auto' \<equiv>
(let committed_locs = []; 
  urgent_locs = [init_loc_impl, goal_loc_impl]; 
  edges = [main_auto_init_edge', main_auto_goal_edge', main_auto_loop_impl]; 
  invs = [] 
in (committed_locs, urgent_locs, edges, invs))"

definition "net_automata' = main_auto' # map action_to_automaton' actions_spec"


text \<open>Next, the broadcast channels\<close>
definition "net_broadcast' = ([]::String.literal list)"

text \<open>We provide concrete definitions for variables\<close>

definition "inv_vars' invs = (
let i = set invs
in prop_to_lock_impl predicate.name ` i \<union> prop_to_var_impl predicate.name ` i)"

definition "snap_vars' snap = (
let pre_vars = map (prop_to_var_impl predicate.name) (imp_defs.rat_impl.pre_imp_list snap); 
    add_vars = map (prop_to_var_impl predicate.name) (imp_defs.rat_impl.add_imp_list snap);
    del_vars = map (prop_to_lock_impl predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list snap)) (imp_defs.rat_impl.del_imp_list snap)) @ map (prop_to_var_impl predicate.name) (imp_defs.rat_impl.del_imp_list snap)
in set (pre_vars @ add_vars @ del_vars)
)"


definition "action_vars' a = (
let inv_vars = inv_vars' (over_all_spec a);
    start_vars = snap_vars' (AtStart a);
    end_vars = snap_vars' (AtEnd a)
in inv_vars \<union> start_vars \<union> end_vars
)"

definition "net_bounds' = (
let action_vars = \<Union> (action_vars' ` set actions_spec); 
    init_vars = prop_to_var_impl predicate.name ` set init_spec'; 
    goal_vars = prop_to_var_impl predicate.name ` set goal_spec; 
    vars_occ = action_vars \<union> init_vars \<union> goal_vars; 
    
    prop_lock_var_defs = map (\<lambda>p. (prop_to_lock_impl predicate.name p, 0, int (length actions_spec))) props_spec;
    prop_var_var_defs = map (\<lambda>p. (prop_to_var_impl predicate.name p, 0, 1)) props_spec; 
    prop_var_defs = filter (\<lambda>x. fst x \<in> vars_occ) (prop_lock_var_defs @ prop_var_var_defs); 

    acts_active_var = (acts_active_impl, 0::int, int (length actions_spec)); 
    planning_lock_var = (planning_lock_impl, 0, 2)
 in [acts_active_var, planning_lock_var] @ prop_var_defs)"

text \<open>Then, we provide the initial configuration\<close>

definition "init_locs' =
init_loc_impl # map (\<lambda>x. off_loc_impl) actions_spec"

definition "init_vars' =
map (map_prod id fst) net_bounds'"

definition "init_cfg' =
  (init_locs', map_of init_vars', \<lambda>x::String.literal. 0::real)"

text \<open>Finally, the formula\<close>
definition reach_formula'::
  "(nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula" 
  where
"reach_formula' = Simple_Network_Language_Model_Checking.formula.EX (sexp.loc 0 goal_loc_impl)"

text \<open>
We need to provide the model checker with the names of locations, clocks and automata.
These are typically removed in a parsing or syntax translation step.
\<close>

find_theorems name: "action*uniq"

definition "auto_names = 
  STR ''main'' # map (\<lambda>x. STR ''act_'' + ast_temporal_action_schema_name x) actions_spec
"

definition "auto_names_to_index =
  List_Index.index auto_names
"


definition "auto_loc_ids_to_names (n::nat) (m::nat) = (
  if (n = 0) then (case m of
      0 \<Rightarrow> (STR ''init'')
    | Suc 0 \<Rightarrow> (STR ''planning'')
    | Suc (Suc 0) \<Rightarrow> (STR ''goal'')
  ) else (case m of
      0 \<Rightarrow> (STR ''off'')
    | Suc 0 \<Rightarrow> (STR ''starting'')
    | Suc (Suc 0) \<Rightarrow> (STR ''running'')
    | Suc (Suc (Suc 0)) \<Rightarrow> (STR ''ending'')
  )
)
"

definition "clock_names =
map (act_to_start_clock_impl ast_temporal_action_schema_name) actions_spec
@ map (act_to_end_clock_impl ast_temporal_action_schema_name) actions_spec
"

end



lemmas ground_ast_problem_code =
  ground_ast_problem_defs.props_spec_def
  ground_ast_problem_defs.ground_non_action_def
  ground_ast_problem_defs.over_all_snap.simps
  ground_ast_problem_defs.over_all_spec.simps
  ground_ast_problem_defs.goal_spec_def 
  ground_ast_problem_defs.dels_spec.simps 
  ground_ast_problem_defs.adds_spec.simps
  ground_ast_problem_defs.pre_spec.simps
  action_defs.app_snap.simps
  ground_ast_problem_defs.at_start_spec.simps
  ground_ast_problem_defs.at_end_spec.simps
  ground_ast_problem_defs.actions_spec_def
  ground_ast_problem_defs.mutex_snap_action'_def
  ground_ast_problem_defs.net_int_clocks'_def
  ground_ast_problem_defs.start_edge'_def
  ground_ast_problem_defs.edge_2'_def
  ground_ast_problem_defs.edge_3'_def
  ground_ast_problem_defs.end_edge'_def
  ground_ast_problem_defs.instant_trans_edge'_def
  ground_ast_problem_defs.action_to_automaton'_def
  ground_ast_problem_defs.init_spec'_def
  ground_ast_problem_defs.main_auto_init_edge'_def
  ground_ast_problem_defs.main_auto_goal_edge'_def
  ground_ast_problem_defs.main_auto'_def
  ground_ast_problem_defs.net_automata'_def
  ground_ast_problem_defs.net_broadcast'_def
  ground_ast_problem_defs.inv_vars'_def
  ground_ast_problem_defs.snap_vars'_def
  ground_ast_problem_defs.action_vars'_def
  ground_ast_problem_defs.net_bounds'_def
  ground_ast_problem_defs.init_locs'_def
  ground_ast_problem_defs.init_vars'_def
  ground_ast_problem_defs.init_cfg'_def
  ground_ast_problem_defs.reach_formula'_def
  ground_ast_problem_defs.auto_names_def
  ground_ast_problem_defs.auto_names_to_index_def
  ground_ast_problem_defs.auto_loc_ids_to_names_def
  ground_ast_problem_defs.clock_names_def

declare ground_ast_problem_code[code]


context ground_ast_problem
begin


subsection \<open>Refinement to monadic code\<close>

text \<open>Some constants need executable copies\<close>

(* tp_nta_reduction_defs.planning_loc, tp_nta_reduction_defs.set_prop_ab, tp_nta_reduction_defs.acts_active, tp_nta_reduction_defs.init_loc *)

lemma prop_to_var_refine: 
  "abstr_model_checking.reduction_ref_impl.prop_to_var \<equiv> prop_to_var_impl predicate.name"
  unfolding abstr_model_checking.reduction_ref_impl.prop_to_var_def
  unfolding prop_to_var_impl_def prop_to_name_spec_def
  by argo

lemma prop_to_lock_refine: 
  "abstr_model_checking.reduction_ref_impl.prop_to_lock \<equiv> prop_to_lock_impl predicate.name"
  unfolding abstr_model_checking.reduction_ref_impl.prop_to_lock_def
  unfolding prop_to_lock_impl_def prop_to_name_spec_def
  by argo

lemma acts_active_refine:
  "abstr_model_checking.reduction_ref_impl.acts_active = acts_active_impl"
  unfolding abstr_model_checking.reduction_ref_impl.acts_active_def
  unfolding acts_active_impl_def
  ..

lemma planning_lock_refine:
  "abstr_model_checking.reduction_ref_impl.planning_lock = planning_lock_impl"
  unfolding abstr_model_checking.reduction_ref_impl.planning_lock_def
  unfolding planning_lock_impl_def ..

lemma act_to_start_clock_refine:
  "abstr_model_checking.reduction_ref_impl.act_to_start_clock = act_to_start_clock_impl ast_temporal_action_schema_name"
  unfolding abstr_model_checking.reduction_ref_impl.act_to_start_clock_def
  unfolding act_to_name_spec_def
  unfolding act_to_start_clock_impl_def
  ..

lemma act_to_end_clock_refine:
  "abstr_model_checking.reduction_ref_impl.act_to_end_clock = act_to_end_clock_impl ast_temporal_action_schema_name"
  unfolding abstr_model_checking.reduction_ref_impl.act_to_end_clock_def
  unfolding act_to_name_spec_def
  unfolding act_to_end_clock_impl_def
  ..

lemma off_loc_refine:
  "abstr_model_checking.reduction_ref_impl.off_loc = off_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.off_loc_def
  unfolding off_loc_impl_def
  ..

lemma starting_loc_refine:
  "abstr_model_checking.reduction_ref_impl.starting_loc = starting_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.starting_loc_def
  unfolding starting_loc_impl_def
  ..

lemma running_loc_refine:
  "abstr_model_checking.reduction_ref_impl.running_loc = running_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.running_loc_def
  unfolding running_loc_impl_def
  ..

lemma ending_loc_refine:
  "abstr_model_checking.reduction_ref_impl.ending_loc = ending_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.ending_loc_def
  unfolding ending_loc_impl_def
  ..

lemma init_loc_refine:
  "abstr_model_checking.reduction_ref_impl.init_loc = init_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.init_loc_def
  unfolding init_loc_impl_def
  ..

lemma planning_loc_refine:
  "abstr_model_checking.reduction_ref_impl.planning_loc = planning_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.planning_loc_def
  unfolding planning_loc_impl_def
  ..

lemma goal_loc_refine:
  "abstr_model_checking.reduction_ref_impl.goal_loc = goal_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.goal_loc_def
  unfolding goal_loc_impl_def
  ..

lemma set_prop_ab_refine:
  "abstr_model_checking.reduction_ref_impl.set_prop_ab n = (set_var n) o (prop_to_var_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.set_prop_ab_def
  unfolding prop_to_var_refine
  ..

lemma is_prop_ab_refine:
  "abstr_model_checking.reduction_ref_impl.is_prop_ab n = (var_is n) o (prop_to_var_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.is_prop_ab_def
  unfolding prop_to_var_refine
  ..

lemma inc_prop_ab_refine:
  "abstr_model_checking.reduction_ref_impl.inc_prop_ab n = (inc_var n) o (prop_to_var_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.inc_prop_ab_def
  unfolding prop_to_var_refine
  ..

lemma set_prop_lock_ab_refine:
  "abstr_model_checking.reduction_ref_impl.set_prop_lock_ab n = (set_var n) o (prop_to_lock_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.set_prop_lock_ab_def
  unfolding prop_to_lock_refine
  ..

lemma is_prop_lock_ab_refine:
  "abstr_model_checking.reduction_ref_impl.is_prop_lock_ab n = (var_is n) o (prop_to_lock_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.is_prop_lock_ab_def
  unfolding prop_to_lock_refine
  ..

lemma inc_prop_lock_ab_refine:
  "abstr_model_checking.reduction_ref_impl.inc_prop_lock_ab n = (inc_var n) o (prop_to_lock_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.inc_prop_lock_ab_def
  unfolding prop_to_lock_refine
  ..

lemma lower_spec_refine:
  "lower_spec = lower_spec_impl"
  apply (intro ext)
  subgoal for x
    apply (cases x rule: ast_temporal_action_schema_cases_unfold)
    by simp+
  done

lemma upper_spec_refine:
  "upper_spec = upper_spec_impl"
  apply (intro ext)
  subgoal for x
    apply (cases x rule: ast_temporal_action_schema_cases_unfold)
    by simp+
  done

schematic_goal l_dur_refine:
  "abstr_model_checking.reduction_ref_impl.l_dur = l_dur_impl"
  apply (intro ext)
  unfolding abstr_model_checking.reduction_ref_impl.l_dur_def
  unfolding lower_spec_refine
  unfolding act_to_start_clock_refine
  unfolding l_dur_impl_def
  ..

schematic_goal u_dur_refine:
  "abstr_model_checking.reduction_ref_impl.u_dur = u_dur_impl"
  apply (intro ext)
  unfolding abstr_model_checking.reduction_ref_impl.u_dur_def
  unfolding upper_spec_refine
  unfolding act_to_start_clock_refine
  unfolding u_dur_impl_def
  ..



text \<open>Now, we will refine these lemmas. Checking list intersection is inefficient
  for all actions. We do not need to, because we have proven that actions only refer to 
  propositions (predicates without arguments)
  at the level of PDDL.\<close>
lemma pre_imp_restr_equiv_pre_imp:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "imp_defs.rat_impl.pre_imp_restr_list a = imp_defs.rat_impl.pre_imp_list a"
proof -
  have "set (imp_defs.rat_impl.pre_imp_list a) \<subseteq> set props_spec"
  proof (intro subsetI)
    fix x
    assume "x \<in> set (imp_defs.rat_impl.pre_imp_list a)"
    thus "x \<in> set props_spec" 
      using assms
      apply (induction a)
      unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.set_impl.app_snap.simps
      using start_pre_in_props end_pre_in_props by blast+
  qed
  thus ?thesis
    unfolding imp_defs.rat_impl.pre_imp_restr_list_def
    by (force simp: filter_id_conv)
qed

lemma over_all_restr_equiv_over_all:
  assumes "a \<in> set actions_spec"
  shows "imp_defs.rat_impl.over_all_restr_list a = over_all_spec a"
proof -
  have "set (over_all_spec a) \<subseteq> set props_spec"
    using over_all_in_props assms by simp
  thus ?thesis unfolding imp_defs.rat_impl.over_all_restr_list_def
    by (force simp: filter_id_conv)
qed


lemma mutex_snap_action_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
          and "b \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
        shows "abstr_model_checking.rat_imp'.prob_list_impl.set_impl.mutex_snap_action a b = 
     mutex_snap_action' a b"
  unfolding mutex_snap_action'_def
  apply (subst abstr_model_checking.rat_imp'.prob_list_impl.set_impl.mutex_snap_action_def)
  unfolding comp_def apply (subst pre_imp_restr_equiv_pre_imp, use assms in blast)+
  apply (subst action_defs.mutex_snap_action_def[symmetric])
  by simp

lemma net_int_clocks_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.net_int_clocks a = net_int_clocks' a"
proof -
  have 1: "filter (\<lambda>aa. abstr_model_checking.reduction_ref_impl.mutex_effects a (AtStart aa)) actions_spec =
    filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec"
    apply (rule filter_eq_conv)
    using mutex_snap_action_refine[OF assms]
    by simp
  
  have 2: "filter (\<lambda>aa. abstr_model_checking.reduction_ref_impl.mutex_effects a (AtEnd aa)) actions_spec =
    filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec"
    apply (rule filter_eq_conv)
    using mutex_snap_action_refine[OF assms]
    by simp
  
  show ?thesis
    unfolding abstr_model_checking.reduction_ref_impl.net_int_clocks_def Let_def
    unfolding 1 2 net_int_clocks'_def
    unfolding act_to_start_clock_refine
    unfolding act_to_end_clock_refine
    by blast
qed

lemma start_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.start_edge a = start_edge' a" 
  unfolding start_edge'_def
  unfolding abstr_model_checking.reduction_ref_impl.start_edge_def
  unfolding abstr_model_checking.reduction_ref_impl.pl_is_1_def
  unfolding planning_lock_refine
  unfolding is_prop_lock_ab_refine
  unfolding is_prop_ab_refine
  unfolding set_prop_ab_refine
  unfolding acts_active_refine
  unfolding off_loc_refine starting_loc_refine
  unfolding act_to_start_clock_refine
  using net_int_clocks_refine assms pre_imp_restr_equiv_pre_imp
  by simp


lemma edge_2_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_2 a = edge_2' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_2_def 
  unfolding abstr_model_checking.reduction_ref_impl.pl_is_1_def
  unfolding planning_lock_refine
  unfolding is_prop_ab_refine
  unfolding inc_prop_lock_ab_refine
  unfolding starting_loc_refine running_loc_refine
  unfolding edge_2'_def
  using over_all_restr_equiv_over_all assms
  by simp

lemma edge_3_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_3 a = edge_3' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_3_def
  unfolding abstr_model_checking.reduction_ref_impl.pl_is_1_def
  unfolding planning_lock_refine
  unfolding edge_3'_def
  unfolding running_loc_refine
  unfolding ending_loc_refine
  unfolding act_to_end_clock_refine
  unfolding inc_prop_lock_ab_refine
  unfolding l_dur_refine u_dur_refine
  using net_int_clocks_refine assms over_all_restr_equiv_over_all
  by simp


lemma end_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.end_edge a = end_edge' a"
  unfolding abstr_model_checking.reduction_ref_impl.end_edge_def
  unfolding abstr_model_checking.reduction_ref_impl.pl_is_1_def
  unfolding planning_lock_refine
  unfolding ending_loc_refine off_loc_refine
  unfolding is_prop_ab_refine
  unfolding is_prop_lock_ab_refine
  unfolding set_prop_ab_refine
  unfolding acts_active_refine
  unfolding end_edge'_def
  using pre_imp_restr_equiv_pre_imp assms
  by auto


lemma instant_trans_edge_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.instant_trans_edge a = instant_trans_edge' a" 
  unfolding abstr_model_checking.reduction_ref_impl.instant_trans_edge_def
  unfolding abstr_model_checking.reduction_ref_impl.pl_is_1_def
  unfolding planning_lock_refine
  unfolding instant_trans_edge'_def
  unfolding starting_loc_refine ending_loc_refine
  unfolding l_dur_refine u_dur_refine
  unfolding act_to_end_clock_refine
  using net_int_clocks_refine assms
  by simp


lemma action_to_automaton_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.action_to_automaton a = action_to_automaton' a"
  unfolding abstr_model_checking.reduction_ref_impl.action_to_automaton_def
  unfolding action_to_automaton'_def
  unfolding starting_loc_refine ending_loc_refine
  using start_edge_refine edge_2_refine edge_3_refine end_edge_refine instant_trans_edge_refine assms
  by simp


text \<open>Now we provide an equivalent definition of the main automaton.\<close>


lemma filter_props_init:
  "(filter (\<lambda>p. p \<in> set props_spec) init_spec) = init_spec'"
  apply (subst filter_True)
  using init_in_props apply blast
  unfolding init_spec_def init_spec'_def
  apply (rule distinct_remdups_id)
  apply (rule distinct_inj_on_map)
  using wf_temporal_problem unfolding wf_temporal_problem_def apply simp
  apply (rule inj_on_subset)
   apply (rule inj_on_to_predicate)
  using init_no_args
  unfolding list_all_iff by auto
  

lemma filter_props_goal:
  "(filter (\<lambda>p. p \<in> set props_spec) goal_spec) = goal_spec"
  using goal_in_props filter_id_conv by fast

  
lemma main_auto_init_edge_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_init_edge = main_auto_init_edge'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_init_edge_def
  unfolding main_auto_init_edge'_def
  unfolding filter_props_init planning_lock_refine
  unfolding planning_loc_refine
  unfolding init_loc_refine
  unfolding acts_active_refine
  unfolding set_prop_ab_refine
  ..

lemma main_auto_goal_edge_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_goal_edge = main_auto_goal_edge'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_def
  unfolding main_auto_goal_edge'_def
  unfolding filter_props_goal
  unfolding planning_loc_refine
  unfolding goal_loc_refine
  unfolding acts_active_refine
  unfolding planning_lock_refine
  unfolding is_prop_ab_refine
  ..

lemma main_auto_loop_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_loop = main_auto_loop_impl"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_loop_def
  unfolding main_auto_loop_impl_def
  unfolding goal_loc_refine ..

lemma main_auto_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto = main_auto'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_def
  unfolding main_auto'_def
  unfolding main_auto_init_edge_refine main_auto_goal_edge_refine
  unfolding main_auto_loop_refine
  unfolding init_loc_refine goal_loc_refine
  ..


text \<open>Finally we can provide another definition of the entire network\<close>

lemma net_automata_refine:
  shows "abstr_model_checking.reduction_ref_impl.net_automata = net_automata'"
  unfolding abstr_model_checking.reduction_ref_impl.timed_automaton_net_def
  unfolding net_automata'_def
  using action_to_automaton_refine main_auto_refine by simp

text \<open>Next, we need to refine the set of broadcast channels (there are none)\<close>


lemma net_broadcast_refine:
  "abstr_model_checking.reduction_ref_impl.net_broadcast = net_broadcast'"
  unfolding abstr_model_checking.reduction_ref_impl.net_broadcast_def
  unfolding net_broadcast'_def by simp


text \<open>Then, we refine the variable bounds\<close>

lemma inv_vars_refine:
  "abstr_model_checking.reduction_ref_impl.inv_vars invs = inv_vars' invs"
  unfolding abstr_model_checking.reduction_ref_impl.inv_vars_def
  unfolding prop_to_lock_refine prop_to_var_refine
  unfolding inv_vars'_def by (simp add: Let_def image_Un)

lemma snap_vars_refine:
  assumes "snap \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.snap_vars snap = snap_vars' snap"
  unfolding abstr_model_checking.reduction_ref_impl.snap_vars_def
  unfolding pre_imp_restr_equiv_pre_imp[OF assms]
  unfolding prop_to_var_refine prop_to_lock_refine
  unfolding snap_vars'_def 
  by presburger

lemma action_vars_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.action_vars a = action_vars' a "
  unfolding abstr_model_checking.reduction_ref_impl.action_vars_def
  unfolding inv_vars_refine
  using assms snap_vars_refine over_all_restr_equiv_over_all
  unfolding action_vars'_def 
  by auto


lemma net_bounds_refine:
  "abstr_model_checking.reduction_ref_impl.net_bounds = net_bounds'"
  unfolding abstr_model_checking.reduction_ref_impl.all_vars_def
  unfolding filter_props_init filter_props_goal
  unfolding prop_to_lock_refine
  unfolding prop_to_var_refine
  unfolding acts_active_refine
  unfolding planning_lock_refine
  unfolding fold_union' set_map
  unfolding net_bounds'_def
  using action_vars_refine
  by auto


text \<open>Refinining the initial configuration and formula\<close>
lemma init_locs_refine:
  "abstr_model_checking.reduction_ref_impl.init_locs = init_locs'"
  unfolding abstr_model_checking.reduction_ref_impl.init_locs_def
  unfolding init_loc_refine off_loc_refine
  unfolding init_locs'_def by blast

lemma init_vars_refine:
  "abstr_model_checking.reduction_ref_impl.init_vars = init_vars'"
  unfolding abstr_model_checking.reduction_ref_impl.init_vars_def
  unfolding net_bounds_refine
  unfolding init_vars'_def
  by blast

lemma init_cfg_refine:
  "(case abstr_model_checking.ref_model_checking.a\<^sub>0 of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, \<lambda>x. real_of_int (y x))))
   = init_cfg'"
  unfolding abstr_model_checking.ref_model_checking.a\<^sub>0_def
  unfolding prod.case
  unfolding init_locs_refine
  unfolding init_vars_refine
  unfolding init_cfg'_def 
  by simp

lemma formula_refine:
  "abstr_model_checking.reduction_ref_impl.reach_formula = reach_formula'"
  unfolding abstr_model_checking.reduction_ref_impl.reach_formula_def
  unfolding goal_loc_refine
  unfolding reach_formula'_def
  by blast

text \<open>Combining all of this, we get to the alternative model checking problem\<close>

lemma model_checking_problem_refine: 
  "\<not> Simple_Network_Impl.sem net_automata' net_broadcast' net_bounds', init_cfg' \<Turnstile> reach_formula'
\<Longrightarrow> \<nexists>tp. valid_ground_plan P tp"
  using form_not_sat_imp_no_valid_ground_plan
  unfolding abstr_model_checking.ref_model_checking.net_impl.sem_def 
  unfolding net_automata_refine
  unfolding net_broadcast_refine
  unfolding net_bounds_refine
  unfolding init_cfg_refine
  unfolding formula_refine
  unfolding Simple_Network_Impl.sem_def
  by blast


end

section \<open>WP-D: the executable admission check + network assembly (re-derived, ast_cont_* namespace)\<close>

text \<open>The temporal well-formedness check routes through the \<^emph>\<open>continuous\<close> checker at the translated
  problem (@{const temporal_to_continuous_problem}); its @{text return_iff} composes
  @{thm check_wf_problem_return_iff} with @{thm ast_temporal_problem.wf_ast_cont_problem_equiv}.\<close>

definition "check_wf_temporal_problem P \<equiv> check_wf_cont_problem (temporal_to_continuous_problem P)"

lemma check_wf_temporal_problem_return_iff[return_iff]:
  "check_wf_temporal_problem P = Inr () \<longleftrightarrow> wf_ast_temporal_problem P"
proof -
  interpret ast_temporal_problem P .
  show ?thesis
    unfolding check_wf_temporal_problem_def check_wf_problem_return_iff
    using wf_ast_cont_problem_equiv wf_ast_temporal_problem_def by simp
qed

lemma isOK_check_wf_temporal_problem[simp]:
  "isOK (check_wf_temporal_problem P) \<longleftrightarrow> wf_ast_temporal_problem P"
proof -
  have "isOK (check_wf_temporal_problem P) \<longleftrightarrow> check_wf_temporal_problem P = Inr ()"
    by (cases "check_wf_temporal_problem P") (auto simp: isOK_def)
  thus ?thesis by (simp add: check_wf_temporal_problem_return_iff)
qed

text \<open>The static admission check for the classical (numeric-free) ground leaf: the wf check plus the
  nine @{locale ground_ast_problem_core} structural side-conditions (including the positivity-re-point's
  @{const act_conds_no_args}) plus @{text \<open>functions D = []\<close>} (the @{locale ground_ast_problem} leaf).\<close>

definition "check_ground_problem P \<equiv> do {
  let D = ast_problem.domain P;
  check_wf_temporal_problem P;
  check (is_pos_conj (goal P)) (ERRS ''Goal not a conjunction of positive literals'');
  check_all_list pred_no_args (predicates D) ''Predicate not grounded (i.e. it has some argument)'' (shows o predicate.name o predicate_decl.pred);
  check_all_list act_no_params (actions D) ''Action not grounded, it has a/some parameter(s)'' (shows o ast_temporal_action_schema_name);
  check_all_list act_no_func_dcs (actions D) ''Action not grounded, it has a functional duration constraint'' (shows o ast_temporal_action_schema_name);
  check_all_list act_dcs_integers (actions D) ''Action's duration constraint is not an integer'' (shows o ast_temporal_action_schema_name);
  check_all_list act_pres_pos (actions D) ''Action has a condition that is not a conjunction of positive literals'' (shows o ast_temporal_action_schema_name);
  check_all_list act_conds_no_args (actions D) ''Action condition is not argument-free (numeric/eqAtm atoms with arguments)'' (shows o ast_temporal_action_schema_name);
  check (consts D = []) (ERRS ''Domain has constants'');
  check (functions D = []) (ERRS ''Domain has functions'');
  check_all_list form_preds_no_args (init P) ''Initial literal not grounded (it refers to constants)''
    (\<lambda>(x::object atom Formulas.formula) (y::string). show y)
}"

lemma check_ground_problem_return_iff[return_iff]:
  "check_ground_problem P = Inr () \<longleftrightarrow> ground_ast_problem P"
proof -
  interpret ast_temporal_problem P .
  show ?thesis
    unfolding check_ground_problem_def
    unfolding ground_ast_problem_def ground_ast_problem_axioms_def
    unfolding ground_ast_problem_core_def ground_ast_problem_core_axioms_def
    by (auto simp: return_iff list_all_iff)
qed

text \<open>The pure network builder: assemble the concrete Munta NTA from the refined constructors.\<close>

definition "make_network_impl P \<equiv> do {
  let automata = ground_ast_problem_defs.net_automata' P;
  let broadcast = ground_ast_problem_defs.net_broadcast';
  let bounds = ground_ast_problem_defs.net_bounds' P;
  let init_locs = ground_ast_problem_defs.init_locs' P;
  let init_vars = ground_ast_problem_defs.init_vars' P;
  let formula = ground_ast_problem_defs.reach_formula';
  let clock_names = ground_ast_problem_defs.clock_names P;
  let auto_names = ground_ast_problem_defs.auto_names P;
  let ids_to_names = ground_ast_problem_defs.auto_loc_ids_to_names;
  let process_names_to_index = ground_ast_problem_defs.auto_names_to_index P;
  Error_Monad.return (clock_names, auto_names, ids_to_names, process_names_to_index,
     broadcast, automata, bounds, formula, init_locs, init_vars)
}"

lemma make_network_impl_return_iff[return_iff]:
  "make_network_impl P = Inr (
    ground_ast_problem_defs.clock_names P,
    ground_ast_problem_defs.auto_names P,
    ground_ast_problem_defs.auto_loc_ids_to_names,
    ground_ast_problem_defs.auto_names_to_index P,
    ground_ast_problem_defs.net_broadcast',
    ground_ast_problem_defs.net_automata' P,
    ground_ast_problem_defs.net_bounds' P,
    ground_ast_problem_defs.reach_formula',
    ground_ast_problem_defs.init_locs' P,
    ground_ast_problem_defs.init_vars' P)"
  unfolding make_network_impl_def by (auto simp: return_iff)

definition check_and_make_network where
"check_and_make_network P \<equiv> do {
  check_ground_problem P;
  make_network_impl P
}"

lemma check_and_make_network_and_plan:
  assumes "(check_and_make_network P = Inr (clocks, auto_names, ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars))"
  shows "\<not> (Simple_Network_Impl.sem automata broadcast bounds, (init_locs, map_of init_vars, (\<lambda>_. 0)) \<Turnstile> formula) \<longrightarrow> (\<nexists>tp. valid_ground_plan P tp)"
  using assms
  unfolding check_and_make_network_def
  unfolding return_iff make_network_impl_return_iff
  using check_ground_problem_return_iff
  using ground_ast_problem.model_checking_problem_refine
  unfolding ground_ast_problem_defs.init_cfg'_def
  by force


end
theory Ground_PDDL_NTA_Reduction_Impl
  imports Ground_PDDL_NTA_Reduction_Correctness 
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Checker"
begin


lemmas return_iff = return_iff check_all_list_return_iff check_wf_problem_return_iff

named_theorems return_if

definition "example_domain =
Domain [] [] [] [] []
"

definition "example_problem = 
  Problem example_domain [] [] (\<^bold>\<not>\<bottom>)
"

value "check_wf_problem example_problem"

definition "check_ground_problem P \<equiv> do {
  let D = ast_problem.domain P;
  let stg = ast_domain.STG D;
  let conT = ast_domain.mp_constT D;
  let mp = ast_problem.mp_objT P;
  check_wf_problem P stg conT mp;
  check (is_pos_conj (goal P)) (ERRS ''Goal not a conjunction of positive literals'');
  check_all_list pred_no_args (predicates D) ''Predicate not grounded (i.e. it has some argument)'' (shows o predicate.name o predicate_decl.pred);
  check_all_list act_no_params (actions D) ''Action not grounded, it has a/some parameter(s)'' (shows o ast_action_schema.name);
  check_all_list act_no_func_dcs (actions D) ''Action not grounded, it has a functional duration constraint'' (shows o ast_action_schema.name);
  check_all_list act_dcs_integers (actions D) ''Action's duration constraint is not an integer'' (shows o ast_action_schema.name);
  check_all_list act_pres_pos (actions D) ''Action has a conditions that is not a conjunction of positive literals'' (shows o ast_action_schema.name);
  check (functions D = []) (ERRS ''Domain has functions'');
  check (consts D = []) (ERRS ''Domain has constants'');
  check_all_list form_preds_no_args (init P) ''Initial literal not grounded (it refers to constants)'' 
    (\<lambda>(x::object atom Formulas.formula) (y::string). show y)
}"

lemma check_ground_problem_return_iff[return_iff]:
  "check_ground_problem P = Inr () \<longleftrightarrow> ground_ast_problem P"
proof -
  interpret ast_problem P .
  show ?thesis 
    unfolding check_ground_problem_def 
    unfolding ground_ast_problem_def
    unfolding wf_ast_problem_def
    unfolding ground_ast_problem_axioms_def
    unfolding list_all_iff
    unfolding return_iff
    by (force simp: wf_problem'_correct return_iff)
qed

value "check_ground_problem example_problem"

lemma context_bind_return_iff[return_iff]:
  "(m \<bind> f = Inr y) = (\<exists>x. m = Inr x \<and> (m = Inr x \<longrightarrow> f x = Inr y))"
  apply (subst return_iff)
  by auto

lemma context_bind_return_iff'[return_iff]:
  "(m \<bind> f = Inr y) = (\<exists>x P. m = Inr x \<and> (m = Inr x \<longleftrightarrow> P) \<and> (P \<longrightarrow> f x = Inr y))"
  apply (subst context_bind_return_iff)
  by simp

context ground_ast_problem
begin
  subsection \<open>Now, we will refine these lemmas. Checking list intersection is inefficient
  for all actions. We do not need to, because we have proven that actions only refer to propositions
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

definition "mutex_snap_action' a b = 
  action_defs.mutex_snap_action (\<lambda>a. set (imp_defs.rat_impl.pre_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.add_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.del_imp_list a)) a b"


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

definition "int_clocks_spec' a =
    map abstr_model_checking.reduction_ref_impl.act_to_start_clock (filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec) 
  @ map abstr_model_checking.reduction_ref_impl.act_to_end_clock (filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec)"
  

lemma int_clocks_spec_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.int_clocks_spec a = int_clocks_spec' a"
proof -
  have 1: "filter (\<lambda>aa. abstr_model_checking.reduction_ref_impl.mutex_effects_spec a (AtStart aa)) actions_spec =
    filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec"
    apply (rule filter_eq_conv)
    using mutex_snap_action_refine[OF assms]
    by simp
  
  have 2: "filter (\<lambda>aa. abstr_model_checking.reduction_ref_impl.mutex_effects_spec a (AtEnd aa)) actions_spec =
    filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec"
    apply (rule filter_eq_conv)
    using mutex_snap_action_refine[OF assms]
    by simp
  
  show ?thesis
    unfolding abstr_model_checking.reduction_ref_impl.int_clocks_spec_def Let_def
    unfolding 1 2 int_clocks_spec'_def
    by blast
qed

definition "start_edge_spec' a = 
(let start_snap = AtStart a; guard = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' start_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' start_snap);
         not_locked_check = map (abstr_model_checking.reduction_ref_impl.is_prop_lock_ab 0) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list start_snap)) (imp_defs.rat_impl.del_imp_list start_snap)); pre_check = map (abstr_model_checking.reduction_ref_impl.is_prop_ab 1) (imp_defs.rat_impl.pre_imp_restr_list start_snap);
         var_check = abstr_model_checking.reduction_ref_impl.bexp_and_all (not_locked_check @ pre_check); add_upds = map (abstr_model_checking.reduction_ref_impl.set_prop_ab 1) (imp_defs.rat_impl.add_imp_list start_snap); del_upds = map (abstr_model_checking.reduction_ref_impl.set_prop_ab 0) (imp_defs.rat_impl.del_imp_list start_snap);
         upds = (abstr_model_checking.reduction_ref_impl.acts_active, binop plus_int (var abstr_model_checking.reduction_ref_impl.acts_active) (exp.const 1)) # del_upds @ add_upds; resets = [abstr_model_checking.reduction_ref_impl.act_to_start_clock a]
     in (abstr_model_checking.reduction_ref_impl.off_loc, var_check, guard, Sil STR '''', upds, resets, abstr_model_checking.reduction_ref_impl.starting_loc))"

lemma start_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.start_edge_spec a = start_edge_spec' a" 
  unfolding start_edge_spec'_def
  unfolding abstr_model_checking.reduction_ref_impl.start_edge_spec_def
  using int_clocks_spec_refine assms
  by simp

definition "edge_3_spec' a =
(let end_snap = AtEnd a; int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' end_snap); guard = abstr_model_checking.reduction_ref_impl.l_dur_spec a @ abstr_model_checking.reduction_ref_impl.u_dur_spec a @ int_clocks;
         upds = map (abstr_model_checking.reduction_ref_impl.inc_prop_lock_ab (- 1)) (imp_defs.rat_impl.over_all_restr_list a); resets = [abstr_model_checking.reduction_ref_impl.act_to_end_clock a]
     in (abstr_model_checking.reduction_ref_impl.running_loc, bexp.true, guard, Sil STR '''', upds, resets, abstr_model_checking.reduction_ref_impl.ending_loc))"

lemma edge_3_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_3_spec a = edge_3_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_3_spec_def
  unfolding edge_3_spec'_def
  using int_clocks_spec_refine assms
  by simp

definition "instant_trans_edge_spec' a =
(let end_snap = AtEnd a; start_snap = AtStart a; int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' end_snap); guard = abstr_model_checking.reduction_ref_impl.l_dur_spec a @ abstr_model_checking.reduction_ref_impl.u_dur_spec a @ int_clocks;
         resets = [abstr_model_checking.reduction_ref_impl.act_to_end_clock a]
     in (abstr_model_checking.reduction_ref_impl.starting_loc, bexp.true, guard, Sil STR '''', [], resets, abstr_model_checking.reduction_ref_impl.ending_loc))"

lemma instant_trans_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.instant_trans_edge_spec a = instant_trans_edge_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.instant_trans_edge_spec_def
  unfolding instant_trans_edge_spec'_def
  using int_clocks_spec_refine assms
  by simp

definition "action_to_automaton_spec' a =
(let committed_locs = []; 
  urgent_locs = [abstr_model_checking.reduction_ref_impl.starting_loc, abstr_model_checking.reduction_ref_impl.ending_loc]; 
  edges = [start_edge_spec' a, abstr_model_checking.reduction_ref_impl.edge_2_spec a, edge_3_spec' a, abstr_model_checking.reduction_ref_impl.end_edge_spec a, instant_trans_edge_spec' a];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

lemma action_to_automaton_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.action_to_automaton_spec a = action_to_automaton_spec' a"
  unfolding abstr_model_checking.reduction_ref_impl.action_to_automaton_spec_def
  unfolding action_to_automaton_spec'_def
  using start_edge_spec_refine edge_3_spec_refine instant_trans_edge_spec_refine assms by simp


thm abstr_model_checking.reduction_ref_impl.main_auto_spec_def
thm abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec_def

definition "init_spec' = (map to_predicate (filter is_predAtom (init P)))"


lemma filter_props_init:
  "(filter (\<lambda>p. p \<in> set props_spec) init_spec) = init_spec'"
  apply (subst filter_True)
  using init_in_props apply blast
  unfolding init_spec_def init_spec'_def
  apply (rule distinct_remdups_id)
  apply (rule distinct_inj_on_map)
  using wf_problem unfolding wf_problem_def apply simp
  apply (rule inj_on_subset)
   apply (rule inj_on_to_predicate)
  using init_no_args
  unfolding list_all_iff by auto
  

lemma filter_props_goal:
  "(filter (\<lambda>p. p \<in> set props_spec) goal_spec) = goal_spec"
  using goal_in_props filter_id_conv by fast

  
(* tp_nta_reduction_spec.planning_lock, tp_nta_reduction_spec.planning_loc, tp_nta_reduction_spec.set_prop_ab, tp_nta_reduction_spec.acts_active, tp_nta_reduction_spec.init_loc *)

definition "planning_lock' = STR ''planning_lock''"

lemma planning_lock_refine:
  "abstr_model_checking.reduction_ref_impl.planning_lock = planning_lock'"
  unfolding abstr_model_checking.reduction_ref_impl.planning_lock_def
  unfolding planning_lock'_def ..

definition "main_auto_init_edge_spec' \<equiv>
(let can_start = Simple_Expressions.bexp.eq (var planning_lock') (exp.const 0); permit_planning = (abstr_model_checking.reduction_ref_impl.planning_lock, exp.const 1); set_active = (abstr_model_checking.reduction_ref_impl.acts_active, exp.const 0);
         set_props = map (abstr_model_checking.reduction_ref_impl.set_prop_ab 1) init_spec'; upds = permit_planning # set_active # set_props
     in (abstr_model_checking.reduction_ref_impl.init_loc, can_start, [], Sil STR '''', upds, [], abstr_model_checking.reduction_ref_impl.planning_loc))
"

lemma main_auto_init_edge_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec = main_auto_init_edge_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec_def
  unfolding main_auto_init_edge_spec'_def
  unfolding filter_props_init 
  ..

definition main_auto_goal_edge_spec'::"nat \<times>
   (String.literal, int) Simple_Expressions.bexp \<times>
   (String.literal, int) acconstraint list \<times>
   String.literal act \<times>
   (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_goal_edge_spec' \<equiv>
(let can_end = [Simple_Expressions.bexp.eq (var abstr_model_checking.reduction_ref_impl.planning_lock) (exp.const 1), Simple_Expressions.bexp.eq (var abstr_model_checking.reduction_ref_impl.acts_active) (exp.const 0)]; 
  goal_sat = map (abstr_model_checking.reduction_ref_impl.is_prop_ab 1) goal_spec;
  cond = abstr_model_checking.reduction_ref_impl.bexp_and_all (can_end @ goal_sat); 
  lock_plan = (abstr_model_checking.reduction_ref_impl.planning_lock, exp.const 2)
in (abstr_model_checking.reduction_ref_impl.planning_loc, cond, [], Sil STR '''', [lock_plan], [], abstr_model_checking.reduction_ref_impl.goal_loc))
"

lemma main_auto_goal_edge_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_spec = main_auto_goal_edge_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_spec_def
  unfolding main_auto_goal_edge_spec'_def
  unfolding filter_props_goal
  ..

definition main_auto_spec'::"nat list \<times>
   nat list \<times>
   (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat) list \<times>
   (nat \<times> (String.literal, int) acconstraint list) list" where
"main_auto_spec' \<equiv>
(let committed_locs = []; 
  urgent_locs = [abstr_model_checking.reduction_ref_impl.init_loc, abstr_model_checking.reduction_ref_impl.goal_loc]; 
  edges = [main_auto_init_edge_spec', main_auto_goal_edge_spec', abstr_model_checking.reduction_ref_impl.main_auto_loop_spec]; 
  invs = [] 
in (committed_locs, urgent_locs, edges, invs))"

lemma main_auto_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_spec = main_auto_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_spec_def
  unfolding main_auto_spec'_def
  unfolding main_auto_init_edge_spec_refine main_auto_goal_edge_spec_refine
  ..

definition "automata_spec' = main_auto_spec' # map action_to_automaton_spec' actions_spec"

lemma automata_spec_refine:
  shows "abstr_model_checking.reduction_ref_impl.automata_spec = automata_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.timed_automaton_net_spec_def
  unfolding automata_spec'_def
  using action_to_automaton_spec_refine main_auto_spec_refine by simp

end
thm ground_ast_problem.action_to_automaton_spec'_def

thm ground_ast_problem.automata_spec'_def

thm ground_ast_problem_defs.init_spec_def

fun to_predicateM where
"to_predicateM (Atom (predAtm x _)) = Error_Monad.return x" |
"to_predicateM x = Error_Monad.error (ERRS ''Not an atomic predicate formula'')"

lemma to_predicateM_return_if[return_if]: 
  "is_predAtom x \<Longrightarrow> ((to_predicateM x = Inr y) \<longleftrightarrow> ground_ast_problem_defs.to_predicate x = y)"
  apply (induction x arbitrary: y rule: ground_ast_problem_defs.to_predicate.induct)
  subgoal apply (subst to_predicateM.simps)
    apply (subst ground_ast_problem_defs.to_predicate.simps)
    by blast
  by simp+

definition init_specM::"ast_problem \<Rightarrow> (unit \<Rightarrow> char list \<Rightarrow> char list) + _" where
"init_specM P \<equiv> do {
  mapM to_predicateM (filter is_predAtom (init P))
}"


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
    have obtain r where
        xs_n_inr: "f (xs ! n) = Inr r" using xs_r n apply (cases "f (xs ! n)") by auto
    have "ys ! n = r" using xs_n_inr ys unfolding comp_def using n by simp
    thus "f (xs ! n) = Inr (ys ! n)" using xs_n_inr by simp
  qed
next
  assume a: "list_all2 (\<lambda>x y. f x = Inr y) xs ys"
  thus "mapM f xs = Inr ys"
    by (induction rule: list_all2_induct) auto
qed


lemma list_all2_return_if[return_if]:
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

lemma init_specM_return_if[return_if]:
  assumes "ground_ast_problem P" 
  shows "(init_specM P = Inr x \<longleftrightarrow> x = ground_ast_problem.init_spec' P)"
  unfolding init_specM_def 
proof -
  show "(mapM to_predicateM (filter is_predAtom (init P)) = Inr x) = (x = ground_ast_problem.init_spec' P)"
    apply (subst mapM_return_iff)
    apply (subst ground_ast_problem.init_spec'_def)
     apply (rule assms)
    apply (rule list_all2_return_if[where P = is_predAtom])
    unfolding list_all_iff using to_predicateM_return_if by auto
qed
  
  
(* tp_nta_reduction_spec.planning_lock, tp_nta_reduction_spec.planning_loc, tp_nta_reduction_spec.set_prop_ab, tp_nta_reduction_spec.acts_active, tp_nta_reduction_spec.init_loc *)

lemma [code]: "ground_ast_problem_defs.prop_to_name_spec = predicate.name"
  unfolding ground_ast_problem_defs.prop_to_name_spec_def by simp

thm tp_nta_reduction_spec.planning_loc_def

definition "planning_lock_specM = "

definition main_auto_init_edge_specM::"_ \<Rightarrow> (unit \<Rightarrow> char list \<Rightarrow> char list) + 
  (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)" where
"main_auto_init_edge_specM P \<equiv> do {
init \<leftarrow> init_specM P;
let can_start = Simple_Expressions.bexp.eq (var tp_nta_reduction_spec.planning_lock) (exp.const 0);
let permit_planning = (tp_nta_reduction_spec.planning_lock, exp.const 1); 
let set_active = (tp_nta_reduction_spec.acts_active, exp.const 0);
let set_props = map (tp_nta_reduction_spec.set_prop_ab ground_ast_problem_defs.prop_to_name_spec 1) init; 
let upds = permit_planning # set_active # set_props;
 Error_Monad.return (tp_nta_reduction_spec.init_loc, can_start, [], Sil STR '''', upds, [], tp_nta_reduction_spec.planning_loc)
}"

value "main_auto_init_edge_specM example_problem" 

thm ground_ast_problem.main_auto_init_edge_spec'_def[no_vars]


definition "main_auto_specM P \<equiv> do {
let committed_locs = []; 
  urgent_locs = [tp_nta_reduction_spec.init_loc, tp_nta_reduction_spec.goal_loc]; 
  edges = [ground_ast_problem.main_auto_init_edge_spec' P, ground_ast_problem.main_auto_goal_edge_spec' P, tp_nta_reduction_spec.main_auto_loop_spec]; 
  invs = [] 
in 
  Error_Monad.return (committed_locs, urgent_locs, edges, invs)
}"

thm ground_ast_problem.main_auto_spec'_def

value "ground_ast_problem.main_auto_spec' example_problem"

definition "automata_specM P \<equiv> do {
  Error_Monad.return (ground_ast_problem.automata_spec' P)
}"

definition make_network where
"make_network P \<equiv> (
  let 
    pre = ground_ast_problem_defs.pre_spec; 
    dels = ground_ast_problem_defs.dels_spec; 
    adds = ground_ast_problem_defs.adds_spec;
    at_start = ground_ast_problem_defs.at_start_spec; 
    at_end = ground_ast_problem_defs.at_end_spec;
    del' = temp_planning_problem_list_defs.del_imp_list at_start at_end dels;
    add' = temp_planning_problem_list_defs.add_imp_list at_start at_end adds; 
    over_all = ground_ast_problem_defs.over_all_spec;
    prop_names = ground_ast_problem_defs.prop_to_name_spec; 
    act_names = ground_ast_problem_defs.act_to_name_spec; 
    actions = ground_ast_problem_defs.actions_spec P;
    props = ground_ast_problem_defs.props_spec P; 
    over_all' = temp_planning_problem_list_defs.over_all_restr_list over_all props;
    pre' = temp_planning_problem_list_defs.pre_imp_restr_list at_start at_end pre props; 
    goal = ground_ast_problem_defs.goal_spec P; 
    init = ground_ast_problem_defs.init_spec P;
    goal' = filter (\<lambda>p. p \<in> set props) goal; 
    init' = filter (\<lambda>p. p \<in> set props) init;
    init_vars = tp_nta_reduction_model_checking.a\<^sub>0 init' goal' AtStart AtEnd over_all' pre' add' del' props actions prop_names;
    vars = tp_nta_reduction_spec.all_vars_spec init' goal' AtStart AtEnd over_all' pre' add' del' props actions prop_names;
    autos = tp_nta_reduction_spec.timed_automaton_net_spec init' goal' AtStart AtEnd over_all' ground_ast_problem_defs.lower_spec ground_ast_problem_defs.upper_spec pre' add' del' 0
     actions act_names prop_names
  in (autos, tp_nta_reduction_spec.broadcast_spec, vars, init_vars, tp_nta_reduction_spec.formula_spec)
)"

definition "make_network_impl1 P \<equiv> do {
  Error_Monad.return (make_network P)
}"


definition "make_network_impl P \<equiv> do {
  check_ground_problem P;
  Error_Monad.return (STR ''123'')
}"

lemma make_network_impl_return_iff[return_iff]:
  "make_network_impl P = Inr x \<longleftrightarrow> undefined"
  apply (subst make_network_impl_def)
  apply (subst context_bind_return_iff')
  sorry

(* Code generation using monads *)

(* Should not need to restrict to list, because we know that all props are in the set of props.
  This would speed everything up by a linear factor.
To do: Use a different locale. *)

thm temp_planning_problem_list_defs.del_imp_list_def

find_theorems name: "mutex_snap_action'"

(* 
Need code equations for:
  tp_nta_reduction_model_checking.a\<^sub>0
  tp_nta_reduction_spec.timed_automaton_net_spec
  ground_ast_problem_defs.prop_to_name_spec
  ground_ast_problem_defs.act_to_name_spec
  ground_ast_problem_defs.over_all_spec
  ground_ast_problem_defs.at_start_spec
  ground_ast_problem_defs.actions_spec
  ground_ast_problem_defs.at_end_spec
  ground_ast_problem_defs.upper_spec
  ground_ast_problem_defs.props_spec
  ground_ast_problem_defs.lower_spec
  tp_nta_reduction_spec.broadcast_spec
  ground_ast_problem_defs.init_spec
  ground_ast_problem_defs.goal_spec
  ground_ast_problem_defs.dels_spec
  ground_ast_problem_defs.adds_spec
  tp_nta_reduction_spec.all_vars_spec
  ground_ast_problem_defs.pre_spec
  tp_nta_reduction_spec.formula_spec
*)

value "ground_ast_problem.automata_spec' example_problem"
value "make_network example_problem"
value "check_ground_problem example_problem"

end
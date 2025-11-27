theory Ground_PDDL_NTA_Reduction_Impl
  imports Ground_PDDL_NTA_Reduction_Correctness 
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Checker"
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


definition "prop_to_var_impl prop_to_name p \<equiv> STR ''var_'' + prop_to_name p"
definition "prop_to_lock_impl prop_to_name p \<equiv> STR ''lock_'' + prop_to_name p"
definition "acts_active_impl \<equiv> STR ''acts_active''"
definition "planning_lock_impl \<equiv> STR ''planning_lock''"

definition "act_to_start_clock_impl act_to_name a \<equiv> STR ''start_'' + act_to_name a"
definition "act_to_end_clock_impl act_to_name a \<equiv> STR ''end_'' + act_to_name a"
definition "urge_clock_impl \<equiv> STR ''urge_clock''"

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


fun lower_spec_impl::"ast_action_schema \<Rightarrow> _" where
"lower_spec_impl (Simple_Action_Schema n ps pre eff) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec_impl (Durative_Action_Schema n ps d cond eff) = map_option (map_lower_bound floor) (dc_list_lower d)"

fun upper_spec_impl::"ast_action_schema \<Rightarrow> _" where
"upper_spec_impl (Simple_Action_Schema n ps pre eff) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec_impl (Durative_Action_Schema n ps d cond eff) = map_option (map_upper_bound floor) (dc_list_upper d)"

definition "l_dur_spec_impl a \<equiv> (case lower_spec_impl a of 
  None \<Rightarrow> [] | Some (lower_bound.GT n) \<Rightarrow> 
    [acconstraint.GT (act_to_start_clock_impl ast_action_schema.name a) n]
| Some (lower_bound.GE n) \<Rightarrow> 
    [acconstraint.GE (act_to_start_clock_impl ast_action_schema.name a) n])"


definition "u_dur_spec_impl a \<equiv> (case upper_spec_impl a of 
  None \<Rightarrow> [] | Some (upper_bound.LT n) \<Rightarrow> 
    [acconstraint.LT (act_to_start_clock_impl ast_action_schema.name a) n]
| Some (upper_bound.LE n) \<Rightarrow> 
    [acconstraint.LE (act_to_start_clock_impl ast_action_schema.name a) n])"

definition main_auto_loop_spec_impl::"(nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)" where
"main_auto_loop_spec_impl \<equiv> (goal_loc_impl, bexp.true, [], Sil STR '''', [], [], goal_loc_impl)"


context ground_ast_problem_defs
begin

text \<open>We define the code that generates the automata\<close>

definition "mutex_snap_action' a b = 
  action_defs.mutex_snap_action (\<lambda>a. set (imp_defs.rat_impl.pre_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.add_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.del_imp_list a)) a b"

definition "int_clocks_spec' a =
    map (act_to_start_clock_impl ast_action_schema.name) (filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec) 
  @ map (act_to_end_clock_impl ast_action_schema.name) (filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec)"

definition "start_edge_spec' a = 
(let start_snap = AtStart a; guard = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' start_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' start_snap);
  not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list start_snap)) (imp_defs.rat_impl.del_imp_list start_snap)); 
  pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list start_snap);
  var_check = bexp_and_all (not_locked_check @ pre_check); 
  add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list start_snap); 
  del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list start_snap);
  upds = (inc_var 1 acts_active_impl) # del_upds @ add_upds; 
  resets = [act_to_start_clock_impl ast_action_schema.name a]
 in (off_loc_impl, var_check, guard, Sil STR '''', upds, resets, starting_loc_impl))"

definition "edge_2_spec' a =
(let 
  check_invs = bexp_and_all (map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (over_all_spec a));
  upds = map ((inc_var 1 \<circ>\<circ> prop_to_lock_impl) predicate.name) (over_all_spec a)
in (starting_loc_impl, check_invs, [], Sil STR '''', upds, [], running_loc_impl))"

definition "edge_3_spec' a =
(let 
  end_snap = AtEnd a; 
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' end_snap); 
  guard = l_dur_spec_impl a @ u_dur_spec_impl a @ int_clocks;
  upds = map ((inc_var (- 1) \<circ>\<circ> prop_to_lock_impl) predicate.name) (over_all_spec a); 
  resets = [act_to_end_clock_impl ast_action_schema.name a]
in (running_loc_impl, bexp.true, guard, Sil STR '''', upds, resets, ending_loc_impl))"

definition "end_edge_spec' a =
(let 
  end_instant = ending_loc_impl; 
  off = off_loc_impl; 
  end_snap = AtEnd a; 
  not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list end_snap)) (imp_defs.rat_impl.del_imp_list end_snap));
  pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list end_snap); 
  check = bexp_and_all (not_locked_check @ pre_check);
  add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list end_snap); 
  del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list end_snap);
  upds = inc_var (- 1) acts_active_impl # del_upds @ add_upds
in (end_instant, check, [], Sil STR '''', upds, [], off))"


definition "instant_trans_edge_spec' a =
(let 
  end_snap = AtEnd a; 
  start_snap = AtStart a; 
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' end_snap); 
  guard = l_dur_spec_impl a @ u_dur_spec_impl a @ int_clocks;
 resets = [act_to_end_clock_impl ast_action_schema.name a]
in (starting_loc_impl, bexp.true, guard, Sil STR '''', [], resets, ending_loc_impl))"


definition "action_to_automaton_spec' a =
(let committed_locs = []; 
  urgent_locs = [starting_loc_impl, ending_loc_impl]; 
  edges = [start_edge_spec' a, edge_2_spec' a, edge_3_spec' a, end_edge_spec' a, instant_trans_edge_spec' a];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

text \<open>We do the same for the main automaton\<close>

definition "init_spec' = (map to_predicate (filter is_predAtom (init P)))"

definition "main_auto_init_edge_spec' \<equiv>
(let can_start = var_is 0 planning_lock_impl;
  permit_planning = set_var 1 planning_lock_impl; 
  set_active = set_var 0 acts_active_impl;
  set_props = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) init_spec'; 
  upds = permit_planning # set_active # set_props
in (init_loc_impl, can_start, [], Sil STR '''', upds, [], planning_loc_impl))
"

definition main_auto_goal_edge_spec'::"nat \<times>
   (String.literal, int) Simple_Expressions.bexp \<times>
   (String.literal, int) acconstraint list \<times>
   String.literal act \<times>
   (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_goal_edge_spec' \<equiv>
(let 
  can_end = [var_is 1 planning_lock_impl, var_is 0 acts_active_impl]; 
  goal_sat = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) goal_spec;
  cond = bexp_and_all (can_end @ goal_sat); 
  lock_plan = (planning_lock_impl, exp.const 2)
in (planning_loc_impl, cond, [], Sil STR '''', [lock_plan], [], goal_loc_impl))
"

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
  urgent_locs = [init_loc_impl, goal_loc_impl]; 
  edges = [main_auto_init_edge_spec', main_auto_goal_edge_spec', main_auto_loop_spec_impl]; 
  invs = [] 
in (committed_locs, urgent_locs, edges, invs))"

definition "automata_spec' = main_auto_spec' # map action_to_automaton_spec' actions_spec"

end


find_theorems "finite ?x \<Longrightarrow> inj ?f \<Longrightarrow> finite ?y"
find_theorems name: "infinite*UNIV"

lemma UNIV_predicate:
  "(UNIV::predicate set) = Pred ` (UNIV::String.literal set)"
  apply (intro equalityI subsetI UNIV_I)
  subgoal for x
    unfolding UNIV_def 
    apply (cases x)
    by blast
  done

lemma inifinite_UNIV_literalI:
  "infinite (UNIV::String.literal set)"
proof (rule notI)
  assume "finite (UNIV::String.literal set)"
  moreover
  have "inj (\<lambda>l::String.literal. (STR ''x'') + l)"
    apply (rule injI)
    apply (subst (asm) String.add_literal_code)+
    using String.Literal_eq_iff by simp
  ultimately
  have "surj (\<lambda>l::String.literal. (STR ''x'') + l)"
    using finite_UNIV_inj_surj by blast
  then obtain s where "STR '''' = STR ''x'' + s" by (rule surjE)
  thus False by (simp add: String.add_literal_code String.Literal_eq_iff)
qed


find_theorems "infinite (?f ` ?x)"

lemma range_inj_infinite:
  assumes "infinite S"
      and "inj f"
    shows "infinite (f ` S)"
proof
  assume a: "finite (f ` S)"
  have "f -` (f ` S) = S" using \<open>inj f\<close> inj_vimage_image_eq by simp
  moreover
  have "finite (f -` (f ` S))" using finite_vimageI a \<open>inj f\<close> by blast
  ultimately
  have "finite S" by auto
  with \<open>infinite S\<close>
  show False by simp
qed

lemma infinite_UNIV_predicateI:
  "infinite (UNIV::predicate set)"
  apply (subst UNIV_predicate)
  apply (rule range_inj_infinite)
   apply (rule inifinite_UNIV_literalI)
  apply (rule injI)
  by blast

instantiation predicate :: card_UNIV
begin 
definition "finite_UNIV = Phantom(predicate) False"
definition "card_UNIV = Phantom(predicate) 0"
instance by intro_classes (simp_all add: finite_UNIV_predicate_def card_UNIV card_UNIV_predicate_def infinite_UNIV_predicateI)
end

find_theorems name: "proper_int*char"

find_theorems name: "ord*list"

find_theorems name: "less*liter"

find_theorems "List.ord.lexordp"

instantiation String.literal :: proper_interval
begin
value "String.digit7 (Char True True True True True True True False)"
value "String.ascii_of (Char True True True True True True True False)"

fun char_less_one::"char \<Rightarrow> char \<Rightarrow> bool"where
"char_less_one c d = (of_char d - of_char c > (0::nat))"

fun list_less_one::"char list \<Rightarrow> char list \<Rightarrow> bool" where
"list_less_one _ [] = False" |
"list_less_one [] (y#ys) = (char_less_one (CHR 0x00) y \<or> length ys > 0)" |
"list_less_one [x] (y#ys) = (char_less_one x (CHR 0x7F) \<or> list_less_one [] ys)" |
"list_less_one (x#xs) (y#ys) = (char_less_one x y \<or> list_less_one xs ys)"


fun proper_interval_literal::"String.literal option \<Rightarrow> String.literal option \<Rightarrow> bool" where
"proper_interval_literal None None = True" |
"proper_interval_literal (Some s) None = True" |
"proper_interval_literal None (Some s) = (s \<noteq> (STR ''''))" |
"proper_interval_literal (Some s) (Some t) = (list_less_one (literal.explode s) (literal.explode t))"

instance 
proof
  show "proper_interval None (None::String.literal option) = True" by simp
  show "\<And>y::String.literal. proper_interval None (Some y) = (\<exists>z. z < y)"
  proof
    fix y::"String.literal"
    assume "proper_interval None (Some y)"
    hence yn: "y \<noteq> STR ''''" by simp
    hence "literal.explode y \<noteq> []" 
      using literal.explode_inject zero_literal.rep_eq by metis
    then obtain c cs where
      xy: "literal.explode y = c # cs" apply (cases "literal.explode y") by simp+
    have "STR '''' < y" using xy zero_literal.rep_eq 
      apply (subst less_literal.rep_eq) by auto
    thus "\<exists>z. z < y" by fast
  next
    fix y::"String.literal"
    assume "\<exists>z. z < y"
    then obtain z where
      le: "z < y" by blast
    {
      assume "y = (STR '''')"
      hence "y \<le> z"
        apply (cases "literal.explode z")
        using zero_literal.rep_eq
        using less_eq_literal.rep_eq
        by auto
      hence False using le by force
    }
    thus "proper_interval None (Some y)" by auto
  qed
  show "\<And>x::String.literal. proper_interval (Some x) None = (\<exists>z. x < z)" 
  proof -
    fix x::"String.literal"
    { have "literal.explode STR ''x'' \<noteq> []"
      proof 
        assume "literal.explode STR ''x'' = []"
        hence "literal.explode STR ''x'' = literal.explode STR ''''"
          using literal.explode_inject zero_literal.rep_eq by auto
        thus False using literal.explode_inject by auto
      qed
      hence "x < x + STR ''x''"
        apply (subst less_literal.rep_eq)
        apply (subst plus_literal.rep_eq)
        apply (rule ord.lexordp_append_rightI)
        by blast
      hence "\<exists>z. x < z" by blast
    }
    thus "proper_interval (Some x) None = (\<exists>z. x < z)" by force
  qed
  show "\<And>x y::String.literal. proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)"
  proof -
    fix x y::String.literal
    {
      assume "proper_interval (Some x) (Some y)" 
      hence undefined unfolding proper_interval_literal.simps
      have "\<exists>z>x. z < y" sorry
    }
    moreover 
    {
      assume "\<exists>z>x. z < y"
      have "proper_interval (Some x) (Some y)" sorry
    }
    ultimately
    show "proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)" by blast
  qed
qed
end


value "STR '''' < STR ''a''"

instantiation predicate :: proper_interval
begin
fun proper_interval_predicate::"predicate option \<Rightarrow> predicate option \<Rightarrow> bool" where
"proper_interval_predicate None None = True" |
"proper_interval_predicate (Some p) None = undefined" |
"proper_interval_predicate None (Some p) = undefined" |
"proper_interval_predicate (Some p) (Some q) = undefined"
end

instantiation predicate :: cproper_interval
begin
  
end

print_derives

lemmas ground_ast_problem_code =
  ground_ast_problem_defs.at_start_spec.simps
  ground_ast_problem_defs.at_end_spec.simps
  ground_ast_problem_defs.actions_spec_def
  ground_ast_problem_defs.mutex_snap_action'_def
  ground_ast_problem_defs.int_clocks_spec'_def
  ground_ast_problem_defs.start_edge_spec'_def
  ground_ast_problem_defs.edge_2_spec'_def
  ground_ast_problem_defs.edge_3_spec'_def
  ground_ast_problem_defs.instant_trans_edge_spec'_def
  ground_ast_problem_defs.action_to_automaton_spec'_def
  ground_ast_problem_defs.init_spec'_def
  ground_ast_problem_defs.main_auto_init_edge_spec'_def
  ground_ast_problem_defs.main_auto_goal_edge_spec'_def
  ground_ast_problem_defs.main_auto_spec'_def
  ground_ast_problem_defs.automata_spec'_def

declare ground_ast_problem_code[code]


context ground_ast_problem
begin

subsection \<open>Refinement to monadic code\<close>

text \<open>Some constants need executable copies\<close>

(* tp_nta_reduction_spec.planning_loc, tp_nta_reduction_spec.set_prop_ab, tp_nta_reduction_spec.acts_active, tp_nta_reduction_spec.init_loc *)

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
  "abstr_model_checking.reduction_ref_impl.act_to_start_clock = act_to_start_clock_impl ast_action_schema.name"
  unfolding abstr_model_checking.reduction_ref_impl.act_to_start_clock_def
  unfolding act_to_name_spec_def
  unfolding act_to_start_clock_impl_def
  ..

lemma act_to_end_clock_refine:
  "abstr_model_checking.reduction_ref_impl.act_to_end_clock = act_to_end_clock_impl ast_action_schema.name"
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
    apply (cases x)
    by simp+
  done

lemma upper_spec_refine:
  "upper_spec = upper_spec_impl"
  apply (intro ext)
  subgoal for x
    apply (cases x)
    by simp+
  done

schematic_goal l_dur_spec_refine:
  "abstr_model_checking.reduction_ref_impl.l_dur_spec = l_dur_spec_impl"
  apply (intro ext)
  unfolding abstr_model_checking.reduction_ref_impl.l_dur_spec_def
  unfolding lower_spec_refine
  unfolding act_to_start_clock_refine
  unfolding l_dur_spec_impl_def
  ..

schematic_goal u_dur_spec_refine:
  "abstr_model_checking.reduction_ref_impl.u_dur_spec = u_dur_spec_impl"
  apply (intro ext)
  unfolding abstr_model_checking.reduction_ref_impl.u_dur_spec_def
  unfolding upper_spec_refine
  unfolding act_to_start_clock_refine
  unfolding u_dur_spec_impl_def
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
    unfolding act_to_start_clock_refine
    unfolding act_to_end_clock_refine
    by blast
qed

lemma start_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.start_edge_spec a = start_edge_spec' a" 
  unfolding start_edge_spec'_def
  unfolding abstr_model_checking.reduction_ref_impl.start_edge_spec_def
  unfolding is_prop_lock_ab_refine
  unfolding is_prop_ab_refine
  unfolding set_prop_ab_refine
  unfolding acts_active_refine
  unfolding off_loc_refine starting_loc_refine
  unfolding act_to_start_clock_refine
  using int_clocks_spec_refine assms pre_imp_restr_equiv_pre_imp
  by simp


lemma edge_2_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_2_spec a = edge_2_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_2_spec_def 
  unfolding is_prop_ab_refine
  unfolding inc_prop_lock_ab_refine
  unfolding starting_loc_refine running_loc_refine
  unfolding edge_2_spec'_def
  using over_all_restr_equiv_over_all assms
  by simp

lemma edge_3_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_3_spec a = edge_3_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_3_spec_def
  unfolding edge_3_spec'_def
  unfolding running_loc_refine
  unfolding ending_loc_refine
  unfolding act_to_end_clock_refine
  unfolding inc_prop_lock_ab_refine
  unfolding l_dur_spec_refine u_dur_spec_refine
  using int_clocks_spec_refine assms over_all_restr_equiv_over_all
  by simp


lemma end_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.end_edge_spec a = end_edge_spec' a"
  unfolding abstr_model_checking.reduction_ref_impl.end_edge_spec_def
  unfolding ending_loc_refine off_loc_refine
  unfolding is_prop_ab_refine
  unfolding is_prop_lock_ab_refine
  unfolding set_prop_ab_refine
  unfolding acts_active_refine
  unfolding end_edge_spec'_def
  using pre_imp_restr_equiv_pre_imp assms
  by auto


lemma instant_trans_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.instant_trans_edge_spec a = instant_trans_edge_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.instant_trans_edge_spec_def
  unfolding instant_trans_edge_spec'_def
  unfolding starting_loc_refine ending_loc_refine
  unfolding l_dur_spec_refine u_dur_spec_refine
  unfolding act_to_end_clock_refine
  using int_clocks_spec_refine assms
  by simp


lemma action_to_automaton_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.action_to_automaton_spec a = action_to_automaton_spec' a"
  unfolding abstr_model_checking.reduction_ref_impl.action_to_automaton_spec_def
  unfolding action_to_automaton_spec'_def
  unfolding starting_loc_refine ending_loc_refine
  using start_edge_spec_refine edge_2_spec_refine edge_3_spec_refine end_edge_spec_refine instant_trans_edge_spec_refine assms
  by simp


text \<open>Now we provide an equivalent definition of the main automaton.\<close>


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

  
lemma main_auto_init_edge_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec = main_auto_init_edge_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec_def
  unfolding main_auto_init_edge_spec'_def
  unfolding filter_props_init planning_lock_refine
  unfolding planning_loc_refine
  unfolding init_loc_refine
  unfolding acts_active_refine
  unfolding set_prop_ab_refine
  ..

lemma main_auto_goal_edge_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_spec = main_auto_goal_edge_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_spec_def
  unfolding main_auto_goal_edge_spec'_def
  unfolding filter_props_goal
  unfolding planning_loc_refine
  unfolding goal_loc_refine
  unfolding acts_active_refine
  unfolding planning_lock_refine
  unfolding is_prop_ab_refine
  ..

lemma main_auto_loop_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_loop_spec = main_auto_loop_spec_impl"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_loop_spec_def
  unfolding main_auto_loop_spec_impl_def
  unfolding goal_loc_refine ..

lemma main_auto_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_spec = main_auto_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_spec_def
  unfolding main_auto_spec'_def
  unfolding main_auto_init_edge_spec_refine main_auto_goal_edge_spec_refine
  unfolding main_auto_loop_spec_refine
  unfolding init_loc_refine goal_loc_refine
  ..


text \<open>Finally we can provide another definition of the entire network\<close>

lemma automata_spec_refine:
  shows "abstr_model_checking.reduction_ref_impl.automata_spec = automata_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.timed_automaton_net_spec_def
  unfolding automata_spec'_def
  using action_to_automaton_spec_refine main_auto_spec_refine by simp

end

text \<open>We will now refine the code to monadic implementations. \<close>

definition init_specM::"ast_problem \<Rightarrow> (unit \<Rightarrow> char list \<Rightarrow> char list) + _" where
"init_specM P \<equiv> do {
  Error_Monad.return (map to_predicate (filter is_predAtom (init P)))
}"


lemma init_specM_return_if:
  assumes "ground_ast_problem P" 
  shows "(init_specM P = Inr x \<longleftrightarrow> x = ground_ast_problem.init_spec' P)"
  unfolding init_specM_def
  apply (subst ground_ast_problem.init_spec'_def)
  using assms by blast+

value "ground_ast_problem_defs.init_spec' example_problem"


definition goal_specM::"ast_problem \<Rightarrow> (unit \<Rightarrow> string \<Rightarrow> string) + _" where
"goal_specM P \<equiv> do {
  Error_Monad.return (remdups (map to_predicate (to_literals (goal P))))
}"


lemma goal_specM_return_if:
  assumes "ground_ast_problem P"
  shows "goal_specM P = Inr x \<longleftrightarrow> x = ground_ast_problem_defs.goal_spec P"
  unfolding goal_specM_def
  using assms ground_ast_problem_defs.goal_spec_def
  by fastforce
  

lemma [code]: "ground_ast_problem_defs.prop_to_name_spec = predicate.name"
  unfolding ground_ast_problem_defs.prop_to_name_spec_def by simp


definition main_auto_init_edge_specM::"_ \<Rightarrow> 
  (unit \<Rightarrow> char list \<Rightarrow> char list) + 
  (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)" where
"main_auto_init_edge_specM P \<equiv> do {
init \<leftarrow> init_specM P;
let can_start = var_is 0 planning_lock_impl;
let permit_planning = set_var 1 planning_lock_impl; 
let set_active = set_var 0 acts_active_impl;
let set_props = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) init; 
let upds = permit_planning # set_active # set_props;
 Error_Monad.return (init_loc_impl, can_start, [], Sil STR '''', upds, [], planning_loc_impl)
}"

value "main_auto_init_edge_specM example_problem"

lemma main_auto_init_edge_specM_return_if:
  assumes "ground_ast_problem P"
  shows "main_auto_init_edge_specM P = Inr x \<longleftrightarrow> x = ground_ast_problem.main_auto_init_edge_spec' P"
  unfolding main_auto_init_edge_specM_def
  apply (subst ground_ast_problem.main_auto_init_edge_spec'_def[OF assms])
  unfolding init_specM_return_if[OF assms] return_iff 
  by auto

definition main_auto_goal_edge_specM::"_ \<Rightarrow> (unit \<Rightarrow> char list \<Rightarrow> char list) + 
  (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)" where
"main_auto_goal_edge_specM P \<equiv> do {
goal' \<leftarrow> goal_specM P;
let can_end = [var_is 1 planning_lock_impl, var_is 0 acts_active_impl]; 
let goal_sat = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) goal';
let cond = bexp_and_all (can_end @ goal_sat); 
let lock_plan = (planning_lock_impl, exp.const 2);
Error_Monad.return (planning_loc_impl, cond, [], Sil STR '''', [lock_plan], [], goal_loc_impl)
}"

value "main_auto_goal_edge_specM example_problem"

lemma main_auto_goal_edge_specM_return_if:
  assumes "ground_ast_problem P"
  shows "main_auto_goal_edge_specM P = Inr x \<longleftrightarrow> x = ground_ast_problem.main_auto_goal_edge_spec' P"
  unfolding main_auto_goal_edge_specM_def
  apply (subst ground_ast_problem.main_auto_goal_edge_spec'_def[OF assms])
  unfolding goal_specM_return_if[OF assms] return_iff 
  by auto


thm temp_planning_problem_list_defs.add_imp_list_def

find_theorems name: "start_edge_spec'"

(* (unit \<Rightarrow> char list \<Rightarrow> char list) + 
  (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)
*)

definition main_auto_specM::"_ \<Rightarrow> (unit \<Rightarrow> string \<Rightarrow> string) +
  (nat list \<times>
      nat list \<times>
      (nat \<times>
       (String.literal, int) Simple_Expressions.bexp \<times>
       (String.literal, int) acconstraint list \<times>
       String.literal act \<times>
       (String.literal \<times> (String.literal, int) exp) list \<times>
       String.literal list \<times> nat) list \<times>
      (nat \<times> (String.literal, int) acconstraint list) list)" where
"main_auto_specM P \<equiv> 
do {
  
  init_edge \<leftarrow> main_auto_init_edge_specM P;
  goal_edge \<leftarrow> main_auto_goal_edge_specM P;
  let loop_edge = main_auto_loop_spec_impl;
  let committed_locs = ([]::nat list); 
  let urgent_locs = [init_loc_impl, goal_loc_impl];
  let edges = [init_edge, goal_edge, loop_edge]; 
  let invs = [];
  Error_Monad.return (committed_locs, urgent_locs, edges, invs)
}"

thm ground_ast_problem.main_auto_spec'_def

value "main_auto_specM example_problem"

lemma main_auto_specM_return_if:
  assumes "ground_ast_problem P"
  shows "main_auto_specM P = Inr x \<longleftrightarrow> x = ground_ast_problem.main_auto_spec' P"
  unfolding main_auto_specM_def
  unfolding ground_ast_problem.main_auto_spec'_def[OF assms]
  by (auto simp: return_iff main_auto_init_edge_specM_return_if[OF assms] main_auto_goal_edge_specM_return_if[OF assms])

text \<open>We have provided a monadic definition of the main automaton. Now, we will provide one for the 
other automata.\<close>


code_thms ground_ast_problem_defs.at_start_spec
value "ground_ast_problem_defs.at_start_spec"

find_theorems name: "ground_ast_problem.start_edge_spec'_def"

definition start_edge_specM where
"start_edge_specM P a \<equiv> do {
let start_snap = AtStart a; 
let guard = map (\<lambda>x. acconstraint.GT x 0) (ground_ast_problem_defs.int_clocks_spec' start_snap) @ map (\<lambda>x. acconstraint.GE x 0) (ground_ast_problem_defs.int_clocks_spec' start_snap);
let not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list start_snap)) (imp_defs.rat_impl.del_imp_list start_snap)); 
let pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list start_snap);
let var_check = bexp_and_all (not_locked_check @ pre_check); 
let add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list start_snap); 
let del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list start_snap);
let upds = (inc_var 1 acts_active_impl) # del_upds @ add_upds; 
let resets = [act_to_start_clock_impl ast_action_schema.name a];
Error_Monad.return (off_loc_impl, var_check, guard, Sil STR '''', upds, resets, starting_loc_impl)
}"


value "ground_ast_problem_defs.automata_spec' example_problem"

definition "automata_specM P \<equiv> do {
  Error_Monad.return (ground_ast_problem_defs.automata_spec' P)
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
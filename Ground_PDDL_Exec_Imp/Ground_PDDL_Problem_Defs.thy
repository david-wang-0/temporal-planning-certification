theory Ground_PDDL_Problem_Defs
  imports "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics"
    "TP_NTA_Reduction.TP_NTA_Reduction_Model_Checking"
begin

instantiation lower_bound::(linorder) linorder
begin
fun less_eq_lower_bound::"('a::linorder) lower_bound \<Rightarrow> ('a::linorder) lower_bound \<Rightarrow> bool" where
"less_eq_lower_bound (lower_bound.GE x) (lower_bound.GE y) = (x \<le> y)" |
"less_eq_lower_bound (lower_bound.GE x) (lower_bound.GT y) = (x \<le> y)" |
"less_eq_lower_bound (lower_bound.GT x) (lower_bound.GE y) = (x < y)" |
"less_eq_lower_bound (lower_bound.GT x) (lower_bound.GT y) = (x \<le> y)"

fun less_lower_bound::"('a::linorder) lower_bound \<Rightarrow> ('a::linorder) lower_bound \<Rightarrow> bool"  where
"less_lower_bound (lower_bound.GE x) (lower_bound.GE y) = (x < y)" |
"less_lower_bound (lower_bound.GE x) (lower_bound.GT y) = (x \<le> y)" |
"less_lower_bound (lower_bound.GT x) (lower_bound.GE y) = (x < y)" |
"less_lower_bound (lower_bound.GT x) (lower_bound.GT y) = (x < y)"
instance 
proof 
  fix x y::"('a::linorder) lower_bound"
  show "(x < y) = (x \<le> y \<and> \<not>y \<le> x)" 
    by (cases x; cases y) auto
next
  fix x::"('a::linorder) lower_bound"
  show "x \<le> x" by (cases x) auto
next 
  fix x y z::"('a::linorder) lower_bound"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) auto
next
  fix x y::"('a::linorder) lower_bound"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) auto
next
  fix x y::"('a::linorder) lower_bound"
  show "x \<le> y \<or> y \<le> x "
    by (cases x; cases y) auto
qed
end

instantiation upper_bound::(linorder) linorder
begin
fun less_eq_upper_bound::"('a::linorder) upper_bound \<Rightarrow> ('a::linorder) upper_bound \<Rightarrow> bool" where
"less_eq_upper_bound (upper_bound.LT x) (upper_bound.LT y) = (x \<le> y)" |
"less_eq_upper_bound (upper_bound.LT x) (upper_bound.LE y) = (x \<le> y)" |
"less_eq_upper_bound (upper_bound.LE x) (upper_bound.LT y) = (x < y)" |
"less_eq_upper_bound (upper_bound.LE x) (upper_bound.LE y) = (x \<le> y)"

fun less_upper_bound::"('a::linorder) upper_bound \<Rightarrow> ('a::linorder) upper_bound \<Rightarrow> bool"  where
"less_upper_bound (upper_bound.LT x) (upper_bound.LT y) = (x < y)" |
"less_upper_bound (upper_bound.LT x) (upper_bound.LE y) = (x \<le> y)" |
"less_upper_bound (upper_bound.LE x) (upper_bound.LT y) = (x < y)" |
"less_upper_bound (upper_bound.LE x) (upper_bound.LE y) = (x < y)"
instance 
proof 
  fix x y::"('a::linorder) upper_bound"
  show "(x < y) = (x \<le> y \<and> \<not>y \<le> x)" 
    by (cases x; cases y) auto
next
  fix x::"('a::linorder) upper_bound"
  show "x \<le> x" by (cases x) auto
next 
  fix x y z::"('a::linorder) upper_bound"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) auto
next
  fix x y::"('a::linorder) upper_bound"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) auto
next
  fix x y::"('a::linorder) upper_bound"
  show "x \<le> y \<or> y \<le> x "
    by (cases x; cases y) auto
qed
end

fun comp_opt_le::"('a::linorder) option \<Rightarrow> ('a::linorder) option \<Rightarrow> bool" where
"comp_opt_le None None = True" |
"comp_opt_le None (Some x) = False" |
"comp_opt_le (Some x) None = True" |
"comp_opt_le (Some x) (Some y) = (x \<le> y)" 

fun comp_opt_ge::"('a::linorder) option \<Rightarrow> ('a::linorder) option \<Rightarrow> bool" where
"comp_opt_ge None None = True" |
"comp_opt_ge None (Some x) = False" |
"comp_opt_ge (Some x) None = True" |
"comp_opt_ge (Some x) (Some y) = (x \<ge> y)"

locale ground_ast_problem_defs = ast_problem P
  for P :: ast_problem
begin

lemma (in ast_problem) wf_fmla_atom_imp_is_predAtom:
  assumes "wf_fmla_atom M a"
  shows "is_predAtom a"
  using assms by (induction a rule: wf_fmla_atom.induct) auto

definition "props_spec \<equiv> map pred (predicates D)"

definition "prop_to_name_spec \<equiv> predicate.name"

definition "actions_spec \<equiv> actions D"

definition "act_to_name_spec \<equiv> ast_action_schema.name"


fun to_predicate::"object atom Formulas.formula \<Rightarrow> predicate" where
"to_predicate (Atom (predAtm x _)) = x"

fun to_literals::"object atom Formulas.formula \<Rightarrow> object atom Formulas.formula list" where
"to_literals (Atom (predAtm x as)) = [Atom (predAtm x as)]" |
"to_literals (x \<^bold>\<and> y) = to_literals x @ to_literals y" |
"to_literals (\<^bold>\<not>\<bottom>) = []"

definition "to_predicates \<equiv> to_literals #> map to_predicate"

definition init_spec::"predicate list" where
"init_spec \<equiv>
  init P
  |> map to_predicate
  |> remdups"


(* To do: ensure that this consists of predicates only *)
definition goal_spec::"predicate list" where
  "goal_spec \<equiv> 
  goal P
  |> to_literals
  |> map to_predicate
  |> remdups"

definition "non_ground_action n anno \<equiv> Ground_Action n anno (Formulas.Not Formulas.Bot) (Effect [] [])"


fun at_start_spec::"ast_action_schema \<Rightarrow> ground_action" where
"at_start_spec (Simple_Action_Schema n ps pre eff) = instantiate_action_schema (Simple_Action_Schema n ps pre eff) [] At_Start" |
"at_start_spec (Durative_Action_Schema n ps d cond eff) = inst_snap_action (Durative_Action_Schema n ps d cond eff) [] At_Start"

fun at_end_spec::"ast_action_schema \<Rightarrow> ground_action" where
"at_end_spec (Simple_Action_Schema n ps pre eff) = non_ground_action n At_End" |
"at_end_spec (Durative_Action_Schema n ps d cond eff) = inst_snap_action (Durative_Action_Schema n ps d cond eff) [] At_End"

fun over_all_snap::"ast_action_schema \<Rightarrow> ground_action" where
"over_all_snap (Simple_Action_Schema n ps pre eff) = 
   non_ground_action n Over_All" |
"over_all_snap (Durative_Action_Schema n ps d cond eff) = 
  inst_snap_action (Durative_Action_Schema n ps d cond eff) [] Over_All"

fun pre_spec::"ground_action \<Rightarrow> predicate list" where
"pre_spec (Ground_Action n anno form eff) = 
  form
  |> to_literals
  |> map to_predicate
  |> remdups"

fun over_all_spec::"ast_action_schema \<Rightarrow> predicate list" where
"over_all_spec x =
  x
  |> over_all_snap
  |> pre_spec"

fun adds_spec::"ground_action \<Rightarrow> predicate list" where
"adds_spec (Ground_Action n anno form eff) =
  eff
  |> ast_effect.adds
  |> map to_predicate
  |> remdups
"

fun dels_spec::"ground_action \<Rightarrow> predicate list" where
"dels_spec (Ground_Action n anno form eff) =
  eff
  |> ast_effect.dels
  |> map to_predicate
  |> remdups
"

fun dc_to_lb::"term duration_constraint \<Rightarrow> rat lower_bound option" where
"dc_to_lb No_Const = None" |
"dc_to_lb (Time_Const duration_op.EQ x) = Some (lower_bound.GE x)" |
"dc_to_lb (Time_Const duration_op.GEQ x) = Some (lower_bound.GE x)" |
"dc_to_lb (Time_Const duration_op.LEQ x) = None"

fun max_lb_opt::"('x::linorder) lower_bound option list \<Rightarrow> ('x::linorder) lower_bound option \<Rightarrow> ('x::linorder) lower_bound option" where
"max_lb_opt [] l = l" |
"max_lb_opt (x#xs) l = max_lb_opt xs (if (comp_opt_ge x l) then x else l)"

definition dc_list_lower::"term duration_constraint list \<Rightarrow> rat lower_bound option" where
"dc_list_lower xs \<equiv> map dc_to_lb xs |> (\<lambda>xs. max_lb_opt xs None)" 


fun dc_to_ub::"term duration_constraint \<Rightarrow> rat upper_bound option" where
"dc_to_ub No_Const = None" |
"dc_to_ub (Time_Const duration_op.EQ x) = Some (upper_bound.LE  x)" |
"dc_to_ub (Time_Const duration_op.GEQ x) = None" |
"dc_to_ub (Time_Const duration_op.LEQ x) = Some (upper_bound.LE x)"

fun min_ub_opt::"('x::linorder) upper_bound option list \<Rightarrow> ('x::linorder) upper_bound option \<Rightarrow> ('x::linorder) upper_bound option" where
"min_ub_opt [] u = u" |
"min_ub_opt (x#xs) u = min_ub_opt xs (if (comp_opt_le x u) then x else u)"

definition dc_list_upper::"term duration_constraint list \<Rightarrow> rat upper_bound option" where
"dc_list_upper xs = map dc_to_ub xs |> (\<lambda>xs. min_ub_opt xs None)" 

fun lower_spec::"ast_action_schema \<Rightarrow> _" where
"lower_spec (Simple_Action_Schema n ps pre eff) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec (Durative_Action_Schema n ps d cond eff) = map_option (map_lower_bound floor) (dc_list_lower d)"

fun upper_spec::"ast_action_schema \<Rightarrow> _" where
"upper_spec (Simple_Action_Schema n ps pre eff) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec (Durative_Action_Schema n ps d cond eff) = map_option (map_upper_bound floor) (dc_list_upper d)"

subsection \<open>Additional well-formedness considerations\<close>

text \<open>Begin: Adapted from Maximillian Vollath\<close>
fun is_pos_lit :: "'a atom Formulas.formula \<Rightarrow> bool" where
  f: "is_pos_lit (\<^bold>\<not>\<bottom>) = True" |
  "is_pos_lit (Atom (predAtm n args)) = True" |
  "is_pos_lit _ = False"

fun is_pos_conj :: "'a atom Formulas.formula \<Rightarrow> bool" where
  "is_pos_conj (f \<^bold>\<and> g) \<longleftrightarrow> is_pos_conj f \<and> is_pos_conj g" |
  "is_pos_conj f \<longleftrightarrow> is_pos_lit f"
(* This does not have to be right recursive for our purposes. It originally was *) 

text \<open>End: Adapted from M. Vollath\<close>

fun atom_no_args::"'a atom \<Rightarrow> bool" where
"atom_no_args (predAtm p []) = True" |
"atom_no_args _ = False"

definition form_preds_no_args::"'a atom Formulas.formula \<Rightarrow> bool" where
"form_preds_no_args form \<equiv> \<forall>a \<in> formula.atoms form. atom_no_args a"

fun pred_no_args::"predicate_decl \<Rightarrow> bool" where
"pred_no_args (PredDecl p as) = (as = [])"

fun act_no_params::"ast_action_schema \<Rightarrow> bool" where
"act_no_params (Simple_Action_Schema n ps pre eff) = (ps = [])" |
"act_no_params (Durative_Action_Schema n ps d pre eff) = (ps = [])" 

fun act_pres_pos::"ast_action_schema \<Rightarrow> bool" where
"act_pres_pos (Simple_Action_Schema n ps pre eff) = (is_pos_conj (pre))" |
"act_pres_pos (Durative_Action_Schema n ps d pre eff) = (list_all is_pos_conj (map snd pre))"

fun act_no_func_dcs::"ast_action_schema \<Rightarrow> bool" where
"act_no_func_dcs (Simple_Action_Schema n ps pre eff) = True" |
"act_no_func_dcs (Durative_Action_Schema n ps dcs pre eff) = (list_all (\<lambda>d. \<not> is_Func_Const d) dcs)"

fun duration_constraint_integer::"term duration_constraint \<Rightarrow> bool" where
"duration_constraint_integer No_Const = True" |
"duration_constraint_integer (Time_Const duration_op.EQ x) = is_integer x" |
"duration_constraint_integer (Time_Const duration_op.GEQ x) = is_integer x" |
"duration_constraint_integer (Time_Const duration_op.LEQ x) = is_integer x"

fun act_dcs_integers::"ast_action_schema \<Rightarrow> bool" where
"act_dcs_integers (Simple_Action_Schema n ps pre eff) = True" |
"act_dcs_integers (Durative_Action_Schema n ps dcs pre eff) = (list_all duration_constraint_integer dcs)"

fun ground_act_pres_pos::"ground_action \<Rightarrow> bool" where
"ground_act_pres_pos (Ground_Action n anno pre eff) = (is_pos_conj pre)"

fun ground_act_no_args::"ground_action \<Rightarrow> bool" where
"ground_act_no_args (Ground_Action n anno pre eff) = (
  form_preds_no_args pre
\<and> list_all form_preds_no_args (ast_effect.adds eff)
\<and> list_all form_preds_no_args (ast_effect.dels eff)
)"

lemma wf_pos_conj_fmla_imp_wf_atoms: 
    assumes "wf_fmla M form"
        and "is_pos_conj form"                
      shows "list_all (wf_fmla_atom M) (to_literals form)"
  using assms
  apply (induction form)
  subgoal for x apply (cases x) by auto
  subgoal by simp
  subgoal for f 
    apply (induction f)
    subgoal for x apply (cases x) by auto
    by auto
  subgoal for f g
    by (cases f) auto
  by auto

lemma is_pos_conj_map_formula:
  assumes "is_pos_conj form"
  shows "is_pos_conj (Formulas.map_formula (map_atom f) form)"
  using assms
  apply (induction form)
  subgoal for x by (cases x) auto
  subgoal by simp
  subgoal for g
    apply (induction g)
    subgoal for x by (cases x) auto
    by auto
  subgoal for f g by (cases f) auto
  by auto

lemma is_pos_conj_Big_And:
  assumes "list_all is_pos_conj x"
  shows "is_pos_conj (BigAnd x)"
  using assms by (induction x) auto

lemma is_pos_conj_to_literals_conv_atoms:
  assumes "is_pos_conj form"
  shows "Atom ` atoms form = set (to_literals form)"
  using assms
  apply (induction form)
  subgoal for x by (cases x) simp+
      apply simp
  subgoal for form
    apply (induction form)
    subgoal for x by (induction x) simp+
    by simp+
  by auto

lemma is_pos_conj_atoms_preds:
  assumes "is_pos_conj form"
  shows "\<forall>a \<in> Atom ` atoms form. is_predAtom a"
  using assms
  apply (induction form rule: is_pos_conj.induct)
       apply auto[1]
  subgoal for v by (cases v) auto
  apply simp
  subgoal for v by (cases v) auto
  by auto

lemma is_pos_conj_predicates: 
  assumes "is_pos_conj form"
  shows "to_predicate ` Atom ` atoms form = set (map to_predicate (to_literals form))"
  using assms unfolding set_remdups set_map 
  using is_pos_conj_to_literals_conv_atoms
  by simp  

lemma form_preds_no_args_imp_atoms_no_args:
  assumes "form_preds_no_args form"
  shows "\<forall>a \<in> Atom ` atoms form. form_preds_no_args a"
  using assms
  unfolding form_preds_no_args_def by simp

lemma form_preds_no_args_Big_And:
  assumes "list_all form_preds_no_args x"
  shows "form_preds_no_args (BigAnd x)"
  using assms unfolding form_preds_no_args_def by (induction x) auto

lemma eff_adds_no_args_conjunct_effect:
  assumes "\<forall>eff \<in> set effs. list_all form_preds_no_args (adds eff)"
  shows "list_all form_preds_no_args (adds (\<And>\<^sub>e\<^sub>f\<^sub>f effs))"
  using assms
  unfolding list_all_iff conjunct_effects_def
  unfolding ast_effect.sel
  unfolding comp_def set_concat
  by auto

lemma eff_dels_no_args_conjunct_effect:
  assumes "\<forall>eff \<in> set effs. list_all form_preds_no_args (dels eff)"
  shows "list_all form_preds_no_args (dels (\<And>\<^sub>e\<^sub>f\<^sub>f effs))"
  using assms
  unfolding list_all_iff conjunct_effects_def
  unfolding ast_effect.sel
  unfolding comp_def set_concat
  by auto

lemma Collect_is_pos_litE:
  assumes "x \<in> Collect is_pos_lit"
      and "\<And>p ps. x = Atom (predAtm p ps) \<Longrightarrow> thesis"
      and "x = \<^bold>\<not>\<bottom> \<Longrightarrow> thesis"
    shows thesis
  using assms
  by (induction x rule: is_pos_lit.induct) auto

lemma instantiate_action_schema_pres_pos:
  assumes "act_pres_pos (Simple_Action_Schema n ps pre eff)"
      and "action_params_match (Simple_Action_Schema n ps pre eff) as"
    shows "ground_act_pres_pos (instantiate_action_schema (Simple_Action_Schema n ps pre eff) as anno)"
proof -
  have 1: "is_pos_conj pre"
    using assms(1) by auto
  show ?thesis 
    using assms 1 is_pos_conj_map_formula by auto
qed

lemma inst_snap_act_pres_pos:
  assumes "act_pres_pos (Durative_Action_Schema n ps d pre eff)"
      and "action_params_match (Durative_Action_Schema n ps d pre eff) as"
    shows "ground_act_pres_pos (inst_snap_action (Durative_Action_Schema n ps d pre eff) as anno)"
proof -
  have 1: "list_all is_pos_conj (filter_time_spec anno pre)"
    using assms(1)
    unfolding  filter_time_spec_def comp_def
    apply (subst (asm) act_pres_pos.simps)
    unfolding list_all_iff by auto
  show ?thesis 
    using assms 1 is_pos_conj_Big_And is_pos_conj_map_formula by auto
qed

lemma max_lb_opt_propI:
  assumes "list_all Q xs"
      and "Q y"
    shows "Q (max_lb_opt xs y)"
  using assms by (induction xs arbitrary: y) auto

lemma dc_list_lower_propI:
  assumes "list_all Q (map dc_to_lb dcs)"  
      and "Q None"
  shows "Q (dc_list_lower dcs)"
  unfolding dc_list_lower_def
  apply (rule max_lb_opt_propI)
  using assms by simp+ 

lemma min_ub_opt_propI:
  assumes "list_all Q xs"
      and "Q y"
    shows "Q (min_ub_opt xs y)"
  using assms by (induction xs arbitrary: y) auto

lemma dc_list_upper_propI:
  assumes "list_all Q (map dc_to_ub dcs)"  
      and "Q None"
  shows "Q (dc_list_upper dcs)"
  unfolding dc_list_upper_def
  apply (rule min_ub_opt_propI)
  using assms by simp+

lemma dc_integer_imp_lb_integer:
  assumes "duration_constraint_integer dc"
      and "\<not> is_Func_Const dc"
  shows "pred_option (pred_lower_bound is_integer) (dc_to_lb dc)"
  using assms apply (induction dc)
    apply simp
  subgoal for op c
    apply (induction op)
    by auto
  by auto

lemma dc_integer_imp_ub_integer:
  assumes "duration_constraint_integer dc"
      and "\<not> is_Func_Const dc"
  shows "pred_option (pred_upper_bound is_integer) (dc_to_ub dc)"
  using assms apply (induction dc)
    apply simp
  subgoal for op c
    apply (induction op)
    by auto
  by auto

lemma start_spec_end_spec_neq:
  "at_start_spec a \<noteq> at_end_spec a" 
  apply (cases a)
  using non_ground_action_def apply simp
  by simp

sublocale imp_defs: temp_planning_problem_list_defs_int 
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  init_spec goal_spec 0 props_spec actions_spec
  by unfold_locales simp

end

locale ground_ast_problem = 
    ground_ast_problem_defs P +
    wf_ast_problem P
  for P :: ast_problem +
  assumes positive_goal: "is_pos_conj (goal P)"
      and preds_no_args: "list_all pred_no_args (predicates D)"
      and acts_no_params: "list_all act_no_params (actions D)"
      and acts_no_func_dcs: "list_all act_no_func_dcs (actions D)" 
      and acts_dcs_integers: "list_all act_dcs_integers (actions D)"
      and positive_act_pres: "list_all act_pres_pos (actions D)"
      and no_functions: "functions D = []"
      and no_consts: "consts D = []"
begin

lemma acts_wf:
  assumes "a \<in> set actions_spec"
  shows " wf_action_schema a"
  using wf_domain assms unfolding wf_domain_def actions_spec_def by blast

lemma distinct_act_names:
  "distinct (map ast_action_schema.name actions_spec)"
  unfolding actions_spec_def using wf_domain wf_domain_def by simp

lemma resolve_action_in_actions:
  assumes "resolve_action_schema n = Some a"
  shows "a \<in> set actions_spec"
  using assms unfolding resolve_action_schema_def actions_spec_def
  by (blast dest: index_by_eq_SomeD)

lemma act_params_match_empty:
  assumes "a \<in> set actions_spec"
  shows "action_params_match a []"
  using assms
  apply (induction a)
  using acts_no_params 
  unfolding action_params_match_def actions_spec_def list_all_iff 
  by auto
  
(* Any wf atomic formula's predicates' ids are in the set of ids that we use as propositions *)
lemma wf_fmla_atom_in_props:
  assumes "wf_fmla_atom M x"
  shows "to_predicate x \<in> set props_spec"
proof -
  obtain p vs where
    x: "x = Atom (predAtm p vs)"
    "wf_pred_atom M (p, vs)"
    using assms
    apply (cases x)
    subgoal for y 
      apply (cases y) by auto
    by auto
  obtain Ts where
    Ts: "sig p = Some Ts"
    using x(2) unfolding wf_pred_atom.simps
    apply (cases "sig p")
    unfolding sig_def by auto
  hence Ts_ran: "Ts \<in> ran sig" 
    by (rule ranI)
  hence p_dom: "p \<in> dom sig" using Ts by auto
  have "fst ` set (map (\<lambda>x. case x of PredDecl p n \<Rightarrow> (p, n)) (predicates D)) = pred ` set (predicates D)"
    apply (intro equalityI subsetI)
    unfolding set_map image_image
     apply (erule imageE)
    subgoal for x predd
      apply (cases predd)
      using predicate_decl.sel by force
    apply (erule imageE)
    subgoal for x predd
      apply (cases predd)
      using predicate_decl.sel by force
    done
  then
  show ?thesis
    unfolding x to_predicate.simps
    unfolding props_spec_def
    using p_dom unfolding sig_def
    unfolding dom_map_of_conv_image_fst by auto
  (* have "snd ` set (map (\<lambda>x. case x of PredDecl p n \<Rightarrow> (p, n)) (predicates local.D)) = {[]}"
  proof (rule equalityI)
    show pred_args: "snd ` (set (map (\<lambda>x. case x of PredDecl p n \<Rightarrow> (p, n)) (predicates D))) \<subseteq> {[]}"
    proof (intro  subsetI)
      fix x
      assume "x \<in> snd ` set (map (\<lambda>x. case x of PredDecl p n \<Rightarrow> (p, n)) (predicates local.D))" 
      then obtain predd p' n' where
        "predd \<in> set (predicates D)"
        "predd = PredDecl p' n'"
        "x = n'" 
        unfolding set_map
        unfolding image_image
        apply -
        apply (erule imageE)
        subgoal for predd
          apply (cases predd)
          by auto
        done
      thus "x \<in> {[]}" using preds_no_args 
        unfolding list_all_iff by fastforce
    qed
    show "{[]} \<subseteq> snd ` set (map (\<lambda>x. case x of PredDecl p n \<Rightarrow> (p, n)) (predicates local.D))"
    proof -
      have 1: "Ts \<in> snd ` set (map (\<lambda>x. case x of PredDecl p n \<Rightarrow> (p, n)) (predicates local.D))"
        apply (rule set_mp)
        apply (rule Misc.ran_map_of)
        using Ts_ran
        unfolding sig_def by auto
      with pred_args
      have "Ts = []" by blast
      thus ?thesis using Ts_ran 1 by auto
    qed
  qed *)
qed


text \<open>Snap actions are well formed, because they are just ground actions obtained using the
functions in the PDDL formalisation\<close>
lemma start_snaps_wf:
  assumes "a \<in> set actions_spec"
  shows "wf_ground_action (at_start_spec a)"
  using assms
proof (induction a)
  case (Simple_Action_Schema n ps pre eff)
  show ?case 
    unfolding at_start_spec.simps
  proof (rule wf_inst_action_schema)
    have 1: "ps = []" 
      using acts_no_params Simple_Action_Schema
      unfolding actions_spec_def list_all_iff by auto
    show "action_params_match (Simple_Action_Schema n ps pre eff) []" 
      unfolding action_params_match_def 1 by simp
    show "wf_action_schema (Simple_Action_Schema n ps pre eff)"
      using wf_domain unfolding wf_domain_def 
      using Simple_Action_Schema unfolding actions_spec_def by blast
  qed
next
  case (Durative_Action_Schema n ps d pre eff)
  show ?case 
    unfolding at_start_spec.simps
  proof (rule wf_inst_durative_action_schema)
    have 1: "ps = []" 
      using acts_no_params Durative_Action_Schema
      unfolding actions_spec_def list_all_iff by auto
    show "action_params_match (Durative_Action_Schema n ps d pre eff) []"
      unfolding action_params_match_def using 1 by simp
    show "wf_action_schema (Durative_Action_Schema n ps d pre eff)"
      using wf_domain unfolding wf_domain_def 
      using Durative_Action_Schema unfolding actions_spec_def by blast
  qed
qed

lemma end_snaps_wf:
  assumes "a \<in> set actions_spec"
  shows "wf_ground_action (at_end_spec a)"
  using assms
proof (induction a)
  case (Simple_Action_Schema n ps pre eff)
  show ?case 
    unfolding at_end_spec.simps
    unfolding non_ground_action_def by auto
next
  case (Durative_Action_Schema n ps d pre eff)
  show ?case 
    unfolding at_end_spec.simps
  proof (rule wf_inst_durative_action_schema)
    have 1: "ps = []" 
      using acts_no_params Durative_Action_Schema
      unfolding actions_spec_def list_all_iff by auto
    show "action_params_match (Durative_Action_Schema n ps d pre eff) []"
      unfolding action_params_match_def using 1 by simp
    show "wf_action_schema (Durative_Action_Schema n ps d pre eff)"
      using wf_domain unfolding wf_domain_def 
      using Durative_Action_Schema unfolding actions_spec_def by blast
  qed
qed

text \<open>The over-all condition is obtained by first instantiating the action.\<close>
lemma over_all_snap_wf:
  assumes "a \<in> set actions_spec"
  shows "wf_ground_action (over_all_snap a)"
  using assms
proof (induction a)
  case (Simple_Action_Schema n ps pre eff)
  show ?case 
    unfolding over_all_snap.simps
    unfolding non_ground_action_def by auto
next
  case (Durative_Action_Schema n ps d pre eff)
  show ?case 
    unfolding over_all_snap.simps
  proof (rule wf_inst_durative_action_schema)
    have 1: "ps = []" 
      using acts_no_params Durative_Action_Schema
      unfolding actions_spec_def list_all_iff by auto
    show "action_params_match (Durative_Action_Schema n ps d pre eff) []"
      unfolding action_params_match_def using 1 by simp
    show "wf_action_schema (Durative_Action_Schema n ps d pre eff)"
      using wf_domain unfolding wf_domain_def 
      using Durative_Action_Schema unfolding actions_spec_def by blast
  qed
qed

text \<open>Snap actions have no arguments\<close>
lemma act_no_params:
  assumes "a \<in> set actions_spec"
  shows "act_no_params a"
  using assms unfolding actions_spec_def using acts_no_params unfolding list_all_iff 
  by simp

lemma constT_None:
  "constT x = None"
  unfolding constT_def no_consts by simp

lemma wf_fmla_no_args: 
  assumes "wf_fmla (ty_term (map_of []) constT) form" 
  shows "form_preds_no_args form" 
  using assms
  apply (induction form)
  unfolding form_preds_no_args_def apply (intro strip ballI)
  unfolding Formulas.formula.set
  subgoal for a x apply (induction a)
    subgoal for n obs 
      apply (cases obs)
       apply simp 
      subgoal for ob' obs'
        unfolding wf_fmla.simps wf_atom.simps
        unfolding wf_pred_atom.simps
        apply (cases "sig n")
         apply simp
        subgoal for as
          apply (cases as)
           apply simp
          unfolding is_of_type_def
          apply (cases ob')
          unfolding constT_None by auto
        done
      done 
    subgoal for x1 x2
      unfolding wf_fmla.simps wf_atom.simps constT_def no_consts
      apply (cases x1)
      by auto
    done
  by auto

lemma wf_fmla_atom_no_args:
  assumes "wf_fmla_atom (ty_term (map_of []) constT) form" 
  shows "form_preds_no_args form" 
  using assms wf_fmla_no_args wf_fmla_atom_alt by auto

lemma map_formula_no_args:
  assumes "form_preds_no_args form"
  shows "form_preds_no_args ((Formulas.map_formula o map_atom) f form)"
  using assms 
  unfolding form_preds_no_args_def
  apply (induction form)
  subgoal for x apply (induction x)
    subgoal for n as
      by (cases as) auto
    by simp
  by auto

lemma map_effect_adds_no_args:
  assumes "list_all form_preds_no_args (adds eff)"
  shows "list_all form_preds_no_args (adds (map_ast_effect f eff))"
  using assms
  unfolding list_all_iff
  unfolding ast_effect.map_sel
  using map_formula_no_args by auto

lemma map_effect_dels_no_args:
  assumes "list_all form_preds_no_args (dels eff)"
  shows "list_all form_preds_no_args (dels (map_ast_effect f eff))"
  using assms
  unfolding list_all_iff
  unfolding ast_effect.map_sel
  using map_formula_no_args by auto

lemma instantiate_action_schema_no_params:
  assumes "act_no_params (Simple_Action_Schema n ps pre eff)"
      and "wf_action_schema (Simple_Action_Schema n ps pre eff)"
    shows "ground_act_no_args (instantiate_action_schema (Simple_Action_Schema n ps pre eff) as anno)"
proof -
  have p: "wf_fmla (ty_term (map_of []) constT) pre" 
   and e: "wf_effect (ty_term (map_of []) constT) eff" 
    using assms unfolding act_no_params.simps wf_action_schema.simps Let_def by blast+


  have pre_no_args: "form_preds_no_args pre" using wf_fmla_no_args p by auto

  have eff_adds_no_args: "list_all form_preds_no_args (adds eff)"
    apply (cases eff) 
    using wf_fmla_atom_no_args e unfolding list_all_iff
    by auto

  have eff_dels_no_args: "list_all form_preds_no_args (dels eff)"
    apply (cases eff) 
    using wf_fmla_atom_no_args e unfolding list_all_iff
    by auto

  show ?thesis
    unfolding instantiate_action_schema.simps Let_def
    using pre_no_args eff_adds_no_args eff_dels_no_args 
    using map_formula_no_args map_effect_adds_no_args map_effect_dels_no_args by fastforce
qed


lemma inst_snap_action_no_params:
  assumes "act_no_params (Durative_Action_Schema n ps dcs pres effs)"
      and "wf_action_schema (Durative_Action_Schema n ps dcs pres effs)"
    shows "ground_act_no_args (inst_snap_action (Durative_Action_Schema n ps dcs pres effs) as anno)"
proof -
  have p: "\<forall>(t, pre) \<in> set pres. wf_fmla (ty_term (map_of []) constT) pre" 
   and e: "\<forall>(t, eff) \<in> set effs. wf_effect (ty_term (map_of []) constT) eff" 
    using assms unfolding act_no_params.simps wf_action_schema.simps Let_def by blast+
  
  have pre_no_args: "\<forall>(t, pre) \<in> set pres. form_preds_no_args pre" using wf_fmla_no_args p by auto

  have eff_adds_no_args: "\<forall>(t, eff) \<in> set effs. list_all form_preds_no_args (adds eff)"
    using wf_fmla_atom_no_args e unfolding list_all_iff
    apply (intro ballI)
    subgoal for x
      apply (cases x)
      subgoal for t eff
        apply (cases eff)
        by auto
      done
    done

  have eff_dels_no_args: "\<forall>(t, eff) \<in> set effs. list_all form_preds_no_args (dels eff)"
    using wf_fmla_atom_no_args e unfolding list_all_iff
    apply (intro ballI)
    subgoal for x
      apply (cases x)
      subgoal for t eff
        apply (cases eff)
        by auto
      done
    done

  show ?thesis unfolding inst_snap_action.simps Let_def 
    unfolding ground_act_no_args.simps
    apply (intro conjI)
      apply (rule map_formula_no_args)
      apply (rule form_preds_no_args_Big_And)
      apply (subst filter_time_spec_def)
      apply (subst list_all_iff)
    using pre_no_args apply auto[1]
     apply (rule map_effect_adds_no_args)
     apply (rule eff_adds_no_args_conjunct_effect)
    apply (subst filter_time_spec_def)
    using eff_adds_no_args apply auto[1]
     apply (rule map_effect_dels_no_args)
     apply (rule eff_dels_no_args_conjunct_effect)
    apply (subst filter_time_spec_def)
    using eff_dels_no_args by auto
qed

lemma start_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (at_start_spec a)"
  using assms
proof (induction a)
  case a: (Simple_Action_Schema n ps pre eff)
  show ?case 
    unfolding at_start_spec.simps 
    apply (rule instantiate_action_schema_no_params)
    using act_no_params
    using acts_wf
    using a by blast+
next
  case a: (Durative_Action_Schema n ps dcs pre eff)
  show ?case 
    unfolding at_start_spec.simps 
    apply (rule inst_snap_action_no_params)
    using act_no_params
    using acts_wf
    using a by blast+
qed

lemma end_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (at_end_spec a)"
  using assms
proof (induction a)
  case a: (Simple_Action_Schema n ps pre eff)
  show ?case 
    using non_ground_action_def 
    using form_preds_no_args_def by fastforce
next
  case a: (Durative_Action_Schema n ps dcs pre eff)
  show ?case 
    unfolding at_end_spec.simps 
    apply (rule inst_snap_action_no_params)
    using act_no_params
    using acts_wf
    using a by blast+
qed

text \<open>The over-all condition is obtained by first instantiating the action.\<close>

lemma over_all_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (over_all_snap a)"
  using assms
proof (induction a)
  case a: (Simple_Action_Schema n ps pre eff)
  show ?case 
    using non_ground_action_def 
    using form_preds_no_args_def by fastforce
next
  case a: (Durative_Action_Schema n ps dcs pre eff)
  show ?case 
    unfolding over_all_snap.simps 
    apply (rule inst_snap_action_no_params)
    using act_no_params
    using acts_wf
    using a by blast+
qed

text \<open>Conditions\<close>
lemma start_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (at_start_spec a)"
  using assms
proof (induction a)
  case 1: (Simple_Action_Schema n ps pre eff)
  have "act_pres_pos (Simple_Action_Schema n ps pre eff)" using 1 positive_act_pres 
    unfolding actions_spec_def list_all_iff by auto
  then show ?case using instantiate_action_schema_pres_pos act_params_match_empty 1 by fastforce
next
  case 1: (Durative_Action_Schema n ps d pre eff)
  have "act_pres_pos (Durative_Action_Schema n ps d pre eff)" using 1 positive_act_pres 
    unfolding actions_spec_def list_all_iff by auto
  then show ?case using inst_snap_act_pres_pos act_params_match_empty 1 by fastforce
qed

lemma end_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (at_end_spec a)"
  using assms
proof (induction a)
  case 1: (Simple_Action_Schema n ps pre eff)
  show ?case unfolding at_end_spec.simps non_ground_action_def by auto
next
  case 1: (Durative_Action_Schema n ps d pre eff)
  have "act_pres_pos (Durative_Action_Schema n ps d pre eff)" using 1 positive_act_pres 
    unfolding actions_spec_def list_all_iff by auto
  then show ?case using inst_snap_act_pres_pos act_params_match_empty 1 by fastforce
qed

lemma over_all_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (over_all_snap a)"
  using assms
proof (induction a)
  case 1: (Simple_Action_Schema n ps pre eff)
  show ?case unfolding  over_all_snap.simps non_ground_action_def by simp
next
  case 1: (Durative_Action_Schema n ps d pre eff)
  have "act_pres_pos (Durative_Action_Schema n ps d pre eff)" using 1 positive_act_pres 
    unfolding actions_spec_def list_all_iff by auto
  then show ?case using inst_snap_act_pres_pos act_params_match_empty 1 by fastforce
qed

text \<open>Conditions and effects of well formed ground actions are in props. Snap actions are ground actions\<close>
lemma wf_ground_action_pres_in_props:
  assumes "wf_ground_action h"
      and "ground_act_pres_pos h"
  shows "(set \<circ> pre_spec) h \<subseteq> set props_spec"
  using assms
proof (induction h)
  case (Ground_Action n anno pre eff)
  have 1: "(wf_fmla objT) pre"
    using Ground_Action by auto
  have 2: "is_pos_conj pre"
    using Ground_Action by auto
  show ?case  
    using wf_pos_conj_fmla_imp_wf_atoms[OF 1 2] 
      wf_fmla_atom_in_props 
    unfolding list_all_iff by auto
qed

lemma wf_ground_action_adds_in_props:
  assumes "wf_ground_action h"
  shows "(set \<circ> adds_spec) h \<subseteq> set props_spec"
  using assms
proof (induction h)
  case (Ground_Action n anno  pre eff)
  have 1: "list_all (wf_fmla_atom objT) (adds eff)"
    using Ground_Action unfolding wf_ground_action.simps apply (induction eff)
    using wf_effect.simps list_all_iff by auto
  show ?case 
    apply (rule subsetI)
    unfolding comp_def adds_spec.simps
    using 1 wf_fmla_atom_in_props 
    unfolding list_all_iff by auto
qed

lemma wf_ground_action_dels_in_props:
  assumes "wf_ground_action h"
  shows "(set \<circ> dels_spec) h \<subseteq> set props_spec"
  using assms
proof (induction h)
  case (Ground_Action n anno  pre eff)
  have 1: "list_all (wf_fmla_atom objT) (dels eff)"
    using Ground_Action unfolding wf_ground_action.simps apply (induction eff)
    using wf_effect.simps list_all_iff by auto
  show ?case 
    apply (rule subsetI)
    unfolding comp_def dels_spec.simps
    using 1 wf_fmla_atom_in_props 
    unfolding list_all_iff by auto
qed

text \<open>Actions' over_all conditions are in props.\<close>

lemma over_all_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (over_all_spec a) \<subseteq> set props_spec"
  using assms
proof (induction a)
  case 1: (Simple_Action_Schema x1 x2 x3 x4)
  hence 2: "wf_action_schema (Simple_Action_Schema x1 x2 x3 x4)" using wf_domain 
    unfolding wf_domain_def actions_spec_def by blast
  show ?case unfolding over_all_spec.simps
    using wf_ground_action_pres_in_props[simplified comp_def]
    using over_all_snap_wf 1 over_all_snap_pre_pos_conj by blast+
next
  case 1: (Durative_Action_Schema x1 x2 x3 x4 x5)
  hence 2: "wf_action_schema (Durative_Action_Schema x1 x2 x3 x4 x5)" using wf_domain 
    unfolding wf_domain_def actions_spec_def by blast
  show ?case unfolding over_all_spec.simps
    using wf_ground_action_pres_in_props[simplified comp_def]
    using over_all_snap_wf  1 over_all_snap_pre_pos_conj by blast+
qed

text \<open>Snap actions are identifiable\<close>

lemma inj_on_at_start_spec: "inj_on at_start_spec (set actions_spec)"
proof -
  { fix x y
    assume x_in_acts: "x \<in> set actions_spec" 
      and y_in_acts: "y \<in> set actions_spec" 
      and neq: "x \<noteq> y"

    have "inj_on ast_action_schema.name (set actions_spec)" using distinct_act_names distinct_map by blast
    hence names_neq: "ast_action_schema.name x \<noteq> ast_action_schema.name y" using neq x_in_acts y_in_acts 
      by (force dest: inj_on_contraD)
    
    have "at_start_spec x \<noteq> at_start_spec y"
      apply (cases x; cases y)
      using names_neq by auto
    }
  thus ?thesis
    apply -
    apply (rule inj_onI)
    by auto
qed

lemma inj_on_at_end_spec: "inj_on at_end_spec (set actions_spec)"
proof -
  { fix x y
    assume x_in_acts: "x \<in> set actions_spec" 
      and y_in_acts: "y \<in> set actions_spec" 
      and neq: "x \<noteq> y"

    have "inj_on ast_action_schema.name (set actions_spec)" using distinct_act_names distinct_map by blast
    hence names_neq: "ast_action_schema.name x \<noteq> ast_action_schema.name y" using neq x_in_acts y_in_acts 
      by (force dest: inj_on_contraD)
    
    have "at_end_spec x \<noteq> at_end_spec y"
      apply (cases x; cases y)
      using names_neq non_ground_action_def by auto
    }
  thus ?thesis
    apply -
    apply (rule inj_onI)
    by auto
qed

lemma at_start_spec_at_end_spec_disj: 
  "at_start_spec ` (set actions_spec) \<inter> at_end_spec ` (set actions_spec) = {}"
proof -
  { fix x y
    assume x_in_acts: "x \<in> set actions_spec" 
      and y_in_acts: "y \<in> set actions_spec" 
    
    have "at_start_spec x \<noteq> at_end_spec y"
      apply (cases x; cases y)
      using non_ground_action_def by auto
    }
  thus ?thesis
    by auto
qed

text \<open>The initial state and goal are in the props\<close>
lemma init_in_props: "set init_spec \<subseteq> set props_spec"
proof -
  have 1: "\<forall>f\<in>set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    using wf_problem unfolding wf_problem_def wf_domain_def by auto
  have "\<forall>f\<in>set (init P). wf_fmla_atom objT f" 
  proof (intro strip ballI)
    fix f
    assume "f \<in> set (init P)"
    then consider "wf_fmla_atom objT f" | "wf_func_assign f" using 1 by auto
    thus "wf_fmla_atom objT f"
    proof (cases)
      case 1
      then show ?thesis by simp
    next
      case 2
      then obtain n as t where
        f: "f = Atom (eqAtm (FuncEnt n as) (TimeEnt t))" 
        apply (cases f)
        subgoal for x
          apply (cases x)
           apply (simp)
          subgoal for a b
            apply (cases a; cases b)
            by auto
          done
        by auto   
      hence "wf_func_args objT (n,as)" using 2 by auto
      hence False using no_functions func_sig_def by auto
      thus ?thesis by auto
    qed
  qed
  thus ?thesis using wf_fmla_atom_in_props init_spec_def by auto
qed

lemma goal_in_props: "set goal_spec \<subseteq> set props_spec"
proof -
  have "wf_fmla objT (goal P)"
    using wf_problem unfolding wf_problem_def
    unfolding props_spec_def goal_spec_def by auto
  hence "list_all (wf_fmla_atom objT) (to_literals (goal P))" 
    using wf_pos_conj_fmla_imp_wf_atoms positive_goal by auto
  hence "set (map to_predicate (to_literals (goal P))) \<subseteq> set props_spec"
    using wf_fmla_atom_in_props unfolding set_map list_all_iff by auto
  thus ?thesis using goal_spec_def by auto
qed
end (* locale ground_ast_problem *)
end
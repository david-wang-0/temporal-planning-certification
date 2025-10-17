theory Ground_PDDL_Problem_TP_Reduction
  imports "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics_Alt"
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

context ast_problem
begin

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

definition "non_ground_action \<equiv> Ground_Action (Formulas.Not Formulas.Bot) (Effect [] [])"


fun at_start_spec::"ast_action_schema \<Rightarrow> ground_action" where
"at_start_spec (Simple_Action_Schema n ps pre eff) = instantiate_action_schema (Simple_Action_Schema n ps pre eff) []" |
"at_start_spec (Durative_Action_Schema n ps d cond eff) = inst_snap_action (Durative_Action_Schema n ps d cond eff) [] At_Start"

fun at_end_spec::"ast_action_schema \<Rightarrow> ground_action" where
"at_end_spec (Simple_Action_Schema n ps pre eff) = non_ground_action" |
"at_end_spec (Durative_Action_Schema n ps d cond eff) = inst_snap_action (Durative_Action_Schema n ps d cond eff) [] At_End"

fun over_all_snap::"ast_action_schema \<Rightarrow> ground_action" where
"over_all_snap (Simple_Action_Schema n ps pre eff) = 
  non_ground_action" |
"over_all_snap (Durative_Action_Schema n ps d cond eff) = 
  inst_snap_action (Durative_Action_Schema n ps d cond eff) [] Over_All"

fun pre_spec::"ground_action \<Rightarrow> predicate list" where
"pre_spec (Ground_Action form eff) = 
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
"adds_spec (Ground_Action form eff) =
  eff
  |> ast_effect.adds
  |> map to_predicate
  |> remdups
"

fun dels_spec::"ground_action \<Rightarrow> predicate list" where
"dels_spec (Ground_Action form eff) =
  eff
  |> ast_effect.dels
  |> map to_predicate
  |> remdups
"

fun dc_to_lb::"term duration_constraint \<Rightarrow> int lower_bound option" where
"dc_to_lb No_Const = None" |
"dc_to_lb (Time_Const duration_op.EQ x) = Some (lower_bound.GE (floor x))" |
"dc_to_lb (Time_Const duration_op.GEQ x) = Some (lower_bound.GE (floor x))" |
"dc_to_lb (Time_Const duration_op.LEQ x) = None"

fun max_lb_opt::"int lower_bound option list \<Rightarrow> int lower_bound option \<Rightarrow> int lower_bound option" where
"max_lb_opt [] l = l" |
"max_lb_opt (x#xs) l = max_lb_opt xs (if (comp_opt_ge x l) then x else l)"

fun dc_list_lower::"term duration_constraint list \<Rightarrow> int lower_bound option" where
"dc_list_lower xs = map dc_to_lb xs |> (\<lambda>xs. max_lb_opt xs None)" 


fun dc_to_ub::"term duration_constraint \<Rightarrow> int upper_bound option" where
"dc_to_ub No_Const = None" |
"dc_to_ub (Time_Const duration_op.EQ x) = Some (upper_bound.LE (floor x))" |
"dc_to_ub (Time_Const duration_op.GEQ x) = None" |
"dc_to_ub (Time_Const duration_op.LEQ x) = Some (upper_bound.LE (floor x))"

fun min_ub_opt::"int upper_bound option list \<Rightarrow> int upper_bound option \<Rightarrow> int upper_bound option" where
"min_ub_opt [] u = u" |
"min_ub_opt (x#xs) u = min_ub_opt xs (if (comp_opt_le x u) then x else u)"

fun dc_list_upper::"term duration_constraint list \<Rightarrow> int upper_bound option" where
"dc_list_upper xs = map dc_to_ub xs |> (\<lambda>xs. min_ub_opt xs None)" 

fun lower_spec::"ast_action_schema \<Rightarrow> _" where
"lower_spec (Simple_Action_Schema n ps pre eff) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec (Durative_Action_Schema n ps d cond eff) = (dc_list_lower d)"

fun upper_spec::"ast_action_schema \<Rightarrow> _" where
"upper_spec (Simple_Action_Schema n ps pre eff) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec (Durative_Action_Schema n ps d cond eff) = (dc_list_upper d)"



end

locale ground_ast_problem_defs = ast_problem P
  for P :: ast_problem
begin

text \<open>Begin: Taken from M. Vollath\<close>
fun is_pos_lit :: "'a atom Formulas.formula \<Rightarrow> bool" where
  f: "is_pos_lit \<bottom> = False" |
  "is_pos_lit (\<^bold>\<not>\<bottom>) = True" |
  "is_pos_lit (Atom (predAtm n args)) = True" |
  "is_pos_lit (\<^bold>\<not>(Atom (predAtm n args))) = False" |
  "is_pos_lit (Atom (eqAtm a b)) = False" |
  "is_pos_lit (\<^bold>\<not>(Atom (eqAtm a b))) = False" |
  "is_pos_lit _ = False"

fun is_pos_conj :: "'a atom Formulas.formula \<Rightarrow> bool" where
  "is_pos_conj (f \<^bold>\<and> g) \<longleftrightarrow> is_pos_conj f \<and> is_pos_conj g" |
  "is_pos_conj f \<longleftrightarrow> is_pos_lit f"
(* This does not have to be right recursive. It could be beneficial *)

text \<open>End: Taken from M. Vollath\<close>

fun pred_no_args::"predicate_decl \<Rightarrow> bool" where
"pred_no_args (PredDecl p as) = (as = [])"

fun act_no_args::"ast_action_schema \<Rightarrow> bool" where
"act_no_args (Simple_Action_Schema n ps pre eff) = (ps = [])" |
"act_no_args (Durative_Action_Schema n ps d pre eff) = (ps = [])" 

fun act_pres_pos::"ast_action_schema \<Rightarrow> bool" where
"act_pres_pos (Simple_Action_Schema n ps pre eff) = (is_pos_conj (pre))" |
"act_pres_pos (Durative_Action_Schema n ps d pre eff) = (list_all is_pos_conj (map snd pre))"

fun ground_act_pres_pos::"ground_action \<Rightarrow> bool" where
"ground_act_pres_pos (Ground_Action pre eff) = (is_pos_conj pre)"

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

lemma instantiate_action_schema_pres_pos:
  assumes "act_pres_pos (Simple_Action_Schema n ps pre eff)"
      and "action_params_match (Simple_Action_Schema n ps pre eff) as"
    shows "ground_act_pres_pos (instantiate_action_schema (Simple_Action_Schema n ps pre eff) as)"
proof -
  have 1: "is_pos_conj pre"
    using assms(1) by auto
  show ?thesis 
    using assms 1 is_pos_conj_map_formula by auto
qed

lemma inst_snap_act_pres_pos:
  assumes "act_pres_pos (Durative_Action_Schema n ps d pre eff)"
      and "action_params_match (Durative_Action_Schema n ps d pre eff) as"
    shows "ground_act_pres_pos (inst_snap_action (Durative_Action_Schema n ps d pre eff) as x)"
proof -
  have 1: "list_all is_pos_conj (filter_time_spec x pre)"
    using assms(1)
    unfolding  filter_time_spec_def comp_def
    apply (subst (asm) act_pres_pos.simps)
    unfolding list_all_iff by auto
  show ?thesis 
    using assms 1 is_pos_conj_Big_And is_pos_conj_map_formula by auto
qed

end

locale ground_ast_problem = 
    ground_ast_problem_defs P +
    wf_ast_problem P
  for P :: ast_problem +
  assumes positive_goal: "is_pos_conj (goal P)"
      and preds_no_args: "list_all pred_no_args (predicates D)"
      and acts_no_args: "list_all act_no_args (actions D)"
      and positive_act_pres: "list_all act_pres_pos (actions D)"
      and no_functions: "functions D = []"
begin

lemma act_params_match_empty:
  assumes "a \<in> set actions_spec"
  shows "action_params_match a []"
  using assms
  apply (induction a)
  using acts_no_args 
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
      using acts_no_args Simple_Action_Schema
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
      using acts_no_args Durative_Action_Schema
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
      using acts_no_args Durative_Action_Schema
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
      using acts_no_args Durative_Action_Schema
      unfolding actions_spec_def list_all_iff by auto
    show "action_params_match (Durative_Action_Schema n ps d pre eff) []"
      unfolding action_params_match_def using 1 by simp
    show "wf_action_schema (Durative_Action_Schema n ps d pre eff)"
      using wf_domain unfolding wf_domain_def 
      using Durative_Action_Schema unfolding actions_spec_def by blast
  qed
qed

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
  case (Ground_Action pre eff)
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
  case (Ground_Action pre eff)
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
  case (Ground_Action pre eff)
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

sublocale abstr_model_checking: tp_nta_reduction_model_checking' 
  init_spec goal_spec at_start_spec at_end_spec 
  over_all_spec 
  lower_spec upper_spec 
  pre_spec adds_spec dels_spec
  0
  props_spec actions_spec
  act_to_name_spec prop_to_name_spec
proof 
  show "0 \<le> (0::int)" by auto
  show "distinct props_spec"
    using wf_problem
    unfolding wf_problem_def wf_domain_def props_spec_def 
    by simp
  show "distinct actions_spec"
  proof -
    have "distinct (map ast_action_schema.name (actions local.D))"
    using wf_problem
    unfolding wf_problem_def wf_domain_def actions_spec_def 
    by simp
    hence "distinct (actions local.D)"
      using distinct_map by blast
    thus ?thesis unfolding actions_spec_def by auto
  qed                                         
  show "\<forall>a\<in>set actions_spec. distinct (over_all_spec a)"
    apply (intro ballI)
    subgoal for a
      apply (induction a)
       apply (subst over_all_spec.simps)
       apply (subst over_all_snap.simps)
       apply (subst non_ground_action_def)
       apply simp
      using distinct_remdups non_ground_action_def by simp
    done
  show "set goal_spec - set props_spec \<subseteq> set init_spec - set props_spec"
    using init_in_props goal_in_props by auto
  show "\<forall>a\<in>set actions_spec. action_and_prop_set.act_mod_props at_start_spec at_end_spec (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) a"
  proof (rule ballI)
    fix a
    assume "a \<in> set actions_spec" 
    thus "action_and_prop_set.act_mod_props at_start_spec at_end_spec (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) a"
      by (intro action_and_prop_set.act_mod_propsI action_and_prop_set.snap_mod_propsI 
          wf_ground_action_adds_in_props wf_ground_action_dels_in_props start_snaps_wf end_snaps_wf)
  qed
  show "action_set_and_props.action_consts at_start_spec at_end_spec (set \<circ> over_all_spec) (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (set actions_spec) \<subseteq> set init_spec - set props_spec"
  proof (rule subsetI)
    fix x
    assume "x \<in> action_set_and_props.action_consts at_start_spec at_end_spec (set \<circ> over_all_spec) (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (set actions_spec)"
    then obtain a where
      a: "x \<in> action_and_prop_set.act_consts at_start_spec at_end_spec (set \<circ> over_all_spec) (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) a" 
      and a_in_acts: "a \<in> set actions_spec" unfolding action_set_and_props.action_consts_def by blast
    then consider "x \<in> action_and_prop_set.snap_consts (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (at_start_spec a)"
      | "x \<in> action_and_prop_set.snap_consts (set \<circ> pre_spec) (set \<circ> adds_spec) (set \<circ> dels_spec) (set props_spec) (at_end_spec a)"
      | "x \<in> ((set \<circ> over_all_spec) a - set props_spec)" unfolding action_and_prop_set.act_consts_def by auto
    hence "x \<in> {}" 
    proof (cases)
      case 1
      obtain pre eff where
        a': "Ground_Action pre eff = at_start_spec a"
        "wf_ground_action (Ground_Action pre eff)" 
        using start_snaps_wf[OF a_in_acts] apply (cases "at_start_spec a") by auto
      have b: "ground_act_pres_pos (at_start_spec a)" using start_snap_pre_pos_conj a_in_acts by blast
      have "(set \<circ> pre_spec) (at_start_spec a) \<union> (set \<circ> adds_spec) (at_start_spec a) \<union> (set \<circ> dels_spec) (at_start_spec a) \<subseteq> set props_spec"
        using wf_ground_action_pres_in_props wf_ground_action_dels_in_props wf_ground_action_adds_in_props
        using a' b by simp
      then show ?thesis using 1 unfolding action_and_prop_set.snap_consts_def by blast
    next
      case 2
      obtain pre eff where
        a': "Ground_Action pre eff = at_end_spec a"
        "wf_ground_action (Ground_Action pre eff)" 
        using end_snaps_wf[OF a_in_acts] apply (cases "at_end_spec a") by auto
      have b: "ground_act_pres_pos (at_end_spec a)" using end_snap_pre_pos_conj a_in_acts by blast
      have "(set \<circ> pre_spec) (at_end_spec a) \<union> (set \<circ> adds_spec) (at_end_spec a) \<union> (set \<circ> dels_spec) (at_end_spec a) \<subseteq> set props_spec"
        using wf_ground_action_pres_in_props wf_ground_action_dels_in_props wf_ground_action_adds_in_props
        using a' b by simp
      then show ?thesis using 2 unfolding action_and_prop_set.snap_consts_def by blast
    next
      case 3
      then show ?thesis using a_in_acts over_all_in_props by auto
    qed
    thus "x \<in> set init_spec - set props_spec" using init_in_props by blast
  qed
  show "inj_on act_to_name_spec (set actions_spec)"
  proof -
    have "distinct (map ast_action_schema.name actions_spec)" 
      using wf_domain wf_domain_def actions_spec_def by presburger
    thus ?thesis unfolding distinct_map act_to_name_spec_def by blast
  qed                                       
  show "inj_on prop_to_name_spec (set props_spec)"
  proof -
    have "distinct (map pred (predicates local.D))"
      using wf_domain unfolding wf_domain_def by auto
    hence "distinct (map predicate.name (map pred (predicates local.D)))"
      apply (rule distinct_inj_map)
      apply (rule injI)
      using predicate.expand by simp
    thus ?thesis
      unfolding prop_to_name_spec_def props_spec_def
      unfolding distinct_map by blast
  qed
qed
end
end
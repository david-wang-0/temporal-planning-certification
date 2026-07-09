theory Ground_PDDL_Problem_Defs
  imports "TP_NTA_Reduction.TP_NTA_Reduction_Model_Checking"
      "Temporal_Planning.Temporal_Instantiations"
      "Temporal_Planning.Temporal_Happening_Semantics"
      "Grounding_Temporal_Common.Temporal_PDDL_Normalization"
begin

subsection \<open>To move\<close>


text \<open>Full case/induction/split rules for \<open>duration_constraint\<close> that also expand the
  \<open>duration_op\<close> into its three constructors EQ/LEQ/GEQ (the generated
  \<open>duration_constraint.cases\<close>/\<open>.induct\<close> only expose the \<open>DurationConstraint\<close> wrapper).
  TODO: move to a more appropriate location.\<close>

lemma duration_constraint_split_full:
  "P (case x of DurationConstraint dop r \<Rightarrow> f dop r)
   = ((\<forall>r. x = DurationConstraint duration_op.EQ r \<longrightarrow> P (f duration_op.EQ r))
      \<and> (\<forall>r. x = DurationConstraint duration_op.LEQ r \<longrightarrow> P (f duration_op.LEQ r))
      \<and> (\<forall>r. x = DurationConstraint duration_op.GEQ r \<longrightarrow> P (f duration_op.GEQ r)))"
  by (cases x rule: duration_constraint_as_formula.cases) auto

lemma duration_constraint_split_full_asm:
  "P (case x of DurationConstraint dop r \<Rightarrow> f dop r)
   = (\<not> ((\<exists>r. x = DurationConstraint duration_op.EQ r \<and> \<not> P (f duration_op.EQ r))
        \<or> (\<exists>r. x = DurationConstraint duration_op.LEQ r \<and> \<not> P (f duration_op.LEQ r))
        \<or> (\<exists>r. x = DurationConstraint duration_op.GEQ r \<and> \<not> P (f duration_op.GEQ r))))"
  by (cases x rule: duration_constraint_as_formula.cases) auto



subsection \<open>\<close>

text \<open>The FPS imports introduce a second @{text "|>"} notation (\<open>Syntax_Utils.app\<close>), identical to
  Munta's \<open>Error_List_Monad.app\<close> already used here. Suppress the duplicate so \<open>|>\<close> resolves uniquely.\<close>
no_notation Syntax_Utils.app (infixl "|>" 59)

text \<open>The FPS imports also introduce a second @{text "#>"} notation (\<open>Syntax_Utils.fcomb\<close>),
  identical to the project's \<open>TP_Utils.comb\<close> already used here. Suppress the duplicate so
  \<open>#>\<close> resolves uniquely to the project's @{const TP_Utils.comb}.\<close>
no_notation Syntax_Utils.fcomb (infixl "#>" 60)

text \<open>Munta's @{const Assertions.models} (separation logic) also binds the @{text "\<Turnstile>"} notation.
  Suppress it so @{text "\<Turnstile>"} resolves to @{const Sema.formula_semantics} (propositional
  satisfaction against a total valuation), which is what the classical world-model bridge below
  uses.\<close>
no_notation Assertions.models (infix "\<Turnstile>" 50)

subsection \<open>Open-world world model (FPS @{const Worlds.valuation} / \<open>\<Turnstile>\<^sub>m\<close>)\<close>

text \<open>The re-point uses Formal-PDDL-Semantics' open-world, partial @{const Worlds.valuation}
  (@{typ \<open>world_model \<Rightarrow> object atom \<rightharpoonup> bool\<close>}) and @{const map_formula_semantics} (\<open>\<Turnstile>\<^sub>m\<close>).
  For a positive predicate conjunction this coincides with subset membership of its literals in the
  logical world model (\<open>pos_conj_models_iff_superset\<close> below); no closed-world layer is introduced.
  Bridge lemmas adapted from the classical grounder \<open>Isabelle-PDDL-Grounding\<close>
  (\<open>val_predAtm_dom\<close> / \<open>valuation_pos_conj_mono\<close>).\<close>

fun to_literals::"object atom Formulas.formula \<Rightarrow> object atom Formulas.formula list" where
"to_literals (Atom (predAtm x as)) = [Atom (predAtm x as)]" |
"to_literals (x \<^bold>\<and> y) = to_literals x @ to_literals y" |
"to_literals _ = []"

text \<open>Nesting-tolerant ground-action positivity: the positive predAtm literals \<open>to_literals\<close>
  keeps are exactly the formula's atoms. Unlike the grounder's right-deep \<open>is_pos_conj\<close> this tolerates
  the nested \<open>BigAnd\<close> of the snap-precondition construction (both \<open>atoms\<close> and \<open>to_literals\<close> flatten
  over \<open>\<^bold>\<and>\<close>). Derived from the grounder's \<open>is_pos_conj\<close> + the eqAtm-free side condition
  \<open>form_preds_no_args\<close>, then lifted over \<open>BigAnd\<close>.\<close>
definition pos_conj_form :: "object atom Formulas.formula \<Rightarrow> bool" where
  "pos_conj_form form \<equiv> (Atom ` atoms form = set (to_literals form))"

lemma pos_conj_form_BigAnd:
  assumes "\<forall>c \<in> set cs. pos_conj_form c"
  shows "pos_conj_form (BigAnd cs)"
  using assms unfolding pos_conj_form_def
  by (induction cs) (auto simp: image_Un)

(* PLACEHOLDER: inst_formula preservation lemmas moved below is_pos_conj_to_literals_conv_atoms *)

fun to_predicate::"object atom Formulas.formula \<Rightarrow> predicate" where
"to_predicate (Atom (predAtm x _)) = x"

text \<open>Open-world bridge (adapted from the classical grounder \<open>Isabelle-PDDL-Grounding\<close>): a
  positive predicate conjunction is satisfied under the FPS partial valuation iff its literals are
  all present in the logical world model. Predicate atoms are always defined, so the definedness
  guard of \<open>\<Turnstile>\<^sub>m\<close> is trivial.\<close>
lemma val_predAtm_dom: "predAtm p xs \<in> dom (valuation M)"
  unfolding valuation_def by (simp add: domIff)

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

text \<open>Positivity (\<open>is_pos_lit\<close> / \<open>is_pos_conj\<close>) is REUSED from the grounder
  (\<open>Grounding_Common.Formula_Utils\<close>, imported via \<open>Grounding_Temporal_Common.Temporal_PDDL_Normalization\<close>):
  there \<open>is_pos_conj\<close> is right-deep and \<open>is_pos_lit\<close> additionally accepts \<open>eqAtm\<close> (and its negation).
  The predAtm-only guarantee the NTA reduction needs is carried separately by the \<open>predAtm_only\<close> side
  condition below (eqAtm-free preconditions/goal), to be discharged once the grounder's eqAtm-elimination
  stage lands (grounder HANDOVER, "Temporal equality-atom (eqAtm) elimination stage").\<close>

fun atom_no_args::"'a atom \<Rightarrow> bool" where
"atom_no_args (predAtm p []) = True" |
"atom_no_args _ = False"

definition form_preds_no_args::"'a atom Formulas.formula \<Rightarrow> bool" where
"form_preds_no_args form \<equiv> \<forall>a \<in> formula.atoms form. atom_no_args a"

fun max_lb_opt::"('x::linorder) lower_bound option list \<Rightarrow> ('x::linorder) lower_bound option \<Rightarrow> ('x::linorder) lower_bound option" where
"max_lb_opt [] l = l" |
"max_lb_opt (x#xs) l = max_lb_opt xs (if (comp_opt_ge x l) then x else l)"

fun min_ub_opt::"('x::linorder) upper_bound option list \<Rightarrow> ('x::linorder) upper_bound option \<Rightarrow> ('x::linorder) upper_bound option" where
"min_ub_opt [] u = u" |
"min_ub_opt (x#xs) u = min_ub_opt xs (if (comp_opt_le x u) then x else u)"

subsection \<open>Additional well-formedness considerations\<close>

fun pred_no_args::"predicate_decl \<Rightarrow> bool" where
"pred_no_args (PredDecl p as) = (as = [])"

fun act_no_params::"ast_temporal_action_schema \<Rightarrow> bool" where
"act_no_params (SimpleActionSchema h b) = (parameters h = [])" |
"act_no_params (DurativeActionSchema h b) = (parameters h = [])" 

fun act_pres_pos::"ast_temporal_action_schema \<Rightarrow> bool" where
"act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff)) = (is_pos_conj pre)" |
"act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff)) = (list_all is_pos_conj (map snd cond))"

text \<open>The eqAtm-free side condition on preconditions/timed-conditions (predAtm-only, no eqAtm). Bundled
  with @{const act_pres_pos} it upgrades the grounder's @{const is_pos_conj} to @{const pos_conj_form}
  of the instantiated ground precondition. To be DISCHARGED once the grounder's eqAtm-elimination stage
  lands (grounder HANDOVER); until then it is a locale assumption.\<close>
fun act_conds_no_args::"ast_temporal_action_schema \<Rightarrow> bool" where
"act_conds_no_args (SimpleActionSchema h (SimpleActionBody pre eff)) = (form_preds_no_args pre)" |
"act_conds_no_args (DurativeActionSchema h (DurativeActionBody dc cond deff)) = (list_all form_preds_no_args (map snd cond))"

fun dc_no_func::"term duration_constraint \<Rightarrow> bool" where
"dc_no_func (DurationConstraint dop (ConstantExpr x)) = True" |
"dc_no_func _ = False"

fun act_no_func_dcs::"ast_temporal_action_schema \<Rightarrow> bool" where
"act_no_func_dcs (SimpleActionSchema h b) = True" |
"act_no_func_dcs (DurativeActionSchema h (DurativeActionBody dc cond deff)) = (list_all dc_no_func (map snd dc))"

fun duration_constraint_integer::"term duration_constraint \<Rightarrow> bool" where
"duration_constraint_integer (DurationConstraint dop (ConstantExpr x)) = is_integer x" |
"duration_constraint_integer _ = False"

fun act_dcs_integers::"ast_temporal_action_schema \<Rightarrow> bool" where
"act_dcs_integers (SimpleActionSchema h b) = True" |
"act_dcs_integers (DurativeActionSchema h (DurativeActionBody dc cond deff)) = (list_all duration_constraint_integer (map snd dc))"

fun ground_act_pres_pos::"ground_action \<Rightarrow> bool" where
"ground_act_pres_pos (GroundAction pre eff) = (pos_conj_form pre)"

fun ground_act_no_args::"ground_action \<Rightarrow> bool" where
"ground_act_no_args (GroundAction pre eff) = (
  form_preds_no_args pre
\<and> list_all form_preds_no_args (ast_effect.adds eff)
\<and> list_all form_preds_no_args (ast_effect.dels eff)
)"

fun dc_to_lb::"term duration_constraint \<Rightarrow> rat lower_bound option" where
"dc_to_lb (DurationConstraint duration_op.EQ (ConstantExpr x)) = Some (lower_bound.GE x)" |
"dc_to_lb (DurationConstraint duration_op.GEQ (ConstantExpr x)) = Some (lower_bound.GE x)" |
"dc_to_lb _ = None"

definition dc_list_lower::"term duration_constraint list \<Rightarrow> rat lower_bound option" where
"dc_list_lower xs \<equiv> map dc_to_lb xs |> (\<lambda>xs. max_lb_opt xs None)" 

fun dc_to_ub::"term duration_constraint \<Rightarrow> rat upper_bound option" where
"dc_to_ub (DurationConstraint duration_op.EQ (ConstantExpr x)) = Some (upper_bound.LE x)" |
"dc_to_ub (DurationConstraint duration_op.LEQ (ConstantExpr x)) = Some (upper_bound.LE x)" |
"dc_to_ub _ = None"

definition dc_list_upper::"term duration_constraint list \<Rightarrow> rat upper_bound option" where
"dc_list_upper xs = map dc_to_ub xs |> (\<lambda>xs. min_ub_opt xs None)" 

locale ground_ast_problem_defs = ast_temporal_problem P
  for P :: ast_temporal_problem
begin

lemma (in ast_temporal_problem) wf_fmla_atom_imp_is_predAtom:
  assumes "wf_fmla_atom M a"
  shows "is_predAtom a"
  using assms by (induction a rule: wf_fmla_atom.induct) auto

definition "props_spec \<equiv> map pred (predicates D)"

definition "prop_to_name_spec \<equiv> predicate.name"

definition "actions_spec \<equiv> actions D"

definition "act_to_name_spec \<equiv> ast_temporal_action_schema_name"

definition "to_predicates \<equiv> to_literals #> map to_predicate"

definition init_spec::"predicate list" where
"init_spec \<equiv>
  init P
  |> filter (is_predAtom)
  |> map to_predicate
  |> remdups"


(* To do: ensure that this consists of predicates only *)
definition goal_spec::"predicate list" where
  "goal_spec \<equiv> 
  goal P
  |> to_literals
  |> map to_predicate
  |> remdups"

definition "ground_non_action \<equiv> GroundAction (Formulas.Not Formulas.Bot) (Effect [] [] [])"

fun at_start_spec::"ast_temporal_action_schema \<Rightarrow> ground_action" where
"at_start_spec (SimpleActionSchema h b) = instantiate_temporal_action_schema (SimpleActionSchema h b) []" |
"at_start_spec (DurativeActionSchema h (DurativeActionBody dc cond deff)) = inst_snap_action_body_elements [] cond deff (tsubst h []) 0 At_Start"

fun at_end_spec::"ast_temporal_action_schema \<Rightarrow> ground_action" where
"at_end_spec (SimpleActionSchema h b) = ground_non_action" |
"at_end_spec (DurativeActionSchema h (DurativeActionBody dc cond deff)) = inst_snap_action_body_elements [] cond deff (tsubst h []) 0 At_End"

fun over_all_snap::"ast_temporal_action_schema \<Rightarrow> ground_action" where
"over_all_snap (SimpleActionSchema h b) = ground_non_action" |
"over_all_snap (DurativeActionSchema h (DurativeActionBody dc cond deff)) = inst_snap_action_body_elements [] cond deff (tsubst h []) 0 Over_All"

fun pre_spec::"ground_action \<Rightarrow> predicate list" where
"pre_spec (GroundAction form eff) = 
  form
  |> to_literals
  |> map to_predicate
  |> remdups"

fun over_all_spec::"ast_temporal_action_schema \<Rightarrow> predicate list" where
"over_all_spec x =
  x
  |> over_all_snap
  |> pre_spec"

fun adds_spec::"ground_action \<Rightarrow> predicate list" where
"adds_spec (GroundAction form eff) =
  eff
  |> ast_effect.adds
  |> map to_predicate
  |> remdups
"

fun dels_spec::"ground_action \<Rightarrow> predicate list" where
"dels_spec (GroundAction form eff) =
  eff
  |> ast_effect.dels
  |> map to_predicate
  |> remdups
"

fun lower_spec::"ast_temporal_action_schema \<Rightarrow> _" where
"lower_spec (SimpleActionSchema h b) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec (DurativeActionSchema h (DurativeActionBody dc cond deff)) = map_option (map_lower_bound floor) (dc_list_lower (map snd dc))"

fun upper_spec::"ast_temporal_action_schema \<Rightarrow> _" where
"upper_spec (SimpleActionSchema h b) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec (DurativeActionSchema h (DurativeActionBody dc cond deff)) = map_option (map_upper_bound floor) (dc_list_upper (map snd dc))"


lemma pre_spec_alt:
  "pre_spec a = 
  ground_action.precondition a
  |> to_literals
  |> map to_predicate
  |> remdups"
  by (cases a) simp


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

lemma is_pos_conj_to_literals_conv_atoms:
  assumes "is_pos_conj form" and "form_preds_no_args form"
  shows "Atom ` atoms form = set (to_literals form)"
  using assms unfolding form_preds_no_args_def
proof (induction form)
  case (Atom x) thus ?case by (cases x) auto
next
  case (And x y)
  from And.prems have px: "is_pos_lit x" and py: "is_pos_conj y"
    and fx: "\<forall>a\<in>atoms x. atom_no_args a" and fy: "\<forall>a\<in>atoms y. atom_no_args a" by auto
  from px have "is_pos_conj x" by (cases x) auto
  hence "Atom ` atoms x = set (to_literals x)" using And.IH(1) fx by simp
  moreover have "Atom ` atoms y = set (to_literals y)" using And.IH(2) py fy by simp
  ultimately show ?case by (simp add: image_Un)
next
  case (Not x) thus ?case by (cases x) (auto elim!: atom_no_args.elims)
qed auto

text \<open>Instantiation preservation (BOUNDARY BRIDGE): inst_formula's atom-map keeps predAtm/eqAtm and
  is identity on predAtm, so is_pos_conj, form_preds_no_args and hence pos_conj_form carry through --
  the grounder's is_pos_conj + eqAtm-free side condition on the (term) snap conditions gives
  pos_conj_form of the (object) instantiated ground precondition.\<close>

lemma is_pos_lit_inst_formula:
  "is_pos_lit L \<Longrightarrow> is_pos_lit (inst_formula f dur L)"
  by (induction L rule: is_pos_lit.induct) (auto simp: inst_formula.simps)

lemma is_pos_lit_imp_is_pos_conj: "is_pos_lit L \<Longrightarrow> is_pos_conj L"
  by (cases L rule: is_pos_conj.cases) auto

lemma is_pos_conj_inst_formula:
  "is_pos_conj c \<Longrightarrow> is_pos_conj (inst_formula f dur c)"
proof (induction c rule: is_pos_conj.induct)
  case (1 F G)
  from "1.prems" have "is_pos_lit F" and "is_pos_conj G" by auto
  from \<open>is_pos_lit F\<close> have "is_pos_lit (inst_formula f dur F)" by (rule is_pos_lit_inst_formula)
  moreover from \<open>is_pos_conj G\<close> have "is_pos_conj (inst_formula f dur G)" by (rule "1.IH")
  ultimately show ?case by (simp add: inst_formula.simps)
next
  case ("2_1" v) thus ?case by (cases v) (auto simp: inst_formula.simps)
next
  case "2_2" thus ?case by (simp add: inst_formula.simps)
next
  case ("2_3" v) thus ?case by (cases "\<^bold>\<not> v" rule: is_pos_lit.cases) (auto simp: inst_formula.simps)
next
  case ("2_4" v va) thus ?case by simp
next
  case ("2_5" v va) thus ?case by simp
qed

lemma form_preds_no_args_inst_formula:
  assumes "form_preds_no_args c"
  shows "form_preds_no_args (inst_formula f dur c)"
proof -
  have h: "atom_no_args (inst_duration_in_atom (map_atom f a) dur)" if "atom_no_args a" for a
    using that by (cases a rule: atom_no_args.cases) auto
  show ?thesis using assms unfolding form_preds_no_args_def inst_formula.simps
    by (auto simp: formula.set_map h)
qed

lemma pos_conj_form_inst_formula:
  assumes "is_pos_conj c" and "form_preds_no_args c"
  shows "pos_conj_form (inst_formula f dur c)"
  unfolding pos_conj_form_def
  using is_pos_conj_to_literals_conv_atoms[OF is_pos_conj_inst_formula[OF assms(1)]
                                              form_preds_no_args_inst_formula[OF assms(2)]] .

lemma is_pos_conj_atoms_preds:
  assumes "form_preds_no_args form"
  shows "\<forall>a \<in> Atom ` atoms form. is_predAtom a"
proof
  fix a assume "a \<in> Atom ` atoms form"
  then obtain x where x: "a = Atom x" and "x \<in> atoms form" by auto
  hence "atom_no_args x" using assms unfolding form_preds_no_args_def by blast
  thus "is_predAtom a" unfolding x by (cases x) auto
qed

lemma is_pos_conj_predicates: 
  assumes "is_pos_conj form" and "form_preds_no_args form"
  shows "to_predicate ` Atom ` atoms form = set (map to_predicate (to_literals form))"
  using assms unfolding set_remdups set_map 
  using is_pos_conj_to_literals_conv_atoms[OF assms]
  by simp 

lemma pos_conj_form_predicates:
  assumes "pos_conj_form form"
  shows "to_predicate ` Atom ` atoms form = set (map to_predicate (to_literals form))"
  using assms unfolding pos_conj_form_def by (metis set_map) 


lemma is_predAtom_imp_is_pos_conj:
  assumes "is_predAtom f"
  shows "is_pos_conj f"
  using assms 
  by (induction f rule: is_predAtom.induct) simp+
  
lemma is_predAtom_literals:
  assumes "is_predAtom f"
  shows "to_literals f = [f]"
  using assms
  by (induction f rule: is_predAtom.induct) simp+

text \<open>Forward (monotone) half of the models/superset correspondence, with NO positivity
  hypothesis: satisfaction always forces the formula's \<^emph>\<open>positively-occurring predicate\<close> literals into
  the logical world model.  @{const to_literals} keeps only those (every other shape --- equality,
  numeric, negated, disjunction, implication --- maps to \<^term>\<open>[]\<close>), so the duration-constraint
  numeric atoms FPS folds into snap preconditions are simply dropped here and handled by the numeric
  layer instead (see the duration-atom-positivity decision in \<open>SEMANTICS_REPOINT_PLAN.md\<close>).  This is
  the grounder's actual contract (cf. classical \<open>valuation_pos_conj_mono\<close>).\<close>
lemma to_literals_subset_if_models:
  assumes "valuation M \<Turnstile>\<^sub>m form"
  shows "set (to_literals form) \<subseteq> fst M"
  using assms
proof (induction form)
  case (Atom x)
  thus ?case by (cases x) (auto simp: valuation_def map_formula_semantics_simps)
next
  case (And f g)
  thus ?case by (auto simp: map_formula_semantics_simps)
qed auto

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

lemma form_preds_no_args_map_atom:
  assumes "form_preds_no_args c"
  shows "form_preds_no_args (Formulas.map_formula (map_atom f) c)"
proof -
  have h: "atom_no_args (map_atom f a)" if "atom_no_args a" for a
    using that by (cases a rule: atom_no_args.cases) auto
  show ?thesis using assms unfolding form_preds_no_args_def
    by (auto simp: formula.set_map h)
qed

lemma pos_conj_form_map_atom:
  assumes "is_pos_conj c" and "form_preds_no_args c"
  shows "pos_conj_form (Formulas.map_formula (map_atom f) c)"
  unfolding pos_conj_form_def
  using is_pos_conj_to_literals_conv_atoms[OF is_pos_conj_map_formula[OF assms(1)]
                                              form_preds_no_args_map_atom[OF assms(2)]] .

lemma instantiate_action_schema_pres_pos:
  assumes "act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "form_preds_no_args pre"
    shows "ground_act_pres_pos (instantiate_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff)) as)"
proof -
  have 1: "is_pos_conj pre"
    using assms by auto
  show ?thesis
    unfolding instantiate_temporal_action_schema.simps instantiate_simple_body.simps Let_def
    using pos_conj_form_map_atom[OF 1 assms(2)] by simp
qed


lemma inst_formula_BigAnd:
  "inst_formula f dur (BigAnd Fs) = BigAnd (map (inst_formula f dur) Fs)"
  by (induction Fs) (auto simp: inst_formula.simps)

text \<open>The snap precondition specs are built with no duration constraints (\<open>dc = []\<close>, cf.
  \<^const>\<open>at_start_spec\<close>/\<^const>\<open>at_end_spec\<close>/\<^const>\<open>over_all_snap\<close>), so the precondition is a positive
  conjunction of the (predicate) timed conditions only -- the numeric duration atoms enter the
  network locale separately via \<^const>\<open>lower_spec\<close>/\<^const>\<open>upper_spec\<close>, not here.\<close>
lemma inst_snap_act_pres_pos:
  assumes "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
      and "list_all form_preds_no_args (map snd cond)"
    shows "ground_act_pres_pos (inst_snap_action_body_elements [] cond deff (tsubst h args) dur anno)"
proof -
  have pos: "list_all is_pos_conj (filter_time_spec anno cond)"
    using assms(1)
    unfolding filter_time_spec_def comp_def
    apply (subst (asm) act_pres_pos.simps)
    unfolding list_all_iff by auto
  have noargs: "list_all form_preds_no_args (filter_time_spec anno cond)"
    using assms(2) unfolding filter_time_spec_def list_all_iff by auto
  have "\<forall>c \<in> set (filter_time_spec anno cond). pos_conj_form (inst_formula (tsubst h args) dur c)"
    using pos noargs unfolding list_all_iff by (blast intro: pos_conj_form_inst_formula)
  hence "pos_conj_form (BigAnd (map (inst_formula (tsubst h args) dur) (filter_time_spec anno cond)))"
    by (auto intro!: pos_conj_form_BigAnd)
  hence "pos_conj_form (inst_formula (tsubst h args) dur (BigAnd (filter_time_spec anno cond)))"
    by (simp only: inst_formula_BigAnd)
  thus ?thesis
    by (simp add: inst_snap_action_body_elements.simps Let_def)
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
  shows "pred_option (pred_lower_bound is_integer) (dc_to_lb dc)"
  using assms
  apply (cases dc rule: duration_constraint_integer.cases)
   apply (simp_all)
  subgoal for dop c
    by (cases dop; cases c) auto
  done

lemma dc_integer_imp_ub_integer:
  assumes "duration_constraint_integer dc"
  shows "pred_option (pred_upper_bound is_integer) (dc_to_ub dc)"
  using assms
  apply (cases dc rule: duration_constraint_integer.cases)
   apply (simp_all)
  subgoal for dop c
    by (cases dop; cases c) auto
  done

sublocale imp_defs: temp_planning_problem_list_defs_int 
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  init_spec goal_spec 0 props_spec actions_spec
  by unfold_locales simp


lemma ground_non_action_pre:
  "pre_spec ground_non_action = []"
  unfolding ground_non_action_def by auto

lemma ground_non_action_adds:
  "adds_spec ground_non_action = []"
  unfolding ground_non_action_def by auto

lemma ground_non_action_dels:
  "dels_spec ground_non_action = []"
  unfolding ground_non_action_def by auto

lemma inj_on_to_predicate:
  "inj_on to_predicate {x. form_preds_no_args x \<and> is_predAtom x}"
proof (rule inj_onI)
    fix x y::"object atom Formulas.formula"
    assume xy: "x \<in> {x. form_preds_no_args x \<and> is_predAtom x}" 
      "y \<in> {x. form_preds_no_args x \<and> is_predAtom x}"
    assume eq: "to_predicate x = to_predicate y"
    obtain m as where
      x: "x = Atom (predAtm m as)"  using xy
      apply (cases x rule: is_predAtom.cases) by auto
    obtain n bs where
      y: "y = Atom (predAtm n bs)" using xy
      apply (cases y rule: is_predAtom.cases) by auto

    have x: "x = Atom (predAtm m [])" using xy x unfolding form_preds_no_args_def 
      by (cases as) auto
    
    have y: "y = Atom (predAtm n [])" using xy y unfolding form_preds_no_args_def 
      by (cases bs) auto

    show "x = y" using eq x y by simp
  qed

lemma ground_act_no_args_imp_dels_no_args:
  assumes "ground_act_no_args h"
      and  "x \<in> set (dels (ground_action.effect h))"
    shows "form_preds_no_args x"
  using assms
  apply (induction h)
  unfolding ground_act_no_args.simps
  subgoal for pre eff
    apply (induction eff)
    unfolding list_all_iff
    unfolding ground_action.sel
    by blast
  done

lemma ground_act_no_args_imp_adds_no_args:
  assumes "ground_act_no_args h"
      and  "x \<in> set (adds (ground_action.effect h))"
    shows "form_preds_no_args x"
  using assms
  apply (induction h)
  unfolding ground_act_no_args.simps
  subgoal for pre eff
    apply (induction eff)
    unfolding list_all_iff
    unfolding ground_action.sel
    by blast
  done

lemma wf_ground_action_dels_preds:
  assumes "wf_ground_action h"
      and  "x \<in> set (dels (ground_action.effect h))"
    shows "is_predAtom x"
  using assms
  apply (induction h)
  unfolding wf_ground_action.simps wf_effect.simps ground_action.sel 
  subgoal for pre eff
    apply (induction eff)
    using wf_fmla_atom_imp_is_predAtom
    by auto
  done

lemma wf_ground_action_adds_preds:
  assumes "wf_ground_action h"
      and  "x \<in> set (adds (ground_action.effect h))"
    shows "is_predAtom x"
  using assms
  apply (induction h)
  unfolding wf_ground_action.simps wf_effect.simps ground_action.sel 
  subgoal for pre eff
    apply (induction eff)
    using wf_fmla_atom_imp_is_predAtom
    by auto
  done

lemma inj_on_to_literals:
  "inj_on to_literals {x. is_predAtom x}"
  apply (rule inj_onI)
  apply (elim CollectE)
  subgoal for x y
    apply (induction x rule: is_predAtom.induct; induction y rule: is_predAtom.induct)
    by simp+
  done

lemma inj_on_set_to_literals:
  "inj_on (\<lambda>x. set (to_literals x)) {x. is_predAtom x}"
  apply (rule inj_onI)
  apply (elim CollectE)
  subgoal for x y
    apply (induction x rule: is_predAtom.induct; induction y rule: is_predAtom.induct)
    by auto
  done

lemma adds_spec_alt:
  "adds_spec h = 
    ground_action.effect h
    |> ast_effect.adds
    |> map to_predicate
    |> remdups"
  by (cases h) auto

lemma dels_spec_alt:
  "dels_spec h = 
    ground_action.effect h
    |> ast_effect.dels
    |> map to_predicate
    |> remdups"
  by (cases h) auto

end


text \<open>Numeric-free / integer-duration assumptions for the (numeric-free) NTA reduction phase that
  the grounder's grounded/positive locales do not cover: no numeric functions, duration constraints
  are function-free and integer-valued. Bundled with the grounder's grounded_temporal_problem
  + positive_temporal_problem by ground_ast_problem below.\<close>
locale integer_duration_problem = wf_ast_temporal_problem P
  for P :: ast_temporal_problem +
  assumes no_functions: "functions D = []"
      and acts_no_func_dcs: "list_all act_no_func_dcs (actions D)"
      and acts_dcs_integers: "list_all act_dcs_integers (actions D)"

locale ground_ast_problem_core =
    ground_ast_problem_defs P +
    wf_ast_temporal_problem P
  for P :: ast_temporal_problem +
  assumes positive_goal: "is_pos_conj (goal P)"
      and preds_no_args: "list_all pred_no_args (predicates D)"
      and acts_no_params: "list_all act_no_params (actions D)"
      and acts_no_func_dcs: "list_all act_no_func_dcs (actions D)"
      and acts_dcs_integers: "list_all act_dcs_integers (actions D)"
      and positive_act_pres: "list_all act_pres_pos (actions D)"
      and conds_no_args: "list_all act_conds_no_args (actions D)"
      and no_consts: "consts D = []"
      and init_no_args: "list_all form_preds_no_args (init P)"

text \<open>Numeric-freeness is an \<^emph>\<open>orthogonal leaf\<close> off the shared @{text ground_ast_problem_core}
  (grounder idiom: cf. the grounder's @{text numeric_free_problem}), \<^bold>\<open>not\<close> part of the core: the
  classical admission bundle @{text ground_ast_problem} is \<open>core\<close> + @{text no_functions}; the numeric
  admission bundle @{text numeric_ground_ast_problem} (in @{text Ground_PDDL_Numeric_Problem_Defs}) is
  \<open>core\<close> + the numeric-fragment well-formedness. The core stays numeric-inclusive so both leaves share it.\<close>

locale ground_ast_problem =
    ground_ast_problem_core P
  for P :: ast_temporal_problem +
  assumes no_functions: "functions D = []"
begin

lemma acts_wf:
  assumes "a \<in> set actions_spec"
  shows " wf_temporal_action_schema a"
  using wf_temporal_domain assms unfolding wf_temporal_domain_def actions_spec_def by blast

lemma distinct_act_names:
  "distinct (map ast_temporal_action_schema_name actions_spec)"
  unfolding actions_spec_def using wf_temporal_domain wf_temporal_domain_def by simp

lemma resolve_action_in_actions:
  assumes "resolve_temporal_action_schema n = Some a"
  shows "a \<in> set actions_spec"
  using assms unfolding resolve_temporal_action_schema_def actions_spec_def
  by (blast dest: index_by_eq_SomeD)

lemma act_params_match_empty:
  assumes "parameters h = []"
  shows "action_params_match h []"
  using assms
  unfolding action_params_match_def
  by simp
  
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
qed


text \<open>Snap actions are well formed, because they are just ground actions obtained using the
functions in the PDDL formalisation\<close>

text \<open>A durative schema in the domain, with empty parameters, yields a well-formed snap action
  via @{const inst_snap_action_body_elements} with no duration constraints in the precondition.\<close>
lemma durative_snap_body_wf:
  assumes "DurativeActionSchema h (DurativeActionBody dc cond deff) \<in> set actions_spec"
  shows "wf_ground_action (inst_snap_action_body_elements [] cond deff (tsubst h []) dur ta)"
proof (rule wf_inst_snap_action_body_elements)
  have wf: "wf_temporal_action_schema (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using acts_wf assms by blast
  hence wfh: "wf_action_head h"
   and wfb: "wf_temporal_durative_action_body (ty_term (map_of (parameters h)) constT) (DurativeActionBody dc cond deff)"
    unfolding wf_temporal_action_schema.simps Let_def by blast+
  have "parameters h = []"
    using acts_no_params assms unfolding actions_spec_def list_all_iff by fastforce
  thus "action_params_match h []"
    using act_params_match_empty by blast
  show "wf_action_head h" using wfh .
  show "wf_cont_change_action_body_elements (ty_term (map_of (parameters h)) constT) [] cond deff"
    using wfb unfolding wf_temporal_durative_action_body.simps
      wf_cont_change_action_body_elements.simps by simp
qed

lemma start_snaps_wf:
  assumes "a \<in> set actions_spec"
  shows "wf_ground_action (at_start_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case
    unfolding at_start_spec.simps
  proof (rule wf_inst_temporal_action_schema)
    have "parameters h = []"
      using acts_no_params SimpleActionSchema unfolding actions_spec_def list_all_iff by fastforce
    thus "action_params_match h []"
      using act_params_match_empty by blast
    show "wf_temporal_action_schema (SimpleActionSchema h b)"
      using acts_wf SimpleActionSchema by blast
  qed
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where
    b: "b = DurativeActionBody dc cond deff" by (cases b)
  show ?case
    unfolding at_start_spec.simps b
    using durative_snap_body_wf DurativeActionSchema b by blast
qed

lemma end_snaps_wf:
  assumes "a \<in> set actions_spec"
  shows "wf_ground_action (at_end_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case
    unfolding at_end_spec.simps
    unfolding ground_non_action_def by auto
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where
    b: "b = DurativeActionBody dc cond deff" by (cases b)
  show ?case
    unfolding at_end_spec.simps b
    using durative_snap_body_wf DurativeActionSchema b by blast
qed

text \<open>The over-all condition is obtained by first instantiating the action.\<close>
lemma over_all_snap_wf:
  assumes "a \<in> set actions_spec"
  shows "wf_ground_action (over_all_snap a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case
    unfolding over_all_snap.simps
    unfolding ground_non_action_def by auto
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where
    b: "b = DurativeActionBody dc cond deff" by (cases b)
  show ?case
    unfolding over_all_snap.simps b
    using durative_snap_body_wf DurativeActionSchema b by blast
qed

text \<open>Snap actions have no arguments\<close>
lemma act_no_params:
  assumes "a \<in> set actions_spec"
  shows "act_no_params a"
  using assms unfolding actions_spec_def using acts_no_params unfolding list_all_iff 
  by simp

lemma act_pres_pos_spec:
  assumes "a \<in> set actions_spec"
  shows "act_pres_pos a"
  using assms unfolding actions_spec_def using positive_act_pres unfolding list_all_iff
  by simp

lemma act_conds_no_args_spec:
  assumes "a \<in> set actions_spec"
  shows "act_conds_no_args a"
  using assms unfolding actions_spec_def using conds_no_args unfolding list_all_iff
  by simp

lemma constT_None:
  "constT x = None"
  by (simp add: domain_signature.constT_def no_consts)

text \<open>An atom that is well-formed over the empty type environment (no constants, no variables)
  cannot have any arguments: a predicate atom's arguments would have to be typed, but no entity is.\<close>
lemma wf_atom_no_args:
  assumes "wf_atom (ty_term (map_of []) constT) (predAtm n obs)"
  shows "atom_no_args (predAtm n obs)"
  using assms
  apply (cases obs)
   apply simp
  subgoal for ob' obs'
    unfolding wf_atom.simps wf_pred_atom.simps
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

text \<open>In the numeric-free setting a well-formed positive conjunction over the empty type
  environment has only argument-free predicate atoms (no numeric/equality atoms, by positivity;
  no arguments, by the empty type environment).\<close>
lemma wf_fmla_imp_wf_atom:
  assumes "wf_fmla tyt form"
      and "a \<in> formula.atoms form"
  shows "wf_atom tyt a"
  using assms by (induction form) auto

text \<open>A well-formed formula ATOM (a single \<open>predAtm\<close> over the empty term signature) is nullary --
  from well-formedness alone (no positivity / eqAtm-free condition needed for effect atoms).\<close>
lemma wf_fmla_atom_no_args:
  assumes "wf_fmla_atom (ty_term (map_of []) constT) form" 
  shows "form_preds_no_args form" 
  unfolding form_preds_no_args_def
proof
  fix a assume a: "a \<in> formula.atoms form"
  have "is_predAtom form" using assms wf_fmla_atom_imp_is_predAtom by blast
  then obtain n obs where feq: "form = Atom (predAtm n obs)"
    by (cases form rule: is_predAtom.cases) auto
  with a have a_eq: "a = predAtm n obs" by simp
  have "wf_atom (ty_term (map_of []) constT) (predAtm n obs)"
    using assms feq wf_fmla_atom_alt by auto
  thus "atom_no_args a" unfolding a_eq using wf_atom_no_args by blast
qed

lemma map_formula_no_args_gen:
  assumes "form_preds_no_args form"
      and "\<And>p. atom_no_args (g (predAtm p []))"
  shows "form_preds_no_args (Formulas.map_formula g form)"
  using assms
  unfolding form_preds_no_args_def
  apply (induction form)
  subgoal for x
    apply (cases x)
          subgoal for p as
            apply (cases as)
            by auto
          by auto
  by auto

lemma map_formula_no_args:
  assumes "form_preds_no_args form"
  shows "form_preds_no_args ((Formulas.map_formula o map_atom) f form)"
  unfolding comp_def
  apply (rule map_formula_no_args_gen[OF assms])
  by simp

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
  assumes "act_no_params (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "wf_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff))"
      and "act_conds_no_args (SimpleActionSchema h (SimpleActionBody pre eff))"
    shows "ground_act_no_args (instantiate_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff)) as)"
proof -
  have ps: "parameters h = []" using assms(1) by simp
  have p: "wf_fmla (ty_term (map_of []) constT) pre" 
   and e: "wf_effect (ty_term (map_of []) constT) eff" 
    using assms(2) ps unfolding wf_temporal_action_schema.simps wf_simple_action_body.simps Let_def by auto

  have pre_no_args: "form_preds_no_args pre" using assms(4) by simp

  have eff_adds_no_args: "list_all form_preds_no_args (adds eff)"
    apply (cases eff) 
    using wf_fmla_atom_no_args e unfolding list_all_iff
    by auto

  have eff_dels_no_args: "list_all form_preds_no_args (dels eff)"
    apply (cases eff) 
    using wf_fmla_atom_no_args e unfolding list_all_iff
    by auto

  show ?thesis
    unfolding instantiate_temporal_action_schema.simps instantiate_simple_body.simps Let_def
    unfolding ground_act_no_args.simps ground_action.sel
    using pre_no_args eff_adds_no_args eff_dels_no_args 
    using map_formula_no_args map_effect_adds_no_args map_effect_dels_no_args by fastforce
qed


lemma inst_snap_action_no_params:
  assumes "act_no_params (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
      and "wf_temporal_action_schema (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
      and "act_pres_pos (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
      and "act_conds_no_args (DurativeActionSchema h (DurativeActionBody dcs cond deff))"
    shows "ground_act_no_args (inst_snap_action_body_elements [] cond deff (tsubst h args) dur ta)"
proof -
  have ps: "parameters h = []" using assms(1) by simp
  have p: "\<forall>(t, pre) \<in> set cond. wf_fmla (ty_term (map_of []) constT) pre" 
   and e: "\<forall>(t, eff) \<in> set deff. wf_effect (ty_term (map_of []) constT) eff" 
    using assms(2) ps unfolding wf_temporal_action_schema.simps wf_temporal_durative_action_body.simps Let_def by auto
  
  have pre_no_args: "\<forall>(t, pre) \<in> set cond. form_preds_no_args pre"
    using assms(4) unfolding act_conds_no_args.simps list_all_iff by auto

  have eff_adds_no_args: "\<forall>(t, eff) \<in> set deff. list_all form_preds_no_args (adds eff)"
    using wf_fmla_atom_no_args e unfolding list_all_iff
    apply (intro ballI)
    subgoal for x
      apply (cases x)
      subgoal for t eff
        apply (cases eff)
        by auto
      done
    done

  have eff_dels_no_args: "\<forall>(t, eff) \<in> set deff. list_all form_preds_no_args (dels eff)"
    using wf_fmla_atom_no_args e unfolding list_all_iff
    apply (intro ballI)
    subgoal for x
      apply (cases x)
      subgoal for t eff
        apply (cases eff)
        by auto
      done
    done

  have adds_eq: "adds (inst_duration_in_ast_effect e dur) = adds e" for e
    by (cases e) auto
  have dels_eq: "dels (inst_duration_in_ast_effect e dur) = dels e" for e
    by (cases e) auto

  show ?thesis unfolding inst_snap_action_body_elements.simps Let_def inst_formula.simps
    unfolding ground_act_no_args.simps ground_action.sel
    unfolding adds_eq dels_eq
    apply (intro conjI)
      apply (rule map_formula_no_args_gen)
       apply (rule form_preds_no_args_Big_And)
       apply (subst filter_time_spec_def)
       apply (subst list_all_iff)
    using pre_no_args apply auto[1]
      apply simp
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
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  obtain pre eff where
    b: "b = SimpleActionBody pre eff" by (cases b)
  show ?case 
    unfolding at_start_spec.simps b
    apply (rule instantiate_action_schema_no_params[where as = "[]", unfolded b])
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec SimpleActionSchema b by blast+
next
  case (DurativeActionSchema h b)
  obtain dcs cond deff where
    b: "b = DurativeActionBody dcs cond deff" by (cases b)
  show ?case 
    unfolding at_start_spec.simps b
    apply (rule inst_snap_action_no_params)
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec DurativeActionSchema b by blast+
qed

lemma end_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (at_end_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case 
    unfolding at_end_spec.simps ground_non_action_def
    by (simp add: form_preds_no_args_def)
next
  case (DurativeActionSchema h b)
  obtain dcs cond deff where
    b: "b = DurativeActionBody dcs cond deff" by (cases b)
  show ?case 
    unfolding at_end_spec.simps b
    apply (rule inst_snap_action_no_params)
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec DurativeActionSchema b by blast+
qed

text \<open>The over-all condition is obtained by first instantiating the action.\<close>

lemma over_all_snap_no_args:
  assumes "a \<in> set actions_spec"
  shows "ground_act_no_args (over_all_snap a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case 
    unfolding over_all_snap.simps ground_non_action_def
    by (simp add: form_preds_no_args_def)
next
  case (DurativeActionSchema h b)
  obtain dcs cond deff where
    b: "b = DurativeActionBody dcs cond deff" by (cases b)
  show ?case 
    unfolding over_all_snap.simps b
    apply (rule inst_snap_action_no_params)
    using act_no_params acts_wf act_pres_pos_spec act_conds_no_args_spec DurativeActionSchema b by blast+
qed

text \<open>Conditions\<close>
lemma start_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (at_start_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  obtain pre eff where b: "b = SimpleActionBody pre eff" by (cases b)
  have p: "act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff))"
    using SimpleActionSchema positive_act_pres unfolding actions_spec_def list_all_iff b by auto
  have n: "form_preds_no_args pre"
    using SimpleActionSchema conds_no_args unfolding actions_spec_def list_all_iff b by auto
  show ?case unfolding at_start_spec.simps b
    using instantiate_action_schema_pres_pos[OF p n, where as = "[]"] by simp
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where b: "b = DurativeActionBody dc cond deff" by (cases b)
  have p: "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using DurativeActionSchema positive_act_pres unfolding actions_spec_def list_all_iff b by auto
  have n: "list_all form_preds_no_args (map snd cond)"
    using act_conds_no_args_spec[OF DurativeActionSchema] unfolding b by simp
  from inst_snap_act_pres_pos[OF p n] show ?case unfolding at_start_spec.simps b by blast
qed

lemma end_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (at_end_spec a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case unfolding at_end_spec.simps ground_non_action_def by (simp add: pos_conj_form_def)
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where b: "b = DurativeActionBody dc cond deff" by (cases b)
  have p: "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using DurativeActionSchema positive_act_pres unfolding actions_spec_def list_all_iff b by auto
  have n: "list_all form_preds_no_args (map snd cond)"
    using act_conds_no_args_spec[OF DurativeActionSchema] unfolding b by simp
  from inst_snap_act_pres_pos[OF p n] show ?case unfolding at_end_spec.simps b by blast
qed

lemma over_all_snap_pre_pos_conj:
  assumes "a \<in> set actions_spec"
  shows "ground_act_pres_pos (over_all_snap a)"
  using assms
proof (induction a rule: ast_temporal_action_schema.induct)
  case (SimpleActionSchema h b)
  show ?case unfolding over_all_snap.simps ground_non_action_def by (simp add: pos_conj_form_def)
next
  case (DurativeActionSchema h b)
  obtain dc cond deff where b: "b = DurativeActionBody dc cond deff" by (cases b)
  have p: "act_pres_pos (DurativeActionSchema h (DurativeActionBody dc cond deff))"
    using DurativeActionSchema positive_act_pres unfolding actions_spec_def list_all_iff b by auto
  have n: "list_all form_preds_no_args (map snd cond)"
    using act_conds_no_args_spec[OF DurativeActionSchema] unfolding b by simp
  from inst_snap_act_pres_pos[OF p n] show ?case unfolding over_all_snap.simps b by blast
qed


text \<open>\<^const>\<open>to_literals\<close> only extracts \<open>predAtm\<close> literals, which are well-formed atoms whenever the
  formula is well-formed -- no positivity needed for the props inclusion.\<close>
lemma wf_fmla_imp_wf_to_literals:
  "wf_fmla M form \<Longrightarrow> list_all (wf_fmla_atom M) (to_literals form)"
  by (induction form rule: to_literals.induct) auto

text \<open>Conditions and effects of well formed ground actions are in props. Snap actions are ground actions\<close>
lemma wf_ground_action_pres_in_props:
  assumes "wf_ground_action h"
      and "ground_act_pres_pos h"
  shows "(set \<circ> pre_spec) h \<subseteq> set props_spec"
  using assms(1)
proof (induction h)
  case (GroundAction pre eff)
  have 1: "(wf_fmla objT) pre"
    using GroundAction by auto
  show ?case  
    using wf_fmla_imp_wf_to_literals[OF 1] 
      wf_fmla_atom_in_props 
    unfolding list_all_iff by auto
qed

lemma wf_ground_action_adds_in_props:
  assumes "wf_ground_action h"
  shows "(set \<circ> adds_spec) h \<subseteq> set props_spec"
  using assms
proof (induction h)
  case (GroundAction pre eff)
  have 1: "list_all (wf_fmla_atom objT) (adds eff)"
    using GroundAction unfolding wf_ground_action.simps apply (induction eff)
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
  case (GroundAction pre eff)
  have 1: "list_all (wf_fmla_atom objT) (dels eff)"
    using GroundAction unfolding wf_ground_action.simps apply (induction eff)
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
  unfolding over_all_spec.simps
  using wf_ground_action_pres_in_props[simplified comp_def]
  using over_all_snap_wf over_all_snap_pre_pos_conj by blast

lemma start_pre_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (pre_spec (at_start_spec a)) \<subseteq> set props_spec"
proof (rule wf_ground_action_pres_in_props[simplified comp_def])
  show "wf_ground_action (at_start_spec a)"
    using start_snaps_wf assms by blast
  show "ground_act_pres_pos (at_start_spec a)" 
    using start_snap_pre_pos_conj assms by blast
qed

lemma start_dels_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (dels_spec (at_start_spec a)) \<subseteq> set props_spec"
proof (rule wf_ground_action_dels_in_props[simplified comp_def])
  show "wf_ground_action (at_start_spec a)"
    using start_snaps_wf assms by blast
qed

lemma start_adds_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (adds_spec (at_start_spec a)) \<subseteq> set props_spec"
proof (rule wf_ground_action_adds_in_props[simplified comp_def])
  show "wf_ground_action (at_start_spec a)"
    using start_snaps_wf assms by blast
qed

lemma end_pre_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (pre_spec (at_end_spec a)) \<subseteq> set props_spec"
proof (rule wf_ground_action_pres_in_props[simplified comp_def])
  show "wf_ground_action (at_end_spec a)"
    using end_snaps_wf assms by blast
  show "ground_act_pres_pos (at_end_spec a)" 
    using end_snap_pre_pos_conj assms by blast
qed

lemma end_dels_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (dels_spec (at_end_spec a)) \<subseteq> set props_spec"
proof (rule wf_ground_action_dels_in_props[simplified comp_def])
  show "wf_ground_action (at_end_spec a)"
    using end_snaps_wf assms by blast
qed

lemma end_adds_in_props:
  assumes "a \<in> set actions_spec"
  shows "set (adds_spec (at_end_spec a)) \<subseteq> set props_spec"
proof (rule wf_ground_action_adds_in_props[simplified comp_def])
  show "wf_ground_action (at_end_spec a)"
    using end_snaps_wf assms by blast
qed

text \<open>The initial state and goal are in the props\<close>

text \<open>In the numeric-free setting the domain declares no functions, so the function signature is
  empty and no initialisation fact can be a (well-formed) function assignment. Hence the
  well-formedness alternative \<open>wf_fmla_atom objT f \<or> wf_func_assign f\<close> of @{const wf_temporal_problem}
  collapses to the predicate-atom case.\<close>
lemma no_functions_no_wf_func_assign:
  "\<not> wf_func_assign f"
proof (rule notI)
  assume "wf_func_assign f"
  then obtain l r where
    f: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
   and wf: "wf_primitive_numeric_expression objT l"
    by (cases f rule: wf_func_assign.cases) auto
  obtain g args where l: "l = PNE g args" by (cases l)
  have "func_sig g = Some (the (func_sig g))"
    using wf unfolding l wf_primitive_numeric_expression.simps wf_func_args.simps
    by (cases "func_sig g") auto
  thus False
    using no_functions unfolding func_sig_def by simp
qed

lemma init_wf_fmla_atoms:
  "\<forall>f\<in>set (init P). wf_fmla_atom objT f"
proof -
  have 1: "\<forall>f\<in>set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    using wf_temporal_problem unfolding wf_temporal_problem_def by auto
  show "\<forall>f\<in>set (init P). wf_fmla_atom objT f" 
    using 1 no_functions_no_wf_func_assign by blast
qed

lemma init_in_props: "set init_spec \<subseteq> set props_spec"
  using init_wf_fmla_atoms wf_fmla_atom_in_props init_spec_def by auto


lemma goal_in_props: "set goal_spec \<subseteq> set props_spec"
proof -
  have "wf_fmla objT (goal P)"
    using wf_temporal_problem unfolding wf_temporal_problem_def
    unfolding props_spec_def goal_spec_def by auto
  hence "list_all (wf_fmla_atom objT) (to_literals (goal P))" 
    using wf_pos_conj_fmla_imp_wf_atoms positive_goal by auto
  hence "set (map to_predicate (to_literals (goal P))) \<subseteq> set props_spec"
    using wf_fmla_atom_in_props unfolding set_map list_all_iff by auto
  thus ?thesis using goal_spec_def by auto
qed
end (* locale ground_ast_problem *)
end
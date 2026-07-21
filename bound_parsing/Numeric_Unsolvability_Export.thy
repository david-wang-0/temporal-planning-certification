theory Numeric_Unsolvability_Export
  imports
    "PDDL_TP_Reduction.Check_Unsolvability"
    Ground_PDDL_Numeric_Code_Export
begin

text \<open>Containers instances for the reduction's OWN numeric expression / comparison types
  (\<open>nexp\<close> / \<open>comp\<close> / \<open>cmp_op\<close> from theory \<open>Temporal_Plans\<close>) -- these are distinct from the FPS
  \<open>numeric_expression\<close> that \<open>Check_Unsolvability\<close> already derives.  The numeric admission check
  @{const check_and_make_numeric_network} sets \<open>func \<times> nexp\<close> update-lists (in
  \<open>upds_no_cross_read_list\<close>), so these element types need \<open>ceq\<close>/\<open>ccompare\<close>/\<open>set_impl\<close>; DList set
  impls keep any nesting \<open>ceq\<close>-only (Containers Userguide S3.5, same rationale as \<open>Check_Unsolvability\<close>).\<close>
derive (eq) ceq cmp_op nexp comp
derive ccompare cmp_op nexp comp
text \<open>\<open>nexp\<close>/\<open>comp\<close> carry a \<^type>\<open>rat\<close> leaf (\<open>NConst\<close>); the numeric admission check puts
  \<open>func \<times> nexp\<close> update-lists into sets, so \<open>rat\<close> needs the full Containers set sort
  \<open>ceq\<close>/\<open>ccompare\<close>/\<open>set_impl\<close> that \<open>Check_Unsolvability\<close> does not provide (it gives only
  \<open>compare\<close>/\<open>linorder\<close>).  Derive \<open>ccompare\<close> from the existing \<open>compare\<close> instance, \<open>ceq\<close> from \<open>equal\<close>.\<close>
derive (eq) ceq rat
derive (compare) ccompare rat
derive (dlist) set_impl rat

text \<open>Suppress the \<open>Eval\<close>-target \<open>term_of\<close>/enumeration machinery for the numeric types (as
  \<open>Check_Unsolvability\<close> does for the propositional AST types): without a \<open>(no) cenum\<close> instance the
  \<open>Eval\<close> code target emits \<open>Code_Evaluation.term_of\<close> code that references \<^ML_structure>\<open>Term\<close> and
  the arbitrary-precision \<open>Bit_Shifts\<close>/\<open>divMod\<close> integer helpers -- none of which survive the
  standalone MLton build.  These types are never enumerated, so \<open>(no) cenum\<close> is sound.\<close>
derive (no) cenum cmp_op nexp comp func rat
derive (dlist) set_impl cmp_op nexp comp

text \<open>@{type func} carries \<open>ceq\<close>/\<open>linorder\<close>/\<open>set_impl\<close> (from \<open>Check_Unsolvability\<close>) but no
  \<open>ccompare\<close> -- the propositional path never put \<open>func\<close> into an RBT/generic set.  The numeric
  admission check does, so derive it here (registers the comparator law the \<open>cproper_interval\<close>
  instance below relies on).\<close>
derive ccompare func

text \<open>@{type func} (the fluent-name wrapper \<open>Func (name: name)\<close>) additionally needs
  \<open>card_UNIV\<close>/\<open>cproper_interval\<close>: the numeric admission check runs \<open>is_empty\<close>/\<open>inf\<close>/\<open>remove\<close> on
  \<open>func set\<close>s (fluent sets in \<open>upds_no_cross_read_list\<close>), whose generic Containers code path
  requires them.  Same construction and rationale as \<open>predicate\<close> in \<open>Check_Unsolvability\<close>:
  \<open>func\<close> is infinite (injects from the infinite \<^type>\<open>String.literal\<close> name).\<close>
lemma infinite_UNIV_func: "infinite (UNIV :: func set)"
proof
  assume "finite (UNIV :: func set)"
  hence "finite (Func ` (UNIV :: name set))" by (blast intro: finite_subset)
  moreover have "inj_on Func (UNIV :: name set)" by (simp add: inj_on_def)
  ultimately have "finite (UNIV :: name set)" by (rule finite_imageD)
  thus False using infinite_literal by simp
qed

instantiation func :: card_UNIV begin
definition "finite_UNIV = Phantom(func) False"
definition "card_UNIV = Phantom(func) 0"
instance by intro_classes (simp_all add: finite_UNIV_func_def card_UNIV_func_def infinite_UNIV_func)
end

instantiation func :: cproper_interval begin
definition cproper_interval_func :: "func proper_interval" where "cproper_interval_func _ _ = undefined"
instance by intro_classes (simp add: infinite_UNIV_func)
end

text \<open>\<^bold>\<open>Unified \<open>Converter\<close> export (propositional + numeric).\<close>  This supersedes the
  propositional-only export in theory \<open>Check_Unsolvability\<close>: it emits the SAME module name
  (\<open>Converter\<close>) and file (\<open>code/Check_Unsolvability.ML\<close>), but from the TOP of the reduction
  stack (session \<open>bound_parsing\<close>), so the numeric network builder
  @{const check_and_make_numeric_network_opt} -- which needs the bound-inference machinery
  (@{const numeric_ground_ast_problem_defs.is_gbound_inv_exec}) that lives ABOVE
  \<open>Check_Unsolvability\<close> -- lands in the same \<open>Converter\<close> structure and shares the parser's
  \<open>problem\<close> type.  The SML tool feeds a parsed problem to BOTH
  @{const check_and_make_network_opt} (propositional path) and
  @{const check_and_make_numeric_network_opt} (numeric path) without a second parser.

  The numeric additions are:
    \<^item> @{const numeric_ground_ast_problem_defs.numeric_draft_actions} -- the INT-ified snap
      projection the (compute-side) bound inference consumes;
    \<^item> @{const check_and_make_numeric_network_opt} -- gate (@{const check_gbounds_opt}) + build;
    \<^item> the neutral projection datatype constructors (\<open>g_int\<close>/\<open>e_int\<close>) the SML glue matches on.\<close>

text \<open>Locale constants carry no auto-generated code equations; wire the one the numeric
  admission check @{const check_and_make_numeric_network} reaches transitively (its ground-data
  accessors are already \<open>[code]\<close> via the classical \<open>ground_ast_problem_code\<close> bundle and the
  \<open>numeric_ground_data_code\<close> bundle in theory \<open>Ground_PDDL_Numeric_Code_Export\<close>).\<close>
declare numeric_ground_ast_problem_defs.check_numeric_ground_problem_def[code]

export_code
  \<comment> \<open>--- propositional entries (verbatim from theory Check_Unsolvability) ---\<close>
  check_and_cert_pddl_problem_no_return check_and_make_network_opt
  parse_convert_run
  parse_convert_check
  rbt_to_list
  Inl Inr
  Result Error
  nat_of_integer integer_of_nat int_of_integer integer_of_int DBMEntry.Le DBMEntry.Lt DBMEntry.INF
  Impl1 Impl2 Impl3 Buechi Reachable_Set Buechi_Set
  formula.EX formula.EG formula.AX formula.AG formula.Leadsto
  sexp.true sexp.not sexp.and sexp.or sexp.imply sexp.eq sexp.le sexp.lt sexp.lt sexp.ge sexp.gt sexp.loc
  bexp.true bexp.not bexp.and bexp.or bexp.imply bexp.eq bexp.le bexp.lt bexp.ge bexp.gt
  exp.const exp.var exp.if_then_else exp.binop exp.unop
  acconstraint.LT acconstraint.LE acconstraint.EQ acconstraint.GT acconstraint.GE
  act.In act.Out act.Sil
  Rat.Fract Rat.of_int rat_of_digits_pair
  predAtm eqAtm predicate Pred Func Either Var Obj PredDecl FuncDecl BigAnd BigOr
  formula.Not formula.Bot Effect duration_op.LEQ duration_op.EQ duration_op.GEQ
  At_Start At_End Over_All
  map_atom Domain Problem
  term.CONST term.VAR
  PNE ConstantExpr DurationExpr FunctionExpr DurationConstraint ActionHead SimpleActionSchema DurativeActionSchema SimpleActionBody DurativeActionBody
  Assign ScaleUp ScaleDown Increase Decrease NumericEffect
  ContinuousIncrease ContinuousDecrease ContinuousEffect
  map_numeric_effect map_numeric_expression
  String.explode String.implode
  \<comment> \<open>--- numeric entries (this session) ---\<close>
  check_and_make_numeric_network_opt
  check_gbounds_opt
  numeric_ground_ast_problem_defs.numeric_draft_actions
  numeric_ground_ast_problem_defs.is_gbound_inv_exec
  GLe_i GGe_i GEq_i GLt_i GGt_i
  EC EV EAdd ESub EMul EDiv
  in Eval module_name Converter file_prefix Check_Unsolvability

end

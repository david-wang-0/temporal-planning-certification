theory Ground_PDDL_Numeric_Problem_Defs
  imports
    Ground_PDDL_Problem_Defs
    TP_NTA_Reduction.TP_NTA_Reduction_Numeric_Defs
begin

section \<open>Numeric admission locale (NUMERIC_EXEC_PLAN WP-B)\<close>

text \<open>The \<^emph>\<open>numeric leaf\<close> of the grounder-idiomatic ladder (see @{text ground_ast_problem_core} in
  @{theory PDDL_TP_Reduction.Ground_PDDL_Problem_Defs}): the static admission bundle for the
  \<^emph>\<open>numeric\<close> NTA reduction over a concrete ground PDDL problem \<open>P\<close>. It is the sibling of the classical
  leaf @{text ground_ast_problem} off the shared, numeric-inclusive @{text ground_ast_problem_core}:
  it keeps the core's nine propositional admission assumptions and \<^bold>\<open>drops @{text no_functions}\<close>
  (numeric fluents are now permitted), adding the numeric-fragment well-formedness that
  @{text numeric_tp_nta_reduction} requires.

  \<^bold>\<open>Numeric data is DEFINED from \<open>P\<close>, not fixed as parameters.\<close> Mirroring how
  @{locale ground_ast_problem_defs} defines @{text props_spec}/@{text pre_spec}/... from \<open>P\<close>, the
  auxiliary @{text numeric_ground_ast_problem_defs} below defines @{text nfluents}/@{text n_pre}/
  @{text n_inv}/@{text upds}/@{text num_init}/@{text num_goal} via the FPS->project boundary
  translation (@{text nexp_of_pddl}/@{text num_comps}/@{text upd_of_ne}). The fluent identity is the
  bare name-wrapper @{typ func} (exact mirror of the propositional @{typ predicate}); the args-carrying
  @{text PNE}/@{text predAtm} are the atom level, and grounded actions are nullary. The propositional
  snaps @{text at_start_spec}/@{text at_end_spec} are the \<^emph>\<open>full\<close> FPS snaps, so they still carry the
  numeric effects/atoms that @{text pre_spec}/@{text adds_spec} project out.

  \<^bold>\<open>What is NOT here.\<close> Two assumptions of the correctness locale are plan-scoped and belong to a
  plan-carrying sub-locale (WP-A), NOT to this plan-free admission bundle:
    \<^item> @{text num_valid} -- plan validity; supplied under the \<open>\<exists>\<pi>. numeric_plan_for_problem \<pi>\<close>
      hypothesis at the Rung-4 lift.
    \<^item> @{text num_seq_in_bounds} -- the range-boundedness reachability invariant (the \<^bold>\<open>boundedness plug
      (WP-E)\<close>, reserved for human design).

  \<^bold>\<open>Remaining parameters.\<close> Only @{text fluent_lo}/@{text fluent_hi} (the WP-E bounds plug) stay
  parameters. The fluent Munta-name map is now DEFINED (mirroring @{text prop_to_var}): the abstract
  @{text ndefs.fluent_to_var} is built off the fixed @{text fluent_to_name}, concretised here as
  @{text \<open>fluent_to_name_spec \<equiv> func.name\<close>}, so @{text fluent_to_var_inj}/@{text fluent_vars_fresh}
  become abstract lemmas (the injectivity obligation is discharged from
  @{text fluent_to_name_spec_inj}); @{text const_to_int} is likewise DEFINED, turning
  @{text const_to_int_of_int} into a lemma.\<close>

subsection \<open>FPS -> project numeric boundary translation\<close>

text \<open>The numeric twin of @{const to_literals}/@{const to_predicate}: map FPS numeric syntax into the
  project's opaque @{typ \<open>('n, 'r) nexp\<close>}/@{typ \<open>('n, 'r) comp\<close>} at the Ground_PDDL boundary.
  Transcendentals (@{const SinExpr}/@{const CosExpr}/@{const ExpExpr}/@{const PiExpr}) and
  @{const DurationExpr} are outside the supported fragment -- they map to a junk @{term \<open>NConst 0\<close>}
  that the @{text nexp_ok}/@{text comp_ok} admission checks statically exclude.\<close>

fun nexp_of_pddl :: "object numeric_expression \<Rightarrow> (func, rat) nexp" where
  "nexp_of_pddl (ConstantExpr r) = NConst r"
| "nexp_of_pddl (FunctionExpr (PNE f _)) = NVar f"
| "nexp_of_pddl (AddExpr a b) = NAdd (nexp_of_pddl a) (nexp_of_pddl b)"
| "nexp_of_pddl (SubExpr a b) = NSub (nexp_of_pddl a) (nexp_of_pddl b)"
| "nexp_of_pddl (MulExpr a b) = NMul (nexp_of_pddl a) (nexp_of_pddl b)"
| "nexp_of_pddl (DivExpr a b) = NDiv (nexp_of_pddl a) (nexp_of_pddl b)"
| "nexp_of_pddl DurationExpr = NConst 0"
| "nexp_of_pddl (SinExpr _) = NConst 0"
| "nexp_of_pddl (CosExpr _) = NConst 0"
| "nexp_of_pddl (ExpExpr _) = NConst 0"
| "nexp_of_pddl PiExpr = NConst 0"

text \<open>Numeric comparison literals of a (positive-conjunction) precondition/goal formula -- the numeric
  twin of @{const to_literals} (which keeps only @{const predAtm} literals). Recurses over @{text \<open>\<^bold>\<and>\<close>}
  and keeps the five numeric-comparison atom kinds.\<close>

fun num_comps :: "object atom Formulas.formula \<Rightarrow> (func, rat) comp list" where
  "num_comps (Atom (numericEqAtm l r))      = [Comp Ceq (nexp_of_pddl l) (nexp_of_pddl r)]"
| "num_comps (Atom (numericLessAtm l r))    = [Comp Clt (nexp_of_pddl l) (nexp_of_pddl r)]"
| "num_comps (Atom (numericLEAtm l r))      = [Comp Cle (nexp_of_pddl l) (nexp_of_pddl r)]"
| "num_comps (Atom (numericGreaterAtm l r)) = [Comp Cgt (nexp_of_pddl l) (nexp_of_pddl r)]"
| "num_comps (Atom (numericGEAtm l r))      = [Comp Cge (nexp_of_pddl l) (nexp_of_pddl r)]"
| "num_comps (x \<^bold>\<and> y) = num_comps x @ num_comps y"
| "num_comps _ = []"

text \<open>A numeric effect becomes a (fluent, RHS) update, folding the effect operator into the RHS
  (simultaneous PDDL semantics; the @{text upds_no_cross_read} admission check makes the sequential
  Munta fold faithful).\<close>

fun upd_of_ne :: "object numeric_effect \<Rightarrow> (func \<times> (func, rat) nexp)" where
  "upd_of_ne (NumericEffect numeric_effect_op.Assign    (PNE f _) e) = (f, nexp_of_pddl e)"
| "upd_of_ne (NumericEffect numeric_effect_op.Increase  (PNE f _) e) = (f, NAdd (NVar f) (nexp_of_pddl e))"
| "upd_of_ne (NumericEffect numeric_effect_op.Decrease  (PNE f _) e) = (f, NSub (NVar f) (nexp_of_pddl e))"
| "upd_of_ne (NumericEffect numeric_effect_op.ScaleUp   (PNE f _) e) = (f, NMul (NVar f) (nexp_of_pddl e))"
| "upd_of_ne (NumericEffect numeric_effect_op.ScaleDown (PNE f _) e) = (f, NDiv (NVar f) (nexp_of_pddl e))"

subsection \<open>Numeric problem data, defined from the ground problem\<close>

text \<open>Numeric twin of @{locale ground_ast_problem_defs}: the numeric problem data as functions of \<open>P\<close>
  (no assumptions). @{text nfluents} mirrors @{text \<open>map pred (predicates D)\<close>}; @{text n_pre}/@{text upds}
  read the numerics that the propositional @{text pre_spec}/@{text adds_spec} project out.\<close>

locale numeric_ground_ast_problem_defs =
    ground_ast_problem_defs P
  for P :: ast_temporal_problem
begin

definition nfluents :: "func list" where
  "nfluents \<equiv> map function_decl.func (functions D)"

text \<open>The fluent's abstract name is its bare @{typ name} (mirror of @{text \<open>prop_to_name_spec \<equiv> predicate.name\<close>}
  in @{locale ground_ast_problem_defs}); the concrete fluent Munta-variable name prefixes it with
  @{text \<open>''fluent_''\<close>} -- a computable ground-level twin of the abstract @{text ndefs.fluent_to_var},
  proved equal to it in WP-C.\<close>

definition "fluent_to_name_spec \<equiv> func.name"

definition "fluent_to_var_spec f \<equiv> STR ''fluent_'' + fluent_to_name_spec f"

definition n_pre :: "ground_action \<Rightarrow> (func, rat) comp list" where
  "n_pre g \<equiv> remdups (num_comps (ground_action.precondition g))"

definition n_inv :: "ast_temporal_action_schema \<Rightarrow> (func, rat) comp list" where
  "n_inv a \<equiv> n_pre (over_all_snap a)"

definition upds :: "ground_action \<Rightarrow> (func \<times> (func, rat) nexp) list" where
  "upds g \<equiv> map upd_of_ne (numeric_effects (ground_action.effect g))"

definition num_goal :: "(func, rat) comp list" where
  "num_goal \<equiv> remdups (num_comps (goal P))"

definition num_init_assignments :: "(func \<times> rat) list" where
  "num_init_assignments \<equiv> List.map_filter
     (\<lambda>x. case x of Atom (numericEqAtm (FunctionExpr (PNE g _)) (ConstantExpr r)) \<Rightarrow> Some (g, r)
                  | _ \<Rightarrow> None)
     (init P)"

definition num_init :: "func \<Rightarrow> rat" where
  "num_init f \<equiv> (case map_of num_init_assignments f of Some r \<Rightarrow> r | None \<Rightarrow> 0)"

text \<open>The rat->int decode is fixed as truncation (@{const floor}); on the integer fragment
  (@{text num_val_ok}) every decoded constant is already an integer, so it is exact -- and its
  left-inverse law @{text const_to_int_of_int} is now a lemma, no longer an admission assumption.\<close>

definition const_to_int :: "rat \<Rightarrow> int" where
  "const_to_int r \<equiv> \<lfloor>r\<rfloor>"

lemma const_to_int_of_int: "const_to_int (Int.of_int m) = m"
  unfolding const_to_int_def by simp

end

subsection \<open>The numeric admission leaf\<close>

locale numeric_ground_ast_problem =
    numeric_ground_ast_problem_defs P +
    ground_ast_problem_core P +
    ndefs: numeric_tp_nta_reduction_defs
      init_spec goal_spec at_start_spec at_end_spec over_all_spec lower_spec upper_spec
      pre_spec adds_spec dels_spec 0 props_spec actions_spec act_to_name_spec prop_to_name_spec
      n_pre n_inv upds num_init num_goal nfluents fluent_to_name_spec fluent_lo fluent_hi const_to_int
  for P :: ast_temporal_problem
    and fluent_lo :: "func \<Rightarrow> int"
    and fluent_hi :: "func \<Rightarrow> int" +
  \<comment> \<open>(2) Numeric well-formedness (mirror @{text numeric_tp_nta_reduction}, over the DEFINED ground data):
      updates functional + cross-read-free, per-fluent bounds ordered, fluent var names injective + FRESH.\<close>
  assumes upds_functional_start:    "\<forall>a \<in> set actions_spec. upds_functional_list (upds (at_start_spec a))"
      and upds_functional_end:      "\<forall>a \<in> set actions_spec. upds_functional_list (upds (at_end_spec a))"
      and upds_no_cross_read_start: "\<forall>a \<in> set actions_spec. upds_no_cross_read_list (upds (at_start_spec a))"
      and upds_no_cross_read_end:   "\<forall>a \<in> set actions_spec. upds_no_cross_read_list (upds (at_end_spec a))"
      and fluent_bounds_valid:      "\<forall>f \<in> set nfluents. fluent_lo f \<le> fluent_hi f"
  \<comment> \<open>(3) Integer-encoding faithfulness on the discrete fragment (grounder-match).\<close>
      and snap_upds_nexp_ok_start:
            "\<forall>a \<in> set actions_spec. \<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_start_spec a)). ndefs.nexp_ok w e)"
      and snap_upds_nexp_ok_end:
            "\<forall>a \<in> set actions_spec. \<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_end_spec a)). ndefs.nexp_ok w e)"
      and snap_pre_comp_ok_start:
            "\<forall>a \<in> set actions_spec. \<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_start_spec a)). ndefs.comp_ok w c)"
      and snap_pre_comp_ok_end:
            "\<forall>a \<in> set actions_spec. \<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_end_spec a)). ndefs.comp_ok w c)"
      and snap_inv_comp_ok:
            "\<forall>a \<in> set actions_spec. \<forall>w. ndefs.num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_inv a). ndefs.comp_ok w c)"
      and num_init_val_ok:          "\<forall>f \<in> set nfluents. num_init f \<in> \<int>"
      and snap_writes_nfluents_start:"\<forall>a \<in> set actions_spec. fst ` set (upds (at_start_spec a)) \<subseteq> set nfluents"
      and snap_writes_nfluents_end:  "\<forall>a \<in> set actions_spec. fst ` set (upds (at_end_spec a)) \<subseteq> set nfluents"
  \<comment> \<open>(4) The OLD static over_all contract (@{text n_inv_eq} / @{text n_inv_readonly} /
      @{text n_inv_init_sat}) has been \<^bold>\<open>removed\<close>: the abstract @{text numeric_tp_nta_reduction} dropped
      it (backlog #8, \<^emph>\<open>design B\<close> in NUMERIC_OVERALL_REDESIGN.md). The over_all fragment is now general
      (arbitrary while-active comparisons); the guard is discharged from plan validity's active clause at
      @{text num_edge_2} (start) and @{text num_edge_3} (end) -- a sound over-approximation, no lock and
      no write-guard -- so the numeric leaf no longer restricts over_all to equalities/read-only.\<close>
  \<comment> \<open>(5) Numeric-goal faithfulness (plan-free half). @{text const_to_int_of_int} is now a lemma of
      the defs locale, no longer assumed; the plan-scoped @{text num_valid}/@{text num_seq_in_bounds}
      are added by the plan-carrying sub-locale (WP-A), NOT here.\<close>
      and num_goal_comp_ok:    "\<And>w. ndefs.num_val_ok w \<Longrightarrow> (\<forall>c \<in> set num_goal. ndefs.comp_ok w c)"
begin

text \<open>The fluent abstract-name map is injective on the declared fluents (the @{text fluent_names}
  @{locale unique_names} obligation of @{locale numeric_tp_nta_reduction}): the domain signature makes
  the declared functions distinct, hence their @{typ func} name wrappers distinct.  Mirror of the
  propositional @{text \<open>inj_on prop_to_name_spec (set props_spec)\<close>} discharge
  (@{text Ground_PDDL_Problem_Reduction}).\<close>

lemma fluent_to_name_spec_inj: "inj_on fluent_to_name_spec (set nfluents)"
proof -
  have "distinct (map function_decl.func (functions D))"
    using wf_domain_signature unfolding wf_domain_signature_def by auto
  hence "distinct (map func.name (map function_decl.func (functions D)))"
    apply (rule distinct_inj_map)
    apply (rule injI)
    using func.expand by simp
  thus ?thesis
    unfolding fluent_to_name_spec_def nfluents_def
    unfolding distinct_map by blast
qed

text \<open>\<^bold>\<open>Next (NUMERIC_EXEC_PLAN WP-A/WP-C).\<close> The plan-carrying locale attaches a numeric plan \<open>\<pi>\<close> and
  the boundedness plug @{text num_seq_in_bounds}, then interprets @{text numeric_tp_nta_reduction_correctness}
  (imported in the WP-A file) to obtain the numeric-net certificate @{text num_valid_plan_imp_form_holds}
  over @{text num_net_impl}.\<close>

end

end

theory Ground_PDDL_Numeric_Code_Export
  imports Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl
begin

section \<open>The verified bound inference at the ground problem: executable twin + code equations\<close>

text \<open>The numeric certifier capstone (theory \<open>Numeric_Unsolvability_Export\<close>) computes the fluent box
  ITSELF with the verified interval bound inference
  (@{const numeric_tp_nta_reduction_defs.inferred_box}, theory \<open>TP_NTA_Reduction_Numeric_Inference\<close>):
  there is no untrusted box input and no executable re-check any more.  The cert locale
  @{locale numeric_ground_ast_problem_cert} assumes exactly that the inference at the injective
  @{text nred'} snaps returns the declared box.  Here we give the ground-level executable twin
  @{text inferred_box_spec} -- over the raw @{text at_start_spec}/@{text at_end_spec} snaps, in the
  no-assumption defs locale, which is what the code generator sees -- and prove it EQUAL to
  @{text \<open>ndefs.reduction_ref_impl.inferred_box\<close>} inside the leaf, so a @{text Some} result of the
  executable twin establishes the cert locale.

  The twin is spelled out (rather than being the locale constant applied to the ground data) because
  @{locale numeric_tp_nta_reduction_defs} inherits assumptions from its propositional base, so the
  exported defining equations of its constants (@{text inferred_box}, @{text draft_acts},
  @{text snap_gaction}, the translation functions) carry the locale predicate as a premise and are
  \<^emph>\<open>not\<close> code equations.  Same idiom as the primed executable net twins of
  \<open>Ground_PDDL_Numeric_NTA_Reduction_Impl\<close>.\<close>

text \<open>Global twins of the locale-internal translation into the inference's draft world
  (@{text nexp_to_dexp} / @{text comp_to_gcomp}, theory \<open>TP_NTA_Reduction_Numeric_Inference\<close>); the
  integer decode @{term cti} is an explicit argument.\<close>
primrec nexp_to_dexp_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> 'n dexp" where
  "nexp_to_dexp_exec cti (NConst c) = DConst (cti c)"
| "nexp_to_dexp_exec cti (NVar f)   = DVar f"
| "nexp_to_dexp_exec cti (NAdd a b) = DAdd (nexp_to_dexp_exec cti a) (nexp_to_dexp_exec cti b)"
| "nexp_to_dexp_exec cti (NSub a b) = DSub (nexp_to_dexp_exec cti a) (nexp_to_dexp_exec cti b)"
| "nexp_to_dexp_exec cti (NMul a b) = DMul (nexp_to_dexp_exec cti a) (nexp_to_dexp_exec cti b)"
| "nexp_to_dexp_exec cti (NDiv a b) = DDiv (nexp_to_dexp_exec cti a) (nexp_to_dexp_exec cti b)"

fun comp_to_gcomp_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) comp \<Rightarrow> 'n gcomp" where
  "comp_to_gcomp_exec cti (Comp p a b) =
     GCmp (cmp_op_to_cmpop p) (nexp_to_dexp_exec cti a) (nexp_to_dexp_exec cti b)"

context numeric_ground_ast_problem_defs
begin

text \<open>A relaxed snap as a guarded draft action, the draft action list (both snaps of every action),
  the draft initial valuation, and the inference run over the declared fluents with its own threshold
  set: verbatim the bodies of @{text snap_gaction} / @{text draft_acts} / @{text draft_init} /
  @{text inferred_box}, at the raw ground snaps.\<close>
definition snap_gaction_spec :: "ground_action \<Rightarrow> func gaction" where
  "snap_gaction_spec s =
     (map (comp_to_gcomp_exec const_to_int) (n_pre s),
      map (\<lambda>(f, e). (f, nexp_to_dexp_exec const_to_int e)) (upds s))"

definition draft_acts_spec :: "func gaction list" where
  "draft_acts_spec =
     concat (map (\<lambda>a. snap_gaction_spec (at_start_spec a) # [snap_gaction_spec (at_end_spec a)]) actions_spec)"

definition draft_init_spec :: "func dval" where
  "draft_init_spec = (\<lambda>f. const_to_int (num_init f))"

definition inferred_box_spec :: "(func \<Rightarrow> int \<times> int) option" where
  "inferred_box_spec =
     infer_fluent_bounds_on nfluents (thr_set nfluents draft_init_spec draft_acts_spec)
       draft_acts_spec draft_init_spec"

text \<open>The serialisable, name-keyed rendering of the inferred box (for the SML tool's diagnostics;
  the certifier itself recomputes the box, it never takes one as input).\<close>
definition inferred_box_list :: "(String.literal \<times> int \<times> int) list option" where
  "inferred_box_list \<equiv>
     map_option (\<lambda>b. map (\<lambda>f. (fluent_to_name_spec f, fst (b f), snd (b f))) nfluents) inferred_box_spec"

end

context numeric_ground_ast_problem
begin

text \<open>The executable twin equals the cert locale's inference.  @{text ndefs.reduction_ref_impl} (the
  @{locale numeric_tp_nta_reduction_defs} part of @{text nred'}) is interpreted at the injective
  @{const AtStart}/@{const AtEnd} snaps with @{text \<open>app_snap n_pre\<close>}/@{text \<open>app_snap upds\<close>},
  which reduce to the raw snap accessors by @{text app_snap.simps}; the translation twins agree by
  structural induction.\<close>

lemma nexp_to_dexp_exec_eq: "nexp_to_dexp_exec const_to_int e = ndefs.reduction_ref_impl.nexp_to_dexp e"
  by (induction e) simp_all

lemma comp_to_gcomp_exec_eq: "comp_to_gcomp_exec const_to_int c = ndefs.reduction_ref_impl.comp_to_gcomp c"
  by (cases c) (simp add: nexp_to_dexp_exec_eq)

lemma snap_gaction_spec_start_eq:
  "snap_gaction_spec (at_start_spec a) = ndefs.reduction_ref_impl.snap_gaction (AtStart a)"
  unfolding snap_gaction_spec_def ndefs.reduction_ref_impl.snap_gaction_def
  by (simp add: comp_to_gcomp_exec_eq nexp_to_dexp_exec_eq)

lemma snap_gaction_spec_end_eq:
  "snap_gaction_spec (at_end_spec a) = ndefs.reduction_ref_impl.snap_gaction (AtEnd a)"
  unfolding snap_gaction_spec_def ndefs.reduction_ref_impl.snap_gaction_def
  by (simp add: comp_to_gcomp_exec_eq nexp_to_dexp_exec_eq)

lemma draft_acts_spec_eq: "draft_acts_spec = ndefs.reduction_ref_impl.draft_acts"
  unfolding draft_acts_spec_def ndefs.reduction_ref_impl.draft_acts_def
  by (simp add: snap_gaction_spec_start_eq snap_gaction_spec_end_eq)

lemma draft_init_spec_eq: "draft_init_spec = ndefs.reduction_ref_impl.draft_init"
  unfolding draft_init_spec_def ndefs.reduction_ref_impl.draft_init_def ..

lemma inferred_box_spec_eq: "inferred_box_spec = ndefs.reduction_ref_impl.inferred_box"
  unfolding inferred_box_spec_def ndefs.reduction_ref_impl.inferred_box_def
  by (simp add: draft_acts_spec_eq draft_init_spec_eq)

end

section \<open>Code equations\<close>

text \<open>Code equations for the numeric ground-data accessors.  Isabelle does not auto-generate
  code equations for locale constants; the classical layer wires its own with
  \<open>ground_ast_problem_code[code]\<close> (theory \<open>Ground_PDDL_NTA_Reduction_Impl\<close>).  Here we do the
  numeric-only twin for the accessors the inference and the admission check consume.
  (\<open>at_start_spec\<close>/\<open>at_end_spec\<close>/\<open>actions_spec\<close> are already \<open>[code]\<close> from the classical bundle.)\<close>

lemmas numeric_ground_data_code =
  numeric_ground_ast_problem_defs.nfluents_def
  numeric_ground_ast_problem_defs.fluent_to_name_spec_def
  numeric_ground_ast_problem_defs.n_pre_def
  numeric_ground_ast_problem_defs.n_inv_def
  numeric_ground_ast_problem_defs.upds_def
  numeric_ground_ast_problem_defs.num_goal_def
  numeric_ground_ast_problem_defs.num_init_assignments_def
  numeric_ground_ast_problem_defs.num_init_def
  numeric_ground_ast_problem_defs.const_to_int_def

declare numeric_ground_data_code[code]

text \<open>Code equations for the inference at the ground problem: the executable twin, its ingredients and
  its name-keyed rendering (all in the no-assumption defs locale, so their defining equations are
  unconditional; the global translation twins and @{const cmp_op_to_cmpop} are \<open>primrec\<close>/\<open>fun\<close>
  equations, \<open>[code]\<close> by construction).\<close>

text \<open>Evaluation sharing for the generated code; none of these equations changes what is computed.
  \<^item> @{text draft_init_spec}: the numeric init assignments are extracted from @{text \<open>init P\<close>} once,
    not again on every fluent lookup.
  \<^item> @{text inferred_box_spec}: the fluents, draft actions and initial valuation are built once and
    shared by the threshold set and the inference.
  \<^item> @{const ginfer_thr_on}: the fixpoint environment is a function, and every iteration otherwise
    wraps the previous one in fresh closures, so a lookup at iteration \<open>k\<close> re-runs all earlier
    iterations. @{text tab_on} evaluates the environment once per tracked fluent into an association
    list and looks it up there; it is the identity (@{text tab_on_eq}).\<close>

lemma (in numeric_ground_ast_problem_defs) draft_init_spec_code:
  "draft_init_spec =
     (let asg = num_init_assignments
      in (\<lambda>f. const_to_int (case map_of asg f of Some r \<Rightarrow> r | None \<Rightarrow> 0)))"
  by (simp add: draft_init_spec_def num_init_def)

lemma (in numeric_ground_ast_problem_defs) inferred_box_spec_let:
  "inferred_box_spec =
     (let fs = nfluents; acts = draft_acts_spec; v0 = draft_init_spec
      in infer_fluent_bounds_on fs (thr_set fs v0 acts) acts v0)"
  by (simp add: inferred_box_spec_def Let_def)

definition tab_on :: "'n list \<Rightarrow> 'n aenv \<Rightarrow> 'n aenv" where
  "tab_on fs E =
     (let t = map (\<lambda>f. (f, E f)) fs
      in (\<lambda>f. case map_of t f of Some i \<Rightarrow> i | None \<Rightarrow> E f))"

lemma tab_on_eq: "tab_on fs E = E"
  by (rule ext) (auto simp: tab_on_def map_of_map_restrict restrict_map_def)

lemma ginfer_thr_on_tab_code [code]:
  "ginfer_thr_on fs T acts v0 =
     while_option (\<lambda>E. \<not> le_on fs (gastep acts E) E)
       (\<lambda>E. tab_on fs (widen_env_thr T E (gastep acts E))) (tab_on fs (init_env v0))"
  by (simp add: ginfer_thr_on_def tab_on_eq)

lemmas inferred_box_spec_code =
  numeric_ground_ast_problem_defs.snap_gaction_spec_def
  numeric_ground_ast_problem_defs.draft_acts_spec_def
  numeric_ground_ast_problem_defs.draft_init_spec_code
  numeric_ground_ast_problem_defs.inferred_box_spec_let
  numeric_ground_ast_problem_defs.inferred_box_list_def

declare inferred_box_spec_code[code]
section \<open>The P-taking numeric network-assembly optimum\<close>

text \<open>Numeric twin of \<open>check_and_make_network_opt\<close> (from theory \<open>Check_Unsolvability\<close>): run the
  verified bound inference on \<open>P\<close> (\<open>None\<close> if some declared fluent gets an infinite endpoint), take the
  inferred box as the per-fluent bounds \<open>lo\<close>/\<open>hi\<close>, and assemble the numeric network with
  \<open>check_and_make_numeric_network\<close>.  No box input, no re-check gate: the inference's result is the
  certificate (theory \<open>Ground_PDDL_Numeric_NTA_Reduction_Bounds\<close>).\<close>

definition check_and_make_numeric_network_opt where
"check_and_make_numeric_network_opt P \<equiv>
   (case numeric_ground_ast_problem_defs.inferred_box_spec P of
      None \<Rightarrow> None
    | Some b \<Rightarrow>
        (case check_and_make_numeric_network P (fst \<circ> b) (snd \<circ> b) of
           Inl _ \<Rightarrow> None
         | Inr net \<Rightarrow> Some net))"

text \<open>DIAGNOSTIC (temporary) twin: report which structural admission clause rejects (\<open>Some 0\<close> =
  accept; \<open>None\<close> = the bound inference itself failed, so there is no box to check against).\<close>
definition check_numeric_admission_diag_opt where
"check_numeric_admission_diag_opt P \<equiv>
   (case numeric_ground_ast_problem_defs.inferred_box_spec P of
      None \<Rightarrow> None
    | Some b \<Rightarrow> Some (numeric_ground_ast_problem_defs.check_numeric_ground_problem_diag P (fst \<circ> b) (snd \<circ> b)))"

text \<open>Don't remove this: a standalone code-generation check of the verified inference at the ground
  problem (the \<open>ivl\<close> quotient type, \<open>while_option\<close>, the translation twins).  The network builder
  \<open>check_and_make_numeric_network_opt\<close> is NOT exported here: its Containers set instances (\<open>ceq\<close> /
  \<open>ccompare\<close> / \<open>card_UNIV\<close> for \<open>predicate\<close>, \<open>func\<close>, \<open>nexp\<close>, ...) are derived only in
  \<open>Check_Unsolvability\<close> / \<open>Numeric_Unsolvability_Export\<close>, where the unified \<open>Converter\<close> export
  covers it.\<close>
export_code
  numeric_ground_ast_problem_defs.inferred_box_list
  Inl Inr nat_of_integer integer_of_int int_of_integer
  in SML module_name NumericProjection
end
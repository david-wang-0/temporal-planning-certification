theory Ground_PDDL_Numeric_Code_Export
  imports "bound_inference.Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl"
begin

section \<open>Deliverable (1): executable @{text is_gbound_inv'} code equation\<close>

context numeric_ground_ast_problem
begin

definition snap_ok :: "ground_action \<Rightarrow> bool" where
  "snap_ok s \<equiv>
     list_all (\<lambda>(f, e).
        case nred.aeval (nred.refine_box (n_pre s) nred.box) e of
          None \<Rightarrow> False
        | Some (al, ah) \<Rightarrow> fluent_lo f \<le> al \<and> ah \<le> fluent_hi f)
       (upds s)"

lemma nred_is_gbound_inv'_code:
  "nred.is_gbound_inv' \<longleftrightarrow>
     list_all (\<lambda>f. fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f) nfluents
   \<and> list_all (\<lambda>a. snap_ok (at_start_spec a) \<and> snap_ok (at_end_spec a)) actions_spec"
  unfolding nred.is_gbound_inv'_def nred.all_snaps_def snap_ok_def
  by (auto simp: list_all_iff)

declare nred_is_gbound_inv'_code[code]

end

section \<open>Global executable interval-check mirror funs (P + lo + hi taking)\<close>

text \<open>Global, code-generatable twins of the locale-internal interval evaluator
  @{const numeric_tp_nta_reduction.aeval} / @{const numeric_tp_nta_reduction.refine_comp} /
  @{const numeric_tp_nta_reduction.refine_box} / @{const numeric_tp_nta_reduction.box}.
  They take the @{text const_to_int} decode @{term cti} and (for @{term box_exec}) the fluent
  bounds @{term lo}, @{term hi} as explicit arguments, so they live at the theory top level and
  code-generate without a locale interpretation.  Bodies are copied verbatim from
  @{theory TP_NTA_Reduction.TP_NTA_Reduction_Numeric_Bounds}.\<close>

definition map_ibnd2_exec ::
  "(int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int) \<Rightarrow> (int \<times> int) option \<Rightarrow> (int \<times> int) option \<Rightarrow> (int \<times> int) option"
  where "map_ibnd2_exec g x y = (case (x, y) of (Some a, Some b) \<Rightarrow> Some (g a b) | _ \<Rightarrow> None)"

fun aeval_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> (int \<times> int) option" where
  "aeval_exec cti B (NConst c) = Some (cti c, cti c)"
| "aeval_exec cti B (NVar f)   = Some (B f)"
| "aeval_exec cti B (NAdd a b) = map_ibnd2_exec (\<lambda>(al, ah) (bl, bh). (al + bl, ah + bh)) (aeval_exec cti B a) (aeval_exec cti B b)"
| "aeval_exec cti B (NSub a b) = map_ibnd2_exec (\<lambda>(al, ah) (bl, bh). (al - bh, ah - bl)) (aeval_exec cti B a) (aeval_exec cti B b)"
| "aeval_exec cti B (NMul a b) = map_ibnd2_exec (\<lambda>(al, ah) (bl, bh).
       (min (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))),
        max (al * bl) (max (al * bh) (max (ah * bl) (ah * bh)))))
       (aeval_exec cti B a) (aeval_exec cti B b)"
| "aeval_exec cti B (NDiv a b) = None"

fun refine_comp_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_comp_exec cti (Comp Cle (NVar f) (NConst c)) B = B(f := (fst (B f), min (snd (B f)) (cti c)))"
| "refine_comp_exec cti (Comp Cge (NVar f) (NConst c)) B = B(f := (max (fst (B f)) (cti c), snd (B f)))"
| "refine_comp_exec cti (Comp Ceq (NVar f) (NConst c)) B =
     B(f := (max (fst (B f)) (cti c), min (snd (B f)) (cti c)))"
| "refine_comp_exec cti (Comp Clt (NVar f) (NConst c)) B = B(f := (fst (B f), min (snd (B f)) (cti c - 1)))"
| "refine_comp_exec cti (Comp Cgt (NVar f) (NConst c)) B = B(f := (max (fst (B f)) (cti c + 1), snd (B f)))"
| "refine_comp_exec cti _ B = B"

definition refine_box_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) comp list \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_box_exec cti cs B = fold (refine_comp_exec cti) cs B"

definition box_exec :: "('n \<Rightarrow> int) \<Rightarrow> ('n \<Rightarrow> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "box_exec lo hi = (\<lambda>f. (lo f, hi f))"

text \<open>The global, P/lo/hi-taking executable certificate: the RHS of \<open>nred_is_gbound_inv'_code\<close>
  re-expressed over the ground data functions and the global mirror interval evaluator.  Lives in
  the defs locale \<open>numeric_ground_ast_problem_defs\<close> (which fixes only \<open>P\<close>), with the fluent bounds
  \<open>lo\<close>, \<open>hi\<close> taken as explicit arguments (they are the box-derived bounds, NOT the leaf
  locale's fixed \<open>fluent_lo\<close>/\<open>fluent_hi\<close>).\<close>

context numeric_ground_ast_problem_defs
begin

definition snap_ok_exec :: "(func \<Rightarrow> int) \<Rightarrow> (func \<Rightarrow> int) \<Rightarrow> ground_action \<Rightarrow> bool" where
  "snap_ok_exec lo hi s \<equiv>
     list_all (\<lambda>(f, e).
        case aeval_exec const_to_int (refine_box_exec const_to_int (n_pre s) (box_exec lo hi)) e of
          None \<Rightarrow> False
        | Some (al, ah) \<Rightarrow> lo f \<le> al \<and> ah \<le> hi f)
       (upds s)"

definition is_gbound_inv_exec :: "(func \<Rightarrow> int) \<Rightarrow> (func \<Rightarrow> int) \<Rightarrow> bool" where
  "is_gbound_inv_exec lo hi \<equiv>
     list_all (\<lambda>f. lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> hi f) nfluents
   \<and> list_all (\<lambda>a. snap_ok_exec lo hi (at_start_spec a) \<and> snap_ok_exec lo hi (at_end_spec a)) actions_spec"

end

section \<open>Deliverable (2): the P-taking numeric network-assembly optimum\<close>

text \<open>Numeric twin of \<open>check_and_make_network_opt\<close> (from theory \<open>Check_Unsolvability\<close>):
  derive the per-fluent bounds \<open>lo\<close>/\<open>hi\<close> from the assoc list \<open>B\<close> (keyed by fluent
  name), assemble the numeric network with \<open>check_and_make_numeric_network\<close>, and gate the result
  on the executable static boundedness certificate \<open>is_gbound_inv_exec\<close>.
  All ingredients are code-generatable, so this exports.\<close>

definition check_and_make_numeric_network_opt where
"check_and_make_numeric_network_opt P B \<equiv>
   (let lo = (\<lambda>f. case map_of B (func.name f) of Some (l, _) \<Rightarrow> l | None \<Rightarrow> 0);
        hi = (\<lambda>f. case map_of B (func.name f) of Some (_, h) \<Rightarrow> h | None \<Rightarrow> 0)
    in case check_and_make_numeric_network P lo hi of
         Inl e \<Rightarrow> None
       | Inr net \<Rightarrow> if numeric_ground_ast_problem_defs.is_gbound_inv_exec P lo hi
                    then Some net else None)"

text \<open>DIAGNOSTIC (temporary) twin: report which structural admission clause rejects (0 = accept).\<close>
definition check_numeric_admission_diag_opt where
"check_numeric_admission_diag_opt P B \<equiv>
   (let lo = (\<lambda>f. case map_of B (func.name f) of Some (l, _) \<Rightarrow> l | None \<Rightarrow> 0);
        hi = (\<lambda>f. case map_of B (func.name f) of Some (_, h) \<Rightarrow> h | None \<Rightarrow> 0)
    in numeric_ground_ast_problem_defs.check_numeric_ground_problem_diag P lo hi)"

text \<open>A bool-returning slice of the gate: build the box bounds from the name-keyed assoc list
  \<open>B\<close> and run ONLY the trusted static certificate \<open>is_gbound_inv_exec\<close> (no net builder, so this
  code-generates).  The SML glue calls this to re-check an inferred box before trusting it.\<close>
definition check_gbounds_opt where
"check_gbounds_opt P B \<equiv>
   (let lo = (\<lambda>f. case map_of B (func.name f) of Some (l, _) \<Rightarrow> l | None \<Rightarrow> 0);
        hi = (\<lambda>f. case map_of B (func.name f) of Some (_, h) \<Rightarrow> h | None \<Rightarrow> 0)
    in numeric_ground_ast_problem_defs.is_gbound_inv_exec P lo hi)"

section \<open>Deliverable (3): the neutral, INT-ified snap-draft projection\<close>

text \<open>A purpose-built, serializable projection of the relaxed snaps that the (future SML)
  bound-inference stage consumes.  It is INT-ified via \<open>const_to_int\<close> and stripped to the
  var-vs-const guard shapes and the update-RHS expression trees.  This is an \<^emph>\<open>untrusted\<close>
  projection (the trusted gate is \<open>is_gbound_inv'\<close>): a lossy/partial mapping is sound -- a
  dropped guard only widens the inferred box.  The datatypes below are neutral (no \<open>func\<close>/
  \<open>rat\<close>/\<open>nexp\<close> dependency), keyed by fluent name @{typ String.literal}.\<close>

datatype g_int = GLe_i String.literal int | GGe_i String.literal int | GEq_i String.literal int
  | GLt_i String.literal int | GGt_i String.literal int

datatype e_int = EC int | EV String.literal
  | EAdd e_int e_int | ESub e_int e_int | EMul e_int e_int | EDiv e_int e_int

type_synonym snap_draft = "g_int list \<times> (String.literal \<times> e_int) list"

text \<open>Total expression-tree projection: constants are INT-decoded, variables keep their fluent
  name, the arithmetic shapes recurse.\<close>
primrec nexp_to_eint :: "(func \<Rightarrow> String.literal) \<Rightarrow> (rat \<Rightarrow> int) \<Rightarrow> (func, rat) nexp \<Rightarrow> e_int" where
  "nexp_to_eint nm cti (NConst c) = EC (cti c)"
| "nexp_to_eint nm cti (NVar f)   = EV (nm f)"
| "nexp_to_eint nm cti (NAdd a b) = EAdd (nexp_to_eint nm cti a) (nexp_to_eint nm cti b)"
| "nexp_to_eint nm cti (NSub a b) = ESub (nexp_to_eint nm cti a) (nexp_to_eint nm cti b)"
| "nexp_to_eint nm cti (NMul a b) = EMul (nexp_to_eint nm cti a) (nexp_to_eint nm cti b)"
| "nexp_to_eint nm cti (NDiv a b) = EDiv (nexp_to_eint nm cti a) (nexp_to_eint nm cti b)"

text \<open>Partial guard projection: keep only the var-vs-const comparison shapes (where the
  interval refinement lands); drop everything else (sound -- a wider box).\<close>
fun comp_to_gint :: "(func \<Rightarrow> String.literal) \<Rightarrow> (rat \<Rightarrow> int) \<Rightarrow> (func, rat) comp \<Rightarrow> g_int option" where
  "comp_to_gint nm cti (Comp Cle (NVar f) (NConst c)) = Some (GLe_i (nm f) (cti c))"
| "comp_to_gint nm cti (Comp Cge (NVar f) (NConst c)) = Some (GGe_i (nm f) (cti c))"
| "comp_to_gint nm cti (Comp Ceq (NVar f) (NConst c)) = Some (GEq_i (nm f) (cti c))"
| "comp_to_gint nm cti (Comp Clt (NVar f) (NConst c)) = Some (GLt_i (nm f) (cti c))"
| "comp_to_gint nm cti (Comp Cgt (NVar f) (NConst c)) = Some (GGt_i (nm f) (cti c))"
| "comp_to_gint nm cti _ = None"

context numeric_ground_ast_problem_defs
begin

definition snap_draft_of :: "ground_action \<Rightarrow> snap_draft" where
  "snap_draft_of s =
     (List.map_filter (comp_to_gint fluent_to_name_spec const_to_int) (n_pre s),
      map (\<lambda>(f, e). (fluent_to_name_spec f, nexp_to_eint fluent_to_name_spec const_to_int e)) (upds s))"

definition numeric_draft_actions ::
  "String.literal list \<times> snap_draft list \<times> (String.literal \<times> int) list" where
  "numeric_draft_actions =
     (map fluent_to_name_spec nfluents,
      concat (map (\<lambda>a. [snap_draft_of (at_start_spec a), snap_draft_of (at_end_spec a)]) actions_spec),
      map (\<lambda>f. (fluent_to_name_spec f, const_to_int (num_init f))) nfluents)"

end

text \<open>Code equations for the numeric ground-data accessors.  Isabelle does not auto-generate
  code equations for locale constants; the classical layer wires its own with
  \<open>ground_ast_problem_code[code]\<close> (theory \<open>Ground_PDDL_NTA_Reduction_Impl\<close>).  Here we do the
  numeric-only twin for the accessors the executable certificate/projection consume, so
  deliverables (1)/(3) code-generate.  (\<open>at_start_spec\<close>/\<open>at_end_spec\<close>/\<open>actions_spec\<close> are already
  \<open>[code]\<close> from the classical bundle.)\<close>

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
  numeric_ground_ast_problem_defs.snap_ok_exec_def
  numeric_ground_ast_problem_defs.is_gbound_inv_exec_def
  numeric_ground_ast_problem_defs.snap_draft_of_def
  numeric_ground_ast_problem_defs.numeric_draft_actions_def

declare numeric_ground_data_code[code]

text \<open>\<^bold>\<open>VERIFIED code-gen of the bound-inference glue surface.\<close> The two functions the (SML)
  bound-inference glue needs -- the snap projection @{const numeric_ground_ast_problem_defs.numeric_draft_actions}
  (feeds the compute-side @{text infer_fluent_bounds}) and the boundedness re-check
  @{const numeric_ground_ast_problem_defs.is_gbound_inv_exec} (the trusted gate on the inferred box) --
  \<^emph>\<open>code-generate cleanly on their own\<close>.  (The full numeric NETWORK builder @{text num_make_network_impl}
  does NOT: it re-triggers the @{text Code_Cardinality.finite'} clash and needs the isolated
  @{text card_UNIV}/@{text proper_interval}/@{text \<open>String.literal\<close>} code-gen block that theory
  @{text Check_Unsolvability} keeps commented out -- the deferred WP-D code-gen tail.)\<close>
export_code
  numeric_ground_ast_problem_defs.numeric_draft_actions
  numeric_ground_ast_problem_defs.is_gbound_inv_exec
  check_gbounds_opt
  GLe_i GGe_i GEq_i GLt_i GGt_i
  EC EV EAdd ESub EMul EDiv
  Inl Inr nat_of_integer integer_of_int int_of_integer
  in SML module_name NumericProjection file "../code/Numeric_Projection.ML"

text \<open>\<^bold>\<open>Code-gen status (2026-07-13).\<close> All definitions/lemmas above are green and typecheck. Actual ML
  emission (\<^bold>\<open>export_code \<dots> in SML\<close>) is \<^emph>\<open>deferred\<close> (David's WP-D decision: defer the code-gen
  typeclass rabbit hole). A probe surfaced a @{text Code_Cardinality.finite'} clash coming from the
  snaps-disjointness check's @{text \<open>set \<dots> \<inter> set \<dots> = {}\<close>} in
  @{const numeric_ground_ast_problem_defs.check_numeric_ground_problem} (reformulate to an executable
  @{const list_all}/@{text \<open>\<notin> set\<close>} form to clear it), and full emission additionally needs the isolated
  @{text proper_interval}/@{text Abs_literal} @{text \<open>String.literal\<close>} code-gen block that
  theory @{text Check_Unsolvability} currently keeps commented out.\<close>

end

theory Ground_PDDL_Numeric_Code_Export
  imports "bound_inference.Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl"
begin

section \<open>Deliverable (1): executable @{text is_gbound_inv'} code equation\<close>

context numeric_ground_ast_problem
begin

definition snap_ok :: "ground_action \<Rightarrow> bool" where
  "snap_ok s \<equiv>
     list_ex (\<lambda>g. snd (nred'.refine_box (n_pre s) nred'.box g)
                  < fst (nred'.refine_box (n_pre s) nred'.box g)) nfluents
   \<or> list_all (\<lambda>(f, e).
        case nred'.aeval (nred'.refine_box (n_pre s) nred'.box) e of
          None \<Rightarrow> False
        | Some (al, ah) \<Rightarrow> fluent_lo f \<le> al \<and> ah \<le> fluent_hi f)
       (upds s)"

lemma nred_is_gbound_inv'_code:
  "nred'.is_gbound_inv' \<longleftrightarrow>
     list_all (\<lambda>f. fluent_lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> fluent_hi f) nfluents
   \<and> list_all (\<lambda>a. snap_ok (at_start_spec a) \<and> snap_ok (at_end_spec a)) actions_spec"
  unfolding nred'.is_gbound_inv'_def nred'.all_snaps_def snap_ok_def
  by (simp add: list_all_iff list_ex_iff ball_Un case_prod_beta ball_conj_distrib)

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

fun refine_left_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_left_exec cti (Comp p (NVar f) e) B =
     (case aeval_exec cti B e of
        None \<Rightarrow> B
      | Some (l, h) \<Rightarrow>
          (case p of
             Cle \<Rightarrow> B(f := (fst (B f), min (snd (B f)) h))
           | Clt \<Rightarrow> B(f := (fst (B f), min (snd (B f)) (h - 1)))
           | Cge \<Rightarrow> B(f := (max (fst (B f)) l, snd (B f)))
           | Cgt \<Rightarrow> B(f := (max (fst (B f)) (l + 1), snd (B f)))
           | Ceq \<Rightarrow> B(f := (max (fst (B f)) l, min (snd (B f)) h))))"
| "refine_left_exec cti _ B = B"

fun refine_right_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_right_exec cti (Comp p e (NVar g)) B =
     (case aeval_exec cti B e of
        None \<Rightarrow> B
      | Some (l, h) \<Rightarrow>
          (case p of
             Cle \<Rightarrow> B(g := (max (fst (B g)) l, snd (B g)))
           | Clt \<Rightarrow> B(g := (max (fst (B g)) (l + 1), snd (B g)))
           | Cge \<Rightarrow> B(g := (fst (B g), min (snd (B g)) h))
           | Cgt \<Rightarrow> B(g := (fst (B g), min (snd (B g)) (h - 1)))
           | Ceq \<Rightarrow> B(g := (max (fst (B g)) l, min (snd (B g)) h))))"
| "refine_right_exec cti _ B = B"

definition refine_comp_exec :: "('r \<Rightarrow> int) \<Rightarrow> ('n, 'r) comp \<Rightarrow> ('n \<Rightarrow> int \<times> int) \<Rightarrow> ('n \<Rightarrow> int \<times> int)" where
  "refine_comp_exec cti c B = refine_right_exec cti c (refine_left_exec cti c B)"

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
     list_ex (\<lambda>g. snd (refine_box_exec const_to_int (n_pre s) (box_exec lo hi) g)
                  < fst (refine_box_exec const_to_int (n_pre s) (box_exec lo hi) g)) nfluents
   \<or> list_all (\<lambda>(f, e).
        case aeval_exec const_to_int (refine_box_exec const_to_int (n_pre s) (box_exec lo hi)) e of
          None \<Rightarrow> False
        | Some (al, ah) \<Rightarrow> lo f \<le> al \<and> ah \<le> hi f)
       (upds s)"

definition is_gbound_inv_exec :: "(func \<Rightarrow> int) \<Rightarrow> (func \<Rightarrow> int) \<Rightarrow> bool" where
  "is_gbound_inv_exec lo hi \<equiv>
     list_all (\<lambda>f. lo f \<le> const_to_int (num_init f) \<and> const_to_int (num_init f) \<le> hi f) nfluents
   \<and> list_all (\<lambda>a. snap_ok_exec lo hi (at_start_spec a) \<and> snap_ok_exec lo hi (at_end_spec a)) actions_spec"

end

section \<open>The exec twins EQUAL the locale interval check (closing the unproven-twin gap)\<close>

text \<open>The global mirror funs were introduced as verbatim copies of the locale-internal
  evaluator; here that correspondence is PROVED, so the executable gate
  @{const numeric_ground_ast_problem_defs.is_gbound_inv_exec} literally decides the
  certificate assumption \<open>nred'.is_gbound_inv'\<close> of @{locale numeric_ground_ast_problem_cert}
  -- the ingredient that lets the numeric certifier capstone (theory
  \<open>Numeric_Unsolvability_Export\<close>) discharge the cert locale by evaluation.\<close>

text \<open>The exec twins take @{term const_to_int}/@{term fluent_lo}/@{term fluent_hi} explicitly; the
  locale-internal evaluator's defining equations are conditional on the (all-parameter) locale
  predicate, so the correspondence is proved INSIDE @{locale numeric_ground_ast_problem} against the
  sublocale interpretation @{text nred'} (which discharges that predicate and fixes
  @{text \<open>const_to_int := const_to_int\<close>}, @{text \<open>fluent_lo := fluent_lo\<close>}, @{text \<open>fluent_hi := fluent_hi\<close>}).\<close>

context numeric_ground_ast_problem
begin

lemma aeval_exec_eq: "aeval_exec const_to_int B e = nred'.aeval B e"
  by (induction e)
     (simp_all add: nred'.aeval.simps map_ibnd2_exec_def nred'.map_ibnd2_def Min_insert Max_insert)

lemma refine_left_exec_eq: "refine_left_exec const_to_int c B = nred'.refine_left c B"
proof (cases c)
  case (Comp p a b)
  then show ?thesis
    by (cases a) (simp_all add: nred'.refine_left.simps aeval_exec_eq)
qed

lemma refine_right_exec_eq: "refine_right_exec const_to_int c B = nred'.refine_right c B"
proof (cases c)
  case (Comp p a b)
  then show ?thesis
    by (cases b) (simp_all add: nred'.refine_right.simps aeval_exec_eq)
qed

lemma refine_comp_exec_eq: "refine_comp_exec const_to_int c B = nred'.refine_comp c B"
  by (simp add: refine_comp_exec_def nred'.refine_comp_def refine_left_exec_eq refine_right_exec_eq)

lemma refine_box_exec_eq: "refine_box_exec const_to_int cs B = nred'.refine_box cs B"
proof -
  have "refine_comp_exec const_to_int = nred'.refine_comp"
    by (simp add: fun_eq_iff refine_comp_exec_eq)
  then show ?thesis
    by (simp add: refine_box_exec_def nred'.refine_box_def)
qed

lemma box_exec_eq: "box_exec fluent_lo fluent_hi = nred'.box"
  by (simp add: box_exec_def nred'.box_def)

lemma snap_ok_exec_eq: "snap_ok_exec fluent_lo fluent_hi s = snap_ok s"
  by (simp add: snap_ok_exec_def snap_ok_def aeval_exec_eq refine_box_exec_eq box_exec_eq)

lemma is_gbound_inv_exec_eq: "is_gbound_inv_exec fluent_lo fluent_hi \<longleftrightarrow> nred'.is_gbound_inv'"
  by (simp add: is_gbound_inv_exec_def nred_is_gbound_inv'_code snap_ok_exec_eq)

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
  bound-inference stage consumes.  It is INT-ified via \<open>const_to_int\<close> and mirrors the abstract
  \<open>comp = Comp cmp_op nexp nexp\<close> LOSSLESSLY: a guard is a comparison of two full expression
  trees, so fluent-vs-fluent guards (painter's \<open>item_id = counter\<close>, majsp's
  \<open>battery \<ge> distance\<close>) survive to the bound inference.  This is an \<^emph>\<open>untrusted\<close>
  projection (the trusted gate is \<open>is_gbound_inv'\<close>): any mapping error is sound -- a wrong
  draft merely proposes a box the gate rejects.  The datatypes below are neutral (no \<open>func\<close>/
  \<open>rat\<close>/\<open>nexp\<close> dependency), keyed by fluent name @{typ String.literal}.\<close>

datatype e_int = EC int | EV String.literal
  | EAdd e_int e_int | ESub e_int e_int | EMul e_int e_int | EDiv e_int e_int

datatype g_int = GCmp_i cmp_op e_int e_int
  \<comment> \<open>reuses the reduction's @{type cmp_op} over two full \<open>e_int\<close> expression trees\<close>

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

text \<open>TOTAL guard projection: every comparison maps to \<open>GCmp_i\<close> over the two projected
  expression trees -- nothing is dropped.  (Kept @{typ \<open>g_int option\<close>}-valued so the
  \<open>map_filter\<close> consumer below is unchanged.)\<close>
fun comp_to_gint :: "(func \<Rightarrow> String.literal) \<Rightarrow> (rat \<Rightarrow> int) \<Rightarrow> (func, rat) comp \<Rightarrow> g_int option" where
  "comp_to_gint nm cti (Comp p a b) =
     Some (GCmp_i p (nexp_to_eint nm cti a) (nexp_to_eint nm cti b))"

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
  GCmp_i Ceq Cle Cge Clt Cgt
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

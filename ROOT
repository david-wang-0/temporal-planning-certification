session Temporal_Munta_Base in Temporal_Munta_Base = Temporal_Planning_Discrete +
  description \<open>Stable, expensive base layer: the Munta model checker + verified certificate
    checker, List-Index and Containers, re-elaborated ONCE on top of the Analysis-FREE
    Formal-PDDL-Semantics Temporal_Planning_Discrete heap (the temporal state-sequence semantics and
    well-formedness, with NO HOL-Analysis / ODE / Product_Order tower). Dropping Product_Order leaves
    Munta's Product_Lexorder as the sole prod::ord instance, so the certificate-checker code
    (Simple_Network_Language_Certificate_Code) co-imports with the net builder with no arity clash --
    this is what makes the unified export (a) possible. The temporal discrete semantics sit BELOW
    this heap as a frozen external FPS image, so editing project theories above does not rebuild
    Munta. Contains no project-local theories.\<close>
  options [timeout = 7200]
  sessions
    "List-Index"
    "Containers"
    "Munta_Certificate_Checker"
  theories [document = false]
    "List-Index.List_Index"
    "Munta_Certificate_Checker.Lasso_Freeness_Certificates_Complete"
    "Munta_Certificate_Checker.Unreachability_Certification"
    "Munta_Certificate_Checker.Unreachability_Certification2"
    "Munta_Certificate_Checker.Simulation_Graphs2"
    "Munta_Certificate_Checker.TA_Simulation"
    "Munta_Certificate_Checker.Normalized_Zone_Semantics_Certification_Impl"
    "Munta_Certificate_Checker.Normalized_Zone_Semantics_Certification_Impl2"
    "Munta_Certificate_Checker.Simple_Network_Language_Certificate_Code"

session Temporal_Planning_Base in Temporal_Planning_Base = Temporal_Munta_Base +
  description \<open>Thin layer loading the grounder's temporal normalization locales (session
    Grounding_Temporal_Common: grounded_temporal_problem / positive_temporal_problem) on top of the
    stable Analysis-free Munta heap. The FPS temporal discrete semantics / well-formedness now live in
    Temporal_Planning_Discrete BELOW the Munta heap, so they are already in the base image and are not
    reloaded here; the Analysis-tainted FPS checkers (Temporal_PDDL_Checker_*, the continuous
    reduction) are dropped entirely -- the net builder uses an in-repo Analysis-free wf-checker. The
    whole development is built on top of this heap in jEdit. Contains no project-local theories (FPS +
    grounder externals only).\<close>
  options [timeout = 7200]
  sessions
    "Utils"
    "Grounding_Temporal_Common"
  theories [document = false]
    "Grounding_Temporal_Common.Temporal_PDDL_Normalization"

session Temporal_Planning_Common in Temporal_Planning_Common = Temporal_Planning_Base +
  theories
    TP_Utils
    ListMisc
    Sequences

session Temporal_Planning_Semantics in Temporal_Planning_Semantics = Temporal_Planning_Common +
  theories
    Temporal_Plans
  document_files (in "../document")
    "root.tex"
    "root.bib"

session TP_NTA_Reduction in TA_Network = Temporal_Planning_Semantics +
  theories
    NTA_Temp_Planning_Sem
    TP_NTA_Reduction_Defs
    TP_NTA_Reduction_Model_Checking
    TP_NTA_Reduction_Utils
    TP_NTA_Reduction_Prelims
    TP_NTA_Reduction_Edges
    TP_NTA_Reduction_Happenings
    TP_NTA_Reduction_Properties
    TP_NTA_Reduction_Steps
    TP_NTA_Reduction_Correctness
    TP_NTA_Reduction_Numeric_Defs
    TP_NTA_Reduction_Numeric_Model_Checking
    TP_NTA_Reduction_Numeric_Prelims
    TP_NTA_Reduction_Numeric_Edges
    TP_NTA_Reduction_Numeric_Projection
    TP_NTA_Reduction_Numeric_Steps
    TP_NTA_Reduction_Correctness_Numeric
    TP_NTA_Reduction_Numeric_Bounds

session PDDL_TP_Reduction in Ground_PDDL_Exec_Imp = TP_NTA_Reduction +
  sessions
    "Grounding_Temporal_Common"
  theories
    (* in-repo Analysis-free wf-checker: vendored FPS checker slice, re-pointed off the
       Analysis-tainted Continuous_Planning onto Analysis_Free_Base (keeps the tower Product_Order-free) *)
    Error_Monad_Add
    PDDL_Checker_Common
    Temporal_Continuous_Reduction_Free
    Ground_PDDL_Problem_Defs
    Ground_PDDL_Problem_Reduction
    Ground_PDDL_Plan_Defs
    Ground_PDDL_Plan_Reduction
    Ground_PDDL_Problem_Code
    Ground_PDDL_NTA_Reduction_Correctness
    Ground_PDDL_NTA_Reduction_Impl
    Ground_PDDL_Numeric_Problem_Defs
    Ground_PDDL_Numeric_NTA_Reduction_Correctness
    Ground_PDDL_Numeric_NTA_Reduction_Impl
    Check_Unsolvability
    Unsolvability_Code_Compile
  export_files (in "../") [1]
    "PDDL_TP_Reduction.Unsolvability_Code_Compile:ML/Check_Unsolvability.ML"

session bound_inference in bound_inference = PDDL_TP_Reduction +
  description \<open>Numeric bound machinery: discharge the num_seq_in_bounds locale assumption from
    the static is_gbound_inv' certificate (Bounds), and compose it with the executable numeric net
    refinement into the cert-level executable soundness (Cert_Impl).\<close>
  theories
    Ground_PDDL_Numeric_NTA_Reduction_Bounds
    Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl

session bound_parsing in bound_parsing = bound_inference +
  description \<open>Bound-parsing / projection glue: the neutral INT-ified snap-draft projection
    (numeric_draft_actions) that feeds the external interval bound-inference, and the executable
    boundedness re-check (is_gbound_inv_exec / check_gbounds_opt) on the inferred box.\<close>
  theories
    Ground_PDDL_Numeric_Code_Export

session PDDL_TP_Reduction_Index = bound_parsing +
  theories Index
  document_files (in "document")
    "root.tex"
    "root.bib"

session Numeric_Bound_Inference in Numeric_Bound_Inference = "HOL-IMP" +
  description \<open>Numeric-fluent bound inference (threshold interval abstract interpretation). Standalone
    on the HOL-IMP heap -- it CANNOT share the reduction's Temporal_Planning_Base heap (HOL-IMP's
    Abs_Int0 option-lattice arity clashes with the Munta/FPS tower), so it is a separate session and the
    inferred box crosses to the reduction as plain data. It COMPUTES a per-fluent box (possibly with
    infinite endpoints); the executable pipeline rejects any problem whose box has an infinite endpoint
    ("bound-inference failed") since the reduction's fluent_lo/hi are finite int.\<close>
  theories
    Numeric_Bound_Inference
    Numeric_Bound_Inference_Threshold
    Numeric_Bound_Inference_Guards
    Numeric_Bound_Inference_Extract
    Numeric_Bound_Inference_Code_Export
  export_files (in "../") [1]
    "Numeric_Bound_Inference.Numeric_Bound_Inference_Code_Export:code/Numeric_Bound_Inference.ML"

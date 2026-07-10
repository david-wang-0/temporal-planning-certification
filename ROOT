session Temporal_Munta_Base in Temporal_Munta_Base = Continuous_Planning +
  description \<open>Stable, expensive base layer: the Munta model checker + verified certificate
    checker and List-Index, re-elaborated ONCE on top of the Formal-PDDL-Semantics
    Continuous_Planning heap (which carries the heavy HOL-Analysis / ODE / algebraic-numbers tower,
    inherited from its cached image). This heap does NOT depend on the temporal PDDL semantics
    session (Temporal_Planning), so editing the temporal / state-sequence theories does not
    invalidate it -- only the thin Temporal_Planning_Base layer above is rebuilt. Contains no
    project-local theories.\<close>
  options [timeout = 7200]
  sessions
    "List-Index"
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
  description \<open>Thin layer loading the Formal-PDDL-Semantics temporal PDDL semantics (session
    Temporal_Planning) plus the grounder's temporal normalization locales (session
    Grounding_Temporal_Common: grounded_temporal_problem / positive_temporal_problem) on top of the
    stable Munta heap. Because Munta lives BELOW this layer, an edit to the temporal / state-sequence
    semantics only re-elaborates these light FPS / grounder theories (~minutes) instead of the whole
    Munta tower. The whole development is built on top of this heap in jEdit. Contains no
    project-local theories (FPS + grounder externals only).\<close>
  options [timeout = 7200]
  sessions
    "Utils"
    "Temporal_Planning"
    "Grounding_Temporal_Common"
  theories [document = false]
    "Temporal_Planning.Temporal_Abstract_Syntax"
    "Temporal_Planning.Temporal_Utils"
    "Temporal_Planning.Temporal_Well_Formedness"
    "Temporal_Planning.Temporal_Happening_Semantics"
    "Temporal_Planning.Temporal_Instantiations"
    "Temporal_Planning.Temporal_Continuous_Reduction"
    "Temporal_Planning.Temporal_State_Sequence_Semantics"
    "Temporal_Planning.Temporal_PDDL_Checker_Numeric"
    "Temporal_Planning.Temporal_PDDL_Checker_Explicit"
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
    "Temporal_Planning"
    "Grounding_Temporal_Common"
  theories
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

session PDDL_TP_Reduction_Index = PDDL_TP_Reduction +
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

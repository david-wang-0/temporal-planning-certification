session Temporal_Planning_Base in Temporal_Planning_Base = Temporal_Planning +
  description \<open>External/library dependencies shared by the whole development. The temporal PDDL
    semantics (Formal-PDDL-Semantics, session Temporal_Planning) is the heap PARENT, so the heavy
    HOL-Analysis / ODE / algebraic-numbers tower is inherited from its cached image rather than
    re-elaborated; the Munta model checker + verified certificate checker and List-Index are loaded on
    top. Contains no project-local theories, so it builds once and loads in jEdit as a stable heap
    while the editable sessions below are developed on top.\<close>
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
    TP_NTA_Reduction_Correctness_Prelims
    TP_NTA_Reduction_Correctness_Edges
    TP_NTA_Reduction_Correctness_Happenings
    TP_NTA_Reduction_Correctness_Steps
    TP_NTA_Reduction_Correctness
    TP_NTA_Reduction_Correctness_Numeric_Tracking
    TP_NTA_Reduction_Correctness_Numeric_StepInfra
    TP_NTA_Reduction_Correctness_Numeric_Projection
    TP_NTA_Reduction_Correctness_Numeric_PhaseLifts
    TP_NTA_Reduction_Correctness_Numeric_Happening
    TP_NTA_Reduction_Correctness_Numeric_Plan

session PDDL_TP_Reduction in Ground_PDDL_Exec_Imp = TP_NTA_Reduction +
  theories
    Ground_PDDL_Problem_Defs
    Ground_PDDL_Problem_Reduction
    Ground_PDDL_Plan_Defs
    Ground_PDDL_Plan_Reduction
    Ground_PDDL_Problem_Code
    Ground_PDDL_NTA_Reduction_Correctness
    Ground_PDDL_NTA_Reduction_Impl
    Check_Unsolvability
    Unsolvability_Code_Compile
  export_files (in "../") [1]
    "PDDL_TP_Reduction.Unsolvability_Code_Compile:ML/Check_Unsolvability.ML"

session PDDL_TP_Reduction_Index = PDDL_TP_Reduction +
  theories Index
  document_files (in "document")
    "root.tex"
    "root.bib"

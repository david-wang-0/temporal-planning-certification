session Temporal_Planning_Base in Temporal_Planning_Base = Munta_Certificate_Checker +
  description \<open>External/library dependencies shared by the whole development: the Munta model
    checker + verified certificate checker, List-Index, and the (old) temporal PDDL semantics.
    Contains no project-local theories, so it builds once and loads in jEdit as a stable heap
    while the editable sessions below are developed on top. P0 (re-point onto the new
    Formal-PDDL-Semantics) is a localized change to the semantics import here.\<close>
  options [timeout = 900]
  sessions
    "List-Index"
    "Temporal_AI_Planning_Languages_Semantics"
  theories [document = false]
    "List-Index.List_Index"
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics"
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Checker"

session Temporal_Planning_Common in Temporal_Planning_Common = Temporal_Planning_Base +
  theories
    Utils
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

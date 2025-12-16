session Temporal_Planning_Base in Temporal_Planning_Base = Munta_Model_Checker +
  sessions "List-Index"
  theories
    Base
    ListMisc
    Temporal_Plans 
    Sequences
  document_files (in "../document")
    "root.bib"

session TP_NTA_Reduction in TA_Network =
  Temporal_Planning_Base + 
  sessions Munta_Certificate_Checker
  theories
    NTA_Temp_Planning_Sem
    TP_NTA_Reduction_Spec
    TP_NTA_Reduction_Model_Checking
    TP_NTA_Reduction_Correctness

session PDDL_TP_Reduction in Ground_PDDL_Exec_Imp = 
  TP_NTA_Reduction +
  sessions Temporal_AI_Planning_Languages_Semantics
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
    


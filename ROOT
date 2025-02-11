session TP_Parsing in Parsing =
    Temporal_AI_Planning_Languages_Semantics +
  sessions 
    Parsing
  theories 
    Ground_PDDL_Parsing

session Temporal_Planning_Base in Temporal_Planning_Base =
    Containers +
    theories
      Base
      Temporal_Plans
      Error_List_Monad_Add

session TP_TA_Reduction in Timed_Automaton =
    Temporal_Planning_Base +
    theories
      Compilation
      Compilation_Correctness
      Diagonal_Timed_Automata
      ground_PDDL_plan

session TP_NTA_Reduction in TA_Network =
    Temporal_Planning_Base +
    sessions
      TP_Parsing
      Timed_Automata
      TA_Planning


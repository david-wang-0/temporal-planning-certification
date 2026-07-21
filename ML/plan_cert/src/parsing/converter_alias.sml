(* The vendored FPS parser (pddl_refactor.sml) + temporal validator reference the PDDL AST +
   numeric/temporal constructors as `Continuous_PDDL_Checker_Exported`.  In this repo that
   export is `Converter` (ML/Check_Unsolvability.ML, via converter.mlb).  Aliasing lets the FPS
   parser be vendored essentially unchanged (only Assigna -> Assign, the one ctor we name
   differently). *)
structure Continuous_PDDL_Checker_Exported = Converter

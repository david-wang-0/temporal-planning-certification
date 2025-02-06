theory Ground_PDDL_Parsing
  imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
          Parsing.JSON_Parsing
begin


text \<open>
This is a parser for the output of the grounder provided by Andrew and Amanda Coles. 
The grounder is based on OPTIC.
\<close>

definition [consuming]:
  "middle l m r \<equiv> l *-- m --* r"

definition [consuming]:
  "paren_open \<equiv> token (exactly ''('')"

definition [consuming]:
  "paren_close \<equiv> token (exactly '')'')"

definition [consuming]:
  "parens p \<equiv> middle paren_open p paren_close"

definition [consuming]:
  "opt_parens p \<equiv> p \<parallel> parens p"

definition 
  "pddl_requirement_keywords \<equiv> ['':strips'', '':equality'', '':typing'', '':action-costs'', 
      '':negative-preconditions'', '':disjunctive-preconditions'', 
      '':existential-preconditions'', '':universal-preconditions'', '':quantified-preconditions'',
      '':adl'', '':numeric-fluents'', '':object-fluents'', '':action-costs'']"

definition 
  "pddl_reserved_keywords \<equiv> set pddl_requirement_keywords \<union> {
      ''define'', ''domain'', '':requirements'', '':predicates'', '':functions'',
      '':types'', '':constants'', '':action'', '':parameters'', '':precondition'', '':effect'', 
      '':invariant'', '':name'', '':vars'', '':set-constraint'',
      ''problem'', '':domain'', '':init'', '':objects'', '':goal'', '':metric'', ''maximize'', ''minimize'',              
      ''='', ''+'', ''-'', ''/'', ''*'', ''<'', ''>'', ''<='', ''>='', ''.'', ''and'', ''or'', ''imply'', ''not'', ''forall'', ''exists'', ''when'',
      ''either'', ''assign'', ''scale-up'', ''scale-down'', ''increase'', ''decrease'',
      ''number'', ''undefined'', ''total-cost'', ''object'',
      ''at'', ''start'', ''end'', ''over'', ''all'', ''?duration''}" 

definition
  "non_white_space \<equiv> do {
    x \<leftarrow> get;
    if x \<notin> (set char_wspace)
    then return x
    else err_expecting (shows ''non-whitespace character'')
  }"

definition             
  "pddl_token \<equiv> repeat1 non_white_space"


definition
  "pddl_keyword v \<equiv> do {
    w \<leftarrow> token pddl_token;
    _ \<leftarrow> if (v \<notin> pddl_reserved_keywords) 
         then error (shows ''Invalid keyword parser: \"'' o shows v o shows ''\" is not a keyword'') 
         else return ();
    if (w = v)
    then return w
    else err_expecting (shows ''PDDL keyword \"'' o shows v o shows ''\"'')
  }"

definition 
  "pddl_identifier \<equiv> do {
    w \<leftarrow> token pddl_token;
    if (w \<notin> pddl_reserved_keywords) 
    then return w
    else err_expecting (shows ''identifier'')
  }"

definition 
  "pddl_domain_head \<equiv> parens (pddl_keyword ''domain'' *-- pddl_identifier)"

definition alt_list::"('i, 'o) parser list \<Rightarrow> ('i, 'o) parser" where
  "alt_list ps \<equiv> fold (\<parallel>) ps (error (shows_string ''''))"

abbreviation (input) app (infixl "|>" 59) where "a |> b \<equiv> b a"

definition 
  "pddl_single_requirement \<equiv> 
    pddl_requirement_keywords
    |> (map pddl_keyword)
    |> alt_list
    |> token"

definition
  "pddl_requirements \<equiv> parens (pddl_keyword '':requirements'' *-- repeat pddl_single_requirement)"

definition
  "pddl_predicates \<equiv> parens (pddl_keyword '':predicates'' *-- repeat (opt_parens pddl_identifier))"

definition
  "pddl_action_params \<equiv> pddl_keyword '':parameters'' *-- parens (return ())"

definition
  "pddl_and p \<equiv> pddl_keyword ''and'' *-- repeat (parens p)"

definition
  "pddl_opt_and p \<equiv> (parens (pddl_and p)) \<parallel> p with (\<lambda>x. [x])"

definition
  "pddl_num \<equiv> lx_rat"

(* It seems that durations use inclusive bounds. *)
definition
  "pddl_duration_constraint \<equiv> (pddl_keyword ''<='' \<parallel> pddl_keyword ''>='') --* (pddl_keyword ''?duration'') *-- pddl_num"

definition 
  "pddl_duration_constraints \<equiv> pddl_opt_and pddl_duration_constraint"

definition
  "pddl_timed_pred \<equiv> 
    ((pddl_keyword ''at'' -- pddl_keyword ''start'')
    \<parallel> (pddl_keyword ''at''-- pddl_keyword ''end'')
    \<parallel> (pddl_keyword ''over'' -- pddl_keyword ''all'')) -- pddl_opt_and pddl_identifier"

definition
  "pddl_conditions \<equiv>
    pddl_keyword '':condition'' *-- pddl_opt_and pddl_timed_pred"

definition
  "pddl_effects \<equiv>
    pddl_keyword '':effects'' *-- pddl_opt_and pddl_timed_pred"

definition
  "pddl_durative_action \<equiv> 
    parens (
      pddl_keyword '':durative-action'' 
  *-- pddl_action_params 
   -- pddl_duration_constraints
   -- pddl_conditions
   -- pddl_effects)"

definition
  "pddl_ground_domain \<equiv> 
    parens (
      pddl_keyword ''define'' 
  *-- pddl_domain_head 
  *-- pddl_requirements 
   -- pddl_predicates 
   -- repeat pddl_durative_action)"

definition
  "pddl_problem_head \<equiv> 
    parens (
      parens (pddl_keyword ''problem'' *-- pddl_identifier)
   -- pddl_domain_head)"

definition
  "pddl_init \<equiv>
    parens (
      pddl_keyword '':init'' 
  *-- repeat (opt_parens pddl_identifier))"

definition
  "pddl_goal \<equiv>
    parens (
      pddl_keyword '':goal''
  *-- repeat (opt_parens pddl_identifier))"


definition
  "pddl_ground_problem \<equiv>
    parens (pddl_keyword ''define'' 
  *-- pddl_problem_head
  *-- pddl_init
   -- pddl_goal)"

end
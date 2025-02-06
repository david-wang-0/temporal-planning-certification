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

abbreviation 
  "str_to_pred x \<equiv> predAtm (Pred x) []"

definition
  "pddl_predicate \<equiv> pddl_identifier with str_to_pred"

definition 
  "pddl_single_requirement \<equiv> 
    pddl_requirement_keywords
    |> (map pddl_keyword)
    |> alt_list
    |> token"

definition
  "pddl_requirements \<equiv> parens (pddl_keyword '':requirements'' *-- repeat pddl_single_requirement)"

definition
  "pddl_predicates \<equiv> parens (pddl_keyword '':predicates'' *-- repeat (opt_parens pddl_predicate))"

definition
  "pddl_action_params \<equiv> pddl_keyword '':parameters'' *-- parens (return [])"

definition
  "pddl_and p \<equiv> pddl_keyword ''and'' *-- repeat (parens p)"

definition
  "pddl_opt_and p \<equiv> (parens (pddl_and p)) \<parallel> p with (\<lambda>x. [x])"

definition
  "pddl_num \<equiv> lx_rat"

fun fract_to_rat::"fract \<Rightarrow> rat" where
"fract_to_rat (fract.Rat True n d) = Fract n d" |
"fract_to_rat (fract.Rat False n d) = Fract (-n) d"

(* It seems that durations use inclusive bounds. *)
definition
  "pddl_duration_constraint \<equiv> 
  ( ( (pddl_keyword ''<='' *-- return duration_op.LEQ)
    \<parallel> (pddl_keyword ''>='' *-- return duration_op.GEQ)
    ) --* (pddl_keyword ''?duration'')
  ) -- pddl_num 
  with 
  (\<lambda>(op, dur). (Time_Const op (fract_to_rat dur)))"

definition 
  "pddl_duration_constraints \<equiv> pddl_opt_and pddl_duration_constraint"

definition
  "pddl_timed_pred \<equiv> 
    ( ((pddl_keyword ''at'' -- pddl_keyword ''start'') *-- (return At_Start))
    \<parallel> ((pddl_keyword ''at''-- pddl_keyword ''end'') *-- (return At_End))
    \<parallel> ((pddl_keyword ''over'' -- pddl_keyword ''all'') *-- (return Over_All))
    ) -- pddl_opt_and pddl_predicate"

definition
  "pddl_conditions \<equiv>
    pddl_keyword '':condition'' *-- pddl_opt_and pddl_timed_pred"

definition 
  "pddl_add_or_del \<equiv> 
    (parens (pddl_keyword ''not'' *-- pddl_identifier with Inl o str_to_pred))
    \<parallel> (pddl_identifier with (Inr o str_to_pred))"

fun left_sum::"('a, 'b) sum \<Rightarrow> 'a option" where
"left_sum (Inl a) = Some a" |
"left_sum (Inr a) = None"

fun right_sum::"('a, 'b) sum \<Rightarrow> 'b option" where
"right_sum (Inr a) = Some a" |
"right_sum (Inl a) = None"

fun sequence_list_opt::"'a option list \<Rightarrow> 'a list option" where
"sequence_list_opt [] = Some []" |
"sequence_list_opt (x#xs) = 
  do {
    x \<leftarrow> x;
    xs \<leftarrow> sequence_list_opt xs;
    Some (x # xs)
  }"

(* fun is_left::"('a, 'b) sum \<Rightarrow> bool" where
"is_left (Inl a) = True" |
"is_left (Inr a) = False"

fun is_right::"('a, 'b) sum \<Rightarrow> bool" where
"is_right (Inr a) = False" |
"is_right (Inl a) = True" *)

fun list_opt_unwrap::"'a list option \<Rightarrow> 'a list" where
"list_opt_unwrap None = []" |
"list_opt_unwrap (Some xs) = xs"

fun is_some::"'a option \<Rightarrow> bool" where
"is_some (Some x) = True" |
"is_some None = False"


definition "collect f xs \<equiv> xs |> map f |> filter is_some |> sequence_list_opt |> list_opt_unwrap"

definition 
  "pddl_timed_effect \<equiv> do {
    annotations \<leftarrow> (
        ((pddl_keyword ''at'' -- pddl_keyword ''start'') *-- (return At_Start))
      \<parallel> ((pddl_keyword ''at''-- pddl_keyword ''end'') *-- (return At_End))
      ) <+? (\<lambda>x. shows ''Expected ground effect'' o x);
    effects \<leftarrow> (
      pddl_opt_and pddl_add_or_del
      with (\<lambda>xs. (collect left_sum xs, collect right_sum xs)));
    return (annotations, effects)
  }"


definition
  "pddl_effects \<equiv> do {
    effects \<leftarrow> pddl_keyword '':effects'' *-- pddl_opt_and pddl_timed_effect;
    let is_as = (\<lambda>(a, b, c). if (a = At_Start) then (Some (b, c)) else None);
    let is_ae = (\<lambda>(a, b, c). if (a = At_End) then (Some (b, c)) else None);
    let combine_list_prod = (\<lambda>(a, b) (c, d). (a @ c, b @ c));
    let combine_effects = (\<lambda>xs. 
      fold combine_list_prod xs ([], []) 
      |> (map_prod (map formula.Atom) (map formula.Atom)) 
      |> uncurry Effect
      );
    let start_effs = effects |> collect is_as |> combine_effects;
    let end_effs = effects |> collect is_ae |> combine_effects;
    return (start_effs, end_effs)
  }"

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
theory Ground_PDDL_Parsing
  imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
          Parsing.JSON_Parsing
          Temporal_Planning_Base.Base
          Temporal_Planning_Base.Error_List_Monad_Add
begin

definition flat222 where
"flat222 \<equiv> \<lambda>(a, b, (c, d), e, f). (a, b, c, d, e, f)"

definition
"flat322 \<equiv> \<lambda>(a, b, c, (d, e), f, g). (a, b, c, d, e, f, g)"

abbreviation
"flat232 \<equiv> flat322 o flat222"

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

abbreviation str_to_pred::"string \<Rightarrow> object atom" where
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

definition pddl_action_params::"(char, variable list) parser" where
  "pddl_action_params \<equiv> pddl_keyword '':parameters'' *-- parens (return [])"

definition
  "pddl_and p \<equiv> pddl_keyword ''and'' *-- repeat (parens p)"

definition
  "pddl_opt_and p \<equiv> (parens (pddl_and p)) \<parallel> p with (\<lambda>x. [x])"

fun fract_to_rat::"fract \<Rightarrow> rat" where
"fract_to_rat (fract.Rat True n d) = Fract n d" |
"fract_to_rat (fract.Rat False n d) = Fract (-n) d"

definition
  "pddl_num \<equiv> lx_rat with fract_to_rat"


(* It seems that durations use inclusive bounds. *)
definition pddl_duration_constraint::"(char, object duration_constraint) parser" where
  "pddl_duration_constraint \<equiv> 
  ( ( (pddl_keyword ''<='' *-- return duration_op.LEQ)
    \<parallel> (pddl_keyword ''>='' *-- return duration_op.GEQ)
    ) --* (pddl_keyword ''?duration'')
  ) -- pddl_num 
  with uncurry Time_Const"

definition 
  "pddl_duration_constraints \<equiv> pddl_opt_and pddl_duration_constraint"

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

(* fun is_left::"('a, 'b) sum \<Rightarrow> bool" where
"is_left (Inl a) = True" |
"is_left (Inr a) = False"

fun is_right::"('a, 'b) sum \<Rightarrow> bool" where
"is_right (Inr a) = False" |
"is_right (Inl a) = True" *)

definition
  "pddl_timed_pred \<equiv> 
    ( ((pddl_keyword ''at'' -- pddl_keyword ''start'') *-- (return At_Start))
    \<parallel> ((pddl_keyword ''at''-- pddl_keyword ''end'') *-- (return At_End))
    \<parallel> ((pddl_keyword ''over'' -- pddl_keyword ''all'') *-- (return Over_All))
    ) -- pddl_opt_and pddl_predicate"

definition 
  "start_filter \<equiv> (\<lambda>(a, b). if (a = At_Start) then Some b else None)"

definition 
  "end_filter \<equiv> (\<lambda>(a, b). if (a = At_End) then Some b else None)"

definition
  "oa_filter \<equiv> (\<lambda>(a, b). if (a = Over_All) then Some b else None)"

definition
  "pddl_conditions \<equiv> do {
    conditions \<leftarrow> pddl_keyword '':condition'' *-- pddl_opt_and pddl_timed_pred;
    let s_effs = conditions |> collect start_filter |> (\<lambda>xs. fold (@) xs []);
    let e_effs = conditions |> collect end_filter |> (\<lambda>xs. fold (@) xs []);
    let oc = conditions |> collect oa_filter |> (\<lambda>xs. fold (@) xs []);
    return (oc, s_effs, e_effs)
  }"

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
    let combine_list_prod = (\<lambda>(a, b) (c, d). (a @ c, b @ c));
    let combine_effects = (\<lambda>xs. 
      fold combine_list_prod xs ([], [])
      );
    let start_effs = effects |> collect start_filter |> combine_effects;
    let end_effs = effects |> collect end_filter |> combine_effects;
    return (start_effs, end_effs)
  }"

definition
  "pddl_durative_action \<equiv> 
    parens (
      (pddl_keyword '':durative-action'' *-- pddl_identifier)
   -- (pddl_action_params 
    *-- pddl_duration_constraints
     -- pddl_conditions
     -- pddl_effects
      )
    ) with flat232"

definition
  "pddl_ground_domain \<equiv> 
    parens (
      pddl_keyword ''define'' 
  *-- pddl_domain_head 
  *-- pddl_requirements 
  *-- pddl_predicates 
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
  *-- repeat (opt_parens pddl_predicate))"

definition
  "pddl_goal \<equiv>
    parens (
      pddl_keyword '':goal''
  *-- repeat (opt_parens pddl_predicate))"


definition
  "pddl_ground_problem \<equiv>
    parens (pddl_keyword ''define'' 
  *-- pddl_problem_head
  *-- pddl_init
   -- pddl_goal)"


definition parse where
  "parse parser s \<equiv> case parse_all lx_ws parser s of
    Inl e \<Rightarrow> Error [e () ''Parser: '' |> String.implode]
  | Inr r \<Rightarrow> Result r"

value [code] "parse pddl_goal (STR ''1234'')"

ML_val \<open>
  @{code parse} @{code pddl_duration_constraints} "1234";\<close>

definition 
  "parse_dom_and_prob d p \<equiv> do {
    (preds, acts) \<leftarrow> parse pddl_ground_domain d;
    (init, goal) \<leftarrow> parse pddl_ground_problem p;
    
    Result (preds, acts, init, goal)
  }"



ML \<open>
  fun parse_domain_and_prob df pf =
  let 
    val p = file_to_string pf; 
    val d = file_to_string df
  in
    @{code parse_dom_and_prob} d p
  end
\<close>



end
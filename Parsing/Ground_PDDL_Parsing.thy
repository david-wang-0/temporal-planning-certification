theory Ground_PDDL_Parsing
  imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
          Parsing.JSON_Parsing
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
  "paren_open \<equiv> (exactly ''('') \<parallel> (token (exactly ''(''))"

definition [consuming]:
  "paren_close \<equiv> (exactly '')'') \<parallel> (token (exactly '')''))"

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
      '':types'', '':constants'', '':action'', '':durative-action'', '':parameters'', 
      '':precondition'', '':condition'', '':duration'', '':effect'', 
      '':invariant'', '':name'', '':vars'', '':set-constraint'',
      ''problem'', '':domain'', '':init'', '':objects'', '':goal'', '':metric'', ''maximize'', ''minimize'',              
      ''='', ''+'', ''-'', ''/'', ''*'', ''<'', ''>'', ''<='', ''>='', ''.'', ''and'', ''or'', ''imply'', ''not'', ''forall'', ''exists'', ''when'',
      ''either'', ''assign'', ''scale-up'', ''scale-down'', ''increase'', ''decrease'',
      ''number'', ''undefined'', ''total-cost'', ''object'',
      ''at'', ''start'', ''end'', ''over'', ''all'', ''?duration''}" 

(* 
definition
  "non_white_space \<equiv> do {
    x \<leftarrow> get;
    if x \<notin> (set char_wspace)
    then return x
    else err_expecting (shows ''non-whitespace character'')
  }" *)

definition
  "lx_dash_underscore \<equiv> do {
    x \<leftarrow> get;
    if x \<in> {CHR ''-'', CHR ''_''}
    then return x
    else err_expecting (shows ''Neither dash (-) nor underscore (_)'')
  }"

definition             
  "pddl_token \<equiv> repeat1 (lx_alphanum \<parallel> lx_dash_underscore)"

definition
  "lx_not_whitespace_nor_parens \<equiv> do {
    x \<leftarrow> get;
    if x \<notin> {CHR ''('', CHR '')'', CHR ''['', CHR '']'', CHR ''{'', CHR ''}''}
    then (
      if x \<notin> (set char_wspace)
      then return x
      else err_expecting (shows ''non-whitespace character'')
    )else err_expecting (shows ''Brackets encountered'')
  }"

definition 
  "pddl_word \<equiv> repeat1 lx_not_whitespace_nor_parens"

definition             
  "pddl_keyword_token \<equiv> 
    ((exactly '':'') -- pddl_word) with (uncurry (@))
    \<parallel> pddl_word"

definition
  "pddl_keyword v \<equiv> do {
    w \<leftarrow> token pddl_keyword_token;
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
  "pddl_predicate \<equiv> opt_parens (pddl_identifier with str_to_pred)"

definition 
  "pddl_single_requirement \<equiv> 
    pddl_requirement_keywords
    |> (map pddl_keyword)
    |> alt_list"

definition
  "pddl_requirements \<equiv> parens (pddl_keyword '':requirements'' *-- repeat pddl_single_requirement)"

definition
  "pddl_predicates \<equiv> parens (pddl_keyword '':predicates'' *-- repeat pddl_predicate)"

definition pddl_action_params::"(char, variable list) parser" where
  "pddl_action_params \<equiv> pddl_keyword '':parameters'' *-- (paren_open -- paren_close) with (\<lambda>_. [])"

definition
  "pddl_and p \<equiv> parens (pddl_keyword ''and'' *-- repeat p)"

definition
  "pddl_opt_and p \<equiv> (pddl_and p) \<parallel> p with (\<lambda>x. [x])"

fun fract_to_rat::"fract \<Rightarrow> rat" where
"fract_to_rat (fract.Rat True n d) = Fract n d" |
"fract_to_rat (fract.Rat False n d) = Fract (-n) d"

definition
  "pddl_num \<equiv> token (lx_rat with fract_to_rat \<parallel> lx_int with of_int)"


(* It seems that durations use inclusive bounds. *)
definition pddl_duration_constraint::"(char, object duration_constraint) parser" where
  "pddl_duration_constraint \<equiv> 
  parens ( 
    ( pddl_keyword ''<='' with (\<lambda>_. duration_op.LEQ)
    \<parallel> pddl_keyword ''>='' with (\<lambda>_. duration_op.GEQ)
    ) -- ((pddl_keyword ''?duration'') *-- pddl_num)
  ) with uncurry Time_Const"

definition 
  "pddl_duration_constraints \<equiv> 
    pddl_keyword '':duration'' *-- pddl_opt_and pddl_duration_constraint"
                 
definition 
  "pddl_add_or_del \<equiv> 
    (parens (pddl_keyword ''not'' *-- pddl_predicate with Pair False))
    \<parallel> (pddl_predicate with Pair True)"


(* fun is_left::"('a, 'b) sum \<Rightarrow> bool" where
"is_left (Inl a) = True" |
"is_left (Inr a) = False"

fun is_right::"('a, 'b) sum \<Rightarrow> bool" where
"is_right (Inr a) = False" |
"is_right (Inl a) = True" *)


definition 
  "pddl_timed_literal l \<equiv> 
    parens ( 
      ( ((pddl_keyword ''at'' -- pddl_keyword ''start'') *-- (return At_Start))
      \<parallel> ((pddl_keyword ''at''-- pddl_keyword ''end'') *-- (return At_End))
      \<parallel> ((pddl_keyword ''over'' -- pddl_keyword ''all'') *-- (return Over_All))
      ) -- pddl_opt_and l
    )"

definition 
  "start_filter \<equiv> (\<lambda>(a, b). if (a = At_Start) then Some b else None)"

definition 
  "end_filter \<equiv> (\<lambda>(a, b). if (a = At_End) then Some b else None)"

definition
  "oa_filter \<equiv> (\<lambda>(a, b). if (a = Over_All) then Some b else None)"

definition
  "add_filter \<equiv> (\<lambda>(a, b). if (a = True) then Some b else None)"

definition
  "del_filter \<equiv> (\<lambda>(a, b). if (a = False) then Some b else None)"

definition
  "pddl_conditions \<equiv> do {
    conditions \<leftarrow> pddl_keyword '':condition'' *-- pddl_opt_and (pddl_timed_literal pddl_predicate);
    let s_conds = conditions |> collect start_filter |> (\<lambda>xs. fold (@) xs []);
    let e_conds = conditions |> collect end_filter |> (\<lambda>xs. fold (@) xs []);
    let oc = conditions |> collect oa_filter |> (\<lambda>xs. fold (@) xs []);
    return (oc, s_conds, e_conds)
  }"

definition 
  "pddl_timed_effects \<equiv> do {
    effs \<leftarrow> pddl_keyword '':effect'' *-- pddl_opt_and (pddl_timed_literal pddl_add_or_del);
    let oc = effs |> collect oa_filter |> (\<lambda>xs. fold (@) xs []);
    _ \<leftarrow> if (oc \<noteq> []) then error (shows ''\"over all\" effects not permitted'') else return ();
  
    let s_effs = effs |> collect start_filter |> (\<lambda>xs. fold (@) xs []);
    let s_adds = s_effs |> collect add_filter;
    let s_dels =  s_effs |> collect del_filter;
    
    let e_effs = effs |> collect end_filter |> (\<lambda>xs. fold (@) xs []);
    let e_adds = e_effs |> collect add_filter;
    let e_dels =  e_effs |> collect del_filter;
    
    return ((s_adds, s_dels), (e_adds, e_dels))
  }"

definition
  "pddl_durative_action \<equiv> 
    parens (
      (pddl_keyword '':durative-action'' *-- pddl_identifier)
   -- (pddl_action_params 
    *-- pddl_duration_constraints
     -- pddl_conditions
     -- pddl_timed_effects
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
      parens (pddl_keyword ''problem'' *-- pddl_identifier)
   -- parens (pddl_keyword '':domain'' *-- pddl_identifier)"

definition
  "pddl_init \<equiv>
    parens (
      pddl_keyword '':init'' 
  *-- repeat1 pddl_predicate)"

definition
  "pddl_goal \<equiv>
    parens (
      pddl_keyword '':goal''
  *-- pddl_opt_and pddl_predicate)"


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
(* 
value "parse (token (pddl_keyword ''domain'')) (STR '' domain'')"

value [code] "parse pddl_goal (STR ''1234'')"

value "parse pddl_num (STR ''123'')"

value "parse (pddl_action_params -- pddl_duration_constraints) (STR '':parameters () :duration (and (>= ?duration 4)  (<= ?duration 4))'')"

value "parse pddl_duration_constraint (STR ''(<= ?duration 4)'')"

value "parse (pddl_opt_and pddl_duration_constraint) (STR ''(and (>= ?duration 4)  (<= ?duration 4))'')"

value "parse pddl_duration_constraints (STR '':duration (and (>= ?duration 4)  (<= ?duration 4))'')"

value "parse (pddl_keyword ''<='' with (\<lambda>_. duration_op.LEQ)) (STR ''<='')"

value "parse pddl_init (STR ''(:init
 (elevator-on-floor_e0_f2)
 (stopped_e0)
 (person-on-floor_p0_f0)
)'')"

value "parse pddl_goal (STR ''(:goal
(and
 (person-on-floor_p0_f1)
 (person-on-floor_p0_f2)
)
)'')" *)

ML_val \<open>
  @{code parse} @{code pddl_duration_constraints} "1234";\<close>

definition 
  "parse_dom_and_prob d p \<equiv> do {
    (preds, acts) \<leftarrow> parse pddl_ground_domain d;
    (init, goal) \<leftarrow> parse pddl_ground_problem p;
    
    Result (preds, acts, init, goal)
  }"


(* ML_val \<open>@{code parse} @{code pddl_domain_head} "(domain fasdf)"\<close>

ML_val \<open>@{code parse} @{code pddl_requirements} "(:requirements :strips)"\<close>

ML_val \<open>@{code parse} @{code pddl_problem_head} "(problem groundproblem) (:domain ground)"\<close>

ML_val \<open>@{code parse} @{code pddl_predicates} "(:predicates (elevator-on-floor_e0_f2))"\<close>

ML_val \<open>@{code parse} @{code pddl_durative_action} 
"(:durative-action _enter-elevator_p0_e0_f0_ :parameters () :duration (and (>= ?duration 4)  (<= ?duration 4)) :condition(and (over all (elevator-on-floor_e0_f0)) (over all (stopped_e0))(at start (person-on-floor_p0_f0)) ) :effect (and (at start (not (person-on-floor_p0_f0)))(at end (person-in-elevator_p0_e0)) ))"\<close>

 *)

ML \<open>
  fun parse_domain_and_problem df pf =
  let 
    val p = file_to_string pf; 
    val d = file_to_string df
  in
    @{code parse_dom_and_prob} d p
  end
\<close>

(* ML_val \<open>OS.FileSys.getDir()\<close>

ML_val \<open>
  parse_domain_and_problem
  "work/temporal_planning_certification/temporal-planning-certification/examples/ground-elevators.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/ground-elevators-prob1.pddl"
\<close> *)

end
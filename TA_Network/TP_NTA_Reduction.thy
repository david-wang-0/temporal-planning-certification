theory TP_NTA_Reduction
  imports Temporal_Planning_Base.Temporal_Plans
          "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics"
          "Show.Show_Instances"
          "List-Index.List_Index"
          "Simple_Networks.Simple_Network_Language_Model_Checking"
          "TA_Planning.Simple_Network_Language_Printing"
          Temporal_Planning_Base.Error_List_Monad_Add
begin

hide_const Simple_Expressions.bexp.true
           Simple_Expressions.bexp.not
           Simple_Expressions.bexp.and
           Simple_Expressions.bexp.or
           Simple_Expressions.bexp.imply
           Simple_Expressions.bexp.eq
           Simple_Expressions.bexp.le
           Simple_Expressions.bexp.lt
           Simple_Expressions.bexp.not
           Simple_Expressions.bexp.ge
           Simple_Expressions.bexp.gt
           Simple_Expressions.exp.const
           Simple_Expressions.exp.var
           Simple_Expressions.exp.if_then_else
           Simple_Expressions.exp.unop
           Simple_Expressions.exp.binop

hide_const UPPAAL_State_Networks_Impl.bexp.not
           UPPAAL_State_Networks_Impl.bexp.and
           UPPAAL_State_Networks_Impl.bexp.or
           UPPAAL_State_Networks_Impl.bexp.imply
           UPPAAL_State_Networks_Impl.bexp.eq
           UPPAAL_State_Networks_Impl.bexp.le
           UPPAAL_State_Networks_Impl.bexp.lt
           UPPAAL_State_Networks_Impl.bexp.not
           UPPAAL_State_Networks_Impl.bexp.ge
           UPPAAL_State_Networks_Impl.bexp.gt

(* To do: implement the compilation abstractly or directly using show? *)

(* To do: How does Simon Wimmer use int (32/64) instead of unlimited integers for some types? *)

context ta_temp_planning
begin
  (* To do: Implement abstract definition later *)
  (* This reduction has a different definition of no self overlap. Ends can interfere. 
     Actions can also have a duration of 0, if this matters. *)
end


text \<open>Converting propositions to variables\<close>
definition get_prop_num::"('p \<Rightarrow> nat option) \<Rightarrow> 'p \<Rightarrow> nat Error_List_Monad.result" where
"get_prop_num prop_nums p \<equiv> case prop_nums p of 
    None \<Rightarrow> Error [''Proposition has no ID'' |> String.implode]
  | Some n \<Rightarrow> Result n"

(* Clocks and variables do not need to be hard-coded *)
abbreviation var_prop_lock::"('p::show) \<Rightarrow> String.literal" where
"var_prop_lock p \<equiv> ''l_'' @ show p |> String.implode"

abbreviation var_prop::"('p::show) \<Rightarrow> String.literal" where
"var_prop \<equiv> String.implode o show"

definition "get_prop_lock prop_nums p \<equiv> get_prop_num prop_nums p \<bind> Result o var_prop_lock"
definition "get_prop_var prop_nums p \<equiv> get_prop_num prop_nums p \<bind> Result o var_prop"

abbreviation "prop_is prop_nums n p \<equiv> get_prop_var prop_nums p \<bind> (\<lambda>x. Result (bexp.eq (exp.var x) (exp.const n)))"
abbreviation "set_prop prop_nums n p \<equiv> get_prop_var prop_nums p \<bind> (\<lambda>x. Result (x, exp.const n))"

abbreviation "prop_lock_is prop_nums n p \<equiv> get_prop_lock prop_nums p \<bind> (\<lambda>x. Result (bexp.eq (exp.var x) (exp.const n)))"
abbreviation "inc_prop_lock prop_nums n p \<equiv> get_prop_lock prop_nums p \<bind> (\<lambda>x. Result (x, (exp.add (exp.var x) (exp.const n))))"

definition "planning_lock \<equiv> ''planning_lock'' |> String.implode"
definition "acts_active \<equiv> ''actions_active'' |> String.implode"

text \<open>Converting actions to clocks\<close>
definition get_act_num:: "('a \<Rightarrow> nat option) \<Rightarrow> 'a \<Rightarrow> nat Error_List_Monad.result" where
"get_act_num act_nums a \<equiv> case act_nums a of 
        None \<Rightarrow> Error [String.implode ''Action has no ID ''] 
      | Some n \<Rightarrow> Result n"

(* Is called with the number of the action *)
abbreviation start_act_clock::"('a::show) \<Rightarrow> String.literal" where
"start_act_clock a \<equiv> ''s_'' @ show a |> String.implode"

abbreviation end_act_clock::"('a::show) \<Rightarrow> String.literal" where
"end_act_clock a \<equiv> ''e_'' @ show a |> String.implode"

definition "get_start_clock act_nums a \<equiv> get_act_num act_nums a \<bind> (Result o start_act_clock)"
definition "get_end_clock act_nums a \<equiv> get_act_num act_nums a \<bind> (Result o end_act_clock)"



text \<open>Utility\<close>
fun bexp_and_all::"('a, 'b) bexp list \<Rightarrow> ('a, 'b) bexp" where
"bexp_and_all [] = bexp.true" |
"bexp_and_all (x#xs) = bexp.and x (bexp_and_all xs)"

section \<open>Reduction\<close>
(* prop_nums is a function that assigns an identifier to a predicate. It could be a number or a string *)
(*  off \<rightarrow> start instant!! \<rightarrow> pass time \<rightarrow> can end \<rightarrow> end instant!! \<rightarrow> off
      
                  increment mutex vars!
      check mutex vars!

      apply effects
      check pres

      update start clock!**
      check mutex actions**

      

                                    check lower constraint!
                                              check upper constraint!
    
                                              decrement mutex vars!
                                                            check mutex vars!

                                                            apply effects
                                                        <-- check pres (optional)

                                              update end clock!**
                                              check mutex actions**

                                    
                                                            

    Mutual exclusivity is calculated using intersection of additions and deletions. 

    Applying effects is convenient in the same transition as checking the mutex variables, because
    only deletions "access" invariants (i.e. make them false).

    Incrementing and decrementing the must happen when transitioning out of and into the urgent 
    locations, to allow simultaneous snap-action execution
    
    Start and end clocks must be updated as the instant is entered, so that mutex conditions can be checked.
    0-separation is hardcoded into this translation.

    Items marked with ! must be scheduled in the order to be correctly applied.

    * and ** mark some relationship
    
    Checking preconditions should be done at the start of the instants. Could result in fewer transitions
    taken while model-checking
    *)
(* intfs is a list of all interfering snap_actions *)
definition pre_eff_to_start_urg_edge::"
  (object atom \<Rightarrow> nat option) \<Rightarrow>
  's \<Rightarrow> 's \<Rightarrow> 
  object atom list \<Rightarrow> 
  object atom list \<times> object atom list \<Rightarrow>
  String.literal \<Rightarrow> 
  String.literal list \<Rightarrow> 
  ('s \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
  's) Error_List_Monad.result" where
"pre_eff_to_start_urg_edge prop_nums inactive s_urg pre eff start_clock intfs = do {
  let guard = map (\<lambda>x. acconstraint.GT x (0::int)) intfs;
  
  let adds = fst eff;
  let dels = snd eff;
  
  not_locked \<leftarrow> combine_map (prop_is prop_nums 0) dels;
  
  pres \<leftarrow> combine_map (prop_is prop_nums 1) pre;
  let check = bexp_and_all (not_locked @ pres);

  dels \<leftarrow> combine_map (set_prop prop_nums 0) dels;
  adds \<leftarrow> combine_map (set_prop prop_nums 1) adds;

  Result (inactive, check, guard, Sil (STR ''''), adds @ dels, [start_clock], s_urg)  
}"

(* In the same instant an action is activated, other actions which interact with an invariant can start.
    Invariants are checked over the open interval according to Fox and Long. Therefore, we add an urgent
    location. *)
definition oc_to_active_edge::"
  (object atom \<Rightarrow> nat option) \<Rightarrow> 
  's \<Rightarrow> 's \<Rightarrow> 
  object atom list \<Rightarrow>
  ('s \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
  's) Error_List_Monad.result" where
"oc_to_active_edge prop_nums s_urg active oc \<equiv> do {
  let to_inc = (\<lambda>v. Result (v, (exp.add (exp.var v) (exp.const 1))));
  
  lock_invs \<leftarrow> combine_map (\<lambda>p. get_prop_var prop_nums p \<bind> to_inc) oc;
  
  Result (s_urg, bexp.true, [], Sil (STR ''''), lock_invs, [], active)
}"


fun duration_constraint_constant::"object duration_constraint \<Rightarrow> int option Error_List_Monad.result" where
"duration_constraint_constant No_Const = Result None" |
"duration_constraint_constant (Func_Const _ f _) = 
  err (''Unground (functional) duration constraint \"'' @ (func.name f) @ ''\" encountered.''|> String.implode)" |
"duration_constraint_constant (Time_Const _ t) = (
  let (n, d) = quotient_of t
  in (
    if (d \<noteq> 1) 
    then (err o String.implode) (''Fraction encountered in duration constraint: '' @ show t @ ''. Needs normalisation to integers'') 
    else Result (Some n)
  )
)"


fun is_lower_constraint::"object duration_constraint \<Rightarrow> bool" where
"is_lower_constraint (Func_Const duration_op.EQ _ _) = True" |
"is_lower_constraint (Func_Const duration_op.GEQ _ _) = True" |
"is_lower_constraint (Time_Const duration_op.EQ _) = True" |
"is_lower_constraint (Time_Const duration_op.GEQ _) = True" |
"is_lower_constraint _ = False"

definition max_lower_dc::"object duration_constraint list \<Rightarrow> int option Error_List_Monad.result" where
"max_lower_dc dcs \<equiv> do {
  let ucs = filter is_lower_constraint dcs;
  consts \<leftarrow> combine_map duration_constraint_constant ucs;
  let consts = consts |> option_list_to_list;
  Result (list_max_opt consts)
}"
(* To do: check mutex when the clock is updated, not after *)

definition dur_consts_to_can_term::"
  's \<Rightarrow> 's \<Rightarrow> 
  object duration_constraint list \<Rightarrow> 
  String.literal \<Rightarrow>
  ('s \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
  's) Error_List_Monad.result" where
"dur_consts_to_can_term active can_terminate dcs start_clock \<equiv> 
do {
  dc \<leftarrow> max_lower_dc dcs;
  let guard = [get_or_default dc 0 |> acconstraint.GT start_clock];
  Result (active, bexp.true, guard, Sil (STR ''''), [], [], can_terminate)
}"
(* To do: numbering states? No. Nodes have names and ids. Transitions are just ids *)

fun is_upper_constraint::"object duration_constraint \<Rightarrow> bool" where
"is_upper_constraint (Func_Const duration_op.EQ _ _) = True" |
"is_upper_constraint (Func_Const duration_op.LEQ _ _) = True" |
"is_upper_constraint (Time_Const duration_op.EQ _) = True" |
"is_upper_constraint (Time_Const duration_op.LEQ _) = True" |
"is_upper_constraint _ = False"

definition min_upper_dc::"object duration_constraint list \<Rightarrow> int option Error_List_Monad.result" where
"min_upper_dc dcs \<equiv> do {
  let ucs = filter is_upper_constraint dcs;
  consts \<leftarrow> combine_map duration_constraint_constant ucs;
  let consts = consts |> option_list_to_list;
  Result (list_min_opt consts)  
}"

definition oc_const_to_urg_edge::"
  (object atom \<Rightarrow> nat option) \<Rightarrow>
  's \<Rightarrow> 's \<Rightarrow>
  object atom list \<Rightarrow>
  object duration_constraint list \<Rightarrow>
  String.literal \<Rightarrow> 
  String.literal \<Rightarrow> 
  String.literal list \<Rightarrow>
  ('s \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
  's) Error_List_Monad.result"  where
"oc_const_to_urg_edge prop_nums dur_sat urg oc dur_consts start_clock end_clock intfe \<equiv> 
do {
  
  let guard = map (\<lambda>x. acconstraint.GT x (0::int)) intfe;

  unlock_invs \<leftarrow> combine_map (inc_prop_lock prop_nums (-1)) oc;

  dc \<leftarrow> min_upper_dc dur_consts;
  let guard = (case dc of Some n \<Rightarrow> [acconstraint.LE start_clock n] | None \<Rightarrow> []);
  
  Result (dur_sat, bexp.true, guard, Sil (STR ''''), unlock_invs, [end_clock], urg)
}"




definition pre_eff_to_end_edge::"
  (object atom \<Rightarrow> nat option) \<Rightarrow>
  's \<Rightarrow> 's \<Rightarrow> 
  object atom list \<Rightarrow> 
  object atom list \<times> object atom list \<Rightarrow>
  ('s \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
  's) Error_List_Monad.result" where
"pre_eff_to_end_edge prop_nums urg inactive pre eff  = do {

  let adds = fst eff;
  let dels = snd eff;
  
  not_locked \<leftarrow> combine_map (prop_lock_is prop_nums 0) dels;
  
  pres \<leftarrow> combine_map (prop_is prop_nums 1) pre;

  let check = bexp_and_all (not_locked @ pres);

  dels \<leftarrow> combine_map (set_prop prop_nums 0) dels;
  adds \<leftarrow> combine_map (set_prop prop_nums 1) adds;
  
  Result (urg, check, [], Sil (STR ''''), adds @ dels, [], inactive)  
}"


(* This is more or less the output of Simple_Network_Language_Export_Code.convert_automaton *)
definition action_to_automaton::"
  (string \<times>            
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times> 
      (object atom list \<times> object atom list) 
      \<Rightarrow> nat option)
  \<Rightarrow> (object atom \<Rightarrow> nat option)
  \<Rightarrow> string \<times> 
      object duration_constraint list \<times> 
      object atom list \<times> 
      object atom list \<times> 
      object atom list \<times> 
      (object atom list \<times> object atom list) \<times> 
      (object atom list \<times> object atom list) 
  \<Rightarrow> String.literal list
  \<Rightarrow> String.literal list
  \<Rightarrow> _" where
"action_to_automaton act_nums prop_nums a intfs intfe  \<equiv> do {
  let (name, dc, oc, pre_at_start, pre_at_end, eff_at_start, eff_at_end) = a;
  num \<leftarrow> get_act_num act_nums a;
  
  let off = (''off_'' @ name |> String.implode, 0::nat);
  let starting = (''starting_'' @ name |> String.implode, 1);
  let active = (''active_'' @ name |> String.implode, 2);
  let can_stop = (''can_stop_'' @ name |> String.implode, 3);
  let stopping = (''stopping_'' @ name |> String.implode, 4);
  
  let node_list = [off, starting, active, can_stop, stopping];

  let names_to_ids = map_of node_list;
  let ids_to_names = map_of (map prod.swap node_list);

  let urgent = [snd starting, snd stopping];
  let committed = ([]::nat list);

  start_clock \<leftarrow> get_start_clock act_nums a;
  end_clock \<leftarrow> get_end_clock act_nums a;

  e1 \<leftarrow> pre_eff_to_start_urg_edge prop_nums (0::nat) (1::nat) pre_at_start eff_at_start start_clock intfs;

  e2 \<leftarrow> oc_to_active_edge prop_nums 1 2 oc;

  e3 \<leftarrow> dur_consts_to_can_term 2 3 dc start_clock;
  
  e4 \<leftarrow> oc_const_to_urg_edge prop_nums 3 4 oc dc start_clock end_clock intfe;

  e5 \<leftarrow> pre_eff_to_end_edge prop_nums 4 1 pre_at_end eff_at_end;

  let edges = [e1, e2, e3, e4, e5];
  let invs = ([]::(nat \<times> (String.literal, int) acconstraint list) list);

  Result (name |> String.implode, names_to_ids, ids_to_names, committed, urgent, edges, invs)
}
"

(* 
Normalise duration constraints by turning rationals into integers. 

Should be done while grounding.

fun duration_constraint_to_upper_const::"'a duration_constraint \<Rightarrow> (String.literal, int) acconstraint option" where
"duration_constraint_to_upper_const (Func_Const _ _ _) = None" |
"duration_constraint_to_upper_const (Time_Const op v) = undefined"



definition normalise_duration_constraints::"object duration_constraint list list \<Rightarrow> _" where
"normalise_duration_constraints dcs = do {
  consts \<leftarrow> combine_map (combine_map duration_constraint_constant) dcs |> err_msg (STR ''Cannot normalise duration constraints'');
  let all_consts = fold (@) consts [];
  Result None
}" *)
                       
(* derive (linorder) compare rat

derive (eq) ceq predicate func atom object 
derive ccompare predicate func atom object
derive (no) cenum atom object
derive (rbt) set_impl func atom object

derive (rbt) mapping_impl object


value "set [predAtm (Pred ''a'') ([]::object list), predAtm (Pred ''b'') ([]::object list)] \<inter> set [predAtm (Pred ''a'') ([]::object list)]"
 *)

definition mutex_effects::"
  'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow>
  'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"mutex_effects p1 a1 d1 p2 a2 d2 \<equiv> 
  set p1 \<inter> (set a2 \<union> set d2) \<noteq> {} \<or>
  set p2 \<inter> (set a1 \<union> set d1) \<noteq> {} \<or>
  set a1 \<inter> set d2 \<noteq> {} \<or>
  set a2 \<inter> set d1 \<noteq> {}
"

definition mutex_start::"
  string \<times> 
    object duration_constraint list \<times>
    object atom list \<times>
    object atom list \<times>
    object atom list \<times>
    (object atom list \<times> object atom list) \<times>
    (object atom list \<times> object atom list)
\<Rightarrow> string \<times> 
    object duration_constraint list \<times>
    object atom list \<times>
    object atom list \<times>
    object atom list \<times>
    (object atom list \<times> object atom list) \<times>
    (object atom list \<times> object atom list)
\<Rightarrow> (bool \<times> bool)" where
"mutex_start a b \<equiv>
   let 
    (_, _, pre, _, _, (adds, dels), _) = a;
    m = mutex_effects pre adds dels;
    (_, _, pre_s, pre_e, _, (adds_s, dels_s), (adds_e, dels_e)) = b
  in
    (m pre_s adds_s dels_s, m pre_e adds_e dels_e)
"

definition mutex_end::"
  string \<times> 
    object duration_constraint list \<times>
    object atom list \<times>
    object atom list \<times>
    object atom list \<times>
    (object atom list \<times> object atom list) \<times>
    (object atom list \<times> object atom list)
\<Rightarrow> string \<times> 
    object duration_constraint list \<times>
    object atom list \<times>
    object atom list \<times>
    object atom list \<times>
    (object atom list \<times> object atom list) \<times>
    (object atom list \<times> object atom list)
\<Rightarrow> (bool \<times> bool)" where
"mutex_end a b \<equiv> 
   let 
    (_, _, _, pre, _, _, (adds, dels)) = a;
    m = mutex_effects pre adds dels;
    (_, _, pre_s, pre_e, _, (adds_s, dels_s), (adds_e, dels_e)) = b
  in
    (m pre_s adds_s dels_s, m pre_e adds_e dels_e)
"

definition mutex_start_end::"
    (string \<times>
     object duration_constraint list \<times>
     object atom list \<times>
     object atom list \<times>
     object atom list \<times> 
    (object atom list \<times> object atom list) \<times> 
    (object atom list \<times> object atom list) 
    \<Rightarrow> nat option)
  \<Rightarrow> (string \<times> 
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times>
      (object atom list \<times> object atom list)) list
  \<Rightarrow> string \<times> 
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times>
      (object atom list \<times> object atom list)
  \<Rightarrow> (String.literal list \<times> String.literal list) Error_List_Monad.result" where
"mutex_start_end act_nums acts act \<equiv> do {                         
  let intfs = filter (fst o mutex_start act) acts;
  let intfe = filter (fst o mutex_end act) acts;
  
  intfs_clocks \<leftarrow> combine_map (get_start_clock act_nums) intfs |> err_msg (String.implode ''List of actions not consistent with ID assignment'');
  intfe_clocks \<leftarrow> combine_map (get_end_clock act_nums) intfe |> err_msg (String.implode ''List of actions not consistent with ID assignment'');

  Result (intfs_clocks, intfe_clocks)
}"


(* If an action's start and end do not interfere, then it could start in the instant it ends. There
is self-overlap, but only in one instance. *)
definition "mutex_snap_fun act_nums acts act \<equiv>
  if (act \<in> set acts) 
  then mutex_start_end act_nums acts act 
  else Error [''Action not in list of actions'' |> String.implode]
"


definition actions_to_automata::"
    (string \<times>
     object duration_constraint list \<times>
     object atom list \<times>
     object atom list \<times>
     object atom list \<times>                                             
    (object atom list \<times> object atom list) \<times>
    (object atom list \<times> object atom list)
     \<Rightarrow> nat option)
  \<Rightarrow> (object atom \<Rightarrow> nat option)
  \<Rightarrow> (string \<times> 
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times>
      (object atom list \<times> object atom list)) list
    \<Rightarrow> _" where
"actions_to_automata act_num prop_num as \<equiv> do {
  let msf = mutex_snap_fun act_num as;
  
  let to_auto = (\<lambda>a. do {
    (intfs, intfe) \<leftarrow> msf a;
    action_to_automaton act_num prop_num a intfs intfe
  });
  
  autos \<leftarrow> combine_map to_auto as;
  
  Result autos
}
"

(*names_to_ids, ids_to_names, committed, urgent, edges, invs*)

(* To do(?): map names rather than actions to numbers *)

definition init_props_and_lock_to_init_edge::"
  (object atom \<Rightarrow> nat option)
\<Rightarrow> 's \<Rightarrow> 's 
\<Rightarrow> object atom list
\<Rightarrow> String.literal
\<Rightarrow> ('s \<times> 
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times>
    's) Error_List_Monad.result" where
"init_props_and_lock_to_init_edge prop_nums i p init_props is_planning \<equiv> do {
  init_upds \<leftarrow> combine_map (set_prop prop_nums 1) init_props;
  let plan_lock = (is_planning, (exp.const 1));
  let can_start = bexp.eq (exp.var is_planning) (exp.const 0);
  Result (i, can_start, [], Sil (STR ''''), plan_lock#init_upds, [], p)
}"

definition goal_props_and_locks_to_goal_edge::"
  (object atom \<Rightarrow> nat option)
\<Rightarrow> 's \<Rightarrow> 's 
\<Rightarrow> object atom list
\<Rightarrow> String.literal
\<Rightarrow> String.literal
\<Rightarrow> ('s \<times> 
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times>
    's) Error_List_Monad.result" where
"goal_props_and_locks_to_goal_edge prop_nums p g goal_props is_planning actions_active \<equiv> do {
  let plan_lock = (is_planning, (exp.const 2));

  let can_end = bexp.eq (exp.var is_planning) (exp.const 0);
  goal_sat \<leftarrow> combine_map (prop_is prop_nums 1) goal_props;
  let cond = bexp_and_all (can_end#goal_sat);
  
  Result (p, cond, [], Sil (STR ''''), [plan_lock], [], g)
}"

(* is_planning_lock permits planning when it is set to 1. active_action_lock is only 0, when all
    actions have terminated. *)
definition main_auto::"
  (object atom \<Rightarrow> nat option)
\<Rightarrow> object atom list
\<Rightarrow> object atom list
\<Rightarrow> String.literal
\<Rightarrow> String.literal
\<Rightarrow> String.literal
\<Rightarrow> (String.literal \<times>
   (String.literal \<Rightarrow> nat option) \<times>
   (nat \<Rightarrow> String.literal option) \<times>
   nat list \<times>
   nat list \<times>
   (nat \<times>
      (String.literal, int) bexp \<times>
      (String.literal, int) acconstraint list \<times> 
      String.literal act \<times> 
      (String.literal \<times> (String.literal, int) exp) list \<times> 
      String.literal list \<times> 
      nat) list \<times>
   (nat \<times> (String.literal, int) acconstraint list) list) Error_List_Monad.result" where
"main_auto prop_nums init_props goal_props auto_name is_planning_lock active_action_lock \<equiv> do {

  let start = (''start'' |> String.implode, 0::nat);
  let planning = (''planning'' |> String.implode, 1::nat);
  let done = (''done'' |> String.implode, 2::nat);

  let urgent = [start, done] |> map snd;
  let committed = [];

  let node_list = [start, planning, done];
  let names_to_ids = map_of node_list;
  let ids_to_names = map_of (map prod.swap node_list);

  e1 \<leftarrow> init_props_and_lock_to_init_edge prop_nums 0 1 init_props is_planning_lock;
  e2 \<leftarrow> goal_props_and_locks_to_goal_edge prop_nums 1 2 goal_props is_planning_lock active_action_lock;
  
  let edges = [e1, e2];
  
  let invs = [];
  
  Result (auto_name, names_to_ids, ids_to_names, committed, urgent, edges, invs)
}"

context
begin

fun longest_pre_suff

(* For every prefix p of the pattern. Compute the longest suffix in p that is also a prefix in p *)
definition construct_lps::"string \<Rightarrow> nat list" where
"construct_lps str \<equiv> undefined"
end

definition unique_main_name::"string list \<Rightarrow> string" where
"unique_main_name names \<equiv> filter (

definition tp_to_ta_net::"
  object atom list \<times>
  (string \<times> object duration_constraint list \<times> 
    object atom list \<times> object atom list \<times> object atom list \<times> 
    (object atom list \<times> object atom list) \<times> (object atom list \<times> object atom list)
  ) list \<times>
  object atom list \<times> object atom list \<Rightarrow> _" where
"tp_to_ta_net args \<equiv>
  let (props, acts, init, goal) = args
  in do {
    let prop_numbering = [0..(length props - 1)] |> map nat |> zip props |> map_of;
    let act_numbering = [0..(length acts - 1)] |> map nat |> zip acts |> map_of;
    
    prop_locks \<leftarrow> combine_map (get_prop_lock prop_numbering) props;
    prop_vars \<leftarrow> combine_map (get_prop_var prop_numbering) props;

    act_start_clocks \<leftarrow> combine_map (get_start_clock act_numbering) acts;
    act_end_clocks \<leftarrow> combine_map (get_end_clock act_numbering) acts;
    
    act_automata \<leftarrow> actions_to_automata act_numbering prop_numbering acts;
    
    let prop_lock_var_defs = map (\<lambda>x. (x, 0, 1)) prop_locks;
    let prop_var_var_defs = map (\<lambda>x. (x, 0, 1)) prop_vars;
    
    let planning_lock = (planning_lock, 0, 2);
    let acts_active = (acts_active, 0, length acts);
    
    Result undefined
  }
"

term combine_map

end
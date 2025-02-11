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
 (* To do: Some functions not executable. Do it later. *)
end
find_consts name: "List_Index"

abbreviation var_pred_lock::"('p::show) \<Rightarrow> String.literal" where
"var_pred_lock p \<equiv> ''l_'' @ show p |> String.implode"

abbreviation var_pred::"('p::show) \<Rightarrow> String.literal" where
"var_pred \<equiv> String.implode o show"

(* To do: do not hard-code show? *)
definition preds_to_vars::"('p::show) list \<Rightarrow> String.literal list" where
"preds_to_vars ps \<equiv> map var_pred ps @ map var_pred_lock ps"

abbreviation start_act_clock::"('a::show) \<Rightarrow> String.literal" where
"start_act_clock a \<equiv> ''s_'' @ show a |> String.implode"

abbreviation end_act_clock::"('a::show) \<Rightarrow> String.literal" where
"end_act_clock a \<equiv> ''e_'' @ show a |> String.implode"

value "String.implode ''123'' # []"

term "fold"

definition acts_to_clocks::"('a::show) list \<Rightarrow> _" where
"acts_to_clocks as \<equiv> 
  as 
  |> map (\<lambda>a. (start_act_clock a, end_act_clock a)) 
  |> (\<lambda>xs. fold (\<lambda>(a, b) xs. (a#b#xs)) xs [])"

fun bexp_and_all::"('a, 'b) bexp list \<Rightarrow> ('a, 'b) bexp" where
"bexp_and_all [] = bexp.true" |
"bexp_and_all (x#xs) = bexp.and x (bexp_and_all xs)"

(* pred_nums is a function that assigns an identifier to a predicate. It could be a number or a string *)
(* Propositions that are deleted cannot be invariant. Invariance is implemented as a counter on the number
    of actions that lock a proposition. A proposition can only be updated when the counter is 0. When
    an action starts, its effects are applied by the first transition. The location is urgent. Other
    actions, which do not interfere with the action can start in the same instant. The next transition 
    increments the counter:
    
    off \<rightarrow> start instant \<rightarrow> pass time \<rightarrow> can end \<rightarrow> end instant \<rightarrow> off
      
      check pre
      apply effects
      check mutex actions
      check mutex vars
                  increment mutex vars

      

                                    check lower constraint
                                              check upper constraint
    
                                              decrement mutex vars
                                                            check mutex vars
                                                            check pre
                                                            apply effects
                                                            check mutex actions
      update start clock
                                              update end clock
                                    
                                                            

    Mutual exclusivity is calculated using intersection of additions and deletions. 
    Applying effects is convenient in the same transition as checking the mutex variables, because
    only deletions "access" invariants (i.e. make them false).
      Incrementing and decrementing the must happen when transitioning out of the urgent locations, to
      allow simultaneous snap-action execution
    
    Start and end clocks must be updated as the instant is entered, so that mutex conditions can be checked.
    0-separation is hardcoded into this translation.
    *)
(* intfs is a list of all interfering snap_actions *)
definition pre_eff_to_start_urg_edge::"
  (object atom \<Rightarrow> int) \<Rightarrow>
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
"pre_eff_to_start_urg_edge pred_nums inactive s_urg pre eff start_clock intfs = do {
  let guard = map (\<lambda>x. acconstraint.GT x (0::int)) intfs;
  
  let adds = fst eff;
  let dels = snd eff;
  
  let not_locked = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (0::int))) o var_pred_lock o pred_nums) dels;
  let pres = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (1::int))) o var_pred o pred_nums) pre;
  let check = bexp_and_all (not_locked @ pres);

  let dels = map ((\<lambda>x. (x, (exp.const 0)::(String.literal, int) exp)) o var_pred o pred_nums) dels;
  let adds = map ((\<lambda>x. (x, exp.const 1)) o var_pred o pred_nums) adds;

  let upds = [start_clock];
  
  let label = Sil (STR '''');
  Result (inactive, check, guard, Sil (STR ''''), adds @ dels, upds, s_urg)  
}"

(* In the same instant an action is activated, other actions which interact with an invariant can start.
    Invariants are checked over the open interval according to Fox and Long. Therefore, we add an urgent
    location. *)
definition oc_to_active_edge::"
  (object atom \<Rightarrow> int) \<Rightarrow> 
  's \<Rightarrow> 's \<Rightarrow> 
  object atom list \<Rightarrow>
  ('s \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
  's) Error_List_Monad.result" where
"oc_to_active_edge pred_nums s_urg active oc  \<equiv> do {
  let lock_invs = map ((\<lambda>x. (x, (exp.add (exp.var x) (exp.const 1)))) o var_pred_lock o pred_nums) oc;
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

definition max_min_dc::"object duration_constraint list \<Rightarrow> int option Error_List_Monad.result" where
"max_min_dc dcs \<equiv> do {
  let ucs = filter is_lower_constraint dcs;
  consts \<leftarrow> combine_map duration_constraint_constant ucs;
  let consts = consts |> option_list_to_list;
  Result (list_max_opt consts)  
}"

fun is_upper_constraint::"object duration_constraint \<Rightarrow> bool" where
"is_upper_constraint (Func_Const duration_op.EQ _ _) = True" |
"is_upper_constraint (Func_Const duration_op.LEQ _ _) = True" |
"is_upper_constraint (Time_Const duration_op.EQ _) = True" |
"is_upper_constraint (Time_Const duration_op.LEQ _) = True" |
"is_upper_constraint _ = False"

definition min_max_dc::"object duration_constraint list \<Rightarrow> int option Error_List_Monad.result" where
"min_max_dc dcs \<equiv> do {
  let ucs = filter is_upper_constraint dcs;
  consts \<leftarrow> combine_map duration_constraint_constant ucs;
  let consts = consts |> option_list_to_list;
  Result (list_min_opt consts)  
}"

definition oc_const_to_urg_edge::"
  (object atom \<Rightarrow> nat) \<Rightarrow>
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
"oc_const_to_urg_edge pred_nums dur_sat urg oc dur_consts start_clock end_clock intfs \<equiv> 
do {
  
  let guard = map (\<lambda>x. acconstraint.GT x (0::int)) intfs;
  let unlock_invs = map ((\<lambda>x. (x, (exp.add (exp.var x) (exp.const (-1))))) o var_pred_lock o pred_nums) oc;

  dc \<leftarrow> min_max_dc dur_consts;
  let guard = (case dc of Some n \<Rightarrow> [acconstraint.LE start_clock n] | None \<Rightarrow> []);
  
  Result (dur_sat, bexp.true, guard, Sil (STR ''''), unlock_invs, [end_clock], urg)
}"
   

definition pre_eff_to_end_edge::"
  (object atom \<Rightarrow> nat) \<Rightarrow>
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
"pre_eff_to_end_edge pred_nums urg inactive pre eff  = do {

  let adds = fst eff;
  let dels = snd eff;
  
  let not_locked = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (1::int))) o var_pred_lock o pred_nums) dels;
  
  let pres = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (1::int))) o var_pred o pred_nums) pre;
  let check = bexp_and_all (not_locked @ pres);

  let dels = map ((\<lambda>x. (x, (exp.const 0)::(String.literal, int) exp)) o var_pred o pred_nums) dels;
  let adds = map ((\<lambda>x. (x, exp.const 1)) o var_pred o pred_nums) adds;
  
  Result (urg, check, [], Sil (STR ''''), adds @ dels, [], inactive)  
}"

(* To do: Ensure that the final state can only be reached if every action has terminated. *)


definition dur_consts_to_intermediate_trans::"
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
"dur_consts_to_intermediate_trans active can_terminate dcs start_clock \<equiv> 
do {
  dc \<leftarrow> max_min_dc dcs;
  let guard = [get_or_default dc 0 |> acconstraint.GT start_clock];
  Result (active, bexp.true, guard, Sil (STR ''''), [], [], can_terminate)
}"
(* To do: numbering states? No. Nodes have names and ids. Transitions are just ids *)


definition action_to_automaton::"
  (string \<times>            
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times> 
      (object atom list \<times> object atom list) 
      \<Rightarrow> nat option)
  \<Rightarrow> (object atom \<Rightarrow> nat)
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
  num \<leftarrow> (case act_nums a of 
        None \<Rightarrow> Error [String.implode ''Action has no ID ''] 
      | Some n \<Rightarrow> Result (show n));
  
  let off = (''off_'' @ name |> String.implode, 0);
  let starting = (''starting_'' @ name |> String.implode, 1);
  let active = (''active_'' @ name |> String.implode, 2);
  let can_stop = (''can_stop_'' @ name |> String.implode, 3);
  let stopping = (''stopping_'' @ name |> String.implode, 4);
  
  let node_list = [off, starting, active, can_stop, stopping];

  let names_to_ids = map_of node_list;
  let ids_to_names = map_of (map prod.swap node_list);

  let urgent = [snd starting, snd stopping];
  let committed = [];

  let start_clock = start_act_clock num;
  let end_clock = end_act_clock num;

  let e1 = pre_eff_to_start_urg_edge prop_nums 0 1 pre_at_start eff_at_start start_clock intfs;

  let e2 = oc_to_active_edge prop_nums 1 2 oc;

  let e3 = dur_consts_to_intermediate_trans 2 3 dc start_clock;
  
  let e4 = oc_const_to_urg_edge prop_nums 3 4 oc dc start_clock end_clock intfe;

  let e5 = pre_eff_to_end_edge prop_nums 4 1 pre_at_end eff_at_end;

  let edges = [e1, e2, e3, e4, e5];
  let invs = [];

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
"mutex_start a b \<equiv> undefined"

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
"mutex_end a b \<equiv> undefined"
    

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
  \<Rightarrow> (String.literal \<times> String.literal) Error_List_Monad.result" where
"mutex_start_end act_nums acts act \<equiv> do {
  num \<leftarrow> (case act_nums act of 
        None \<Rightarrow> Error [String.implode ''Action has no ID ''] 
      | Some n \<Rightarrow> Result (show n));
 
  

  Result (undefined, undefined)
}"

definition mutex_snap_fun::"
    (string \<times>
     object duration_constraint list \<times>
     object atom list \<times>
     object atom list \<times>
     object atom list \<times> 
    (object atom list \<times> object atom list) \<times> 
    (object atom list \<times> object atom list) 
    \<Rightarrow> nat option)
  \<Rightarrow> string \<times> 
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times>
      (object atom list \<times> object atom list) list
  \<Rightarrow> (string \<times> 
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times>
      (object atom list \<times> object atom list) \<times>
      (object atom list \<times> object atom list) 
      \<Rightarrow> String.literal \<times> String.literal
    ) list Error_List_Monad.result" where
"mutex_snap_fun act_nums act \<equiv> do {
  
}"



(* Needs a step that turns rational duration constraints into upper and lower integer constraints *)
definition actions_to_automata::"
    (string \<times>
     object duration_constraint list \<times>
     object atom list \<times>
     object atom list \<times>
     object atom list \<times> object ast_effect \<times> object ast_effect
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
  Result undefined
}
"

definition tp_to_ta_net::"
  object atom list \<times>
  (string \<times> object duration_constraint list \<times> 
    object atom list \<times> object atom list \<times> object atom list \<times> 
    (object atom list \<times> object atom list) \<times> (object atom list \<times> object atom list)
  ) list \<times>
  object atom list \<times> object atom list \<Rightarrow> _" where
"tp_to_ta_net args \<equiv>
  let (preds, acts, init, goal) = args
  in do {
    let pred_numbering = [0..(length preds - 1)] |> map nat |> zip preds |> map_of;
    let preds_to_nats = (\<lambda>xs. xs |> map pred_numbering |> sequence_list_opt |> list_opt_unwrap);
    
    let nat_preds = preds_to_nats preds;
    let nat_init = preds_to_nats init;
    let nat_goal = preds_to_nats goal;

    let variables = STR ''lock'' # preds_to_vars nat_preds;
    
    let act_numbering = [0..(length acts - 1)] |> map nat |> zip acts |> map_of;
    let nat_acts = map act_numbering acts |> sequence_list_opt |> list_opt_unwrap;
    
    let clocks = acts_to_clocks nat_acts;
    
    Result undefined
  }
"

term combine_map

end
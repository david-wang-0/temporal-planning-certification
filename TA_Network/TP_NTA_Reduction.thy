theory TP_NTA_Reduction
  imports Temporal_Planning_Base.Temporal_Plans
          "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics"
          "Show.Show_Instances"
          "TA_Library.Error_List_Monad"
          "List-Index.List_Index"
          "Simple_Networks.Simple_Network_Language_Model_Checking"
          "TA_Planning.Simple_Network_Language_Printing"
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

definition is_ground_list::"object atom list \<Rightarrow> _" where
"is_ground_list a = undefined"

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
(* Propositions that are deleted cannot be invariant. Invariance is implemented as a lock counter.
    Assumption: Mutual exclusivity is calculated using intersection of additions and deletions. *)
(* intfs is a list of all interfering snap_actions *)
definition pre_eff_oc_to_start_edge::"
  's \<Rightarrow> 's \<Rightarrow> 
  object atom list \<Rightarrow> 
  object atom list \<times> object atom list \<Rightarrow> 
  object atom list \<Rightarrow> 
  String.literal list \<Rightarrow> _" where
"pre_eff_oc_to_start_edge inactive active pre eff oc intfs pred_nums start_clock = do {
  let guard = map (\<lambda>x. acconstraint.GT x (0::int)) intfs;
  let adds = fst eff;
  let dels = snd eff;
  
  let not_locked = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (0::int))) o var_pred_lock o pred_nums) dels;
  let pres = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (1::int))) o var_pred o pred_nums) pre;
  let check = bexp_and_all (not_locked @ pres);

  let dels = map ((\<lambda>x. (x, (exp.const 0)::(String.literal, int) exp)) o var_pred o pred_nums) dels;
  let adds = map ((\<lambda>x. (x, exp.const 1)) o var_pred o pred_nums) adds;

  let lock_invs = map ((\<lambda>x. (x, (exp.add (exp.var x) (exp.const 1)))) o var_pred_lock o pred_nums) oc;

  let upds = [start_clock];
  
  let label = Sil (STR '''');
  Result (inactive, check, guard, label, adds @ dels @ lock_invs, upds, active)  
}"


fun duration_constraint_to_upper_const::"'a duration_constraint \<Rightarrow> (String.literal, int) acconstraint option" where
"duration_constraint_to_upper_const (Func_Const _ _ _) = None" |
"duration_constraint_to_upper_const (Time_Const op v) = undefined"


(* I claim that locking invariants like this is valid. This rests on the assumption that the mutually
  exclusive snap-actions are provided adequately *)
definition pre_eff_oc_const_to_end_edge::"
  's \<Rightarrow> 's \<Rightarrow> 
  object atom list \<Rightarrow> 
  object atom list \<times> object atom list \<Rightarrow> 
  object atom list \<Rightarrow> 
  object duration_constraint list \<Rightarrow>
  String.literal list \<Rightarrow> _" where
"pre_eff_oc_const_to_end_edge can_terminate inactive pre eff oc con intfs pred_nums start_clock = do {
  let guard = map (\<lambda>x. acconstraint.GT x (0::int)) intfs;
  let adds = fst eff;
  let dels = snd eff;

  let del_m_inv = filter (\<lambda>x. x \<notin> set oc) dels;
  let del_in_inv = filter (\<lambda>x. x \<in> set oc) dels;
  
  let not_locked_1 = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (0::int))) o var_pred_lock o pred_nums) del_m_inv;
  let not_locked_2 = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (1::int))) o var_pred_lock o pred_nums) del_in_inv;
  let not_locked = not_locked_1 @ not_locked_2;
  
  let pres = map ((\<lambda>x. bexp.eq (exp.var x) (exp.const (1::int))) o var_pred o pred_nums) pre;
  let check = bexp_and_all (not_locked @ pres);

  let dels = map ((\<lambda>x. (x, (exp.const 0)::(String.literal, int) exp)) o var_pred o pred_nums) dels;
  let adds = map ((\<lambda>x. (x, exp.const 1)) o var_pred o pred_nums) adds;

  let unlock_invs = map ((\<lambda>x. (x, (exp.add (exp.var x) (exp.const (-1))))) o var_pred_lock o pred_nums) oc;

  let upds = [start_clock];
  
  let label = Sil (STR '''');
  Result (can_terminate, check, guard, label, adds @ dels @ unlock_invs, upds, inactive)  
}"

(* guards are clock constraints *)
(* checks are binary constraints on variables *)


definition action_to_automaton::"
  string \<times> 
    object duration_constraint list \<times> 
    object atom list \<times> 
    object atom list \<times> 
    object atom list \<times> (object atom list \<times> object atom list) \<times> (object atom list \<times> object atom list) 
  \<Rightarrow> (string \<times>            
      object duration_constraint list \<times>
      object atom list \<times>
      object atom list \<times>
      object atom list \<times> 
      object ast_effect \<times> 
      object ast_effect
      \<Rightarrow> nat option)
  \<Rightarrow> string list
  \<Rightarrow> string list
  \<Rightarrow> _" where
"action_to_automaton a f intfs intfe \<equiv> do {
  let (name, dc, oc, pre_at_start, pre_at_end, eff_at_start, eff_at_end) = a;
  num \<leftarrow> (case f a of 
        None \<Rightarrow> Error [String.implode ''Action has no ID ''] 
      | Some n \<Rightarrow> Result (show n));
  let inactive = (''inactive_'' @ name |> String.implode);
  let active = (''active_'' @ name |> String.implode);
  let can_terminate = (''can_terminate_'' @ name |> String.implode);

  let start_trans = 
  
  Result (name |> String.implode)
}
"


fun duration_constraint_constant::"object duration_constraint \<Rightarrow> _" where
"duration_constraint_constant No_Const = Result 0" |
"duration_constraint_constant (Func_Const _ f _) = 
  err (''Unground (functional) duration constraint \"'' @ (func.name f) @ ''\" encountered.''|> String.implode)" |
"duration_constraint_constant (Time_Const _ t) = Result t"


definition normalise_duration_constraints::"object duration_constraint list list \<Rightarrow> _" where
"normalise_duration_constraints dcs = do {
  consts \<leftarrow> combine_map (combine_map duration_constraint_constant) dcs |> err_msg (STR ''Cannot normalise duration constraints'');
  let all_consts = fold (@) consts [];
  Result None
}"

(* Needs a step that turns rational duration constraints into upper and lower integer constraints *)
definition actions_to_automata::"
  (string \<times> object duration_constraint list \<times> object atom list \<times> object atom list \<times> object atom list \<times> object ast_effect \<times> object ast_effect) list 
  \<Rightarrow>
  (string \<times>
   object duration_constraint list \<times>
   object atom list \<times>
   object atom list \<times>
   object atom list \<times> object ast_effect \<times> object ast_effect
   \<Rightarrow> nat option)
  \<Rightarrow> _" where
"actions_to_automata as an \<equiv> do {
  Result undefined
}
"

definition tp_to_ta_net::"object atom list \<times>
            (string \<times> object duration_constraint list \<times> object atom list \<times> object atom list \<times> object atom list \<times> (object atom list \<times> object atom list) \<times> (object atom list \<times> object atom list)) list \<times>
            object atom list \<times> object atom list \<Rightarrow> _" where
"tp_to_ta_net args \<equiv>
  let (preds, acts, init, goal) = args
  in do {
    let pred_numbering = [0..(length preds - 1)] |> map nat |> zip preds |> map_of;
    let preds_to_nats = (\<lambda>xs. xs |> map pred_numbering |> sequence_list_opt |> list_opt_unwrap);
    
    let nat_preds = preds_to_nats preds;
    let nat_init = preds_to_nats init;
    let nat_goal = preds_to_nats goal;

    let variables = ''lock'' # preds_to_vars nat_preds;
    
    let act_numbering = [0..(length acts - 1)] |> map nat |> zip acts |> map_of;
    let nat_acts = map act_numbering acts |> sequence_list_opt |> list_opt_unwrap;
    
    let clocks = acts_to_clocks nat_acts;
    
    Result undefined
  }
"

term combine_map

end
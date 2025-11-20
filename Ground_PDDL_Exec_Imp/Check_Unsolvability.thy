theory Check_Unsolvability
  imports Munta_Certificate_Checker.Simple_Network_Language_Certificate_Code Containers.Containers
    Ground_PDDL_NTA_Reduction_Correctness "Show.Shows_Literal"
begin


term ast_problem.wf_func_assign
print_derives
find_theorems name: "show*int"

typ String.literal



instantiation predicate::"show"
begin
definition "shows_prec p (x::predicate) \<equiv> \<lambda>y. show ''Pred'' @ show (predicate.name x) @ y"
definition "shows_list (x::predicate list) = showsp_list shows_prec 0 x"
instance
  by standard (simp_all add: shows_prec_predicate_def shows_list_predicate_def show_law_simps)
end

instantiation func::"show"
begin
definition "shows_prec p (x::func) \<equiv> \<lambda>y. show ''Func'' @ show (func.name x) @ y"
definition "shows_list (x::func list) = showsp_list shows_prec 0 x"
instance
  by standard (simp_all add: shows_prec_func_def shows_list_func_def show_law_simps)
end

instantiation atom::("show") "show"
begin

fun showf_atom where
"showf_atom (predAtm n as) y = show ''('' @ show n @ show as @ show '')'' @ y" |
"showf_atom (eqAtm a b) y = show ''('' @ show a @ show ''='' @ show b @ show '')'' @ y"

definition "shows_prec p (x::('a::show) atom) \<equiv> \<lambda>y. showf_atom x y"
definition "shows_list (x::('a::show) atom list) = showsp_list shows_prec 0 x"
instance
  apply standard 
  subgoal for _ x apply (cases x) by (simp add: shows_prec_atom_def shows_list_atom_def show_law_simps)+
  unfolding shows_prec_atom_def shows_list_atom_def
  apply (rule showsp_list_append)
  apply (intro ballI)
  subgoal for _ _ _ _ _ _ x  
    apply (cases x) by (simp add: shows_prec_atom_def shows_list_atom_def show_law_simps)+
  done
end


definition compute_model::"
    (nat \<Rightarrow> nat \<Rightarrow> String.literal) \<times>
       (String.literal \<Rightarrow> nat) \<times>
       String.literal list \<times>
       (nat list \<times>
        nat list \<times>
        (nat \<times>
         (String.literal, int) Simple_Expressions.bexp \<times>
         (String.literal, int) acconstraint list \<times>
         String.literal act \<times>
         (String.literal \<times> (String.literal, int) exp) list \<times>
         String.literal list \<times> nat) list \<times>
        (nat \<times>
         (String.literal,
          int) acconstraint list) list) list \<times>
       (String.literal \<times> int \<times> int) list \<times>
       (nat, nat, String.literal,
        int) Simple_Network_Language_Model_Checking.formula \<times>
       nat list \<times>
       (String.literal \<times> int) list
  \<Rightarrow>
    ((String.literal \<Rightarrow> nat) \<times>
     (String.literal \<Rightarrow> nat) \<times>
     (nat \<Rightarrow> nat \<Rightarrow> nat) \<times>
     (nat \<Rightarrow> String.literal) \<times>
     (nat \<Rightarrow> String.literal) \<times>
     (nat \<Rightarrow> nat \<Rightarrow> nat))
  \<Rightarrow> (String.literal list \<times>
            (String.literal \<times> int \<times> int) list \<times>
            (nat list \<times>
             nat list \<times>
             (nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat) list \<times>
             (nat \<times> (String.literal, int) acconstraint list) list) list \<times>
            nat list list \<times>
            nat list list list \<times>
            nat list \<times>
            (String.literal \<times> int) list \<times>
            (nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula \<times>
            nat \<times> (nat \<Rightarrow> nat) \<times> nat \<times> (String.literal \<Rightarrow> nat) \<times> (String.literal \<Rightarrow> nat) \<times> (String.literal \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> String.literal) \<times> (nat \<Rightarrow> String.literal)) Error_List_Monad.result" where
"compute_model model renaming \<equiv>
   do {
    let (ids_to_names, 
      process_names_to_index, 
      broadcast, 
      automata, 
      bounds, 
      formula, 
      L\<^sub>0, 
      s\<^sub>0) = model;
    let (var_renaming, clock_renaming, location_renaming,
      inv_renum_vars, 
      inv_renum_clocks, 
      inv_renum_states) = renaming;
    (m, num_states, num_actions, renum_acts, _, renum_clocks, renum_states, _, _, _)
      \<leftarrow> make_renaming broadcast automata bounds;
    assert (renum_clocks STR ''_urge'' = m) STR ''Computed renaming: _urge is not last clock!'';
    let renum_vars = var_renaming;
    let renum_clocks = clock_renaming;
    let renum_states = location_renaming;
    assert (renum_clocks STR ''_urge'' = m) STR ''Given renaming: _urge is not last clock!'';
    let _ = println (STR ''Renaming'');
    let (broadcast', automata', bounds') = rename_network
      broadcast bounds automata renum_acts renum_vars renum_clocks renum_states;
    let _ = println (STR ''Calculating ceiling'');
    let k = Simple_Network_Impl_nat_defs.local_ceiling broadcast' bounds' automata' m num_states;
    let urgent_locations = map (\<lambda>(_, urgent, _, _). urgent) automata';
    Result (broadcast, bounds, automata, urgent_locations, k, L\<^sub>0, s\<^sub>0, formula,
          m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
          inv_renum_states, inv_renum_vars, inv_renum_clocks)
   }"


definition "certificate_check" where
"certificate_check mode num_split dc state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars
    inv_renum_clocks \<equiv> do { 
 case mode of
    Debug \<Rightarrow> rename_check_dbg num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
        m num_states num_actions renum_acts renum_vars renum_clocks renum_states
        inv_renum_states inv_renum_vars inv_renum_clocks
        (reach_of state_space)
  | Impl1 \<Rightarrow> rename_check num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      (reach_of state_space)
  | Impl2 \<Rightarrow> rename_check2 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      (reach_of state_space) |> Heap_Monad.return
  | Impl3 \<Rightarrow> rename_check3 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      (reach_of state_space) |> Heap_Monad.return
  | Buechi \<Rightarrow> rename_check_buechi num_split broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      (buechi_of state_space) |> Heap_Monad.return
}
" for num_split and state_space :: "nat state_space"

lemma certificate_check_okay: 
  fixes num_split state_space
  assumes "mode \<noteq> Buechi" "mode \<noteq> Debug"
  shows "<emp> certificate_check mode num_split False state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
        m num_states num_actions renum_acts renum_vars renum_clocks renum_states
        inv_renum_states inv_renum_vars inv_renum_clocks
    <\<lambda> Sat \<Rightarrow> \<up>((\<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Simple_Network_Rename_Formula
        broadcast bounds
        renum_acts renum_vars renum_clocks renum_states STR ''_urge''
        s\<^sub>0 L\<^sub>0 automata formula)
     | Unsat \<Rightarrow> true
     | Preconds_Unsat \<Rightarrow> true
    >\<^sub>t"
proof (cases mode)
  case Impl1
  then show ?thesis 
  unfolding certificate_check_def
  by (simp add: certificate_check_rename)
next
  case Impl2
  define check where "check \<equiv> rename_check2 num_split False broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
     m num_states num_actions renum_acts renum_vars renum_clocks renum_states (reach_of state_space)"
  show ?thesis 
    unfolding certificate_check_def
    apply (subst Impl2)
    apply (subst mode.case)
    apply (rule return_cons_rule)
    apply (subst check_def[symmetric])
    apply (cases check)
    using certificate_check_rename2[of broadcast bounds renum_acts renum_vars renum_clocks renum_states s\<^sub>0 L\<^sub>0 automata formula
        num_split k m num_states num_actions "(reach_of state_space)", simplified check_def[symmetric]]
    by auto
next
  case Impl3
  define check where "check \<equiv> rename_check3 num_split False broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
     m num_states num_actions renum_acts renum_vars renum_clocks renum_states (reach_of state_space)"
  show ?thesis 
    unfolding certificate_check_def
    apply (subst Impl3)
    apply (subst mode.case)
    apply (rule return_cons_rule)
    apply (subst check_def[symmetric])
    apply (cases check)
    using certificate_check_rename3[of broadcast bounds renum_acts renum_vars renum_clocks renum_states s\<^sub>0 L\<^sub>0 automata formula
        num_split k m num_states num_actions "(reach_of state_space)", simplified check_def[symmetric]]
    by auto
qed (auto simp: assms)

instance Error_List_Monad.result::(heap)heap
  by countable_datatype


(* Note, that the state_space variable is the certificate. The naming convention is from the 
original function written by Simon Wimmer. *)
definition convert_check ::
    "mode
     \<Rightarrow> nat
        \<Rightarrow> bool
           \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> String.literal) \<times>
              (String.literal \<Rightarrow> nat) \<times>
              String.literal list \<times>
              (nat list \<times>
               nat list \<times>
               (nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat) list \<times> (nat \<times> (String.literal, int) acconstraint list) list) list \<times>
              (String.literal \<times> int \<times> int) list \<times> (nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula \<times> nat list \<times> (String.literal \<times> int) list
              \<Rightarrow> (String.literal \<Rightarrow> nat) \<times> (String.literal \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> String.literal) \<times> (nat \<Rightarrow> String.literal) \<times> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> int state_space \<Rightarrow> bool \<Rightarrow> Simple_Network_Language_Export_Code.result Error_List_Monad.result Heap" where
"convert_check mode num_split dc model renaming state_space show_cert \<equiv> 
(case do {
    r \<leftarrow> compute_model model renaming;
    let (broadcast, bounds, automata, urgent_locations, k, L\<^sub>0, s\<^sub>0, formula,
      m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
      inv_renum_states, inv_renum_vars, inv_renum_clocks) = r;
    let is_urgent = (\<lambda>(L::int list, L'::int list). list_ex (\<lambda>(l, urgent). l \<in> set urgent) (zip L (map (map int) urgent_locations)));
    let inv_renum_clocks = (\<lambda>i. if i = m then STR ''_urge'' else inv_renum_clocks i);
    let t = now ();
    let state_space = convert_state_space m is_urgent state_space;
    let t = now () - t;
    let _ = println (STR ''Time for converting state space: '' + time_to_string t);
    let _ = start_timer ();
    let _ = save_time STR ''Time for converting DBMs in certificate'';
    let _ =
      println (STR ''Number of discrete states: ''+ show_lit (len_of_state_space state_space));
    let _ = do {
      if show_cert then do {
        let _ = print_sep ();
        let _ = println (STR ''Certificate'');
        let _ = print_sep ();
        let _ = show_state_space m inv_renum_states inv_renum_vars inv_renum_clocks state_space;
        let _ = print_sep ();
        Heap_Monad.return ()}
      else Heap_Monad.return ()
    };
    Result (certificate_check mode num_split dc state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
        m num_states num_actions renum_acts renum_vars renum_clocks renum_states
        inv_renum_states inv_renum_vars inv_renum_clocks)
} 
of Result c \<Rightarrow> do {
    let t = now ();
    check \<leftarrow> c;
    let _ = (case check of
          Renaming_Failed \<Rightarrow> do {let _ = println STR ''Renaming failed''; Heap_Monad.return ()}
        | Preconds_Unsat \<Rightarrow> do {let _ = println STR ''Preconditions were not met''; Heap_Monad.return ()}
        | Sat \<Rightarrow> do {let _ = println STR ''Certificate was accepted''; Heap_Monad.return ()}
        | Unsat \<Rightarrow> do {let _ = println STR ''Certificate was rejected''; Heap_Monad.return ()});
    let t = now () - t;
    let _ = println (STR ''Time for certificate checking: '' + time_to_string t);
    Heap_Monad.return (Result check)
  }
| Error es \<Rightarrow> Heap_Monad.return (Error es))
" for num_split and state_space :: "int state_space"

(* A function needs to output a network and such *)

find_theorems name: tp_nta_reduction_spec

find_theorems name: "form_not_sat*ground"

thm ground_ast_problem.form_not_sat_imp_no_valid_ground_plan[no_vars]

definition make_network where
"make_network P \<equiv> (
    (tp_nta_reduction_spec.timed_automaton_net_spec (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))
      (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P)) AtStart AtEnd
      (temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P)) ground_ast_problem_defs.lower_spec ground_ast_problem_defs.upper_spec
      (temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec)
      (temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec) 0 (ground_ast_problem_defs.actions_spec P)
      ground_ast_problem_defs.act_to_name_spec ground_ast_problem_defs.prop_to_name_spec),
    tp_nta_reduction_spec.broadcast_spec,
    (tp_nta_reduction_spec.all_vars_spec (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))
      (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P)) AtStart AtEnd
      (temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec)
      (temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec) (ground_ast_problem_defs.props_spec P)
      (ground_ast_problem_defs.actions_spec P)
      ground_ast_problem_defs.prop_to_name_spec),
    tp_nta_reduction_model_checking.a\<^sub>0 
      (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))
      (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P)) 
      AtStart AtEnd
      (temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec)
      (temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec)
      (ground_ast_problem_defs.props_spec P) 
      (ground_ast_problem_defs.actions_spec P) 
      ground_ast_problem_defs.prop_to_name_spec,
    tp_nta_reduction_spec.formula_spec
)"

schematic_goal make_network_alt[code]:
  "make_network P \<equiv> ?x"
  unfolding make_network_def
  apply (abstract_let "tp_nta_reduction_spec.timed_automaton_net_spec (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))
      (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P)) AtStart AtEnd
      (temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P)) ground_ast_problem_defs.lower_spec
      ground_ast_problem_defs.upper_spec
      (temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec
        (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec)
      (temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec) 0
      (ground_ast_problem_defs.actions_spec P) ground_ast_problem_defs.act_to_name_spec ground_ast_problem_defs.prop_to_name_spec" autos)
  apply (abstract_let "tp_nta_reduction_spec.all_vars_spec (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))
      (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P)) AtStart AtEnd
      (temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec
        (ground_ast_problem_defs.props_spec P))
      (temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec)
      (temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec) (ground_ast_problem_defs.props_spec P)
      (ground_ast_problem_defs.actions_spec P) ground_ast_problem_defs.prop_to_name_spec" vars)
  apply (abstract_let "tp_nta_reduction_model_checking.a\<^sub>0 (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))
         (filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P)) AtStart AtEnd
         (temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P))
         (temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec
           (ground_ast_problem_defs.props_spec P))
         (temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec)
         (temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec)
         (ground_ast_problem_defs.props_spec P) (ground_ast_problem_defs.actions_spec P) ground_ast_problem_defs.prop_to_name_spec" init_vars)
  apply (abstract_let "(filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.init_spec P))" init')
  apply (abstract_let "(filter (\<lambda>p. p \<in> set (ground_ast_problem_defs.props_spec P)) (ground_ast_problem_defs.goal_spec P))" goal')
  apply (abstract_let "ground_ast_problem_defs.init_spec P" init)
  apply (abstract_let "ground_ast_problem_defs.goal_spec P" goal)
  apply (abstract_let "temp_planning_problem_list_defs.pre_imp_restr_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.pre_spec
           (ground_ast_problem_defs.props_spec P)" pre')
  apply (abstract_let "temp_planning_problem_list_defs.over_all_restr_list ground_ast_problem_defs.over_all_spec (ground_ast_problem_defs.props_spec P)" over_all')
  apply (abstract_let "ground_ast_problem_defs.props_spec P" props)
  apply (abstract_let "ground_ast_problem_defs.actions_spec P" actions)
  apply (abstract_let "ground_ast_problem_defs.act_to_name_spec" act_names)
  apply (abstract_let "ground_ast_problem_defs.prop_to_name_spec" prop_names)
  apply (abstract_let "ground_ast_problem_defs.over_all_spec" over_all)
  apply (abstract_let "temp_planning_problem_list_defs.add_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.adds_spec" add')
  apply (abstract_let "temp_planning_problem_list_defs.del_imp_list ground_ast_problem_defs.at_start_spec ground_ast_problem_defs.at_end_spec ground_ast_problem_defs.dels_spec" del')
  apply (abstract_let "ground_ast_problem_defs.at_start_spec" at_start)
  apply (abstract_let "ground_ast_problem_defs.at_end_spec" at_end)
  apply (abstract_let "ground_ast_problem_defs.adds_spec" adds)
  apply (abstract_let "ground_ast_problem_defs.dels_spec" dels)
  apply (abstract_let "ground_ast_problem_defs.pre_spec" pre)
  .

term "make_network P"


find_theorems name: "abs*let"

term "ground_ast_problem P"
definition "example_domain =
Domain [] [] [] [] []
"

definition "example_problem = 
  Problem example_domain [] [] (\<^bold>\<not>\<bottom>)
"

value "check_wf_problem example_problem"

definition "check_ground_problem P \<equiv> do {
  let D = ast_problem.domain P;
  let stg = ast_domain.STG D;
  let conT = ast_domain.mp_constT D;
  let mp = ast_problem.mp_objT P;
  check_wf_problem P stg conT mp;
  check (is_pos_conj (goal P)) (ERRS ''Goal not a conjunction of positive literals'');
  check_all_list pred_no_args (predicates D) ''Predicate not grounded (i.e. it has some argument)'' (shows o predicate.name o predicate_decl.pred);
  check_all_list act_no_params (actions D) ''Action not grounded, it has a/some parameter(s)'' (shows o ast_action_schema.name);
  check_all_list act_no_func_dcs (actions D) ''Action not grounded, it has a functional duration constraint'' (shows o ast_action_schema.name);
  check_all_list act_dcs_integers (actions D) ''Action's duration constraint is not an integer'' (shows o ast_action_schema.name);
  check_all_list act_pres_pos (actions D) ''Action has a conditions that is not a conjunction of positive literals'' (shows o ast_action_schema.name);
  check (functions D = []) (ERRS ''Domain has functions'');
  check (consts D = []) (ERRS ''Domain has constants'');
  check_all_list form_preds_no_args (init P) ''Initial literal not grounded (it refers to constants)'' 
    (\<lambda>(x::object atom Formulas.formula) (y::string). show y)
}"

lemma check_ground_problem_return_iff[return_iff]:
  "check_ground_problem P = Inr () \<longleftrightarrow> ground_ast_problem P"
proof -
  interpret ast_problem P .
  show ?thesis 
    unfolding check_ground_problem_def 
    unfolding ground_ast_problem_def
    unfolding wf_ast_problem_def
    unfolding ground_ast_problem_axioms_def
    unfolding list_all_iff
    by (fastforce simp: wf_problem'_correct return_iff)
qed



value "make_network example_problem"
value "check_ground_problem example_problem"

(* Need a function that can be called with the computed certificate and renaming *)

(* To do:
  - Write a function, which checks all the conditions of the locale.
  - Do the functions implemented in the locale need to be re-implemented for executability?
*)

definition make_certified_net where
"make_certified_net problem certifier \<equiv> 
do {
  let (names, network) = undefined problem;
  (renaming, cert) \<leftarrow> (case certifier (names, network) of
    None \<Rightarrow> (Error [STR ''Certificate could not be generated''])
  | Some x \<Rightarrow> (Result x));
  Result (network, renaming, cert)
}"

(* The problem and domain must be parsed using the code from the validator *)
(* The network is generated by calling a function that converts a ground problem into a network *)
definition check_and_cert_pddl_problem where
"check_and_cert_pddl_problem problem mode num_split certifier show_cert \<equiv> 
case make_certified_net problem certifier of 
  Result (network, renaming, cert) \<Rightarrow> do {
    res \<leftarrow> convert_check mode num_split False network renaming cert show_cert;
    let _ = (case res of 
      Result r \<Rightarrow> (case r of
        Sat \<Rightarrow> do {let _ = println STR ''The planning problem is unsolvable.''; Heap_Monad.return ()}
      | _   \<Rightarrow> do {let _ = println STR ''Something went wrong.''; Heap_Monad.return ()})
    | Error es \<Rightarrow> do {let _ = map println es; Heap_Monad.return ()});
    Heap_Monad.return ()
  }
| Error es \<Rightarrow> do {let _ = map println es; Heap_Monad.return ()}
" for num_split 

(* To do:
  - Change the parser for PDDL. (ML)
  - Extend the theory of the temporal validator to express facts about ground domains. (Isabelle)
  - Prove abstract temporal planning locale equivalent to temporal validator locale. (Isabelle)
    - Should be done after updating the abstract temporal planning locale.
  - Update temporal planning locales. (Isabelle)
    - This is can be done now, since the datatypes in use are known.
  - Convert networks of timed automata to correct formal for MLunta (ML).
  - Convert certificates to correct format for Isabelle (ML).
  - Convert renamings to correct format for Isabelle (ML).
 *)

end
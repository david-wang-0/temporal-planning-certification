theory Check_Unsolvability
  imports Munta_Certificate_Checker.Simple_Network_Language_Certificate_Code Containers.Containers
begin
term "parse_compute a b"
term "rename_check3"

term "convert_renaming a b c"

(* This is like parse_compute, but skips the parse step *)
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
      (reach_of state_space) |> return
  | Impl3 \<Rightarrow> rename_check3 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      (reach_of state_space) |> return
  | Buechi \<Rightarrow> rename_check_buechi num_split broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      (buechi_of state_space) |> return
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
definition "convert_check" where
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
        return ()}
      else return ()
    };
    Result (certificate_check mode num_split dc state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
        m num_states num_actions renum_acts renum_vars renum_clocks renum_states
        inv_renum_states inv_renum_vars inv_renum_clocks)
} 
of Result c \<Rightarrow> do {
    let t = now ();
    check \<leftarrow> c;
    let _ = (case check of
          Renaming_Failed \<Rightarrow> do {let _ = println STR ''Renaming failed''; return ()}
        | Preconds_Unsat \<Rightarrow> do {let _ = println STR ''Preconditions were not met''; return ()}
        | Sat \<Rightarrow> do {let _ = println STR ''Certificate was accepted''; return ()}
        | Unsat \<Rightarrow> do {let _ = println STR ''Certificate was rejected''; return ()});
    let t = now () - t;
    let _ = println (STR ''Time for certificate checking: '' + time_to_string t);
    return (Result check)
  }
| Error es \<Rightarrow> return (Error es))
" for num_split and state_space :: "int state_space"

term heap
(* Need a function that can be called with the computed certificate and renaming *)

definition certify_and_check where
"certify_and_check model mode num_split dc renaming state_space show_cert \<equiv> undefined
"
for num_split and state_space :: "int state_space" (* for ... overrides global names to bind a local variable *) 

definition make_certified_net where
"make_certified_net problem domain certifier \<equiv> 
do {
  let (names, network) = undefined problem domain;
  (renaming, cert) \<leftarrow> (case certifier (names, network) of
    None \<Rightarrow> (Error [STR ''Certificate could not be generated''])
  | Some x \<Rightarrow> (Result x));
  Result (network, renaming, cert)
}"

(* The problem and domain must be parsed using the code from the validator *)
(* The network is generated by calling a function that converts a ground problem into a network *)
definition check_and_cert_pddl_problem where
"check_and_cert_pddl_problem problem domain mode num_split certifier show_cert \<equiv> 
case make_certified_net problem domain certifier of 
  Result (network, renaming, cert) \<Rightarrow> do {
    res \<leftarrow> convert_check mode num_split False network renaming cert show_cert;
    let _ = (case res of 
      Result r \<Rightarrow> (case r of
        Sat \<Rightarrow> do {let _ = println STR ''The planning problem is unsolvable.''; return ()}
      | _   \<Rightarrow> do {let _ = println STR ''Something went wrong.''; return ()})
    | Error es \<Rightarrow> do {let _ = map println es; return ()});
    return ()
  }
| Error es \<Rightarrow> do {let _ = map println es; return ()}
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
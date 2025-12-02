theory Check_Unsolvability
  imports 
    Ground_PDDL_NTA_Reduction_Impl 
    "Show.Shows_Literal"
    Munta_Certificate_Checker.Simple_Network_Language_Certificate_Code
begin

fun act_sym where
"act_sym (In a) = a" |
"act_sym (Out a) = a" |
"act_sym (Sil a) = a"


definition action_list where
"action_list automata broadcast \<equiv>
((
  automata 
  |> map (\<lambda>(_, _, trans, _). trans)
  |> foldl (@) []
  |> map (\<lambda>(_, _, _, a, _, _, _). a)
  |> map act_sym) 
@ broadcast)"

declare Simple_Network_Impl.action_set_def[code del]

lemma [code]: "Simple_Network_Impl.action_set = (\<lambda>automata broadcast. action_list automata broadcast |> set)"
  sorry                               


definition "clkp_set_impl automata =
automata
|> map (\<lambda>A. snd (snd (snd A)))
|> map (map (\<lambda>(l, invs). invs))
|> map (map collect_clock_pairs)
|> foldl (@) []
|> foldl (\<union>) {}"


definition "clk_set_impl automata = 
(automata 
|> clkp_set_impl
|> (`) fst)
\<union> (
automata
|> map (\<lambda>A. (fst (snd (snd A))))
|> map (map (\<lambda>(_, _, _, _, _, r, _). set r))
|> foldl (@) []
|> foldl (\<union>) {})"

lemma trans_refine:
  "(\<Union>(l, e, g, a, r, u, l')\<in>Simple_Network_Language.trans (Simple_Network_Language.Prod_TA_Defs.N (set broadcast, map automaton_of automata, map_of bounds') i). {l, l'}) = 
  (automata ! i
  |> (\<lambda>(_,_,ts,_). ts)
  |> map (\<lambda>(l, _, _, _, _, _, l'). {l, l'})
  |> foldl (\<union>) {}
  )"
  sorry


declare Simple_Network_Impl.clk_set'_def[code del] 

lemma [code]: "Simple_Network_Impl.clk_set' = (\<lambda>automata. clk_set_impl automata)"
  sorry

definition "loc_set_impl automata p \<equiv>
(fst (snd (snd (automata ! p))))
|> map (\<lambda>(l, _, _, _, _, _, l'). {l, l'})
|> foldl (\<union>) {}"

declare Simple_Network_Impl.loc_set'_def[code del]

lemma [code]: "Simple_Network_Impl.loc_set' = (\<lambda>automata p. loc_set_impl automata p)"
  sorry


fun prod_TA_loc_set_impl where
"prod_TA_loc_set_impl (broadcast, automata, bounds) = 
(
let trans = [0..<length automata] 
    |> (map (\<lambda>p. automata ! p |> (\<lambda>(_, _, trans,_). trans)));
  locs = trans 
    |> map (map (\<lambda>(l, _, _, _, _, _, l'). {l, l'})) 
    |> foldl (@) []
    |> foldl (\<union>) {}
in locs
)"

(* It's better not to declare these deleted.
If they are deleted, they will throw an error during runtime.
If not, any export that refers to them will throw an error
declare Prod_TA_Defs.loc_set_def[code del] *)

lemma loc_set_alt:
  "Prod_TA_Defs.loc_set (set broadcast, map automaton_of automata, map_of bounds) = 
    prod_TA_loc_set_impl (broadcast, automata, bounds)"
  sorry



fun prop_TA_var_set_impl where
"prop_TA_var_set_impl (broadcast, automata, bounds) = 
([0..<length automata]
|> (map (\<lambda>p. automata ! p |> (\<lambda>(_, _, trans,_). trans)))
|> (map (map (\<lambda>(_, b, _, _, _, _, _). b)))
|> (map (map vars_of_bexp))
|> foldl (@) []
|> foldl (\<union>) {}) 
\<union>
([0..<length automata]
|> (map (\<lambda>p. automata ! p |> (\<lambda>(_, _, trans,_). trans)))
|> (map (map (\<lambda>(_, _, _, _, u, _, _). u)))
|> (map (map (map (\<lambda>(x, e). {x} \<union> vars_of_exp e))))
|> foldl (@) []
|> foldl (@) []
|> foldl (\<union>) {}) "

(* declare Prod_TA_Defs.var_set_def[code del] *)

lemma var_set_alt:
  "Prod_TA_Defs.var_set (set broadcast, map automaton_of automata, map_of bounds) 
    = prop_TA_var_set_impl (broadcast, automata, bounds)"
  sorry


fun prod_TA_act_set_impl where
"prod_TA_act_set_impl (broadcast, automata, bounds) =
([0..<length automata]
|> (map (\<lambda>p. automata ! p |> (\<lambda>(_, _, trans,_). trans)))
|> (map (map (\<lambda>(_, _, _, a, _, _, _). set_act a)))
|> foldl (@) []
|> foldl (\<union>) {}
)
\<union>
set broadcast"

(* declare Prod_TA_Defs.act_set_def[code del] *)

lemma act_set_alt:
  "Prod_TA_Defs.act_set (set broadcast, map automaton_of automata, map_of bounds)
    = prod_TA_act_set_impl (broadcast, automata, bounds)" sorry


derive (eq) ceq bexp act acconstraint exp

derive compare act acconstraint
derive (compare) ccompare act acconstraint

derive (collect) set_impl bexp exp

derive (rbt) set_impl act acconstraint

derive (no) ccompare exp bexp


declare make_renaming_def[code del]


schematic_goal make_renaming'[code]: "make_renaming \<equiv> ?x"
  apply (rule HOL.eq_reflection)
  unfolding make_renaming_def
  unfolding var_set_alt
  unfolding loc_set_alt
  ..

(* Circular dependency error resolved by providing a module name ... *)

declare Simple_Network_Impl_nat_defs.clkp_set''_def[code del]

definition "clkp_set''_impl automata i l \<equiv> 
Simple_Network_Impl_nat_defs.clkp_inv automata i l \<union> 
(automata ! i
|> (\<lambda>a. fst (snd (snd a)))
|> map (\<lambda>(l', b, g, _). if l' = l then collect_clock_pairs g else {})
|> foldl (\<union>) {})"

lemma [code]: "Simple_Network_Impl_nat_defs.clkp_set'' = clkp_set''_impl"
  sorry

lemma set_foldl_append: "(set (foldl (@) xs ys)) = \<Union>(set ` (insert xs (set ys)))"
  apply (induction ys arbitrary: xs)
  by auto

lemma invs_refine: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd o snd) automata)) =
  automata
  |> map (\<lambda>(committed, urgent, trans, invs). invs)
  |> map (map (\<lambda>(loc, inv). loc))
  |> foldl (@) []
  |> set"
  unfolding image_set
  unfolding map_map
  unfolding comp_def
  unfolding set_foldl_append
  by force

schematic_goal in_states_refine: "L \<in> Prod_TA_Defs.states (set broadcast, map automaton_of automata, map_of bounds')
  = ?x"
  unfolding Prod_TA_Defs.states_def
  unfolding mem_Collect_eq
  unfolding trans_refine 
  ..

thm Simple_Network_Rename_Formula_String_Defs.check_renaming_def[no_vars]

thm Simple_Network_Rename_Formula_String_Defs.check_renaming_def

declare Simple_Network_Rename_Formula_String_Defs.check_renaming_def[code del]

schematic_goal check_renaming_imp[code]: "Simple_Network_Rename_Formula_String_Defs.check_renaming = ?x"
  unfolding Simple_Network_Rename_Formula_String_Defs.check_renaming_def
  unfolding var_set_alt loc_set_alt act_set_alt
  unfolding image_set
  unfolding invs_refine
  unfolding in_states_refine
  ..

declare Simple_Network_Impl_nat_defs.check_precond2_def[code del]

schematic_goal check_precond2_impl[code]: "Simple_Network_Impl_nat_defs.check_precond2 = ?x"
  unfolding Simple_Network_Impl_nat_defs.check_precond2_def
  unfolding list_all_iff[symmetric]
  unfolding image_set
  unfolding Simple_Network_Impl_Defs.n_vs_def
  unfolding Prod_TA_Defs.n_ps_def
  unfolding Prod_TA_Defs.bounds_def (* Some of these constants have no definitions *)
  unfolding prod.case fst_conv snd_conv length_map
  ..


(* export_code Simple_Network_Impl_nat_defs.check_precond2
  in Eval module_name check_precond_2_test file_prefix x *)

declare Simple_Network_Impl_nat_ceiling_start_state_axioms_def[code del]

schematic_goal nat_ceiling_start_state_axioms_impl[code]: "Simple_Network_Impl_nat_ceiling_start_state_axioms = ?x"
  unfolding Simple_Network_Impl_nat_ceiling_start_state_axioms_def
  unfolding list_all_iff[symmetric]
  unfolding Simple_Network_Impl_Defs.n_vs_def
  unfolding Prod_TA_Defs.n_ps_def
  unfolding Prod_TA_Defs.bounds_def
  unfolding image_set
  unfolding prod.case fst_conv snd_conv length_map
  ..

thm Simple_Network_Impl_nat_defs.states_i_def
declare Simple_Network_Impl_nat_defs.states_i_def[code del]

schematic_goal states_i_impl[code]: "Simple_Network_Impl_nat_defs.states_i = ?x"
  unfolding Simple_Network_Impl_nat_defs.states_i_def
  unfolding list_all_iff[symmetric]
  unfolding Simple_Network_Impl_Defs.n_vs_def
  unfolding Prod_TA_Defs.n_ps_def
  unfolding Prod_TA_Defs.bounds_def
  unfolding image_set
  unfolding prod.case fst_conv snd_conv length_map
  ..



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

(* export_code certificate_check
  in Eval module_name make_renaming file_prefix Test *)

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
        \<Rightarrow> (String.literal \<Rightarrow> nat) \<times> (String.literal \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> String.literal) \<times> (nat \<Rightarrow> String.literal) \<times> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> int state_space \<Rightarrow> bool \<Rightarrow> 
  Simple_Network_Language_Export_Code.result Error_List_Monad.result Heap" where
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

find_theorems name: "Error_List*case"

thm return_cons_rule

find_theorems "?P \<Longrightarrow>\<^sub>A ?R ?x"

thm return_cons_rule

(* This made things really hard *)
lemma Error_List_Monad_result_case_rule:
  assumes "\<And>x. result = Result x \<Longrightarrow> <P> Heap_Monad.return x <R>"
          "\<And>x. <R x> f1 x <Q>" 
      and "\<And>x. result = Error x \<Longrightarrow> <P> Heap_Monad.return x <S>"
          "\<And>x. <S x> f2 x <Q>" 
  shows "<P> (case result of Result x \<Rightarrow> f1 x | Error x \<Rightarrow> f2 x) <Q>"
  apply (cases result)
   apply (rule ssubst, assumption)
   apply (subst Error_List_Monad.result.case)
   apply (rule Hoare_Triple.cons_pre_rule[OF _ assms(2)])
   apply (frule assms(1)) 
  apply (erule Unreachability_Misc.return_htD)
   apply (rule ssubst, assumption)
   apply (subst Error_List_Monad.result.case)
  apply (rule Hoare_Triple.cons_pre_rule[OF _ assms(4)])
   apply (frule assms(3)) 
  by (erule Unreachability_Misc.return_htD)


lemma convert_check_okay:
  fixes num_split state_space
  assumes mode: "mode \<noteq> Buechi" "mode \<noteq> Debug"
      and model: "model = (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0)"
  shows "
    <emp> 
      convert_check mode num_split False model renaming state_space show_cert
    <\<lambda> 
      Result Sat \<Rightarrow> \<up>((\<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula))
    | Result Renaming_Failed \<Rightarrow> true
    | Result Preconds_Unsat \<Rightarrow> true
    | Result Unsat \<Rightarrow> true
    | Error e \<Rightarrow> true
    >\<^sub>t"
proof (cases "make_renaming broadcast automata bounds")
  case res1: (Result x1)

  obtain a b c d e f where
    renaming: "renaming = (a, b, c, d, e, f)" by (cases renaming) auto

  obtain aa ba ca da ea fa g where
    x1: "x1 = (aa, ba, ca, da, ea, fa, g)" by (cases x1) auto

  obtain renum_states renum_vars x y where
    g: "g = (renum_states, renum_vars, x, y)" by (cases g) auto

  obtain broadcast' automata' bounds' where
    rename: "rename_network broadcast bounds automata da a b c = (broadcast', automata', bounds')" 
    by (cases "rename_network broadcast bounds automata da a b c") auto

  show ?thesis
  proof (cases "Error_List_Monad.assert (fa STR ''_urge'' = aa) STR ''Computed renaming: _urge is not last clock!''")
    case res2: (Result x2)
    show ?thesis 
    proof (cases "Error_List_Monad.assert (b STR ''_urge'' = aa) STR ''Given renaming: _urge is not last clock!''")
      case res3: (Result x1)
      show ?thesis 
        unfolding convert_check_def 
        unfolding Let_def
        unfolding compute_model_def Let_def
        unfolding model prod.case
        unfolding renaming
        unfolding prod.case
        unfolding res1
        unfolding x1
        unfolding bind.simps
        unfolding Error_List_Monad.result.case
        unfolding g prod.case
        unfolding res2
        unfolding Error_List_Monad.result.case 
        unfolding res3
        unfolding Error_List_Monad.result.case 
        unfolding rename prod.case
        unfolding Error_List_Monad.result.case 
        unfolding prod.case 
        unfolding Error_List_Monad.result.case 
        unfolding bind.simps
        apply (rule bind_rule)
         apply (rule certificate_check_okay[OF mode])
        apply (rule return_cons_rule) subgoal for x
          by (cases x) auto
        done
    next
      case err3: (Error x2)
      show ?thesis 
        unfolding convert_check_def Let_def
        unfolding compute_model_def Let_def
        unfolding model prod.case
        unfolding renaming
        unfolding prod.case
        unfolding res1
        unfolding x1
        unfolding bind.simps
        unfolding Error_List_Monad.result.case
        unfolding g prod.case
        unfolding res2
        unfolding Error_List_Monad.result.case 
        unfolding err3
        unfolding Error_List_Monad.result.case 
        apply (rule return_cons_rule)
        by simp
    qed
  next
    case err2: (Error x2)
    show ?thesis 
      unfolding convert_check_def Let_def
      unfolding compute_model_def Let_def
      unfolding model prod.case
      unfolding renaming
      unfolding prod.case
      unfolding res1
      unfolding x1
      unfolding bind.simps
      unfolding Error_List_Monad.result.case
      unfolding g prod.case
      unfolding err2
      unfolding Error_List_Monad.result.case 
      apply (rule return_cons_rule)
      by simp
  qed
next
  case err3: (Error x2)
  show ?thesis 
    unfolding convert_check_def Let_def
    unfolding compute_model_def Let_def
    unfolding model prod.case
    apply (induction renaming)
    unfolding prod.case
    unfolding err3
    unfolding bind.simps
    unfolding Error_List_Monad.result.case
    apply (rule return_cons_rule)
    unfolding Error_List_Monad.result.case
    by auto
qed
(* Hoare Logic is tedious in this case
  unfolding convert_check_def
proof (rule Error_List_Monad_result_case_rule)
  fix c
  assume comp: "compute_model model renaming \<bind>
         (\<lambda>r. let (broadcast, bounds, automata, urgent_locations, k, L\<^sub>0, s\<^sub>0, formula, m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states, inv_renum_states, inv_renum_vars,
                     inv_renum_clocks) = r;
                   is_urgent = \<lambda>(L, L'). list_ex (\<lambda>(l, urgent). l \<in> set urgent) (zip L (map (map int) urgent_locations)); inv_renum_clocks = \<lambda>i. if i = m then STR ''_urge'' else inv_renum_clocks i; t = now ();
                   state_space = convert_state_space m is_urgent state_space; t = now () - t; _ = println (STR ''Time for converting state space: '' + time_to_string t); _ = start_timer ();
                   _ = save_time STR ''Time for converting DBMs in certificate''; _ = println (STR ''Number of discrete states: '' + show_lit (len_of_state_space state_space));
                   _ = if show_cert
                       then let _ = print_sep (); _ = println STR ''Certificate''; _ = print_sep (); _ = show_state_space m inv_renum_states inv_renum_vars inv_renum_clocks state_space; _ = print_sep ()
                            in Heap_Monad.return ()
                       else Heap_Monad.return ()
               in Result
                   (certificate_check mode num_split False state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states
                     inv_renum_vars inv_renum_clocks)) =
         Result c"
  show "<emp> Heap_Monad.return c <\<lambda>c. \<up>(\<exists>state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states (inv_renum_states::nat \<Rightarrow> nat \<Rightarrow> nat)
                     (inv_renum_vars::nat \<Rightarrow> String.literal) (inv_renum_clocks::nat \<Rightarrow> String.literal). c = certificate_check mode num_split False state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states
                     inv_renum_vars inv_renum_clocks)>"
  proof (cases "compute_model model renaming")
    case res1: (Result x1)
    
    show ?thesis
    proof (cases x1)
      case x1: (fields a1 b1 c1 d1 e1 f1 g1)
      show ?thesis
      proof (cases g1)
        case g1: (fields a2 b2 c2 d2 e2 f2 g2)
        show ?thesis 
        proof (cases g2)
          case g2: (fields a3 b3 c3 d3 e3 f3)
          have c: "c =  (certificate_check mode num_split False (convert_state_space c2 (\<lambda>(L, L'). list_ex (\<lambda>(l, urgent). l \<in> set urgent) (zip L (map (map int) d1))) state_space) a1 b1 c1 e1 f1 a2 b2 c2 d2 e2 f2 a3 b3 c3 d3 e3
             (\<lambda>i. if i = c2 then STR ''_urge'' else f3 i))"
            using comp unfolding res1 x1 g1 g2 bind.simps Let_def Error_List_Monad.result.case prod.case by auto
          show ?thesis 
            unfolding c
            apply (rule return_cons_rule)
            by fastforce
        qed
      qed
    qed
  next
    case err1: (Error x2)
    show ?thesis using comp unfolding err1 bind.simps Let_def Error_List_Monad.result.case by auto
  qed
next
  fix c
  show "<\<up> (\<exists>state_space broadcast bounds automata k m num_states num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states inv_renum_vars inv_renum_clocks.
                c =
                certificate_check mode num_split False state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states inv_renum_vars
                 inv_renum_clocks)> let t = now ()
                                    in c \<bind>
                                       (\<lambda>check.
                                           let _ = case check of Renaming_Failed \<Rightarrow> let _ = println STR ''Renaming failed'' in Heap_Monad.return ()
                                                   | Preconds_Unsat \<Rightarrow> let _ = println STR ''Preconditions were not met'' in Heap_Monad.return ()
                                                   | Sat \<Rightarrow> let _ = println STR ''Certificate was accepted'' in Heap_Monad.return ()
                                                   | Unsat \<Rightarrow> let _ = println STR ''Certificate was rejected'' in Heap_Monad.return ();
                                               t = now () - t; _ = println (STR ''Time for certificate checking: '' + time_to_string t)
                                           in Heap_Monad.return
                                               (Result
                                                 check)) <\<lambda>r. case r of Result Sat \<Rightarrow> \<up> (\<not> Simple_Network_Language_Model_Checking.N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula) | Result _ \<Rightarrow> true
                                                               | Error e \<Rightarrow> true>\<^sub>t"
  proof (rule Hoare_Triple.norm_pre_pure_rule2)
    assume "\<exists>state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states (inv_renum_states::nat \<Rightarrow> nat \<Rightarrow> nat)
                     (inv_renum_vars::nat \<Rightarrow> String.literal) (inv_renum_clocks::nat \<Rightarrow> String.literal).
       c =
       certificate_check mode num_split False state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states inv_renum_vars
        inv_renum_clocks"
    then obtain state_space broadcast' bounds' automata' k  m num_states num_actions renum_acts renum_vars renum_clocks and renum_states inv_renum_states::"nat \<Rightarrow> nat \<Rightarrow> nat" and inv_renum_vars::"nat \<Rightarrow> String.literal" and inv_renum_clocks::"nat \<Rightarrow> String.literal" where
    c: "c =
       certificate_check mode num_split False state_space broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula m num_states num_actions renum_acts renum_vars renum_clocks renum_states inv_renum_states inv_renum_vars
        inv_renum_clocks"  by blast
    show " <emp> let t = now ()
          in c \<bind>
             (\<lambda>check.
                 let _ = case check of Renaming_Failed \<Rightarrow> let _ = println STR ''Renaming failed'' in Heap_Monad.return ()
                         | Preconds_Unsat \<Rightarrow> let _ = println STR ''Preconditions were not met'' in Heap_Monad.return () | Sat \<Rightarrow> let _ = println STR ''Certificate was accepted'' in Heap_Monad.return ()
                         | Unsat \<Rightarrow> let _ = println STR ''Certificate was rejected'' in Heap_Monad.return ();
                     t = now () - t; _ = println (STR ''Time for certificate checking: '' + time_to_string t)
                 in Heap_Monad.return
                     (Result check)) <\<lambda>r. case r of Result Sat \<Rightarrow> \<up> (\<not> Simple_Network_Language_Model_Checking.N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula) | Result _ \<Rightarrow> true | Error e \<Rightarrow> true>\<^sub>t"
      
  qed
qed
*)

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


(* The certifier takes a list of names clocks and automata, 
  which it would otherwise obtain when parsing *)
definition make_certified_net where
"make_certified_net problem certifier \<equiv> 
case check_and_make_network problem of
  Inl e \<Rightarrow> Error [STR ''Could not make network'', (e () []) |> String.implode]
| Inr (clocks, names, network) \<Rightarrow>
  do {
    (renaming, cert) \<leftarrow> (case certifier (clocks, (names, network)) of
      None \<Rightarrow> (Error [STR ''Certificate could not be generated''])
    | Some x \<Rightarrow> (Result x));
    Result (network, renaming, cert)
  }" 

lemma make_certified_net_okay:
  assumes "make_certified_net problem certifier = Result (network, renaming, cert)"
      and net: "network = (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars)"
      and not_sat: "\<not> (Simple_Network_Impl.sem automata broadcast bounds, (init_locs, map_of init_vars, (\<lambda>_. 0)) \<Turnstile> formula)"
    shows "(\<nexists>tp. valid_ground_plan problem tp)"
proof (cases "check_and_make_network problem")
  case (Inl a)
  thus ?thesis using assms(1)
    unfolding make_certified_net_def by simp
next
  case inr: (Inr k)
  show ?thesis
  proof (cases k)
    case (fields a b c d e f g)
    show ?thesis 
    proof (cases "certifier (a, b, c, d, e, f, g)")
      case None
      then show ?thesis 
        using assms(1)
        unfolding make_certified_net_def
        unfolding inr
        unfolding sum.case
        unfolding fields
        unfolding prod.case by simp
    next
      case (Some h)
      obtain x y where
        h: "h = (x, y)" by (cases h) auto
      have vars: "((c, d, e, f, g), x, y) = ((ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars), renaming, cert)"
        using assms(1)
        unfolding make_certified_net_def
        using inr fields Some h net by simp
      show ?thesis 
        using inr vars fields
        using not_sat
        using check_and_make_network_and_plan by simp
    qed
  qed
qed

(* (nat \<Rightarrow> nat \<Rightarrow> String.literal) \<times>
  (String.literal \<Rightarrow> nat) \<times>
  String.literal list \<times>
  (nat list \<times> nat list \<times> (nat \<times> (String.literal, int) Simple_Expressions.bexp \<times> (String.literal, int) acconstraint list \<times> String.literal act \<times> (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat) list \<times> (nat \<times> (String.literal, int) acconstraint list) list
    ) list \<times>
  (String.literal \<times> int \<times> int) list \<times> (nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula \<times> nat list \<times> (String.literal \<times> int) list *)

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
    Heap_Monad.return (res)
  }
| Error es \<Rightarrow> do {let _ = map println es; Heap_Monad.return (Error es)}
" for num_split

lemma check_and_cert_pddl_problem_okay: 
  assumes mode: "mode \<noteq> Buechi" "mode \<noteq> Debug"
  shows "
    <emp> 
      check_and_cert_pddl_problem problem mode num_split certifier show_cert 
    <\<lambda> Result Sat \<Rightarrow> \<up>((\<nexists>tp. valid_ground_plan problem tp))
     | _ \<Rightarrow> true>\<^sub>t"
proof (cases "make_certified_net problem certifier")
  case (Result res)
  obtain network renaming cert where
    res: "res = (network, renaming, cert)" by (cases res) auto
  obtain ids_to_names process_names_to_index 
    broadcast automata bounds formula init_locs init_vars where
    net: "network = (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars)"
    by (cases network) auto

  have intermediate_res: "\<not> Simple_Network_Impl.sem automata broadcast bounds,(init_locs, map_of init_vars, \<lambda>_. 0) \<Turnstile> formula 
    \<Longrightarrow> \<nexists>tp. valid_ground_plan problem tp" 
    apply (rule make_certified_net_okay[OF Result[simplified res net]])
    by auto


  have conv_commute: "(Simple_Network_Language.conv_A \<circ> automaton_of) x = (automaton_of \<circ> conv_automaton) x" for x
  proof -
    have 1: "map conv_ac (default_map_of [] d x) = default_map_of [] (map (\<lambda>(s, cc). (s, map conv_ac cc)) d) x" for d x
      unfolding default_map_of_def unfolding FinFun.map_default_def unfolding map_of_map
      by (cases "map_of d x") auto
    show ?thesis 
      apply (induction x)
      unfolding Simple_Network_Language.conv_A_def Simple_Network_Language.conv_t_def 
      unfolding conv_automaton_def
      unfolding automaton_of_def
      unfolding comp_def
      unfolding prod.case
      unfolding set_map
      unfolding 1 by simp
  qed
      

  show ?thesis 
    unfolding check_and_cert_pddl_problem_def
    unfolding Result Error_List_Monad.result.case
    unfolding res prod.case
    apply (rule bind_rule)
     apply (rule convert_check_okay[OF mode])
     apply (rule net)
    unfolding Let_def
    apply (rule return_cons_rule)
    subgoal for x
      apply (cases x)
      subgoal for b apply (cases b)
           apply simp
          apply simp
         apply simp
         apply (intro strip)
         apply (erule conjE)
        unfolding Simple_Network_Language.conv_def 
        unfolding prod.case 
        unfolding map_map
        unfolding conv_commute
        using intermediate_res
        unfolding Simple_Network_Impl.sem_def
        by auto
      by auto
    done
next
  case (Error x2)
  show ?thesis unfolding check_and_cert_pddl_problem_def
    unfolding Error
    unfolding Error_List_Monad.result.case Let_def
    apply (rule return_cons_rule) 
    by auto
qed

definition check_and_cert_pddl_problem_no_return where
"check_and_cert_pddl_problem_no_return problem mode num_split certifier show_cert =
do {
  _ \<leftarrow> check_and_cert_pddl_problem problem mode num_split certifier show_cert;
  Heap_Monad.return ()
}
" for num_split


export_code check_and_cert_pddl_problem_no_return
  in Eval module_name Certifier file_prefix certifier
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
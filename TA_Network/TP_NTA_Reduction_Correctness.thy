theory TP_NTA_Reduction_Correctness
  imports TP_NTA_Reduction_Spec
begin

instance rat::time 
  apply standard 
  using dense_order_class.dense apply blast
  using verit_eq_simplify(24) by blast

context tp_nta_reduction_spec
begin

subsection \<open>Automata\<close>

definition "ntas \<equiv> 
let (automata, clocks, vars, formula) = timed_automaton_net_spec 
in automata"                                     

text \<open>The returned automata also contain extra values\<close>
abbreviation "get_actual_auto \<equiv> snd o snd o snd"

subsubsection \<open>Actual automata\<close>

definition actual_autos where
"actual_autos = map get_actual_auto ntas"

subsection \<open>Actions\<close>
(* This needs to be lifted out of the locale *)
definition "broadcast \<equiv> []::String.literal list"

definition lower_sem where
"lower_sem \<equiv> (map_option (map_lower_bound Rat.of_int)) o lower"

definition upper_sem where
"upper_sem \<equiv> (map_option (map_upper_bound Rat.of_int)) o upper"

definition "form \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in formula"

lemma form_alt: "form \<equiv> Simple_Network_Language_Model_Checking.formula.EX (sexp.loc 0 GoalLocation)"
  unfolding form_def Let_def timed_automaton_net_spec_def prod.case .

definition "nta_vars \<equiv> let (automata, clocks, vars, formula) = timed_automaton_net_spec in vars"

definition "init_vars \<equiv> map (\<lambda>x. (fst x, 0::int)) nta_vars"

interpretation nta_sem: Simple_Network_Impl actual_autos broadcast nta_vars .

context 
  fixes \<pi>
  assumes vp: "valid_plan \<pi> (set init) (set goal) at_start at_end (set \<circ> over_all) lower_sem upper_sem (set \<circ> pre) (set \<circ> adds) (set \<circ> dels) (Rat.of_int \<epsilon>)"
      and pap: "plan_actions_in_problem \<pi> (set actions)"
      and nso: "no_self_overlap \<pi>"
begin
interpretation planning_sem: nta_temp_planning 
  "set init" "set goal" 
  at_start at_end 
  "set o over_all" 
  lower_sem upper_sem 
  "set o pre" "set o adds" "set o dels"
  "Rat.of_int \<epsilon>"
  "set props"
  "set actions"
  \<pi> 
  1
  apply standard 
  subgoal using some_propositions unfolding List.card_set apply (induction props) by auto
  subgoal using some_actions unfolding List.card_set apply (induction actions) by auto
  subgoal by simp
  subgoal by simp
  subgoal using eps_range unfolding Rat.of_int_def by auto
  subgoal using domain_ref_fluents using fluent_imp_const_valid_dom by blast
  using domain_ref_fluents init_props goal_props at_start_inj at_end_inj snaps_disj vp pap nso by simp+


definition to_var_asmt::"'proposition set \<Rightarrow> 'proposition set \<Rightarrow> 'proposition variable \<Rightarrow> int option" where
"to_var_asmt ps iv vr \<equiv> (
  case vr of
    PropVar p \<Rightarrow> if (p \<in> ps) then 1 else 0
  | PropLock p \<Rightarrow> if (p \<in> iv) then 1 else 0
) |> Some
"


(* The main automaton is the first automaton, so the index must be incremented *)
definition enter_start_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"enter_start_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := StartInstant act];

  ds = dels (at_start act) |> map PropVar;
  as = adds (at_start act) |> map PropVar;
  var_asmt' = var_asmt(ds [\<mapsto>] (list_of (0::int) (length ds)));
  var_asmt'' = var_asmt'(as [\<mapsto>] (list_of (0::int) (length as)));

  clock_asmt' = clock_asmt(ActStart act := 0)
in (act_locs', var_asmt'', clock_asmt')
"

definition enter_start_instants::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"enter_start_instants ns s \<equiv>
  seq_apply (map enter_start_instant ns) s
"


(* It is valid to assume that variables have an assignment. Hidden assumption (at this level)

The initial variable assignment has a domain equal to the set of actually occurring variables and
in no step is a variable unassigned *)
definition leave_start_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"leave_start_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := Running act];
  locks = over_all act |> map PropLock;
  cur_asmt = map (get_default 0 var_asmt) locks;
  next_asmt = map (\<lambda>x. x + 1) cur_asmt;
  var_asmt' = var_asmt(locks [\<mapsto>] next_asmt)
in (act_locs', var_asmt', clock_asmt)
"

definition leave_start_instants::"
nat list
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval) list" where
"leave_start_instants ns s \<equiv>
  seq_apply (map leave_start_instant ns) s
"
definition enter_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"enter_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := EndInstant act];

  locks = over_all act |> map PropLock;
  cur_asmt = map (get_default 1 var_asmt) locks;
  next_asmt = map (\<lambda>x. x - 1) cur_asmt;
  var_asmt' = var_asmt(locks [\<mapsto>] next_asmt);
  clock_asmt' = clock_asmt(ActEnd act := 0)
in (act_locs', var_asmt', clock_asmt')
"

definition "enter_end_instants ns s \<equiv> seq_apply (map enter_end_instant ns) s"

definition leave_end_instant::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"leave_end_instant n s \<equiv>
let 
  act = actions ! n;
  (act_locs, var_asmt, clock_asmt) = s;
  act_locs' = act_locs[Suc n := Off act];

  
  ds = dels (at_end act) |> map PropVar;
  as = adds (at_end act) |> map PropVar;
  var_asmt' = var_asmt(ds [\<mapsto>] (list_of (0::int) (length ds)));
  var_asmt'' = var_asmt'(as [\<mapsto>] (list_of (0::int) (length as)))
in (act_locs', var_asmt'', clock_asmt)
"

definition "leave_end_instants ns s \<equiv> seq_apply (map leave_end_instant ns) s"

(* apply all snap actions of the nth happening in the plan *)
definition apply_nth_happening::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"apply_nth_happening n s \<equiv>
let
  h = happ_at planning_sem.happ_seq (time_index \<pi> n);
  act_indices = [0..<length actions];
  start_indices = filter (\<lambda>n. at_start (actions ! n) \<in> h) act_indices;
  end_indices = filter (\<lambda>n. at_end (actions ! n) \<in> h) act_indices
in 
  [s] 
  |> (\<lambda>s. ext_seq s (map enter_end_instant end_indices))
  |> (\<lambda>s. ext_seq s (map enter_start_instant start_indices))
  |> (\<lambda>s. ext_seq s (map leave_end_instant end_indices))
  |> (\<lambda>s. ext_seq s (map leave_start_instant start_indices))
"

definition pass_time::"
real
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock, real) cval)" where
"pass_time t s \<equiv> map_prod id (map_prod id (\<lambda>clock_asmt. clock_asmt \<oplus> t)) s"


find_theorems name: "real*of"

definition get_delay::"nat \<Rightarrow> real" where
"get_delay i \<equiv>
  if (i = 0) 
  then \<epsilon> + 1
  else real_of_rat (htpl \<pi> ! i - htpl \<pi> ! (i - 1)) 
"


definition delay_and_apply::"
nat
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) 
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real)) list" where
"delay_and_apply i s \<equiv>
let
  delay = get_delay i
in
  s 
  |> pass_time delay
  |> apply_nth_happening i
"

definition start_planning::"
('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"start_planning s \<equiv>
let 
  (locs, var_asmt, clock_asmt) = s;
  main_auto_index = 0;

  locs' = locs[main_auto_index := Planning];
  
  init_props = map PropVar init;
  var_asmt' = var_asmt(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0);
  var_asmt'' = var_asmt'(init_props [\<mapsto>] (list_of (1::int) (length init)))
in (locs', var_asmt'', clock_asmt)"

definition end_planning::"
('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))
\<Rightarrow> ('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))" where
"end_planning s \<equiv>
let
  (locs, var_asmt, clock_asmt) = s;
  main_auto_index = 0;

  locs' = locs[main_auto_index := GoalLocation];
  
  init_props = map PropLock init;
  var_asmt' = var_asmt(PlanningLock \<mapsto> 2)
in (locs', var_asmt', clock_asmt)"


primcorec goal_run::"
  ('action location list \<times>
    ('proposition variable \<rightharpoonup> int) \<times>
    ('action clock, real) cval) 
\<Rightarrow> ('action location list \<times>
    ('proposition variable \<rightharpoonup> int) \<times>
    ('action clock, real) cval) stream" where
"goal_run s = s ## (goal_run s)"

(* Just for testing *)
definition "goal_state \<equiv> (GoalLocation # map Off actions, map_of (zip (map fst nta_vars) (map (fst o snd) nta_vars)), (\<lambda>x. 0))"

definition plan_steps::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) list" where
"plan_steps \<equiv>
let 
  htp_indices = [0..<length (htpl \<pi>)];
  apply_happs = map delay_and_apply htp_indices;
  seq = [nta_sem.a\<^sub>0] 
        |> (\<lambda>s. ext_seq s [start_planning]) 
        |> (\<lambda>s. ext_seq'' s apply_happs)
        |> (\<lambda>s. ext_seq s [end_planning])
in seq"

definition plan_state_sequence::"('action location list \<times>
    ('proposition variable \<Rightarrow> int option) \<times>
    ('action clock, real) cval) stream" where
"plan_state_sequence \<equiv> plan_steps @- (goal_run (last plan_steps))"



(* To do: move *)

lemma action_variables: 
  assumes "a \<in> set actions"
  shows "action_vars_spec a \<subseteq> PropLock ` (set props) \<union> PropVar ` (set props)"
  unfolding action_vars_spec_def Let_def inv_vars_spec_def set_map set_append snap_vars_spec_def 
  using domain_ref_fluents[simplified fluent_domain_def, THEN bspec, OF assms] 
  unfolding act_ref_fluents_def by auto

lemma init_variables:
  "PropVar ` (set init) \<union> PropVar ` (set goal) \<subseteq> PropVar ` (set props)"
  using init_props goal_props by auto



lemma all_actual_variables: "set (map fst all_vars_spec) = {ActsActive, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)"
proof -
  have 1: "set (map fst (filter (\<lambda>x. fst x \<in> \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)) (map (\<lambda>p. (PropLock p, 0, int (length actions))) props @ map (\<lambda>p. (PropVar p, 0, 1)) props))) 
    = \<Union> (set (map action_vars_spec actions)) \<union> set (map PropVar init) \<union> set (map PropVar goal)"
    apply (subst filter_append)
    unfolding filter_map comp_def
    unfolding set_append fst_conv map_append
    unfolding map_map comp_def fst_conv
    apply (subst (3) comp_def[of _ PropLock, symmetric])
    apply (subst filter_map[symmetric])
    apply (subst (4) comp_def[of _ PropVar, symmetric])
    apply (subst filter_map[symmetric])
    using action_variables init_variables 
    by auto
  show ?thesis 
    unfolding all_vars_spec_def Let_def prod.case fold_union'
    unfolding map_append
    unfolding set_append
    apply (subst list.map)+
    apply (subst fst_conv)+
    apply (subst list.set)+
    apply (subst 1)
    unfolding set_map ..
qed

lemma conv_committed: assumes "p < length (map (automaton_of o conv_automaton) actual_autos)"
  shows "committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = committed (map automaton_of actual_autos ! p)"
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "actual_autos ! p")
  subgoal for a b c d
    apply (rule ssubst[of "actual_autos ! p"])
     apply simp
    unfolding comp_apply
    unfolding conv_automaton_def automaton_of_def committed_def prod.case fst_conv ..
  done

lemma no_committed: 
  assumes "p < length actual_autos"
  shows "committed (map automaton_of actual_autos ! p) = {}"
  using assms
  unfolding actual_autos_alt automaton_of_def committed_def main_auto_spec_def Let_def action_to_automaton_spec_def
  apply (subst list.map)
  apply (subst map_map)
  unfolding comp_apply unfolding 

lemma conv_invs:
  assumes "p < length (map (automaton_of \<circ> conv_automaton) actual_autos)"
  shows "Simple_Network_Language.inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>x. map conv_ac (inv (map automaton_of actual_autos ! p) x))"
  apply (subst inv_def)+
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_map)
  using assms apply simp
  apply (cases "actual_autos ! p")
  subgoal for _ _ _ d
    apply (erule ssubst[of "(actual_autos ! p)"])
    apply (subst comp_apply)
    apply (subst conv_automaton_def)
    apply (subst prod.case)+
    apply (subst automaton_of_def)
    apply (subst prod.case)+
    apply (subst snd_conv)+
    apply (subst automaton_of_def)
    apply (subst prod.case)+
    apply (subst snd_conv)+
    apply (induction d)
     apply (subst list.map)
    unfolding default_map_of_def
     apply simp
    subgoal for d ds
      apply (induction d)
      subgoal for i c
        apply (rule ext)
        subgoal for x
          apply (subst list.map)
          apply (subst prod.case)+
          unfolding map_of_Cons_code
          apply (subst map_default_def)+
          apply (cases "i = x")
           apply (subst if_P, assumption)+
           apply simp
          apply (subst if_not_P, assumption)+
          apply (subst (asm) map_default_def)
          apply (rule subst[of "FinFun.map_default [] (map_of (map (\<lambda>(s, cc). (s, map conv_ac cc)) ds)) x" "map conv_ac (case map_of ds x of None \<Rightarrow> [] | Some b' \<Rightarrow> b')"])
           apply simp
          apply (subst map_default_def)
          by blast
        done
      done
    done
  done

lemma no_invs': assumes "p < length actual_autos"
  shows "inv (automaton_of (actual_autos ! p)) = (\<lambda>x. [])"
proof -
  have 1: "p' < length actions" if "p = Suc p'" for p'
    using assms that
    unfolding actual_autos_def ntas_def timed_automaton_net_spec_def Let_def prod.case 
    by simp+
  show ?thesis
  unfolding actual_autos_def  ntas_def timed_automaton_net_spec_def Let_def prod.case
  apply (subst map_map[symmetric])
  apply (subst map_snd_zip)
   apply simp
  unfolding main_auto_spec_def Let_def action_to_automaton_spec_def
  unfolding comp_apply
  apply (subst list.map)
  apply (subst map_map)
  unfolding snd_conv comp_def inv_def
  apply (cases p)
   apply simp
   apply (subst automaton_of_def)
   apply (subst prod.case)+
   apply (subst snd_conv)+
   apply (subst default_map_of_def) apply simp
  subgoal for p'
    apply (rule ssubst[of p])
     apply assumption
    apply (subst nth_Cons_Suc)
    apply (drule 1)
    apply (subst nth_map)
     apply assumption
    unfolding automaton_of_def prod.case snd_conv 
    apply (subst default_map_of_def)
    by simp
  done
qed

lemma no_invs: assumes "p < length (map (automaton_of \<circ> conv_automaton) actual_autos)"
  shows "inv (map (automaton_of \<circ> conv_automaton) actual_autos ! p) = (\<lambda>x. [])"
  apply (subst conv_invs[OF assms])
  apply (subst nth_map)
  using assms apply simp
  using no_invs'
  apply (subst no_invs')
  using assms by auto


lemma cval_add_0: "z\<oplus>(0::real) = z" unfolding cval_add_def 
  by simp

lemma step_t_possible:
  assumes "Simple_Network_Language.bounded (map_of nta_vars) y"
  shows "nta_sem.sem \<turnstile> \<langle>x, y, z\<rangle> \<rightarrow>\<^bsub>Simple_Network_Language.label.Del\<^esub> \<langle>x, y, z\<rangle>"
  apply (subst (2) cval_add_0[symmetric])
  unfolding nta_sem.sem_def
  apply (rule step_t)
  subgoal unfolding TAG_def using no_invs by simp
  subgoal unfolding TAG_def by simp
  subgoal unfolding TAG_def by blast
  subgoal unfolding TAG_def using assms by simp
  done

lemmas non_t_step_intro = step_t_possible[THEN step_u'.intros, rotated, rotated]

find_theorems name: "steps_append"

definition exec_state_to_loc_list::"'action set \<Rightarrow> 'action location list" where
"exec_state_to_loc_list S \<equiv> 
let es_to_loc = (\<lambda>a. if a \<in> S then Running a else Off a)
in (Planning # map es_to_loc actions)"

definition prop_state_to_var_asmt::"'proposition set \<Rightarrow> ('proposition \<Rightarrow> nat) \<Rightarrow> 'proposition variable \<Rightarrow> int option" where
"prop_state_to_var_asmt P PI p \<equiv> case p of
  PropVar p \<Rightarrow> if (p \<in> P) then Some 1 else Some 0
| PropLock p \<Rightarrow> Some (PI p)"

fun act_clock_spec::"rat \<Rightarrow> 'action clock \<Rightarrow> real" where
"act_clock_spec t (ActStart a) = real_of_rat (planning_sem.last_snap_exec (at_start a) t)" |
"act_clock_spec t (ActEnd a) = real_of_rat (planning_sem.last_snap_exec (at_end a) t)"


(* To do: actions must be distinct *)
(* Propositions must be distinct *)
lemma apply_happening_steps: 
  assumes "n < length (htpl \<pi>)"
      and "t = time_index \<pi> n"
      and "L = exec_state_to_loc_list (planning_sem.ES t)"
      and "\<forall>v \<in> actual_variables. v_asmt v = prop_state_to_var_asmt (planning_sem.plan_state_seq n) (planning_sem.invariant_state t) v"
      and "\<forall>c \<in> all_ta_clocks. c_asmt c = act_clock_spec t c"
    shows "nta_sem.steps (apply_nth_happening n (L, v_asmt, c_asmt))"
  sorry

lemma "nta_sem.steps ((undefined, undefined, undefined) # (undefined, undefined, undefined) # undefined)"
  apply (rule nta_sem.steps.intros)
   apply (subst prod.case)+
  apply (rule non_t_step_intro)
  sorry

find_theorems name: "urge*bisim"

lemma a\<^sub>0_alt: "nta_sem.a\<^sub>0 = (InitialLocation # map Off actions, map_of (map (\<lambda>x. (fst x, 0)) nta_vars), \<lambda>_. 0)"
  unfolding nta_sem.a\<^sub>0_def
  unfolding ntas_inits_alt
  unfolding init_vars_def
  ..

(* Todo?: Change the locale definition to make sure that the set of propositions occurring in actions
  is exactly the set of fluents *)

lemma map_of_zip_dom_to_range':
  "a \<in> set A \<Longrightarrow> length A = length B \<Longrightarrow> \<exists>x. map_of (zip A B) a = Some x \<and> x \<in> set B"
  apply (frule map_of_zip_fst)
   apply assumption
  apply (rule ssubst[of "map_of (zip A B) a"])
   apply assumption
  apply (subst (asm) index_less_size_conv[symmetric])
  by simp

lemma planning_start_state_char: 
  assumes "start_planning nta_sem.a\<^sub>0 = (l1, v1, c1)"
  shows "l1 = Planning # map Off actions 
    \<and> v1 PlanningLock = Some 1 
    \<and> v1 ActsActive = Some 0 
    \<and> (\<forall>p \<in> set init. v1 (PropVar p) = Some 1)
    \<and> (\<forall>v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0) 
    \<and> (\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None) 
    \<and> c1 = (\<lambda>_. 0)"
proof (intro conjI)
  have "l1 = Planning # map Off actions"
       "c1 = (\<lambda>_. 0)"
       and v1: "v1 = (map_of (map (\<lambda>x. (fst x, 0)) nta_vars))(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0, map PropVar init [\<mapsto>] list_of 1 (length init))"
    using assms unfolding a\<^sub>0_alt start_planning_def Let_def prod.case by simp+
  thus "l1 = Planning # map Off actions" "c1 = (\<lambda>_. 0)" by simp+
  show "v1 PlanningLock = Some 1" unfolding v1
    apply (subst Map.map_upds_apply_nontin) by auto
  show "v1 ActsActive = Some 0" unfolding v1
    apply (subst Map.map_upds_apply_nontin) by auto
  show "\<forall>p\<in>set init. v1 (PropVar p) = Some 1"
  proof (rule ballI)
    fix p
    assume a: "p \<in> set init"
    hence l: "0 < length init" by auto
    hence s: "set (list_of 1 (length init)) = {1}"
      apply (rule set_list_of) .
      
    have "map_of (zip (rev (map PropVar init)) (rev (list_of 1 (length init)))) (PropVar p) = Some 1" 
      using map_of_zip_dom_to_range'[of "PropVar p" "(rev (map PropVar init))", simplified, of "rev (list_of 1 (length init))", simplified length_list_of length_rev set_rev s]
      a by auto
    hence "map_of (rev (zip (map PropVar init) (list_of 1 (length init)))) (PropVar p) = Some 1" 
      apply -
      apply (subst zip_rev[symmetric])
       apply (subst length_list_of)
      by simp+
    thus "v1 (PropVar p) = Some 1" unfolding v1
      apply (subst map_upds_def)
      apply (subst map_add_Some_iff)
      by auto
  qed
  show "\<forall>v\<in>actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0" 
  proof (rule ballI)
    fix v
    assume a: "v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init)"
    hence b: "v \<in> actual_variables" by simp
    have "map_of (rev (zip (map PropVar init) (list_of 1 (length init)))) v = None"
      apply (subst zip_rev[symmetric])
      unfolding length_list_of
       apply simp
      apply (subst map_of_zip_is_None)
      unfolding length_list_of length_rev
       apply simp
      using a by simp
    moreover
    have 1: "(map (\<lambda>x. (fst x, 0)) nta_vars) = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" by auto
    have "((map_of (map (\<lambda>x. (fst x, 0)) nta_vars))(PlanningLock \<mapsto> 1, ActsActive \<mapsto> 0)) v = Some 0"
      apply (subst fun_upd_other)
      using a apply simp
      apply (subst fun_upd_other)
      using a apply simp
      using b unfolding actual_variables_correct
      apply (subst 1)
      apply (subst map_of_map)
      apply (subst comp_apply)
      apply (subst (asm) set_map)
      apply (erule imageE)
      subgoal for x
        apply (cases x)
        subgoal for y z
          using weak_map_of_SomeI by fastforce
        done
      done
    ultimately
    show "v1 v = Some 0" 
      unfolding v1
      apply (subst map_upds_def)
      apply (subst map_add_Some_iff)
      apply (rule disjI2)
      by simp
  qed
  show "\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None"
  proof (intro allI impI)
    fix v
    assume "v \<notin> actual_variables"
    with actual_variables_correct
    have 1: "v \<notin> set (map fst nta_vars)" by argo
    with all_actual_variables nta_vars'
    have 2: "v \<notin> {ActsActive, PlanningLock} \<union> (\<Union> (action_vars_spec ` set actions) \<union> PropVar ` set init \<union> PropVar ` set goal)" by simp
    
    have 3: "(map (\<lambda>x. (fst x, 0)) nta_vars) = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" by auto
    show "v1 v = None"
      unfolding v1
      apply (subst map_upds_apply_nontin)
      using 2 apply simp
      apply (subst fun_upd_other)
      using 2 apply simp
      apply (subst fun_upd_other)
      using 2 apply simp
      apply (subst 3)
      apply (subst map_of_map)
      apply (subst comp_def)
      using 1 
      unfolding set_map map_of_eq_None_iff[symmetric]
      by simp
  qed
qed

lemma init_vars_alt: "init_vars = map (\<lambda>(x, v). (x, (\<lambda>_. 0) v)) nta_vars" unfolding init_vars_def by auto

find_theorems name: "int" "((?f (?n::nat))::int)"

lemma init_vars_bounded: "bounded (map_of nta_vars) (map_of init_vars)"
  unfolding bounded_def
proof (intro conjI ballI)
  show 1: "dom (map_of init_vars) = dom (map_of nta_vars)" unfolding init_vars_alt apply (subst dom_map_of_map) apply (subst dom_map_of_conv_image_fst) by blast
  { fix x
    assume "x \<in> dom (map_of init_vars)" 
    then obtain y where
      y: "map_of nta_vars x = Some y" using 1 by auto
    hence "fst y = 0" unfolding nta_vars' unfolding all_vars_spec_def Let_def
      apply -
      apply (drule map_of_SomeD)
      by auto
    thus "fst (the (map_of nta_vars x)) \<le> the (map_of init_vars x)" unfolding init_vars_alt map_of_map comp_apply
      using y by simp
      
  }
  { fix x
    assume "x \<in> dom (map_of init_vars)"then obtain y where
      y: "map_of nta_vars x = Some y" using 1 by auto
    hence "snd y \<ge> 0" unfolding nta_vars' unfolding all_vars_spec_def Let_def
      apply -
      apply (drule map_of_SomeD)
      unfolding set_append
      apply (induction y)
      by auto
    thus "the (map_of init_vars x) \<le> snd (the (map_of nta_vars x))" unfolding init_vars_alt map_of_map comp_apply
      using y by simp
  }
qed
      
lemma main_auto_init_edge_spec_simp: "main_auto_init_edge_spec = (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning)"
  unfolding main_auto_init_edge_spec_def Let_def ..
(* 
lemma step_int_simp: "x = (l, b, g, Sil a, f, r, l') \<Longrightarrow>
  TRANS ''silent'' \<bar> (l, b, g, Sil a, f, r, l') \<in> Simple_Network_Language.trans (N ! p) \<Longrightarrow>
  ''committed'' \<bar> l \<in> committed (N ! p) \<or> (\<forall>p<length N. L ! p \<notin> committed (N ! p)) \<Longrightarrow>
  ''bexp'' \<bar> Simple_Expressions.check_bexp s b True \<Longrightarrow>
  ''guard'' \<bar> u \<turnstile> g \<Longrightarrow>
  ''target invariant'' \<bar> \<forall>p<length N. u' \<turnstile> Simple_Network_Language.inv (N ! p) (L' ! p) \<Longrightarrow>
  ''loc'' \<bar> L ! p = l \<Longrightarrow>
  ''range'' \<bar> p < length L \<Longrightarrow> ''new loc'' \<bar> L' = L[p := l'] \<Longrightarrow>
  ''new valuation'' \<bar> u' = [r\<rightarrow>0]u \<Longrightarrow> ''is_upd'' \<bar> is_upds s f s' \<Longrightarrow>
  ''bounded'' \<bar> Simple_Network_Language.bounded B s' \<Longrightarrow> 
  (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>" apply (rule step_int) *)

lemma initial_steps_are_steps: "nta_sem.steps (ext_seq' [nta_sem.a\<^sub>0] start_and_init_delay)"
proof -
  have "nta_sem.steps [nta_sem.a\<^sub>0, start_planning nta_sem.a\<^sub>0, pass_time (real_of_int (\<epsilon> + 1)) (start_planning nta_sem.a\<^sub>0)]" 
  proof (rule nta_sem.steps.intros)
    show "(case nta_sem.a\<^sub>0 of (L, s, u) \<Rightarrow> \<lambda>(L', s', u'). nta_sem.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (start_planning nta_sem.a\<^sub>0)"
    proof -
      obtain l1 v1 c1 where
        "start_planning nta_sem.a\<^sub>0 = (l1, v1, c1)"
        "l1 = Planning # map Off actions"
        "v1 PlanningLock = Some 1"
        "v1 ActsActive = Some 0"
        "\<forall>p \<in> set init. v1 (PropVar p) = Some 1"
        "\<forall>v \<in> actual_variables - ({PlanningLock, ActsActive} \<union> PropVar ` set init). v1 v = Some 0" 
        "\<forall>v. v \<notin> actual_variables \<longrightarrow> v1 v = None"
        "c1 = (\<lambda>_. 0)" using planning_start_state_char apply (cases "start_planning nta_sem.a\<^sub>0") by blast

      obtain l v and c::"'action clock \<Rightarrow> real" where
        arc: "(l, v, c) = nta_sem.a\<^sub>0" apply (cases "nta_sem.a\<^sub>0::('action location list \<times> ('proposition variable \<Rightarrow> int option) \<times> ('action clock \<Rightarrow> real))") by simp
      have "nta_sem.sem \<turnstile> \<langle>l, v, c\<rangle> \<rightarrow> \<langle>l1, v1, c1\<rangle>"
      proof (rule non_t_step_intro[where a = "Internal (STR '''')", simplified])
        show "nta_sem.sem \<turnstile> \<langle>l, v, c\<rangle> \<rightarrow>\<^bsub>Internal (STR '''')\<^esub> \<langle>l1, v1, c1\<rangle>"
          unfolding nta_sem.sem_def
        proof (rule step_u.step_int)
          show "TRANS ''silent'' \<bar> (InitialLocation, Simple_Expressions.bexp.eq (var PlanningLock) (exp.const 0), [], Sil STR '''', (PlanningLock, exp.const 1) # (ActsActive, exp.const 0) # map (set_prop_ab 1) init, [], Planning) \<in> Simple_Network_Language.trans (map (automaton_of \<circ> conv_automaton) actual_autos ! 0)" 
            apply (subst TAG_def)
            apply (subst nth_map)
             apply (subst actual_autos_def)
             apply (subst ntas_def)
            apply (subst timed_automaton_net_spec_def)
            unfolding Let_def prod.case
             apply simp
             apply (subst actual_autos_def)
             apply (subst ntas_def)
            apply (subst timed_automaton_net_spec_def)
            unfolding Let_def prod.case
            apply (subst nth_map)
             apply simp
            find_theorems name: "List.upt_"
            apply (subst upt_conv_Cons)
             apply simp
            apply (subst nth_zip)
              apply simp
             apply simp
            apply (subst nth_Cons_0)+
            unfolding main_auto_spec_def Let_def prod.case comp_apply snd_conv
            unfolding conv_automaton_def prod.case
            unfolding automaton_of_def prod.case
            unfolding Simple_Network_Language.trans_def fst_conv snd_conv
            unfolding set_map
            apply (subst list.set)
            apply (subst image_insert)
            apply (subst main_auto_init_edge_spec_def)
            unfolding Let_def prod.case
            by simp
            
          show "''committed'' \<bar> InitialLocation \<in> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! 0) \<or> (\<forall>p<length (map (automaton_of \<circ> conv_automaton) actual_autos). l ! p \<notin> committed (map (automaton_of \<circ> conv_automaton) actual_autos ! p))"
            apply (subst TAG_def)
            apply (subst conv_committed)
            using some_actual_autos apply simp
            apply (rule disjI2)
            apply (intro allI impI)
            subgoal for p
            apply (subst conv_committed)
            using some_actual_autos apply simp
      
            apply (subst nth_map)
            using some_actual_autos apply simp
            using actual_autos_alt

        qed sorry
        show "Simple_Network_Language.bounded (map_of nta_vars) v"
          using arc unfolding nta_sem.a\<^sub>0_def
          using init_vars_bounded by simp
      qed
    qed
    show "nta_sem.steps [start_planning nta_sem.a\<^sub>0, pass_time (real_of_int (plus_int \<epsilon> 1)) (start_planning nta_sem.a\<^sub>0)]" sorry
  qed
  thus ?thesis using start_and_init_delay_def by auto
qed

lemma plan_steps_are_steps: "nta_sem.steps plan_steps"
  unfolding plan_steps_def Let_def
  sorry


lemma end_of_steps_is_run: "nta_sem.run (goal_run (last plan_steps))" sorry

lemma "nta_sem.run (goal_run goal_state)" sorry


qed

lemma "nta_sem.steps (undefined # undefined # undefined)"
  find_theorems intro name: "steps"
  apply (rule nta_sem.stepsI)
  using nta_sem.steps.intros
  sorry

lemma state_seq_sat_goal: "ev (holds (\<lambda>(L, s, _). check_sexp (sexp.loc 0 GoalLocation) L (the \<circ> s))) plan_state_sequence"
  find_theorems intro name: "ev" sorry

find_theorems name: "nta_sem*steps"

lemma state_seq_is_run: "nta_sem.run plan_state_sequence"
  find_theorems name: "run*con"
  apply (rule nta_sem.extend_run'[where zs = plan_state_sequence])
  unfolding plan_state_sequence_def
  sorry

find_theorems name: "Simple_Network_Language_Model_Checking.step_u'.intros"

lemma "nta_sem.sem, nta_sem.a\<^sub>0 \<Turnstile> form"
proof -
  show "?thesis" unfolding form_alt 
    unfolding models_def formula.case
    find_theorems name: "nta_semEx_ev"
    apply (subst nta_sem.Ex_ev_def)
    find_theorems (200) name: "nta_sem*run"
    find_theorems name: deadlock
    apply (rule exI)
    apply (rule conjI)

     apply (coinduction rule: nta_sem.run.coinduct)
qed

end
end
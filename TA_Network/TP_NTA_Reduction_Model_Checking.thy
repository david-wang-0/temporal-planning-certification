theory TP_NTA_Reduction_Model_Checking
  imports TP_NTA_Reduction_Spec
begin

locale type_naming =
  fixes mem_to_name:: "'ty \<Rightarrow> String.literal"

locale unique_names = type_naming mem_to_name 
  for mem_to_name:: "'ty \<Rightarrow> String.literal" +
  fixes S::   "'ty set"
  assumes a: "inj_on mem_to_name S"
begin
lemma b:
  "n \<in> S \<Longrightarrow> m \<in> S \<Longrightarrow> n \<noteq> m \<Longrightarrow> mem_to_name n \<noteq> mem_to_name m"
  "n \<in> S \<Longrightarrow> m \<in> S \<Longrightarrow> mem_to_name n = mem_to_name m \<Longrightarrow> n = m"
  using a unfolding inj_on_def by blast+ 

lemmas names_unique = a b
end

locale tp_nta_reduction_model_checking = tp_nta_reduction_spec
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name +
  action_names: unique_names act_to_name "set actions" +
  prop_names: unique_names prop_to_name "set props"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
begin

lemma variables_unique: 
    "acts_active \<noteq> planning_lock"
    "acts_active \<noteq> prop_to_lock p"
    "acts_active \<noteq> prop_to_var p"
    "planning_lock \<noteq> prop_to_lock p"
    "planning_lock \<noteq> prop_to_var p"
    "prop_to_lock p \<noteq> prop_to_var q"
    "p \<in> set props \<Longrightarrow> q \<in> set props \<Longrightarrow> p \<noteq> q \<Longrightarrow> prop_to_var p \<noteq> prop_to_var q"
    "p \<in> set props \<Longrightarrow> q \<in> set props \<Longrightarrow> prop_to_var p = prop_to_var q \<Longrightarrow> p = q"
    "p \<in> set props \<Longrightarrow> q \<in> set props \<Longrightarrow> p \<noteq> q \<Longrightarrow> prop_to_lock p \<noteq> prop_to_lock q"
    "p \<in> set props \<Longrightarrow> q \<in> set props \<Longrightarrow> prop_to_lock p = prop_to_lock q \<Longrightarrow> p = q"
  unfolding prop_to_var_def prop_to_lock_def acts_active_def planning_lock_def
  by ((rule notI)?, (subst (asm) String.add_literal_code String.Literal_eq_iff)+, (use prop_names.names_unique in blast))+

lemma variables_inj: 
  "inj_on prop_to_var (set props)"
  "inj_on prop_to_lock (set props)" 
  using variables_unique unfolding inj_on_def by blast+

lemma clocks_unique:
    "urge_clock \<noteq> act_to_start_clock a"
    "urge_clock \<noteq> act_to_end_clock a"
    "act_to_start_clock a \<noteq> act_to_end_clock b"
    "a \<in> set actions \<Longrightarrow> b \<in> set actions \<Longrightarrow> a \<noteq> b \<Longrightarrow> act_to_start_clock a \<noteq> act_to_start_clock b"
    "a \<in> set actions \<Longrightarrow> b \<in> set actions \<Longrightarrow> act_to_start_clock a = act_to_start_clock b \<Longrightarrow> a = b"
    "a \<in> set actions \<Longrightarrow> b \<in> set actions \<Longrightarrow> a \<noteq> b \<Longrightarrow> act_to_end_clock a \<noteq> act_to_end_clock b"
    "a \<in> set actions \<Longrightarrow> b \<in> set actions \<Longrightarrow> act_to_end_clock a = act_to_end_clock b \<Longrightarrow> a = b"
  unfolding urge_clock_def act_to_start_clock_def act_to_end_clock_def
  by ((rule notI)?, (subst (asm) String.add_literal_code String.Literal_eq_iff)+, (use action_names.names_unique in blast))+

lemma clock_cons_unique:
  "act_to_start_clock \<noteq> act_to_end_clock" unfolding act_to_start_clock_def act_to_end_clock_def 
  apply (rule notI)
  by (simp add: String.add_literal_code fun_eq_iff)
  
lemma clocks_inj:
  "inj_on act_to_start_clock (set actions)"
  "inj_on act_to_end_clock (set actions)"
  using clocks_unique unfolding inj_on_def by blast+


thm Simple_Network_Rename_Formula.models_iff[no_vars, unfolded Simple_Network_Rename_Start.a\<^sub>0_def]
term "Simple_Network_Language_Model_Checking.N broadcast_spec automata_spec bounds_spec,Simple_Network_Rename_Start.a\<^sub>0 init_vars_spec init_locs_spec \<Turnstile> formula_spec"

definition "a\<^sub>0 = (init_locs_spec, map_of init_vars_spec, \<lambda>_. 0)"

(* definition "net_sem = Simple_Network_Impl.sem automata_spec broadcast_spec bounds_spec" *)
text \<open>Locales for theory\<close>
sublocale net_impl: Simple_Network_Impl automata_spec broadcast_spec bounds_spec .
sublocale graph_impl: Graph_Defs "\<lambda>(L, s, u) (L', s', u'). step_u' net_impl.sem L s u L' s' u'" .

find_theorems name: "network_impl123.sem_def"
find_theorems name: "network_impl123."

find_theorems name: "Simple_Network_Impl*ax"

end

find_theorems name: "Simple_Network_Impl"

locale tp_nta_reduction_model_checking' = tp_nta_reduction_spec' 
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name +
  action_names: unique_names act_to_name "set actions" +
  prop_names: unique_names prop_to_name "set props"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
begin
(* Plans are equivalent for both locales, but the other one has a few things that make 
  proofs easier. I.e. labelled actions as opposed to snap actions *)
sublocale ref_model_checking: tp_nta_reduction_model_checking 
  "rat_impl.list_inter props init" 
  "rat_impl.list_inter props goal"
  AtStart AtEnd rat_impl.over_all_restr_list lower upper 
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  \<epsilon> props actions act_to_name prop_to_name 
  by unfold_locales 

term "Simple_Network_Language_Model_Checking.N broadcast_spec automata_spec bounds_spec,(init_locs_spec, map_of init_vars_spec, \<lambda>_. 0) \<Turnstile> formula_spec"

end


text \<open>Now we add the assumption that a plan exists.\<close>

text \<open>This locale is not meant to directly be instantiated.\<close>
locale tp_nta_reduction_correctness = temp_plan_for_problem_list_impl_int 
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi> +
  action_names: unique_names act_to_name "set actions" +
  prop_names: unique_names prop_to_name "set props"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list" 
    and \<pi>:: "('i, 'action, int) temp_plan"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
begin
sublocale tp_nta_reduction_model_checking 
  by unfold_locales
end

(* Demo: Useful for final proof *)
lemma assumes "tp_nta_reduction_model_checking init goal at_start at_end over_all pre adds dels \<epsilon> props actions act_to_name prop_to_name"
  and "temp_plan_for_problem_list_impl_int at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>"
shows "tp_nta_reduction_correctness init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name"
  unfolding tp_nta_reduction_correctness_def 
  using assms unfolding tp_nta_reduction_model_checking_def 
  by auto

text \<open>This is the locale we instantiate, if we instantiate one\<close>
locale tp_nta_reduction_correctness' = temp_plan_for_problem_list_impl_int'
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi> +
  action_names: unique_names act_to_name "set actions" +
  prop_names: unique_names prop_to_name "set props"
    for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list" 
    and \<pi>:: "('i, 'action, int) temp_plan"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
begin
sublocale tp_nta_reduction_model_checking' 
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
  by unfold_locales 
   
find_consts name: "local*list*inte"             
sublocale ref_correctness: tp_nta_reduction_correctness
  "rat_impl.list_inter props init" 
  "rat_impl.list_inter props goal"
  AtStart AtEnd rat_impl.over_all_restr_list lower upper 
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  \<epsilon> props actions \<pi> act_to_name prop_to_name 
  by unfold_locales 
end

(* Demo: Prove that the locale assumptions for the model checking locale hold and assume a valid plan exists.
Show that something can be proven in the locale. *)


(* 
locale tp_nta_reduction_rename = tp_nta_reduction_spec +
  assumes infinite_actions: "infinite (UNIV::'action set)"
      and infinite_propositions: "infinite (UNIV::'proposition set)"
      and act_names_unique: "inj_on act_to_name (set actions)"
      and prop_names_unique: "inj_on prop_to_name (set props)"
      and renaming_ok: "Simple_Network_Rename_Formula_String
            broadcast_spec
            bounds_spec
            renum_acts renum_vars renum_clocks renum_states
            automata_spec
            urge_spec 
            formula_spec
            init_vars_spec
            init_locs_spec"
begin
sublocale x: Simple_Network_Rename_Formula_String 
            broadcast_spec
            bounds_spec
            renum_acts renum_vars renum_clocks renum_states
            automata_spec
            urge_spec 
            formula_spec
            init_vars_spec
            init_locs_spec
  using renaming_ok .

definition "x \<equiv> 1"
find_theorems name: "urge_bisim"
find_theorems name: models_iff'
thm Simple_Network_Language_Renaming.Simple_Network_Rename_Formula.models_iff'[no_vars]
end
find_theorems name: "urge_bisim"
find_theorems name: "test_123" *)

end
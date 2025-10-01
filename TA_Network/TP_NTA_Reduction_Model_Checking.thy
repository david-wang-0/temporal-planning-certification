theory TP_NTA_Reduction_Model_Checking
  imports TP_NTA_Reduction_Spec
begin

locale tp_nta_reduction_model_checking = tp_nta_reduction_spec +
  assumes infinite_actions: "infinite (UNIV::'action set)"
      and infinite_propositions: "infinite (UNIV::'proposition set)"
      and act_names_unique: "inj_on act_to_name (set actions)"
      and prop_names_unique: "inj_on prop_to_name (set props)"
begin
term "Simple_Network_Language_Model_Checking.N broadcast_spec automata_spec bounds_spec,(init_locs_spec, map_of init_vars_spec, \<lambda>_. 0) \<Turnstile> formula_spec"
find_consts name: Simple_Network_Language_Model_Checking_def
end
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
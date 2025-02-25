theory TP_NTA_Printing
  imports TP_NTA_Reduction "TA_Planning.Simple_Network_Language_Printing"
begin


definition tp_net_to_JSON::"
  (String.literal \<Rightarrow> nat option) \<times>
  (nat \<Rightarrow> String.literal option) \<times>
  (String.literal \<times>
    (String.literal \<Rightarrow> nat option) \<times>
    (nat \<Rightarrow> String.literal option) \<times>
    nat \<times>
    nat list \<times>
    nat list \<times>
    nat list \<times>
    (nat \<times>
      (String.literal, int) bexp \<times>
      (String.literal, int) acconstraint list \<times>
      String.literal act \<times> 
      (String.literal \<times> (String.literal, int) exp) list \<times> 
      String.literal list \<times> 
      nat) list \<times>
    (nat \<times> (String.literal, int) acconstraint list) list
  ) list \<times>
  String.literal list \<times> 
  (String.literal \<times> int \<times> int) list \<times> 
  (nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula
\<Rightarrow> _" where
"tp_net_to_JSON net \<equiv>
let 
  (act_name_nums, act_num_names, automata, clocks, vars, formula) = net;
  automata = zip (map fst automata) (map (snd o snd) automata)
in 
  net_to_JSON act_num_names (automata, clocks, vars, formula)"


definition [code]: "parse_tp_to_JSON d p \<equiv> do {
  (preds, acts, init, goal) \<leftarrow> parse_dom_and_prob d p;
  autos \<leftarrow> tp_to_ta_net (preds, acts, init, goal);
  tp_net_to_JSON autos
}"

definition [code]: "parse_tp_to_opt_JSON d p \<equiv> (
  case parse_tp_to_JSON d p of 
  Error es \<Rightarrow> do {let _ = show es |> String.implode |> println; None}
| Result res \<Rightarrow> do {res |> show |> String.implode |> Some}
)"

definition [code]: "parse_tp_to_JSON_string d p \<equiv> 
(case (parse_tp_to_JSON d p) of
  Error es \<Rightarrow> show es
| Result res \<Rightarrow> show res) |> String.implode"

(* 
code_printing
  constant upto \<rightharpoonup> (SML) "_ upto _" *)

code_printing
  constant println \<rightharpoonup> (SML) "writeln _"
       and          (OCaml) "print'_string _"

export_code parse_tp_to_opt_JSON Result Error String.explode int_of_integer nat_of_integer
  JSON.Object JSON.Array JSON.String JSON.Int JSON.Nat JSON.Rat JSON.Boolean JSON.Null fract.Rat
  shows_json
in SML module_name TP_NTA_Printing file "../ML/TP_NTA_Printing.sml"


ML \<open>
  fun parse_and_print df pf out_f =
  let 
    val p = file_to_string pf; 
    val d = file_to_string df
    val s = @{code parse_tp_to_JSON_string} d p
  in
    string_to_file s out_f
  end
\<close>

(*
ML_val \<open>
  parse_and_print
  "work/temporal_planning_certification/temporal-planning-certification/examples/blocks-world/ground-blocks.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/blocks-world/ground-blocks-prob-1.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/out/blocks-world-1.muntax"
\<close>

ML_val \<open>
  parse_and_print
  "work/temporal_planning_certification/temporal-planning-certification/examples/elevators-new/ground-elevators.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/elevators-new/ground-elevators-prob1.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/out/elevators-1.muntax"
\<close>


ML_val \<open>
  parse_and_print
  "work/temporal_planning_certification/temporal-planning-certification/examples/blocks-world/ground-blocks-2.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/blocks-world/ground-blocks-prob-2.pddl"
  "work/temporal_planning_certification/temporal-planning-certification/examples/out/blocks-world-2.muntax"
\<close>
 *)

end
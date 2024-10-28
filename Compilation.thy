theory Compilation
  imports Prop_Plans Diagonal_Timed_Automata
begin

datatype state =
  Init 
  | Goal
  | Main
  | StateDecoding nat 
  | Decision nat
  | Execution nat


datatype ('action) clock =
  Delta
  | PropClock nat
  | Start 'action
  | End 'action
  | ExecStart 'action
  | ExecEnd 'action
  | Running 'action
  | Stop

datatype alpha = Unit


instantiation prod ::  (linorder, linorder) linorder begin
definition less_eq_prod::"'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod x y \<equiv>
    (let (a, b) = x;
        (c, d) = y
    in (a < c) \<or> (a = c \<and> b \<le> d))"
lemma "less_eq_prod \<equiv> less_eq"
  
end

find_theorems name: linorder
context temp_planning_problem
begin


text \<open>Preventing time from passing in any location other than the main location.\<close>
fun invs::"('action clock, 't, state) invassn" where
  "invs Main  = GE Stop 0"
| "invs _     = EQ Stop 0"

definition init_asmt::"('action clock, 't) clkassn list" where
"init_asmt \<equiv> sorted_list_of_set {(PropClock n, 0) | n. True}"

definition initial_transition::"(alpha, 'action clock, 't, state) transition" where
"initial_transition \<equiv> Init \<times> GE Stop 0 \<times> Unit \<times> "
end

end
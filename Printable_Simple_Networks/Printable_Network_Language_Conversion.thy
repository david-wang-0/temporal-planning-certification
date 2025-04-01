theory Printable_Network_Language_Conversion
  imports Printable_Network_Expression_Conversion
    Simple_Networks.Simple_Network_Language
begin

(* To do: Redefine the semantics for the printable version *)
type_synonym
  ('a, 'b) printable_upd = "('a * ('a, 'b) Printable_Simple_Expressions.exp) list"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) printable_transition =
  "'s \<times> ('x, 'v) Printable_Simple_Expressions.bexp \<times> ('c, 't) cconstraint \<times> 'a \<times> ('x, 'v) printable_upd \<times> 'c list \<times> 's"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) printable_sta =
  "'s set \<times> 's set \<times> ('a, 's, 'c, 't, 'x, 'v) printable_transition set \<times> ('c, 't, 's) invassn"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) printable_nta = "'a set \<times> ('a act, 's, 'c, 't, 'x, 'v) printable_sta list \<times> ('x \<rightharpoonup> 'v * 'v)"

abbreviation to_simple_update::"'a * ('a, 'b::linordered_ring) Printable_Simple_Expressions.exp 
  \<Rightarrow> 'a * ('a, 'b::linordered_ring) Simple_Expressions.exp" where
"to_simple_update \<equiv> map_prod id to_simple_exp"

abbreviation to_simple_updates::"('a, 'b::linordered_ring) printable_upd \<Rightarrow> ('a, 'b) upd" where
"to_simple_updates \<equiv> map to_simple_update"

fun to_simple_transition::"('a, 's, 'c, 't, 'x, 'v::linordered_ring) printable_transition 
  \<Rightarrow> ('a, 's, 'c, 't, 'x, 'v) transition" where
"to_simple_transition (s, g, c, a, u, r, t) = (s, to_simple_bexp g, c, a, to_simple_updates u, r, t)"

fun to_simple_sta::"('a, 's, 'c, 't, 'x, 'v::linordered_ring) printable_sta \<Rightarrow> ('a, 's, 'c, 't, 'x, 'v) sta" where
"to_simple_sta (c, u, t, invs) = (c, u, to_simple_transition ` t, invs)"

fun to_simple_network::"('a, 's, 'c, 't, 'x, 'v::linordered_ring) printable_nta \<Rightarrow> ('a, 's, 'c, 't, 'x, 'v) nta" where
"to_simple_network (broadcast, automata, bounds) = (broadcast, map to_simple_sta automata, bounds)"


end
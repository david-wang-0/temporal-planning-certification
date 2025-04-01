theory Printable_Simple_Expressions
imports
    Main
begin
text \<open>Simple expressions are equipped with addition and multiplication for printing. This works for
integers\<close>

datatype ('a, 'b) bexp =
  true |
  not "('a, 'b) bexp" |
  "and" "('a, 'b) bexp" "('a, 'b) bexp" |
  or "('a, 'b) bexp" "('a, 'b) bexp" |
  imply "('a, 'b) bexp" "('a, 'b) bexp" | \<comment> \<open>Boolean connectives\<close>
  eq "('a, 'b) exp" "('a, 'b) exp" |
  le "('a, 'b) exp" "('a, 'b) exp" |
  lt "('a, 'b) exp" "('a, 'b) exp" |
  ge "('a, 'b) exp" "('a, 'b) exp" |
  gt "('a, 'b) exp" "('a, 'b) exp"
and ('a, 'b) exp =
  const 'b | var 'a | if_then_else "('a, 'b) bexp" "('a, 'b) exp" "('a, 'b) exp" |
  add "('a, 'b) exp" "('a, 'b) exp" | mult "('a, 'b) exp" "('a, 'b) exp" 
(*| 
  neg "('a, 'b) exp" *)
(* There is a unary operator in the original abstract syntax. 
    I do not know where it is used. *)

typ int
find_consts name: "linordered_ring"
find_theorems name: "Int*lino"
find_theorems name: "linordered*_ring_class"

(* the linordered_ring is currently sufficient for multiplication and addition *)
inductive check_printable_bexp::"('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b :: linordered_ring) bexp \<Rightarrow> bool \<Rightarrow> bool" 
and is_val_printable where
  "check_printable_bexp s true True" |
  "check_printable_bexp s (not e) (\<not> b)" if "check_printable_bexp s e b" |
  "check_printable_bexp s (and e1 e2) (a \<and> b)" if "check_printable_bexp s e1 a" "check_printable_bexp s e2 b" |
  "check_printable_bexp s (or e1 e2) (a \<or> b)" if "check_printable_bexp s e1 a" "check_printable_bexp s e2 b" |
  "check_printable_bexp s (imply e1 e2) (a \<longrightarrow> b)" if "check_printable_bexp s e1 a" "check_printable_bexp s e2 b" |
  "check_printable_bexp s (eq a b) (x = v)" if "is_val_printable s a v" "is_val_printable s b x" |
  "check_printable_bexp s (le a b) (v \<le> x)" if "is_val_printable s a v" "is_val_printable s b x" |
  "check_printable_bexp s (lt a b) (v < x)" if "is_val_printable s a v" "is_val_printable s b x" |
  "check_printable_bexp s (ge a b) (v \<ge> x)" if "is_val_printable s a v" "is_val_printable s b x" |
  "check_printable_bexp s (gt a b) (v > x)" if "is_val_printable s a v" "is_val_printable s b x" |
  "is_val_printable s (const c) c" |
  "is_val_printable s (var x)   v" if "s x = Some v" |
  "is_val_printable s (if_then_else b e1 e2) (if bv then v1 else v2)"
  if "is_val_printable s e1 v1" "is_val_printable s e2 v2" "check_printable_bexp s b bv" |
  "is_val_printable s (add e1 e2) (v1 + v2)" if "is_val_printable s e1 v1" "is_val_printable s e2 v2" |
  "is_val_printable s (mult e1 e2) (v1 * v2)" if "is_val_printable s e1 v1" "is_val_printable s e2 v2" 


(* Simple Network Language expressions use functions in the arguments. 
I cannot think of a way to check whether the binary operator that is
used to construct a bexp is (+), for instance. *)
(* fun showsp_exp::"(('a::show), ('b::show)) exp \<Rightarrow> string \<Rightarrow> string" and
  showsp_bexp::"('a, 'b::show) bexp \<Rightarrow> string \<Rightarrow> string" where
"showsp_exp (exp.mult a b) = shows ''('' o showsp_exp a o shows '') * ('' o showsp_exp b o shows '')''" |
"showsp_exp (exp.add a b) = shows ''('' o showsp_exp a o shows '') + ('' o showsp_exp b o shows '')''" |
"showsp_exp (exp.if_then_else b x y) = shows ''('' o showsp_bexp b o shows '') ? ('' o showsp_exp x o shows '') : ('' o showsp_exp y o shows '')''" |
"showsp_exp (exp.const c) = shows c" |
"showsp_exp (exp.var v) = shows v" |
"showsp_bexp bexp.true = shows ''True''" |
"showsp_bexp (bexp.not b) = shows ''~('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.and a b) = shows ''('' o showsp_bexp a o shows '') && ('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.or a b) = shows ''('' o showsp_bexp a o shows '') || ('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.imply a b) = shows ''('' o showsp_bexp a o shows '') -> ('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.eq x y) = shows ''('' o showsp_exp x o shows '') = ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.le x y) = shows ''('' o showsp_exp x o shows '') <= ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.lt x y) = shows ''('' o showsp_exp x o shows '') < ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.ge x y) = shows ''('' o showsp_exp x o shows '') >= ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.gt x y) = shows ''('' o showsp_exp x o shows '') > ('' o showsp_exp y o shows '')''" *)

(* Why does show return a function? *)

end
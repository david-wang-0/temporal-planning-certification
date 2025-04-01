theory Printable_Network_Expression_Conversion
  imports Printable_Simple_Expressions Simple_Networks.Simple_Expressions
begin
type_synonym ('a, 'b) pexp =  "('a, 'b) Printable_Simple_Expressions.exp"
type_synonym ('a, 'b) pbexp = "('a, 'b) Printable_Simple_Expressions.bexp"

fun to_simple_bexp::"('a, 'b::linordered_ring) pbexp \<Rightarrow> ('a, 'b) Simple_Expressions.bexp"
  and to_simple_exp::"('a, 'b) pexp \<Rightarrow> ('a, 'b) Simple_Expressions.exp" where
"to_simple_bexp (Printable_Simple_Expressions.bexp.true) = true" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.not b) = not (to_simple_bexp b)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.and b c) = and (to_simple_bexp b) (to_simple_bexp c)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.imply b c) = imply (to_simple_bexp b) (to_simple_bexp c)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.or b c) = or (to_simple_bexp b) (to_simple_bexp c)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.eq x y) = eq (to_simple_exp x) (to_simple_exp y)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.le x y) = le (to_simple_exp x) (to_simple_exp y)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.lt x y) = lt (to_simple_exp x) (to_simple_exp y)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.ge x y) = ge (to_simple_exp x) (to_simple_exp y)" |
"to_simple_bexp (Printable_Simple_Expressions.bexp.gt x y) = gt (to_simple_exp x) (to_simple_exp y)" |
"to_simple_exp (Printable_Simple_Expressions.exp.const c) = const c" |
"to_simple_exp (Printable_Simple_Expressions.exp.var v) = var v" |
"to_simple_exp (Printable_Simple_Expressions.exp.if_then_else b x y) = if_then_else (to_simple_bexp b) (to_simple_exp x) (to_simple_exp y)" |
"to_simple_exp (Printable_Simple_Expressions.exp.add x y) = binop (+) (to_simple_exp x) (to_simple_exp y)" |
"to_simple_exp (Printable_Simple_Expressions.exp.mult x y) = binop (*) (to_simple_exp x) (to_simple_exp y)"

inductive_cases check_printable_bexp_elims:
  "check_printable_bexp s Printable_Simple_Expressions.bexp.true bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.not b) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.and b1 b2) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.or b1 b2) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.imply b1 b2) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.le i x) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.lt i x) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.ge i x) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.eq i x) bv"
  "check_printable_bexp s (Printable_Simple_Expressions.bexp.gt i x) bv"

inductive_cases is_val_printable_elims:
  "is_val_printable s (Printable_Simple_Expressions.exp.const c) d"
  "is_val_printable s (Printable_Simple_Expressions.exp.var v) x"
  "is_val_printable s (Printable_Simple_Expressions.exp.if_then_else b x y) v"
  "is_val_printable s (Printable_Simple_Expressions.exp.add x y) v"
  "is_val_printable s (Printable_Simple_Expressions.exp.mult x y) v"

find_theorems name: "check_printable_bexp_is_val_printable.induct"

lemma exp_conv_complete: "(check_printable_bexp s b v \<longrightarrow> check_bexp s (to_simple_bexp b) v) 
  \<and> (is_val_printable s e w \<longrightarrow> is_val s (to_simple_exp e) w)"
  apply (induction rule: check_printable_bexp_is_val_printable.induct)
  prefer 13
  subgoal by (subst to_simple_exp.simps; rule check_bexp_is_val.intros)
  by (auto intro: check_bexp_is_val.intros)

find_theorems name: "Simple_Expressions.check_bexp*indu"

find_theorems name: "to_simple_bexp*el"


lemma exp_conv_sound: "(check_bexp s b' v \<longrightarrow> (\<forall>b. to_simple_bexp b = b'  \<longrightarrow> check_printable_bexp s b v))
  \<and> (is_val s e' w \<longrightarrow> (\<forall>e. to_simple_exp e = e' \<longrightarrow> is_val_printable s e w))"
  apply (induction rule: check_bexp_is_val.induct)
  subgoal for s
    apply (rule allI)
    subgoal for b
      apply (cases b)
      by (auto intro: check_printable_bexp_is_val_printable.intros)
    done
  subgoal for s b v
    apply (rule allI)
    subgoal for b'
      apply (rule impI)
      apply (cases rule: to_simple_bexp.elims, assumption)
      by (auto intro: check_printable_bexp_is_val_printable.intros)
    done
              apply (intro allI impI, cases rule: to_simple_bexp.elims, assumption, 
          (auto intro: check_printable_bexp_is_val_printable.intros)[10])+ (* Same as above subgoal *)
  subgoal by (intro allI impI, cases rule: to_simple_exp.elims, assumption, 
      (auto intro: check_printable_bexp_is_val_printable.intros)[5]) (* expressions *)
  subgoal by (intro allI impI, cases rule: to_simple_exp.elims, assumption, 
      (auto intro: check_printable_bexp_is_val_printable.intros)[5]) 
  subgoal for s x xv y yv b bv
    apply (intro allI impI)
    subgoal for e
      apply (cases rule: to_simple_exp.elims, assumption)
          apply auto[2]
      subgoal for b' x' v'
        apply (erule ssubst[of e])
        apply (rule check_printable_bexp_is_val_printable.intros)
        by auto
      by auto
    done
   by (intro allI impI, cases rule: to_simple_exp.elims, assumption, 
      (auto intro: check_printable_bexp_is_val_printable.intros)[5])+

lemma exp_conv_corr: "check_printable_bexp s b v = check_bexp s (to_simple_bexp b) v"
  using exp_conv_sound exp_conv_complete by blast

end
theory Base                
  imports Main "Containers.Containers"
begin

section \<open>Utility Functions and Lemmas\<close>

abbreviation (input) comb (infixl "#>" 59) where "a #> b \<equiv> (\<lambda>x. b (a x))"


lemma list_all2_twist: "list_all2 P xs ys \<longleftrightarrow> list_all2 (\<lambda>y x. P x y) ys xs" for xs ys P
  apply (subst list_all2_iff)+
  apply (rule iffI; rule conjI; simp)
   apply (drule conjunct2)
   apply (rule ballI)
    subgoal for x
      apply (induction x)
      subgoal for a b
        apply (drule bspec[where x = "(b, a)"])
        apply (subst in_set_zip)
         apply (subst (asm) in_set_zip)
         apply auto
        done
      done
    apply (drule conjunct2)
    apply (rule ballI)
    subgoal for x
      apply (induction x)
      subgoal for a b
        apply (drule bspec[where x = "(b, a)"])
        apply (subst in_set_zip)
         apply (subst (asm) in_set_zip)
         apply auto
        done
      done
    done

lemma distinct_inj_on_map: "distinct xs \<Longrightarrow> inj_on f (set xs) \<Longrightarrow> distinct (map f xs)"
  apply (induction xs)
  unfolding inj_on_def 
  by auto
                            
lemma distinct_inj_map: "distinct xs \<Longrightarrow> inj f \<Longrightarrow> distinct (map f xs)"
  apply (induction xs)
  unfolding inj_def
  by auto


fun sequence_list_opt::"'a option list \<Rightarrow> 'a list option" where
"sequence_list_opt [] = Some []" |
"sequence_list_opt (x#xs) = 
  do {
    x \<leftarrow> x;
    xs \<leftarrow> sequence_list_opt xs;
    Some (x # xs)
  }"

fun list_opt_unwrap::"'a list option \<Rightarrow> 'a list" where
"list_opt_unwrap None = []" |
"list_opt_unwrap (Some xs) = xs"

fun is_some::"'a option \<Rightarrow> bool" where
"is_some (Some x) = True" |
"is_some None = False"

abbreviation "option_list_to_list \<equiv> list_opt_unwrap o sequence_list_opt o (filter is_some)"


fun list_min_opt'::"('a::linorder) list \<Rightarrow> 'a \<Rightarrow> 'a" where
"list_min_opt' [] y = y" |
"list_min_opt' (x#xs) y = (if (x < y) then list_min_opt' xs x else list_min_opt' xs y)"

fun list_min_opt::"('a::linorder) list \<Rightarrow> 'a option" where
"list_min_opt [] = None" |
"list_min_opt (x#xs) = Some (list_min_opt' xs x)"

fun list_max_opt'::"('a::linorder) list \<Rightarrow> 'a \<Rightarrow> 'a" where
"list_max_opt' [] y = y" |
"list_max_opt' (x#xs) y = (if (x > y) then list_max_opt' xs x else list_max_opt' xs y)"

fun list_max_opt::"('a::linorder) list \<Rightarrow> 'a option" where
"list_max_opt [] = None" |
"list_max_opt (x#xs) = Some (list_max_opt' xs x)"

                                       
fun fun_upd_lists::"('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> 'b)" where
"fun_upd_lists f [] ys = f" |
"fun_upd_lists f (x # xs) (y # ys) = fun_upd_lists (f(x := y)) xs ys" |
"fun_upd_lists f _ _ = f"



definition "is_integer q \<equiv> \<exists>a b. q = Fract a b \<and> 0 < b \<and> coprime a b \<and> b = 1"

definition "is_integer_code (q::rat) \<equiv> snd (quotient_of q) = 1"

lemma is_integer_code[code]: "is_integer q = is_integer_code q"
  apply (rule iffI)
  unfolding is_integer_def is_integer_code_def 
  subgoal apply (elim exE conjE)
    subgoal for a b
      apply (erule ssubst)
      apply (subst quotient_of_Fract)
      by simp
    done
  subgoal 
    apply (rule Rat_cases[of q])
    subgoal for a b
      apply simp
      apply (cases "Rat.normalize (a, b)")
      subgoal for a' b'
    apply (subst (asm) quotient_of_Fract)
    apply (rule exI)
        apply (subst Rat.normalize_eq[symmetric])
         apply assumption
        by simp
      done
    done
  done


lemma is_integer_add:
  assumes "is_integer q"
      and "is_integer r"
    shows "is_integer (q + r)"
proof -
  obtain a b where
    "q = Fract a 1"
    "r = Fract b 1" using assms is_integer_def by auto
  hence "q + r = Fract (a + b) 1" by auto
  thus ?thesis using is_integer_def by auto
qed

lemma is_integer_of_int:
  assumes "is_integer q"
  shows "rat_of_int (floor q) = q"
proof -
  obtain a b where
    q: "q = Fract a b"
    "b = 1" using assms is_integer_def by auto
  have "rat_of_int a = q" using q Fract_of_int_eq by auto
  moreover
  have "floor q = a" using q by simp
  moreover
  have "floor (rat_of_int a) = a" by simp
  ultimately
  show ?thesis by simp
qed


lemma is_integer_floor_less: 
  assumes "x < y"
      and "is_integer x"
      and "is_integer y"
    shows "floor x < floor y"
  using assms
  apply -
  apply (subst (asm) is_integer_of_int[symmetric, of x], simp)
  apply (subst (asm) is_integer_of_int[symmetric, of y], simp)
  apply (subst (asm) of_int_less_iff)
  by (assumption)

(* lemma is_integer_floor_le: 
  assumes "x \<le> y"
      and "is_integer x"
      and "is_integer y"
    shows "floor x \<le> floor y"
  using assms is_integer_floor_less by linarith *)

thm Archimedean_Field.floor_mono

lemma is_integer_floor_ne:
  assumes "x \<noteq> y"
      and "is_integer x"
      and "is_integer y"
    shows "floor x \<noteq> floor y"
  using assms is_integer_floor_less 
  by (force elim: neqE)

end

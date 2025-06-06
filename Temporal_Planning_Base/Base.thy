theory Base                
  imports Main Containers.Containers
begin

section \<open>Time\<close>
(* 
class time = linordered_ab_group_add + zero_less_one +
  assumes dense: "x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
  assumes non_trivial: "\<exists> x. x \<noteq> 0"
begin

lemma non_trivial_neg: "\<exists> x. x < 0"
proof -
  from non_trivial obtain x where "x \<noteq> 0" by auto
  then show ?thesis
  proof (cases "x < 0", auto, goal_cases)
    case 1
    then have "x > 0" by auto
    then have "(-x) < 0" by auto
    then show ?case by blast
  qed
qed

lemma GreatestI_time:
  assumes "P k" and minor: "\<And>y. P y \<Longrightarrow> y \<le> k"
  shows "P (Greatest P)"
  using assms GreatestI2_order by blast

end *)

section \<open>Utility Functions and Lemmas\<close>

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


fun list_of'::"'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_of' x 0 xs = xs" |
"list_of' x (Suc n) xs = list_of' x n (x#xs)"

definition "list_of x n = list_of' x n []"

lemma length_list_of': "length (list_of' x n xs) = n + length xs"
  apply (induction n arbitrary: xs)
  by auto

lemma length_list_of: "length (list_of x n) = n"
  unfolding list_of_def length_list_of' by auto

lemma set_list_of': "0 < n \<Longrightarrow> set (list_of' x n xs) = insert x (set xs)"
  apply (induction n arbitrary: x xs)
   apply blast
  subgoal for n x xs
    by fastforce
  done

lemma set_list_of: 
  "0 < n \<Longrightarrow> set (list_of x n) = {x}"
  "set (list_of x 0) = {}"
  unfolding list_of_def set_list_of' by auto

lemma nth_list_of: 
  assumes "n < m"
  shows "list_of x m ! n = x"
proof -
  find_theorems name: "set*nth"
  from assms
  have "0 < m" by simp
  hence "set (list_of x m) = {x}" using set_list_of by simp
  hence "\<forall>y \<in> set (list_of x m). y = x" by blast
  with all_set_conv_all_nth
  have "\<forall>i<length (list_of x m). (list_of x m ! i) = x" 
    by simp
  with assms 
  show ?thesis unfolding length_list_of by simp 
qed

lemma list_of'_append: "(list_of' x n xs) @ ys = list_of' x n (xs @ ys)"
  apply (induction n arbitrary: xs ys)
   apply simp
  subgoal for n xs ys
    by simp
  done

find_theorems "Suc ?x + ?y"

lemma list_of'_Suc': "list_of' x (Suc n) [] = (list_of' x n []) @ [x]"
    apply (subst list_of'.simps)
    apply (subst (2) append_Nil[symmetric])
    apply (subst list_of'_append)
  by (rule HOL.refl)

lemma list_of'_1: "list_of' x 1 [] = [x]"
  by simp

lemma list_of'_append_same: "list_of' x n [] @ list_of' x m [] = list_of' x (n + m) []"
proof (induction m arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case 
    apply (subst add_Suc_shift[symmetric])
    apply (subst add_Suc)
    apply (subst list_of'_Suc')
    apply (subst list_of'_Suc')
    apply (subst Suc.IH[symmetric])
    by simp
qed

lemma list_of_Suc: "list_of x (Suc n) = x # list_of x n"
proof -
  have "list_of' x (Suc n) [] = list_of' x 1 [] @ list_of' x n []"
    apply (subst list_of'_append_same)
    by simp
  thus ?thesis unfolding list_of_def list_of'_1
    by simp
qed

text \<open>Obtaining a unique name by appending underscores\<close>

fun matches_start::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"matches_start [] ys = True" |
"matches_start xs [] = False" |
"matches_start (x#xs) (y#ys) = (if (x \<noteq> y) then False else matches_start xs ys)"

function unique_name::"string \<Rightarrow> string list \<Rightarrow> string" where
"unique_name s [] = s" |
"unique_name s (x#xs) = (if (matches_start s x) then unique_name (s@''_'') (x#xs) else unique_name s xs)"
  apply pat_completeness 
  by auto
termination sorry
 

value "unique_name ''main'' [''main_'', ''main__'', ''abc'', ''_main_'', ''__main'']"

fun get_or_default::"'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
"get_or_default None d = d" |
"get_or_default (Some x) _ = x"




end

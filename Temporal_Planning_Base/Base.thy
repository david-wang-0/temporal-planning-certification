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

function upto_aux_nat::"nat \<Rightarrow> nat \<Rightarrow> nat list" where
"upto_aux_nat m n = (if (m < n) then m#upto_aux_nat (m+1) n else [])"
  by auto
termination by (relation "measure (\<lambda>(x, y). y - x)") auto

definition "upto_nat \<equiv> upto_aux_nat 0"

(* 
value "KMP_search (array_of_list ''be'') (array_of_list ''ababcababdababe'')"
value "length ''ababcababdababe''" *)
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

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


(* needs a different name *)
(* Turns a list into a list of functions, by applying a function with two arguments to each member. 
  Then applies the list of functions sequentially beginning at some starting element and creates 
  another list this way. This sounds like an imperative program, because it is used to simulate 
  the execution of an imperative program (a PDDL plan). It could be implemented as a monad.*)
fun fold_map::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b list" where
"fold_map f [] y = []" |
"fold_map f (Cons x xs) y = Cons (f x y) (fold_map f xs (f x y))"

definition fold_map'::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b list" where
"fold_map' f xs y \<equiv> 
  let 
    fs = map f xs
  in foldl (\<lambda>ys f. case ys of Cons y ys \<Rightarrow> Cons (f y) (Cons y ys)) [y] fs
"

lemma tl_rev_foldl:
  assumes "ys = Cons y' ys'"
  shows "tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) (ys @ [y]) (map f xs))) 
  = rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) ys (map f xs))"
  using assms
proof (induction xs arbitrary: ys y' ys')
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) ys (map f (a # xs))) = rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) (f a y' # ys) (map f xs))"
    apply (subst list.map)
    apply (subst foldl.simps)
    apply (subst Cons(2))
    apply (subst list.case)
    apply (subst Cons(2))
    ..
  with Cons.IH[of \<open>f a y' # ys\<close>]
  have " tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) ((f a y' # ys) @ [y]) (map f xs))) = rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) (f a y' # ys) (map f xs))"
    by blast
  thus "tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) (ys @ [y]) (map f (a # xs)))) 
  = rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) ys (map f (a # xs)))" 
    apply (subst list.map)
    apply (subst list.map)
    apply (subst foldl.simps)
    apply (subst foldl.simps)
    unfolding Cons(2)
    by auto
qed

lemma hd_rev_foldl: 
  assumes "ys = Cons y' ys'"
  shows "hd (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) ys (map f xs))) = hd (rev ys)"
  using assms
proof (induction xs arbitrary: ys y' ys')
  case Nil
  then show ?case by simp

next
  case (Cons a xs)
  have 1: "hd (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) (f a y' # ys) (map f xs))) = hd (rev (f a y' # ys))"
    using Cons.IH by blast
  have 2: "hd (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) (f a y' # ys) (map f xs))) = hd (rev ys)" 
    apply (subst 1)
    apply (subst hd_rev)+
    using Cons(2) 
    by auto
  show ?case 
    apply (subst list.map)
    apply (subst foldl.simps)
    apply (subst Cons(2))
    apply (subst list.case)
    using 2 Cons(2) by simp
qed

lemma foldl_not_Nil: 
  assumes "ys = Cons y' ys'"
  shows "foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) ys (map f xs) \<noteq> []"
  using assms
  apply (induction xs arbitrary: ys y' ys')
  by auto


lemma fold_map_spec: "tl (rev (fold_map' f xs y)) = fold_map f xs y"
  unfolding fold_map'_def Let_def
proof (induction xs arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "fold_map f xs (f a y) = tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y] (map f xs)))"
    apply (subst Cons.IH[symmetric]) ..
  also 
  have "... = tl (tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y, y] (map f xs))))"
    apply (subst tl_rev_foldl[where ys = "[f a y]", simplified, symmetric])
    by auto
  finally
  have 1: "fold_map f xs (f a y) = tl (tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y, y] (map f xs))))" .
  have 2: "tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y, y] (map f xs))) = rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y] (map f xs))"
    using tl_rev_foldl[where ys = "[f a y]"] by auto
  have 3: "f a y = hd (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y] (map f xs)))" 
    using hd_rev_foldl[of "[f a y]", symmetric] by auto
  
  have 4: "rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y] (map f xs)) \<noteq> []" using foldl_not_Nil by fast
  
  have 5: "f a y # tl (rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y] (map f xs))) = rev (foldl (\<lambda>ys f. case ys of y # ys \<Rightarrow> f y # y # ys) [f a y] (map f xs))"
    apply (subst 3)
    apply (rule hd_Cons_tl)
    by (rule 4)
  show ?case
    apply (subst list.map)
    apply (subst foldl.simps)
    apply (subst list.case)
    apply (subst fold_map.simps)
    apply (subst 1)
    apply (subst 2)+
    using 5 by simp
qed

type_synonym 's state_sequence = "'s list"

fun extend_sequence::"('comm \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'comm list \<Rightarrow> 's state_sequence \<Rightarrow> 's state_sequence" where
"extend_sequence f cs [] = []" |
"extend_sequence f cs [s] = s # fold_map f cs s" |
"extend_sequence f cs (s#S) = s # extend_sequence f cs S"

lemma extend_sequence_fold_map: "z # fold_map f (xs @ ys) z = extend_sequence f ys (z # fold_map f xs z)"
proof (induction xs arbitrary: ys z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have IH': "f x z # fold_map f (xs @ ys) (f x z) = extend_sequence f ys (f x z # fold_map f xs (f x z))" using Cons.IH .
  show ?case 
    apply -
    apply (subst append_Cons)
    apply (subst fold_map.simps)
    apply (subst IH')
    apply (subst fold_map.simps)
    apply (subst extend_sequence.simps)
    by simp
qed

    

lemma extend_sequence_append: "extend_sequence f (xs @ ys) zs = extend_sequence f ys (extend_sequence f xs zs)"
proof (induction zs arbitrary: xs ys)
  case Nil
  then show ?case by auto
next
  case (Cons z zs)
  then show ?case 
  proof (cases zs)
    case Nil
    show ?thesis unfolding Nil
      apply (subst (2) extend_sequence.simps)
      apply (subst extend_sequence_fold_map[symmetric])
      apply (subst extend_sequence.simps)
      by simp
  next
    fix z' zs'
    assume zs: "zs = z' # zs'"
    show ?thesis 
      unfolding zs
      apply (subst extend_sequence.simps)
      apply (subst Cons.IH[simplified zs])
      apply (subst extend_sequence.simps)
      apply (cases zs')
      by simp+
  qed
qed

(* Things above this line are probably not used *)

fun seq_apply::"('a \<Rightarrow> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"seq_apply [] x = []" |
"seq_apply (f#fs) x = f x # (seq_apply fs (f x))"

find_theorems name: "foldl*fold"

lemma fold_map_is_seq_apply: "fold_map f ys xs = seq_apply (map f ys) xs"
  apply (induction ys arbitrary: xs)
   apply simp
  subgoal for y ys
    apply (subst fold_map.simps)
    apply (subst list.map)
    apply (subst seq_apply.simps)
    by blast
  done

fun ext_seq::"'a list \<Rightarrow> ('a \<Rightarrow> 'a) list \<Rightarrow> 'a list" where
"ext_seq xs [] = xs" |
"ext_seq [] fs = []" |
"ext_seq [x] fs = x # seq_apply fs x" |
"ext_seq (x#xs) fs = x # ext_seq xs fs"


fun ext_seq'::"'s list \<Rightarrow> ('s \<Rightarrow> 's list) \<Rightarrow> 's list" where
"ext_seq' [] f = []" |
"ext_seq' [s] f = s # f s" |
"ext_seq' (s#S) f = s # (ext_seq' S f)"

fun ext_seq''::"'s list \<Rightarrow> ('s \<Rightarrow> 's list) list \<Rightarrow> 's list" where
"ext_seq'' s [] = s" |
"ext_seq'' s (f#fs) = ext_seq'' (ext_seq' s f) fs"

lemma ext_seq'_seq_apply_is_ext_seq: "ext_seq' xs (seq_apply fs) = ext_seq xs fs"
  apply (induction xs)
   apply (induction fs)
    apply simp
   apply simp
  subgoal for x xs
    apply (induction xs)
     apply (induction fs)
      apply simp
     apply simp
    subgoal for x' xs'
      apply (induction fs)
       apply simp
      subgoal for f fs
        by simp
      done
    done
  done

(* 
lemma ext_seq'_assoc: "ext_seq' (ext_seq' xs f) g = ext_seq' xs (\<lambda>x. ext_seq' (f x) g)"
  apply (induction xs)
   apply simp
  subgoal for x xs
    apply (induction xs)
    apply (subst ext_seq'.simps)+ *)

(* Not a monad. Extending an empty sequence behaves weirdly *)

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

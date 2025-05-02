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
"ext_seq' (x#xs) f = x # (ext_seq' xs f)"

fun ext_seq''::"'s list \<Rightarrow> ('s \<Rightarrow> 's list) list \<Rightarrow> 's list" where
"ext_seq'' s [] = s" |
"ext_seq'' s (f#fs) = ext_seq'' (ext_seq' s f) fs"

fun seq_apply''::"('a \<Rightarrow> 'a list) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"seq_apply'' [] x = []" |
"seq_apply'' (f#fs) x = ext_seq'' (f x) fs" 

lemma ext_seq_alt: 
  assumes "xs \<noteq> []"
shows "ext_seq (xs::'x list) fs = xs @ seq_apply fs (last xs)"
  using assms
  apply (induction xs)
   apply simp
  subgoal for x xs'
    apply (induction xs')
     apply (cases fs)
      apply simp
    apply simp
    subgoal for x' xs''
      apply (cases fs)
       apply simp
      subgoal for f fs'
        apply (induction xs'')
         apply simp
        subgoal for x'' xs'''
          by simp
        done
      done
    done
  done



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

lemma ext_seq''_alt: "ext_seq'' xs fs = foldl ext_seq' xs fs"
  apply (induction fs arbitrary: xs)
   apply (induction xs)
    apply simp
  apply simp
  subgoal for f fs xs
    apply (subst foldl.simps)
    apply (subst ext_seq''.simps)
    by simp
  done

lemma seq_apply''_alt:
  "seq_apply'' [] x = []"
  "seq_apply'' (f#fs) x = foldl ext_seq' (f x) fs"
  by (simp add: ext_seq''_alt)+

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


lemma seq_apply_nth_Suc:
  assumes "i < length fs"
  shows "(s#seq_apply fs s) ! Suc i = (fs ! i) ((s#seq_apply fs s) ! i)"
  using assms
proof  (induction i arbitrary: s fs)
  case 0
  then show ?case apply (cases fs) by auto
next
  case (Suc i)
  then obtain f' fs' where
    fs': "fs = f'#fs'" apply (cases fs) by auto
  hence 1: "(f' s # seq_apply fs' (f' s)) ! Suc i = (fs' ! i) ((f' s # seq_apply  fs' (f' s)) ! i)" using Suc by simp
  
  show ?case 
    apply (subst nth_Cons_Suc)
    apply (subst nth_Cons_Suc)
    apply (subst fs')+
    apply (subst seq_apply.simps)+
    apply (subst 1)
    apply (subst nth_Cons_Suc)
    by blast
qed

lemma seq_apply_pre_post:
  assumes "\<forall>s. \<forall>i < length fs. P s i \<longrightarrow> Q ((fs ! i) s) (Suc i)"
      and "\<forall>s. \<forall>i < length fs. Q s (Suc i) \<longrightarrow> P s (Suc i)"
      and "P s 0"
    shows "(\<forall>i < length fs. P ((s#seq_apply fs s) ! i) i \<and> Q ((s#seq_apply fs s) ! (Suc i)) (Suc i))"
proof -
  have "P ((s # seq_apply fs s) ! i) i \<and> Q ((s # seq_apply fs s) ! Suc i) (Suc i)" if "i < length fs" for i
    using that proof (induction i)
    case 0
    have "P ((s # seq_apply fs s) ! 0) 0" using assms(3) by simp
    moreover
    from 0 
    obtain f fs' where
      fs: "fs = f#fs'" 
      "f = fs!0" apply (cases fs) by auto
    have "((s # seq_apply fs s) ! Suc 0) = (fs!0) s" using fs by fastforce
    with assms(1,3) 0
    have "Q ((s # seq_apply fs s) ! Suc 0) (Suc 0)" by auto
    ultimately
    show ?case by simp
  next
    case (Suc i)
    have Pi: "P ((s # seq_apply fs s) ! i) i"
     and Qi: "Q ((s # seq_apply fs s) ! Suc i) (Suc i)" using Suc by simp+
    have Si: "Suc i < length fs" using Suc by blast
    from assms(2) Si Qi
    have PSi: "P ((s # seq_apply fs s) ! Suc i) (Suc i)" by auto
    have "(s # seq_apply fs s) ! Suc (Suc i) = (fs ! Suc i) ((s # seq_apply fs s) ! Suc i)" using seq_apply_nth_Suc[OF Si] by blast
    hence "Q ((s # seq_apply fs s) ! Suc (Suc i)) (Suc (Suc i))" using PSi assms(1) Si by simp
    thus "P ((s # seq_apply fs s) ! Suc i) (Suc i) \<and> Q ((s # seq_apply fs s) ! Suc (Suc i)) (Suc (Suc i))" using PSi by simp
  qed
  thus "\<forall>i<length fs. P ((s # seq_apply fs s) ! i) i \<and> Q ((s # seq_apply fs s) ! Suc i) (Suc i)" 
    by auto
qed

lemma seq_apply_not_Nil:
  assumes "0 < length fs"
      and "\<forall>f \<in> set fs. \<forall>s. f s \<noteq> []"
    shows "seq_apply fs s \<noteq> []"
  using assms
  apply (induction fs)
  by simp+

lemma ext_seq'_not_Nil:
  assumes "\<forall>s. f s \<noteq> []"
      and "xs \<noteq> []"
    shows "ext_seq' xs f \<noteq> []"
  using assms
  apply (induction xs)
   apply simp
  subgoal for x xs
    apply (cases xs)
    by simp+
  done

lemma ext_seq'_alt:
  assumes "xs \<noteq> []"
  shows "ext_seq' xs f = xs @ f (last xs)"
  using assms
  apply (induction xs)
  apply simp
  subgoal for x xs
    apply (cases xs)
    by simp+
  done


lemma ext_seq''_alt_append:
  assumes "xs \<noteq> []"
      and "\<forall>f \<in> set fs. \<forall>s. f s \<noteq> []"  
    shows "ext_seq'' xs fs = xs @ seq_apply'' fs (last xs)"
  using assms
proof (induction fs arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs xs')
  have "ext_seq'' xs' (f # fs) = ext_seq'' (ext_seq' xs' f) fs" by simp
  moreover
  have "ext_seq' xs' f \<noteq> []" using Cons ext_seq'_not_Nil by auto
  ultimately
  have "ext_seq'' xs' (f # fs) = ext_seq' xs' f @ seq_apply'' fs (last (ext_seq' xs' f))" using Cons by auto
  hence "ext_seq'' xs' (f # fs) = (xs' @ f (last xs')) @ seq_apply'' fs (last (xs' @ f (last xs')))" using Cons ext_seq'_alt by metis
  hence 1: "ext_seq'' xs' (f # fs) = xs' @ f (last xs') @ seq_apply'' fs (last (f (last xs')))" using last_append Cons by simp

  have "xs' @ seq_apply'' (f # fs) (last xs') = xs' @ ext_seq'' (f (last xs')) fs" by simp
  moreover 
  have "f (last xs') \<noteq> []" using Cons by simp
  ultimately
  have 2: "xs' @ seq_apply'' (f # fs) (last xs') = xs' @ f (last xs') @ seq_apply'' fs (last (f (last xs')))" using Cons by simp
  
  show ?case using 1 2 by simp
qed

lemma ext_seq''_not_Nil:
  assumes "0 < length xs"
      and "\<forall>f \<in> set fs. \<forall>s. f s \<noteq> []"
    shows "ext_seq'' xs fs \<noteq> []"
  using assms
proof (induction fs arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case f: (Cons f fs)
  show ?case 
  proof (cases xs)
    case Nil
    then show ?thesis using f by simp
  next
    case (Cons x' xs')
    have "ext_seq'' (x' # xs') (f # fs) = ext_seq'' (ext_seq' (x' # xs') f) fs" by simp
    moreover
    have "ext_seq' (x' # xs') f \<noteq> []" using f ext_seq'_not_Nil by auto
    ultimately
    show ?thesis using f.IH[of "ext_seq' (x' # xs') f"] f(3) Cons by simp
  qed
qed
     

lemma seq_apply''_not_Nil:
  assumes "0 < length fs"
      and "\<forall>f \<in> set fs. \<forall>s. f s \<noteq> []"
    shows "seq_apply'' fs s \<noteq> []" 
  using assms apply (induction fs arbitrary: s)
  apply simp
  subgoal for f fs s
    apply (cases fs)
     apply simp
    apply (subst seq_apply''.simps)
    apply (rule ext_seq''_not_Nil)
    by simp+
  done

lemma seq_apply''_append_1:
  assumes "0 < length fs"
      and "\<forall>f \<in> set fs. \<forall>s. f s \<noteq> []"
      and "\<forall>s. f s \<noteq> []"
  shows "seq_apply'' fs s @ (f (last (seq_apply'' fs s))) = seq_apply'' (fs @ [f]) s"
  using assms 
proof (induction fs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons f' fs)
  have 1: "seq_apply'' (f' # fs) s = (f' s) @ seq_apply'' fs (last (f' s))"
    apply (subst seq_apply''.simps)
    apply (subst ext_seq''_alt_append)
    using Cons by simp+

  have 2: "seq_apply'' (f' # fs) s @ f (last (seq_apply'' (f' # fs) s)) = f' s @ (seq_apply'' fs (last (f' s)) @ f (last (f' s @ (seq_apply'' fs (last (f' s))))))" using 1 by simp
  show ?case 
  proof (cases "fs = []")
    case True
    with 2
    have "seq_apply'' (f' # fs) s @ f (last (seq_apply'' (f' # fs) s)) = seq_apply'' [f'] s @ f (last (seq_apply'' [f'] s))" by blast
    moreover
    have "seq_apply'' [f'] s @ f (last (seq_apply'' [f'] s)) = f' s  @ f (last (f' s))" by simp
    ultimately
    have 3: "seq_apply'' (f' # fs) s @ f (last (seq_apply'' (f' # fs) s)) = f' s @ f (last (f' s))" by auto

    have "seq_apply'' ((f' # fs) @ [f]) s = seq_apply'' [f', f] s" using True by simp
    hence "seq_apply'' ((f' # fs) @ [f]) s = ext_seq' (f' s) f" by simp
    moreover
    have "f' s \<noteq> []" using Cons by simp
    ultimately
    have 4: "seq_apply'' ((f' # fs) @ [f]) s = f' s @ f (last (f' s))" using ext_seq'_alt by auto
    show ?thesis using 3 4 by simp
  next
    case False
    have 5: "seq_apply'' fs (last (f' s)) \<noteq> []" 
      apply (rule seq_apply''_not_Nil)
      using Cons(3) False by simp+
    have "seq_apply'' (f' # fs) s @ f (last (seq_apply'' (f' # fs) s)) =  f' s @ seq_apply'' fs (last (f' s)) @ f (last (seq_apply'' fs (last (f' s))))" 
      apply (subst 2)
      apply (subst last_append)
      using 5 by auto
    also have "... = f' s @ seq_apply'' (fs @ [f]) (last (f' s))" 
      apply (subst Cons.IH)
      using False Cons by simp+
    also have "... = seq_apply'' ((f' # fs) @ [f]) s" 
      apply (subst append_Cons)
      apply (subst seq_apply''.simps)
      apply (subst ext_seq''_alt_append)
      using Cons by simp+
    finally 
    show ?thesis by simp
  qed
qed

lemma seq_apply''_take_n_nth_Suc:
  assumes "0 < i"
      and "i < length fs"
      and "\<forall>f \<in> set fs. \<forall>s. f s \<noteq> []"
    shows "seq_apply'' (take (Suc i) fs) s = seq_apply'' (take i fs) s @ (fs ! i) (last (seq_apply'' (take i fs) s))"
proof -
  have take_Suc_i: "take (Suc i) fs = take i fs @ [fs ! i]" using take_Suc_conv_app_nth assms by blast

  have take_i_def: "\<forall>f\<in>set (take i fs). \<forall>s. f s \<noteq> []" 
    apply (rule ballI)
    apply (drule set_mp[OF set_take_subset])
    apply (drule bspec[OF assms(3)]) by blast

  show ?thesis 
    apply (subst take_Suc_i)
    apply (subst seq_apply''_append_1)
    using assms apply simp
    using take_i_def apply simp
    using assms in_set_conv_nth apply simp
    by simp
qed

lemma seq_apply''_pre_post_induct:
  fixes fs::"('a \<Rightarrow> 'a list) list"
  assumes fs_len: "0 < length fs"
      and f_wf: "\<forall>f \<in> set fs. \<forall>x. f x \<noteq> []"
      and P0: "P s 0"
      and PQ: "\<forall>i < length fs. \<forall>s. P s i \<longrightarrow> (Q (last ((fs ! i) s)) (Suc i))"
      and QP: "\<forall>i < length fs. \<forall>s. Q s i \<longrightarrow> P s i"
    shows "Q (last (seq_apply'' fs s)) (length fs)"
proof -
  from assms(1)
  obtain f' fs' where
    fs: "fs = f'#fs'" by (cases fs, auto)

  have "Q (last (seq_apply'' (take i fs) s)) i" if "0 < i" "i \<le> length fs" for i
    using that
  proof (induction i)
    case 0
    then show ?case by blast
  next
    case i: (Suc i)
    show ?case 
    proof (cases i)
      case 0
      then have "seq_apply'' (take (Suc i) fs) s = seq_apply'' [(fs ! 0)] s" using fs by simp
      hence "seq_apply'' (take (Suc i) fs) s = (fs ! 0) s" by simp
      moreover
      have "Q (last ((fs ! 0) s)) (Suc i)" using P0 PQ 0 i by force
      ultimately
      show ?thesis by simp
    next
      case i'[simp]: (Suc i')
      have 1: "seq_apply'' (take (Suc i) fs) s = seq_apply'' (take i fs) s @ (fs ! i) (last (seq_apply'' (take i fs) s))" (is "?seq = ?seq1 @ (fs ! i) ?s")
        apply (subst seq_apply''_take_n_nth_Suc)
        using i' apply simp
        using i(3) apply simp
        using f_wf apply simp
        by blast

      have "Q ?s i" 
        apply (rule i(1))
        using i' i by simp+
      hence "P ?s i" using QP i i' by simp
      hence 2: "Q (last ((fs ! i) ?s)) (Suc i)" using PQ i i' by fastforce

      have 3: "(fs ! i) (last (seq_apply'' (take i fs) s)) \<noteq> []" using f_wf i by auto

      show ?thesis 
        apply (subst 1)
        apply (subst last_append)
        apply (subst if_not_P)
         apply (rule 3)
        using 2 by blast
    qed
  qed
  thus ?thesis using fs_len take_all by fastforce
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

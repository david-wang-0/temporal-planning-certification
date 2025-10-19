theory ListMisc
  imports "Automatic_Refinement.Misc" "List-Index.List_Index"
begin

locale filter_sorted_distinct_list =
  fixes xs::"nat list"
    and P::"nat \<Rightarrow> bool"
    and ys
  assumes ys: "ys = filter P xs"
      and sorted: "sorted xs"
      and distinct: "distinct xs"
begin

  lemma ys_mono: "ys ! m < ys ! n" if "m < n" "n < length ys" for m n
    apply (rule distinct_sorted_mono)
    using that sorted distinct unfolding ys
    by (auto intro: sorted_filter')

  lemma ys_sorted: "ys ! m \<le> ys ! n" if "m \<le> n" "n < length ys" for m n
    using that by (cases "m = n") (fastforce dest: le_neq_implies_less ys_mono)+

  lemma ys_mono': "n < m" 
    if "ys ! n < ys ! m" 
      "n < length ys" 
    for m n
    apply (rule contrapos_pp[OF that(1)])
    using ys_sorted[OF _ that(2), of m] by simp
   
  lemma ys_Suc: "ys ! j < ys ! Suc j" if "Suc j < length ys" for j
    using ys_mono that by blast

  lemma ys_exI: "\<exists>ij < length ys. ys ! ij = (xs ! j)" 
    if "j < length xs" 
       "P (xs ! j)" 
    for j
    apply (subst in_set_conv_nth[symmetric])
    by (simp add: that ys)

  lemma length_ys: "length ys \<le> length xs" 
    unfolding ys 
    apply (rule order_trans)
     apply (rule length_filter_le)
    by simp

  lemma nth_ys_ran: "\<forall>j < length ys. ys ! j \<in> set xs"
    apply (subst all_set_conv_all_nth[symmetric])
    unfolding ys by simp

  lemma ys_inc_all: "\<not> P m" 
    if jl: "Suc j < length ys"
      and m: "m \<in> set xs"
      and x: "Suc (ys ! j) \<le> m" "m < ys ! Suc j" 
    for j m
  proof (intro notI)
    assume a: "P m"
    obtain xm where
      xm: "xm < length xs"
      "m = xs ! xm" using in_set_conv_nth m by metis
    obtain im where
      im: "im < length ys" "ys ! im = m"
      using ys_exI xm a by blast
    hence "ys ! j < ys ! im" "ys ! im < ys ! Suc j" using x by simp_all
    hence "j < im" "im < Suc j"
      using jl im(1)
      by (auto elim!: ys_mono')
    thus False by simp
  qed

  lemma ys_inc_all_below: "\<not> (P m)" 
    if jl: "0 < length ys" 
      and m: "m \<in> set xs"
   and x: "m < ys ! 0" for m
  proof (intro notI)
    assume a: "P m"
    obtain xm where
      xm: "xm < length xs"
      "m = xs ! xm" using in_set_conv_nth m by metis
    obtain im where
      im: "im < length ys" "ys ! im = m"
      using ys_exI xm a  by blast
    hence o: "ys ! im < ys ! 0" using x by simp_all
    have "im < 0"
      apply (rule ys_mono')
      using o im by auto
    thus False by simp
  qed

  lemma ys_inc_all_above: "\<not> P m" 
    if x: "ys ! (length ys - 1) < m"
    and m: "m \<in> set xs" for m
  proof (cases "length ys = 0")
    case True
    then show ?thesis by (auto dest:  arg_cong[where f = set] simp: ys m)
  next
    case False
    show ?thesis 
    proof (intro notI)
      from False 
      have jl: "0 < length ys" by simp
      assume a: "P m" 
      obtain xm where
        xm: "xm < length xs"
        "m = xs ! xm" using in_set_conv_nth m by metis
      obtain im where
        im: "im < length ys" "ys ! im = m"
        using ys_exI xm a by blast
      hence o: "ys ! (length ys - 1) < ys ! im" using x by blast
      have "(length ys - 1) < im"
        apply (rule ys_mono')
        using o jl by auto
      thus False using im by simp
    qed
  qed

lemma length_0_imp_no_P:
  assumes "length ys = 0"
  shows "\<forall>x \<in> set xs. \<not> P x"
  using assms ys
  by (auto dest: arg_cong[of _ _ set])
end

definition "unzip xs = (map fst xs, map snd xs)"

lemma zip_unzip:
  "length xs = length ys \<Longrightarrow> unzip (zip xs ys) = (xs, ys)"
  "uncurry zip (unzip xs) = xs"     
  subgoal by (induction xs arbitrary: ys) (auto simp: unzip_def)
  by (simp add: unzip_def)

lemma replicate_length_conv_map:
  "replicate (length xs) n = map (\<lambda>x. n) xs"
  by (induction xs) (use replicate_append_same in auto)

lemma foldr_map_filter:
  "sum_list (map (\<lambda>x. if P x then 1 else 0) xs) = sum_list (map (\<lambda>x. 1) (filter P xs))"
  unfolding sum_list.eq_foldr
  apply (induction xs) by auto

lemma distinct_sum_list_1_conv_card_set:
  assumes "distinct xs"
  shows "sum_list (map (\<lambda>x. 1) xs) = card (set xs)"
  using assms by (induction xs) simp_all

lemma sum_list_map_if:
"sum_list (map (\<lambda>x. if P x then (n::int) else m) xs)
  = sum_list (map (\<lambda>x. n) (filter P xs)) + sum_list (map (\<lambda>x. m) (filter (\<lambda>x. \<not>P x) xs))"
  unfolding sum_list.eq_foldr
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    apply (cases "P x") by auto
qed
  
lemma sum_list_map_if':
"sum_list (map (\<lambda>x. if P x then (n::nat) else m) xs)
  = sum_list (map (\<lambda>x. n) (filter P xs)) + sum_list (map (\<lambda>x. m) (filter (\<lambda>x. \<not>P x) xs))"
  unfolding sum_list.eq_foldr
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    apply (cases "P x") by auto
qed

lemma map_upds_append:
  assumes "length xs = length xs'"
      and "length ys = length ys'"
    shows "f(xs @ ys [\<mapsto>] xs' @ ys') = f(xs [\<mapsto>] xs', ys [\<mapsto>] ys')"
  unfolding map_upds_def using assms map_of_append by simp

find_theorems "sum_list (map (\<lambda>x. 0) ?xs)"

lemma sum_list_max: 
  assumes "\<forall>x \<in> set xs. x \<le> n"
  shows "sum_list xs \<le> length xs * n"
  using assms 
  unfolding sum_list.eq_foldr 
  apply (induction xs)
  by auto

lemma assumes "\<forall>x \<in> set xs. x = 1"
  shows "sum_list xs = length xs"
  using assms 
  apply (induction xs)
  by simp+

lemma sum_list_binary_less_than_length_if:
  assumes "\<forall>x \<in> set xs. x \<in> ({0, 1}::nat set)"
          and "\<exists>x \<in> set xs. x = 0"
        shows "sum_list xs < length xs"
proof (cases "0 < length xs")
  case True
  obtain x0 where
    "x0 \<in> set xs" "x0 = 0" using assms by auto
  hence "x0 \<in> set_mset (mset xs)" by auto

  have set_sort_key: "set (sort_key id xs) = set xs" by simp
  have length_sort_key: "length (sort_key id xs) = length xs" by simp
  with True
  have not_empty_sort_key: "sort_key id xs \<noteq> []" by fastforce
  hence hd_tl_sort_key: "hd (sort_key id xs) # (tl (sort_key id xs)) = sort_key id xs" by simp
  
  have "\<exists>y \<in> set (sort_key id xs). y = 0" using assms set_sort_key by auto
  have set_sort_key_ran: "\<forall>y \<in> set (sort_key id xs). y \<in> {0, 1}" using assms(1) set_sort_key by blast
  have tl_sort_key_ran: "\<forall>y \<in> set (tl (sort_key id xs)). y \<in> {0, 1}" using  set_sort_key_ran 
    apply (subst (asm) hd_tl_sort_key[symmetric]) by auto

  have hd_sort_key_0: "hd (sort_key id xs) = 0" 
  proof (rule ccontr)
    assume a: "hd (sort_key id xs) \<noteq> 0"
    
    have "hd (sort_key id xs) \<in> set xs" using hd_in_set set_sort_key not_empty_sort_key by blast
    hence 1: "hd (sort_key id xs) = 1" using assms(1) a by fastforce

    have "sorted (sort_key id xs)" by (metis eq_id_iff sorted_sort)
    hence "\<forall>y \<in> set (tl (sort_key id xs)). hd (sort_key id xs) \<le> y" by (metis ball_empty list.collapse list.sel(2) list.set(1) sorted_wrt.simps(2))
    hence "\<forall>y \<in> set (tl (sort_key id xs)). y = 1" using 1 tl_sort_key_ran by auto
    with 1
    have "\<forall>y \<in> set (sort_key id xs). y = 1" apply (subst hd_tl_sort_key[symmetric]) by simp
    with set_sort_key assms(2)
    show False by auto
  qed
  
  have mset_sort_key: "mset (sort_key id xs) = mset xs" by simp
  hence "sum_list xs = sum_list (sort_key id xs)" unfolding sum_list.eq_foldr
    apply (subst foldr_fold)
     apply force
    apply (subst foldr_fold)
    apply force
    apply (rule fold_permuted_eq[where P = "\<lambda>_. True" and f = "(+)"])
    by simp+
  hence "sum_list xs = sum_list (hd (sort_key id xs) # tl (sort_key id xs))" using hd_tl_sort_key by auto
  also have "... = 0 + sum_list (tl (sort_key id xs))" using hd_sort_key_0 by auto
  also have "... \<le> length (tl (sort_key id xs))" using tl_sort_key_ran sum_list_max by fastforce
  also have "... < length (sort_key id xs)" apply (subst (2) hd_tl_sort_key[symmetric]) by simp
  finally
  show ?thesis using length_sort_key by simp
next 
  case False
  thus ?thesis using assms(2) by simp
qed


find_theorems "sum_list (map ?f ?xs)"


lemma sum_list_sub_nat_distrib:
  assumes "\<forall>x \<in> set xs. ((f x)::nat) \<ge> g x"
  shows "sum_list (map (\<lambda>x. f x - g x) (xs)) = sum_list (map f xs) - sum_list (map g xs)"
  using assms unfolding sum_list.eq_foldr
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "f x - g x + foldr (+) (map (\<lambda>x. f x - g x) xs) 0 = f x + foldr (+) (map f xs) 0 - (g x + foldr (+) (map g xs) 0)" (is "?a = ?b")
  proof -
    have "?a = f x - g x + (foldr (+) (map f xs) 0 - foldr (+) (map g xs) 0)" apply (subst Cons.IH) using Cons by auto
    also have "... = f x - g x + foldr (+) (map f xs) 0 - foldr (+) (map g xs) 0" 
    proof -
      have "(foldr (+) (map f xs) 0 \<ge> foldr (+) (map g xs) 0)" using Cons(2) sum_list_mono unfolding sum_list.eq_foldr by fastforce
      thus ?thesis by simp
    qed
    also have "... = f x + foldr (+) (map f xs) 0 - g x - foldr (+) (map g xs) 0" 
    proof -
      have "f x \<ge> g x" using Cons by simp
      thus ?thesis by simp
    qed
    also have "... = f x + foldr (+) (map f xs) 0 - (g x + foldr (+) (map g xs) 0)" by simp
    finally show ?thesis by blast
  qed
  then show ?case by simp
qed


lemma map_of_zip_fst:
  assumes "x \<in> set as"
     and "length as = length bs"
   shows "map_of (zip as bs) x = Some (bs ! (List_Index.index as x))"
  using assms
proof (induction as arbitrary: bs)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then obtain c cs where
    bs[simp]: "bs =c#cs" by (cases bs, auto)
  show ?case 
  proof (cases "x = a")
    case [simp]: True
    hence "List_Index.index (a # as) x = 0" by auto
    hence "bs ! (List_Index.index (a # as) x) = c" using nth_Cons_0 by simp
    moreover
    have "map_of (zip (a # as) bs) x = Some c" by auto
    ultimately
    show ?thesis by simp
  next
    case False
    show ?thesis 
      apply (subst bs)+
      apply (subst zip_Cons_Cons)
      apply (subst map_of_Cons_code(2))
      using False Cons
      by simp
  qed
qed

lemma map_of_map_inj_on_fst: 
  assumes "inj_on f ({x} \<union> (fst ` set xs))"
    shows "map_of (map (\<lambda>(k, v). (f k, v)) xs) (f x) = map_of xs x"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain i j where
    a: "a = (i, j)" by fastforce
  have ix: "f i \<noteq> f x" if "i \<noteq> x" using Cons(2) that unfolding inj_on_def a by auto
  show ?case 
    unfolding a
      apply (subst map_of_Cons_code)
      apply (cases "i = x")
       apply simp
      apply (subst list.map)
      apply (subst prod.case)+
      apply (subst map_of_Cons_code)
    using ix Cons.IH Cons(2) by auto
qed



fun list_pairwise::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_pairwise P [] = True" |
"list_pairwise P (x#xs) = (list_all (P x) xs \<and> list_pairwise P xs)"

(* Todo?: list_pairwise and Set.pairwise conditional equivalence.
    Not needed yet. *)

find_theorems "?x \<noteq> ?y \<Longrightarrow> (?x < ?y \<Longrightarrow> ?thesis) \<Longrightarrow> (?y < ?x \<Longrightarrow> ?thesis) \<Longrightarrow> ?thesis"

lemma list_pairwise_nth: "list_pairwise P xs \<longleftrightarrow> (\<forall>i j. j < length xs \<longrightarrow> i < j \<longrightarrow> P (xs ! i) (xs ! j))"
proof (intro iffI strip)
  fix i j
  assume p:   "list_pairwise P xs" 
    and j:    "j < length xs" 
    and ij:   "i < j" 
  show "P (xs ! i) (xs ! j)" using p j ij
  proof (induction xs arbitrary: i j)
    case Nil
    then show ?case by auto
  next
    case 1: (Cons x xs)
    have p:   "list_pairwise P (x # xs)"
     and j:   "j < length (x # xs)"
     and ij:  "i < j" using 1 by auto
    have IH': "\<And>i j. j < length xs \<Longrightarrow> i < j \<Longrightarrow> P (xs ! i) (xs ! j)" using 1 by auto
    show ?case
    proof (cases "length xs")
      case 0
      then show ?thesis using 1 by simp
    next
      case (Suc nat)
      show ?thesis 
      proof (cases i)
        assume i0: "i = 0"
        have "list_all (P ((x#xs) ! i)) xs" using p i0 nth_Cons_0 by simp
        hence "\<forall>y \<in> set xs. (P ((x#xs) ! i)) y" unfolding list_all_iff by blast
        moreover
        have "((x # xs) ! j) \<in> set xs" using ij j by simp
        ultimately
        show ?thesis by blast
      next
        fix i'
        assume i: "i = Suc i'" 
        have xsi: "(x # xs) ! i = xs ! i'" using i by simp
        moreover
        obtain j' where
          j': "j = Suc j'" 
              "j' < length xs" using lessE[OF ij] j by fastforce
        hence ij': "i' < j'" using ij i by blast
        have xsj: "(x # xs) ! j = xs ! j'" using j' by auto
        moreover
        have "P (xs ! i') (xs ! j')" using IH' j' i ij' by blast
        ultimately
        show ?thesis by argo
      qed
    qed
  qed
next
  assume "\<forall>i j. j < length xs \<longrightarrow> i < j \<longrightarrow> P (xs ! i) (xs ! j)" 
  thus "list_pairwise P xs"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    have "list_pairwise P xs" using Cons by fastforce
    moreover
    have "\<forall>j < length xs. P x (xs ! j)" using Cons by fastforce
    hence "list_all (P x) xs" using list_all_iff unfolding set_conv_nth by blast
    ultimately
    show ?case by simp
  qed
qed

lemma list_pairwise_nth_refl:
  assumes refl: "\<forall>x y. P x y \<longleftrightarrow> P y x"
  shows "list_pairwise P xs \<longleftrightarrow> (\<forall>i j. i < length xs \<longrightarrow> j < length xs \<longrightarrow> i \<noteq> j \<longrightarrow> P (xs ! i) (xs ! j))"
  unfolding list_pairwise_nth 
  apply (rule iffI)
   apply (intro strip)
   apply (erule neqE)
    apply blast
  using refl apply blast
  by simp

lemma list_pairwise_map:
  assumes "list_pairwise (\<lambda>x y. P (f x) (f y)) xs"
  shows "list_pairwise P (map f xs)"
  using assms apply (induction xs)
   apply simp
  subgoal for x xs
    apply (subst list.map list_pairwise.simps list.pred_map comp_def)+ 
    by auto
  done


definition nth_opt where
"nth_opt xs n \<equiv> if n < length xs then Some (xs ! n) else None"

lemma dom_nth_opt:
  "dom (nth_opt xs) = {i. i < length xs}" 
  unfolding nth_opt_def 
  by (induction xs) auto

lemma ran_nth_opt:
  "ran (nth_opt xs) = set xs" 
  unfolding nth_opt_def unfolding ran_def
  apply (intro equalityI subsetI)
   apply (erule CollectE)
   apply (erule exE)
  unfolding set_conv_nth
  subgoal for x i
    apply (cases "i < length xs")
    by auto
  by auto


lemma nth_opt_Some:
  "nth_opt xs n = Some x \<Longrightarrow> x = xs ! n"
  "Some x = nth_opt xs n \<Longrightarrow> x = xs ! n"
  unfolding nth_opt_def
  by (cases "n < length xs"; simp)+


end
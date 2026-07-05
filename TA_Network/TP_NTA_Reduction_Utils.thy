theory TP_NTA_Reduction_Utils
  imports TP_NTA_Reduction_Model_Checking
begin

text \<open>Generic helper lemmas (pure-HOL + Munta-global), factored out of the reduction proofs.\<close>

lemma fold_union:
  "fold (\<union>) S T =  \<Union> (set S) \<union> T"
  by (induction S arbitrary: T) auto

lemma fold_union':
  "fold (\<union>) S {} =  \<Union> (set S)"
  apply (subst fold_union)
  apply (subst Un_empty_right)
  ..

lemma set_nthI:
  assumes "n < length xs"
  shows "xs ! n \<in> set xs" using assms in_set_conv_nth by auto

lemma sum_list_eq:
  assumes "distinct xs" "distinct ys" "set xs = set ys" 
  shows "sum_list ((map f xs)::nat list) = sum_list (map f ys)"
proof -
  have "mset xs = mset ys" using assms set_eq_iff_mset_eq_distinct by blast
  hence "mset (map f xs) = mset (map f ys)" by simp
  hence "fold (+) (map f xs) 0 = fold (+) (map f ys) 0"
    apply -
    apply (rule fold_permuted_eq[where P = "\<lambda>_. True"])
       apply simp
      apply simp
     apply simp
    by simp
  moreover
  have "foldr (+) (map f xs) 0 = fold (+) (map f xs) 0"
    apply (subst foldr_fold)
    by auto
  moreover
  have "foldr (+) (map f ys) 0 = fold (+) (map f ys) 0"
    apply (subst foldr_fold)
    by auto
  ultimately
  show ?thesis unfolding sum_list.eq_foldr by argo
qed

lemma foldr_assoc: "foldr (+) xs (n + 0::nat) = (foldr (+) xs 0) + n"
  apply (induction xs)
   apply simp
  subgoal for x xs
    by auto
  done

lemma dom_map_of_map:
  "dom (map_of (map (\<lambda> (a, b). (f a, g b)) xs)) = f ` fst ` set xs"
  unfolding dom_map_of_conv_image_fst by (auto 4 3)

lemma map_of_NoneI:
  "map_of xs x = None" if "x \<notin> fst ` set xs"
  by (simp add: map_of_eq_None_iff that)

lemma map_const_eq_conv_length_eq:
  "map (\<lambda>x. n) xs = map (\<lambda>y. m) ys \<longleftrightarrow> length xs = length ys \<and> ((xs \<noteq> []) \<longrightarrow> n = m)"
  apply (rule iffI)
   apply (induction xs arbitrary: ys)
    apply simp
  subgoal for x xs ys
    apply (induction ys)
    by auto
  apply (induction xs arbitrary: ys)
   apply simp
  subgoal for x xs ys
    apply (induction ys)
    by auto
  done

lemma is_upds_inc_vars: 
  assumes "set xs \<subseteq> dom v"
      and "distinct xs"
      and "upds = (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs)"
      and "v' = v(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the o v) xs))"
  shows "is_upds v upds v'"
  using assms(1,2)
  unfolding assms(3,4)
proof (induction xs arbitrary: v)
  case Nil
  then show ?case 
    apply simp
    by (rule is_upds.intros)
next
  case (Cons x xs v)
  have 1: "is_upd v (x, binop plus_int (var x) (exp.const n)) (v(x \<mapsto> the (v x) + n))" (is "is_upd v ?upd ?v'")
    unfolding is_upd_def
     apply (intro exI conjI)
       apply (rule HOL.refl)
      apply (rule check_bexp_is_val.intros(14)[of _ _ "the (v x)"])
      apply (rule check_bexp_is_val.intros)
       using Cons(2) apply auto[1]
        apply (rule check_bexp_is_val.intros)
       by simp
   from Cons(3)
   have "\<forall>x' \<in> set xs. x \<noteq> x'" by auto
   hence 2: "map (the o v) xs = map (the o ?v') xs"
     unfolding comp_def using fun_upd_other by auto

   have "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the \<circ> ?v') xs)))"
     apply (rule Cons.IH)
     using Cons(2,3) by auto
   hence 3: "is_upds ?v' (map (\<lambda>v. (v, binop plus_int (var v) (exp.const n))) xs) (?v'(xs [\<mapsto>] map (\<lambda>x. x + n) (map (the \<circ> v) xs)))"
     apply (subst 2) by simp
   show ?case 
    apply (subst list.map)+
    apply (subst map_upds_Cons)
     apply (rule is_upds.intros(2)[OF 1])
     using 3 unfolding comp_apply by simp
qed

lemma single_upd_bounded:
  assumes "bounded M v"
      and "M x = Some (l, u)"
      and "l \<le> y"
      and "y \<le> u"
    shows "bounded M (v(x \<mapsto> y))"
proof -
  from assms[simplified bounded_def]
  have dom_v_M: "dom v = dom M"
    and bounds: "\<forall>x \<in> dom v. fst (the (M x)) \<le> the (v x) \<and> the (v x) \<le> snd (the (M x))"
    by auto
  
  from assms(2) dom_v_M
  have dom': "dom (v (x \<mapsto> y)) = dom v" by auto

  have "fst (the (M a)) \<le> the ((v (x \<mapsto> y)) a) \<and> the ((v (x \<mapsto> y)) a) \<le> snd (the (M a))" if "a \<in> dom (v (x \<mapsto> y))" for a
  proof (cases "a = x")
    case True
    then show ?thesis using assms(2,3,4) by simp
  next
    case False
    hence 1: "the (v a) = the ((v (x \<mapsto> y)) a)" using that by simp
    
    have "a \<in> dom v" using dom' that by argo
    from bounds[THEN bspec, OF this]
    show ?thesis unfolding 1 by simp
  qed
  with dom' dom_v_M
  show ?thesis unfolding bounded_def by simp
qed

find_theorems name: "map_upds"

lemma upds_bounded:
  assumes "bounded M v"
      and "length xs = length ys"
      and "\<forall>n < length xs. \<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> (ys ! n) \<and> (ys ! n) \<le> u"   
    shows "bounded M (v(xs [\<mapsto>] ys))"
  using assms
proof (induction xs arbitrary: ys v)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y' ys' where
    ys': "ys = y'#ys'"
    "length (x # xs) = length (y' # ys')" apply (cases ys) by simp+
  obtain l u where
    "M x = Some (l, u)"
    "l \<le> y'"
    "y' \<le> u" using Cons(4)[simplified ys'(1)] by auto
  with Cons(2)
  have 1: "Simple_Network_Language.bounded M (v(x \<mapsto> y'))" by (auto intro: single_upd_bounded)
  have 2: "\<forall>n<length xs. \<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> ys' ! n \<and> ys' ! n \<le> u"
  proof (intro allI impI)
    fix n
    assume a: "n < length xs"
    hence 1: "Suc n < length (x # xs)" by simp
    have "xs ! n = (x # xs) ! Suc n" by simp
    moreover
    have "ys' ! n = (y' # ys') ! Suc n" using ys' by simp
    ultimately
    show "\<exists>l u. M (xs ! n) = Some (l, u) \<and> l \<le> ys' ! n \<and> ys' ! n \<le> u" using Cons(4)[simplified ys'(1), THEN spec[of _ "Suc n"], THEN mp[OF _ 1]] by simp 
  qed
  with 1 ys'(2) Cons(4)
  have "Simple_Network_Language.bounded M ((v(x \<mapsto> y'))(xs [\<mapsto>] ys'))"
    apply -
    apply (rule Cons.IH)
      apply assumption
    by simp+
  thus ?case unfolding ys'(1) by simp
qed

lemma all_zip_replicate:
  assumes "x \<in> set xs"
  shows "\<forall>m. (x, m) \<in> set (zip xs (replicate (length xs) n)) \<longrightarrow> m = n"
  using assms
proof (induction xs arbitrary: n x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have IH: "\<forall>m. (x, m) \<in> set (zip as (replicate (length as) n)) \<longrightarrow> m = n"
    using Cons apply (cases "x \<in> set as")
     apply simp using set_zip_leftD by metis
  show ?case 
    apply (subst length_Cons)
    apply (subst replicate.simps)
    apply (subst zip_Cons_Cons)
    apply (rule allI)
    subgoal for m
      apply (cases "m = n")
       apply simp
      apply (subst list.set)
      using IH by auto
    done
qed

lemma map_of_determ:
  assumes "\<forall>m. (x, m) \<in> set xs \<longrightarrow> m = n"
          and "(x, n) \<in> set xs"
        shows "map_of xs x = Some n"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain c d where
    a: "a = (c, d)" by fastforce
  then show ?case 
  proof (cases "a = (x,n)")
    case True
    then show ?thesis by simp
  next
    case False
    then 
    consider "x \<noteq> c" | "x = c \<and> n \<noteq> d" using a by blast
    then show ?thesis 
    proof cases
      case 1
      hence "map_of (a # xs) x = map_of xs x" using a map_of_Cons_code by auto
      moreover
      have i: "(x, n) \<in> set xs" using Cons (3) a 1 by auto
      moreover
      from Cons(2) i 1 False a
      have "\<forall>m. (x, m) \<in> set xs \<longrightarrow> m = n" by force
      ultimately
      show ?thesis using Cons.IH by metis
    next
      case 2
      then show ?thesis using a Cons by simp
    qed
  qed
qed

lemma map_upds_with_replicate:
  assumes "x \<in> set xs"
  shows "(v(xs [\<mapsto>] (replicate (length xs) n))) x = Some n"
proof -
  have "(x, n) \<in> set (zip xs (replicate (length xs) n))"
    apply (subst set_zip)
    using length_replicate assms
    using nth_replicate
    by (auto simp: set_conv_nth)
  thus ?thesis
    using assms 
    unfolding map_upds_def 
    apply (subst map_add_find_right)
     apply (rule map_of_determ)
    apply (subst set_rev)
    using all_zip_replicate
    by (fast, auto)
qed


lemma map_upds_with_map:
  assumes "x \<in> set xs"
      and "length xs = length ys"
  shows "(v(xs [\<mapsto>] (map (\<lambda>x. n) ys))) x = Some n"
proof -
  have "\<forall>m. (x, m) \<in> set (zip xs (map (\<lambda>x. n) ys)) \<longrightarrow> m = n"
    apply (subst set_zip)
    by auto
  moreover
  have "(x, n) \<in> set (zip xs (map (\<lambda>x. n) ys))"
    apply (subst set_zip)
    using assms
    by (auto simp: set_conv_nth set_zip)
  ultimately
  show ?thesis
    using assms unfolding map_upds_def 
    apply (subst map_add_find_right)
    by (auto intro: map_of_determ)
qed

lemma distinct_map_upds:
  assumes "x \<in> set xs"
      and "distinct xs"
    shows "(v(xs [\<mapsto>] (map f xs))) x = Some (f x)"
  using assms 
  unfolding map_upds_def
  apply (subst map_add_find_right)
   apply (subst zip_rev[symmetric])
    apply simp
   apply (rule map_of_is_SomeI[where y = "f x"])
    apply simp
   apply (subst zip_rev)
    apply simp
   apply (subst set_rev)
   apply (subst in_set_zip)
   apply (subst (asm) in_set_conv_nth)
  by auto

  
end

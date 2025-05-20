theory Sequences
  imports Base
begin
definition "seq_apply fs x = map (\<lambda>i. (fold (id) (take i fs) x)) [1..<length fs + 1]"

definition "ext_seq f xs \<equiv> xs @ f (last xs)"

definition "ext_seq' fs xs = fold ext_seq fs xs"

definition "seq_apply' fs x = tl (ext_seq' fs [x])"

lemma length_seq_apply[simp]: 
  "length (seq_apply fs s) = length fs"
  unfolding seq_apply_def
  apply (subst length_map)
  apply (subst length_upt)
  by simp

lemma length_ext_seq[simp]:
  "length (ext_seq f xs) = length xs + length (f (last xs))"
  unfolding ext_seq_def by simp

lemma seq_apply_Nil[simp]: "seq_apply [] xs = []" 
  "fs = [] \<Longrightarrow> seq_apply fs x = []" unfolding seq_apply_def by auto

lemma seq_apply_nth_conv_fold:
  assumes "i < length fs"
  shows "(seq_apply fs x) ! i = fold id (take (Suc i) fs) x"
  unfolding seq_apply_def
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_upt)
  using assms apply simp
  by auto

lemma seq_apply_nth_0:
  assumes "0 < length fs"
  shows "seq_apply fs x ! 0 = (fs ! 0) x"
  apply (subst seq_apply_nth_conv_fold[OF assms])
  apply (subst take_Suc_conv_app_nth[OF assms])
  by simp


lemma seq_apply_nth_Suc:
  assumes "Suc i < length fs"
  shows "(seq_apply fs s) ! (Suc i) = (fs ! (Suc i)) ((seq_apply fs s) ! i)"
  apply (subst seq_apply_nth_conv_fold)
  using assms apply simp
  apply (subst seq_apply_nth_conv_fold)
  using assms apply simp
  apply (subst take_Suc_conv_app_nth)
  using assms by auto

lemma seq_apply_Cons_nth:
  assumes "i \<le> length fs"
  shows "(x#(seq_apply fs x)) ! i = fold id (take i fs) x"
  apply (cases i)
   apply simp
  subgoal for i'
    apply (simp)
    apply (subst seq_apply_nth_conv_fold)
    using assms by simp+
  done   

lemma seq_apply_Cons_nth_Suc:
  assumes "i < length fs"
  shows "(x#(seq_apply fs x)) ! (Suc i) = (fs ! i) ((x#(seq_apply fs x)) ! i)"
  apply (subst nth_Cons_Suc)
  apply (subst seq_apply_Cons_nth)
  using assms apply simp
  apply (subst seq_apply_nth_conv_fold)
  using assms apply simp
  apply (subst take_Suc_conv_app_nth[OF assms])
  by simp

lemma seq_apply_not_Nil[simp]:
  assumes "fs \<noteq> []"
  shows "seq_apply fs x \<noteq> []"
  apply (subst length_greater_0_conv[symmetric])
  using assms length_seq_apply 
  by simp

lemma last_seq_apply: 
  assumes "fs \<noteq> []"
  shows "last (seq_apply fs x) = fold id fs x"
  apply (subst last_conv_nth)
  using assms[THEN seq_apply_not_Nil] apply simp
  apply (subst seq_apply_nth_conv_fold)
  using assms apply simp
  apply (subst take_all)
  by simp+

lemma seq_apply_take:
  "take i (seq_apply fs x) = seq_apply (take i fs) x"
  unfolding seq_apply_def
  apply (subst take_map)
  apply (cases "i \<le> length fs")
  apply (subst take_upt, simp)
  apply (subst length_take)
  apply (subst min_absorb2, simp)
  by auto

lemma seq_apply_take_last:
  assumes "i < length fs"
  shows "last (take (Suc i) (seq_apply fs x)) = seq_apply fs x ! i"
  apply (subst take_Suc_conv_app_nth)
  using assms apply simp
  apply (subst last_appendR)
  by simp+

lemma seq_apply_take_last_conv_fold:
  assumes "i < length fs"
  shows "last (take (Suc i) (seq_apply fs x)) = fold id (take (Suc i) fs) x"
  apply (subst seq_apply_take_last)
  using assms apply simp
  apply (subst seq_apply_nth_conv_fold[OF assms])
  by auto

lemma seq_apply_last_conv_fold:
  assumes "0 < length fs"
  shows "last (seq_apply fs x) = fold id fs x"
  apply (subst take_all[symmetric, of fs "Suc (length fs - 1)"])
   apply simp
  apply (subst seq_apply_take[symmetric])
  apply (subst seq_apply_take_last_conv_fold)
  using assms apply simp
  apply (subst take_all)
  by simp+

lemma take_Suc_not_Nil:
  assumes "xs \<noteq> []"
  shows "take (Suc n) xs \<noteq> []"
  using assms by simp

lemma seq_apply_Cons_take_last:
  assumes "i \<le> length fs"
  shows "last (take (Suc i) (x#(seq_apply fs x))) = (x#seq_apply fs x) ! i"
  apply (cases i)
   apply simp
  subgoal 
    apply (subst take_Suc_Cons)
    apply (rule ssubst[of i], assumption)
    apply (subst nth_Cons_Suc)
    apply (subst last_ConsR)
    apply (rule take_Suc_not_Nil)
     apply (rule seq_apply_not_Nil)
    using assms apply fastforce
    apply (rule seq_apply_take_last)
    using assms by simp
  done

lemma seq_apply_take_Suc_Cons: 
  assumes "i \<le> length fs" 
  shows "take (Suc i) (seq_apply (f#fs) x) = f x # (take i (seq_apply fs (f x)))"
proof -
  have 1: "[Suc 1..<length (f # take i fs) + 1]  = map Suc [1..<length (take i fs) + 1]" 
    apply (subst length_Cons)
    apply (subst length_take)+
    apply (subst min_absorb2[OF assms])+
    apply (induction i) by simp+

  have 2: "map (\<lambda>ia. fold (\<lambda>x. x) (take ia (f # take i fs)) x) [Suc 1..<length (f # take i fs) + 1] =
    map (\<lambda>ia. fold (\<lambda>x. x) (take ia (take i fs)) (f x)) [1..<length (take i fs) + 1]" 
    apply (subst 1)
    apply (subst map_map)
    apply (subst comp_def)
    apply (subst take_Suc_Cons)
    apply (subst fold_Cons)
    apply (subst comp_def)
    by (rule HOL.refl)

  show ?thesis
    apply (subst seq_apply_take)
    apply (subst take_Suc_Cons)
    apply (subst seq_apply_take)
    unfolding seq_apply_def
    apply (subst upt_conv_Cons)
     apply simp
    apply (subst list.map)
    apply (subst One_nat_def)
    apply (subst take_Suc_Cons)
    apply (subst take_0)
    apply (subst fold.simps)+
    apply (subst id_def)+
    apply (subst comp_def)
    apply (subst 2)
    by blast
qed

lemma seq_apply_1:
  "seq_apply [f] x = [f x]"
  unfolding seq_apply_def by simp

lemma take_append_left:
  "take (length xs) (xs @ ys) = xs"
  by simp


lemma seq_apply_append_1:
  assumes "fs \<noteq> []"
  shows "(seq_apply (fs @ [g']) x) = seq_apply fs x @ [g' (last (x#seq_apply fs x))]"
  apply (cases fs)
  using assms apply simp
  subgoal for f' fs'
    apply (subst take_all[symmetric, of "fs @ [g']" "Suc (length fs)"])
    apply simp
    apply (subst seq_apply_take[symmetric])
    apply (subst take_Suc_conv_app_nth)
     apply simp
    apply (subst seq_apply_take)
    apply (subst take_append_left)
    apply (erule ssubst)
    apply (subst seq_apply_nth_conv_fold)
     apply simp
    apply (subst take_Suc_conv_app_nth)
     apply simp
    apply (subst take_append_left)
    apply (subst nth_append_length)
    apply (subst last_ConsR)
     apply simp
    apply (subst seq_apply_last_conv_fold)
    by simp+
  done 
   

lemma seq_apply_Cons_append_1:
  "x # (seq_apply (fs @ [g']) x) = x#seq_apply fs x @ [g' (last (x#seq_apply fs x))]"
  apply (cases fs)
   apply (erule ssubst)
   apply (simp add: seq_apply_1)
  using seq_apply_append_1
  by fast

lemma ext_seq_seq_apply_take_append:
  assumes xs: "xs \<noteq> []"
      and i: "i \<le> length gs"
    shows "xs @ seq_apply (fs @ take i gs) (last xs) = (xs @ seq_apply fs (last xs)) @ take i (seq_apply gs (last (xs @ seq_apply fs (last xs))))" 
  using assms
proof (induction i arbitrary: fs xs gs)
  case 0
  then show ?case by simp
next
  case (Suc i)
  obtain g' gs' where
    gs: "gs = g'#gs'" using Suc by (cases gs; auto)

  consider (n) "fs = []" | (s) "fs \<noteq> []" by blast
  note c = this

  have "xs @ seq_apply (fs @ take (Suc i) gs) (last xs) = xs @ seq_apply ((fs @ [g']) @ take i gs') (last xs)" using gs by auto
  hence 1: "xs @ seq_apply (fs @ take (Suc i) gs) (last xs)= (xs @ seq_apply (fs @ [g']) (last xs)) @ take i (seq_apply gs' (last (xs @ seq_apply (fs @ [g']) (last xs))))" 
    apply (subst (asm) Suc.IH) using gs Suc by auto
  show ?case
  proof (cases rule: c)
    case n
    show ?thesis
      apply (subst 1)
      unfolding gs
      apply (subst seq_apply_take_Suc_Cons)
      using gs Suc apply simp
      unfolding n
      by (simp add: seq_apply_1)
  next
    case s
    show ?thesis 
      apply (subst 1)
      unfolding seq_apply_append_1[OF s]
      apply (subst last_ConsR, simp add: s)+
      apply (subst last_appendR, simp)+
      apply (subst last_ConsL, simp) 
      unfolding gs
      apply (subst seq_apply_take_Suc_Cons)
      using gs Suc apply simp
      apply (subst last_appendR, simp add: s)+
      by simp
  qed 
qed
    


lemma ext_seq_seq_apply_append_take: 
  assumes xs: "xs \<noteq> []"
      and i2: "i \<le> length xs + length (fs @ gs)"
  shows "take i (ext_seq (seq_apply gs) (ext_seq (seq_apply fs) xs)) = take i (ext_seq (seq_apply (fs @ gs)) xs)"
proof (cases "i \<le> length xs")
  case i: True
  show ?thesis unfolding ext_seq_def using i by simp
next
  case i: False
  then show ?thesis 
  proof (cases "i \<le> length xs + length fs")
    case i1: True
    from i i1
    have i0: "i - (length xs + length fs) = 0" "i - length xs - length fs = 0" by simp+
    
    show ?thesis 
      unfolding ext_seq_def
      apply (subst take_append)
      apply (subst length_append)
      apply (subst length_seq_apply)
      apply (subst (2) take_append)
      apply (subst (2) seq_apply_take)
      apply (subst (2) take_append)
      apply (subst i0)+
      apply (subst take0)+
      apply (subst append_Nil2)+
      apply (subst seq_apply_take[symmetric])
      apply (subst take_append[symmetric])
      by simp
  next
    case i1: False
  
    from i i1 i2
    
    show ?thesis 
        unfolding ext_seq_def
        apply (subst take_append)
        apply (subst length_append)
        apply (subst length_seq_apply)
        apply (subst take_all)
         apply simp
        apply (subst take_append)
        apply (subst (2) take_all)
         apply simp
        apply (subst (2) seq_apply_take)
        apply (subst take_append)
        apply (subst (2) take_all)
         apply simp
        apply (subst ext_seq_seq_apply_take_append)
          apply simp
        using xs apply simp
         apply simp
        by simp
  qed
qed

lemma ext_seq_seq_apply_append_distrib:
  assumes "xs \<noteq> []"
  shows "(ext_seq (seq_apply gs) (ext_seq (seq_apply fs) xs)) = (ext_seq (seq_apply (fs @ gs)) xs)"
  apply (subst take_all[symmetric, of "ext_seq (seq_apply gs) (ext_seq (seq_apply fs) xs)" "length xs + length fs + length gs"])
  apply simp
  apply (subst ext_seq_seq_apply_append_take)
  using assms apply simp
   apply simp
  apply (subst take_all)
  by simp+

context
  fixes fs::"('a \<Rightarrow> 'a) list"
    and P Q::"nat \<Rightarrow>'a \<Rightarrow> bool"
    and R::"'a \<Rightarrow> bool"
    and S::"'a \<Rightarrow> bool"
  assumes PQ: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> (Q i ((fs ! i) s))"
      and QP: "\<And>i s. Suc i < length fs \<Longrightarrow> Q i s \<Longrightarrow> P (Suc i) s"
begin

(* In progress: Consider how pre- and post-conditions work when there is a conditional delay *)

(* The implications only hold when there are actual functions.
  Therefore, we need to first consider cases in which there are some functions *)
lemma seq_apply_pre_post_induct_steps_pre:
  assumes i: "i < length fs"
      and Px0: "P 0 x"
    shows "P i ((x#seq_apply fs x) ! i)"
  using i
proof (induction i)
  case 0
  then show ?case using Px0 by simp
next
  case (Suc i)
  hence i: "i < length fs" by simp
  show ?case 
    apply (rule QP[OF Suc(2)])
    apply (subst seq_apply_Cons_nth_Suc[OF i])
    apply (rule PQ[OF i])
    using Suc by simp
qed

lemma seq_apply_pre_post_induct_steps_post:
  assumes i: "i < length fs"
      and Px0: "P 0 x"
    shows "Q i ((x#seq_apply fs x) ! (Suc i))"
  apply (subst seq_apply_Cons_nth_Suc[OF i])
  apply (rule PQ[OF i])
  by (rule seq_apply_pre_post_induct_steps_pre[OF assms])


lemma seq_apply_pre_post_induct_length_post:
  assumes l: "0 < length fs"
      and Px0: "P 0 x"
    shows "Q (length fs - 1) (last (x#seq_apply fs x))"
proof - 
  have "Q (length fs - 1) ((x # seq_apply fs x) ! Suc (length fs - 1))" 
    using seq_apply_pre_post_induct_steps_post[of "length fs - 1", OF _ Px0] l by simp
  thus ?thesis
    apply (subst (asm) seq_apply_Cons_nth)
    using assms apply simp
    apply (subst last_conv_nth, simp)
    apply (subst seq_apply_Cons_nth, simp add: assms)
    apply (subst take_all, simp)
    apply (subst (asm) take_all)
    by simp+
qed

lemma seq_apply_pre_post_induct_weaken_pre_strengthen_post:
  assumes Rx0: "R x"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. Q (length fs - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. 0 = length fs \<Longrightarrow> R x \<Longrightarrow> S x"
    shows "S (last (x#seq_apply fs x))"
  apply (cases fs)
  subgoal 
    apply (rule ssubst[of fs], assumption)
    apply (subst seq_apply_Nil)
    using RS0 Rx0 by simp+
  subgoal for f fs'
    apply (rule QSl)
    apply (rule seq_apply_pre_post_induct_length_post, simp)
    apply (rule RP0, simp)
    by (rule Rx0)
  done

lemma last_append_conv_last_Cons: "last (xs @ ys) = last ((last xs) # ys)"
  by simp

lemma ext_seq_pre_post_induct_weaken_pre_strengthen_post:
  assumes Rx0: "R (last xs)"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. Q (length fs - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. length fs = 0\<Longrightarrow> R x \<Longrightarrow> S x"
    shows "S (last (ext_seq (seq_apply fs) xs))"
  apply (subst ext_seq_def)
  apply (subst last_append_conv_last_Cons)
  apply (rule seq_apply_pre_post_induct_weaken_pre_strengthen_post)
  using assms by simp+

lemma seq_apply_take_induct_list_prop:
  assumes base: "\<And>x. LP [x]"
      and step: "\<And>xs ys. LP xs \<Longrightarrow> LP (last xs # ys) \<Longrightarrow> LP (xs @ ys)"
      and Rx0: "R x"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and r: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> LP [s, (fs ! i) s]"
      and i: "0 < i" "i \<le> length fs + 1"
    shows "LP (take i (x#seq_apply fs x))"
proof -
  { fix j
    assume "j \<le> length fs"
    hence "LP (take (Suc j) (x # seq_apply fs x))"
      apply (induction j)
      subgoal apply (subst take_Suc_Cons) 
        apply (subst take_0)
        by (rule base)
      subgoal for j'
        apply (subst take_Suc_conv_app_nth)
        apply simp
        apply (subst seq_apply_Cons_nth_Suc)
        apply simp
        apply (rule step)
         apply simp
        apply (subst seq_apply_Cons_take_last)
         apply simp
        apply (rule r)
          apply simp
        using seq_apply_pre_post_induct_steps_pre Rx0 RP0 by fastforce
      done
  } note j = this
  show ?thesis
  apply (cases i)
    using i apply simp
    subgoal for j
      using j i by simp
    done
qed

(* Later used to instantiate the induction principle for steps *)
lemma seq_apply_induct_list_prop:
  assumes base: "\<And>x. LP [x]"
      and step: "\<And>xs ys. LP xs \<Longrightarrow> LP (last xs # ys) \<Longrightarrow> LP (xs @ ys)"
      and Rx0: "R x"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and ind_step: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> LP [s, (fs ! i) s]"
    shows "LP (x#seq_apply fs x)"
  apply (subst take_all[symmetric])
   apply (rule order.refl)
  apply (rule seq_apply_take_induct_list_prop)
  using assms by simp+

lemma ext_seq_induct_list_prop:
  assumes base: "\<And>x. LP [x]"
      and step: "\<And>xs ys. LP xs \<Longrightarrow> LP (last xs # ys) \<Longrightarrow> LP (xs @ ys)"
      and LPxs: "LP xs"
      and Rx0: "R (last xs)"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and ind_step: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> LP [s, (fs ! i) s]"
    shows "LP (ext_seq (seq_apply fs) xs)"
  unfolding ext_seq_def
  apply (rule step)
   apply (rule LPxs)
  apply (rule seq_apply_induct_list_prop)
  using assms by simp+


end

lemma ext_seq_last:
  assumes f_wf: "\<And>s. f s \<noteq> []"
  shows "last (ext_seq f xs) = last (f (last xs))"
  unfolding ext_seq_def
  apply (subst last_append)
  using f_wf by simp

lemma ext_seq_not_Nil:
  "xs \<noteq> [] \<Longrightarrow> ext_seq f xs \<noteq> []"
  "f (last xs) \<noteq> [] \<Longrightarrow> ext_seq f xs \<noteq> []"
  unfolding ext_seq_def by simp+

lemma ext_seq'_Cons:
  "ext_seq' (f#fs) xs = ext_seq' fs (ext_seq f xs)"
  unfolding ext_seq'_def
  by simp

lemma ext_seq'_with_Nil:
  "ext_seq' [] xs = xs"
  "fs = [] \<Longrightarrow> ext_seq' fs xs = xs"
  unfolding ext_seq'_def by simp+

lemma ext_seq'_take_0:
  "ext_seq' (take 0 fs) xs = xs"
  using ext_seq'_with_Nil by simp

lemma ext_seq'_not_Nil:
  assumes xs_not_Nil: "xs \<noteq> []"
    shows "ext_seq' fs xs \<noteq> []"
  using assms
  apply (induction fs arbitrary: xs)
   apply (subst ext_seq'_with_Nil)
  apply simp
  subgoal for f' fs' xs
    apply (subst ext_seq'_Cons)
    using ext_seq_not_Nil(1) by auto
  done

lemma ext_seq'_take_Suc:
  assumes i: "i < length fs"
  shows "ext_seq' (take (Suc i) fs) xs = ext_seq (fs ! i) (ext_seq' (take i fs) xs)"
  unfolding ext_seq'_def
  using assms 
  apply (subst take_Suc_conv_app_nth[OF i])
  by simp

lemma tl_ext_seq'_single:
  "tl (ext_seq' [] [x]) = []"
  apply (subst ext_seq'_with_Nil)
  by simp

lemma tl_fold_ext_seq_Nil:
  "tl (fold ext_seq [] xs) = tl xs" 
  "fs = [] \<Longrightarrow> tl (fold ext_seq fs xs) = tl xs"
  by simp+

lemma tl_ext_seq_not_Nil:
  "xs \<noteq> [] \<Longrightarrow> tl (ext_seq f xs) = tl xs @ (f (last xs))"
  unfolding ext_seq_def by simp

lemma ext_seq_conv_last:
  assumes "xs \<noteq> []"
  shows "ext_seq f xs = xs @ tl (ext_seq f [last xs])"
  apply (subst ext_seq_def)+
  by simp

lemma ext_seq_last_of_last:
  "last (ext_seq f xs) = last (ext_seq f [last xs])"
  unfolding ext_seq_def
  by simp

lemma ext_seq_fold_Cons:
  "fold ext_seq (f#fs) xs = ext_seq f xs @ tl (fold ext_seq fs [last (ext_seq f xs)])"
proof (induction fs arbitrary: f xs)
  case Nil
  then show ?case by simp
next
  case (Cons f' fs')
  show ?case 
    apply (subst fold_Cons)
    apply (subst comp_apply)
    apply (subst Cons.IH)
    apply (subst ext_seq_def)
    apply (subst Cons.IH)
    apply (subst (6) ext_seq_def)
    apply (subst append.simps)+
    apply (subst list.sel)
    apply (subst last_ConsL)
     apply simp
    apply (subst ext_seq_last_of_last[symmetric])
    by simp
qed

 
lemma ext_seq'_append:
  "ext_seq' (fs @ gs) xs = ext_seq' gs (ext_seq' fs xs)"
  unfolding ext_seq'_def by simp

lemma ext_seq'_as_seq_apply':
  "ext_seq' fs xs = xs @ seq_apply' fs (last xs)"
  unfolding seq_apply'_def ext_seq'_def
proof (induction fs arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  show ?case 
    apply (subst fold_Cons)
    apply (subst comp_def)
    apply (subst Cons.IH)
    apply (subst ext_seq_fold_Cons)
    apply (subst tl_append2)
    using ext_seq_not_Nil apply blast
    apply (subst tl_ext_seq_not_Nil)
     apply simp
    apply (subst list.sel)
    apply (subst ext_seq_last_of_last[symmetric])
    apply (subst ext_seq_def)
    by simp
qed

lemma tl_fold_ext_seq:
  assumes "xs \<noteq> []"
  shows "tl (fold ext_seq fs (x # xs)) = fold ext_seq fs (xs)"
  using assms
proof (induction fs arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs xs)
  then show ?case 
    apply (subst fold_Cons)
    apply (subst comp_def)
    apply (subst ext_seq_def)
    apply (subst append.simps)
    apply (subst Cons.IH)
    apply blast
    apply (subst fold_Cons, subst comp_def)
    apply (subst ext_seq_def)
    by simp
qed


lemma seq_apply'_as_ext_seq':
  assumes "f x \<noteq> []"
  shows "seq_apply' (f#fs) x = ext_seq' fs (f x)"
  unfolding ext_seq'_def seq_apply'_def
  apply (subst fold_Cons)
  apply (subst comp_def)
  apply (subst ext_seq_def)
  apply (subst append.simps)+
  apply (subst last_ConsL)
   apply simp
  apply (subst tl_fold_ext_seq[OF assms])
  by blast

lemma seq_apply'_not_Nil:
  assumes "\<And>f s. f \<in> set fs \<Longrightarrow> f s \<noteq> []"
    and "0 < length fs"
    shows "seq_apply' fs x \<noteq> []"
  using assms
  apply (induction fs)
   apply simp
  subgoal for f fs
    apply (subst seq_apply'_as_ext_seq')
     apply simp
    using ext_seq'_not_Nil
    by auto
  done

context 
  fixes fs::"('a \<Rightarrow> 'a list) list"
      and P Q::"nat \<Rightarrow>'a \<Rightarrow> bool"
      and R::"'a \<Rightarrow> bool"
      and S::"'a \<Rightarrow> bool"
  assumes f_wf: "\<And>f x. f \<in> set fs \<Longrightarrow> f x \<noteq> []"
      and PQ: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> (Q i (last ((fs ! i) s)))"
      and QP: "\<And>i s. i < length fs - 1 \<Longrightarrow> Q i s \<Longrightarrow> P (Suc i) s"
begin

lemma ext_seq'_pre_post_induct_steps_pre:
  assumes i: "i < length fs"
      and Px0: "P 0 (last xs)"
    shows "P i (last (ext_seq' (take i fs) xs))"
  using i
proof (induction i)
  case 0
  then show ?case apply (subst ext_seq'_take_0) by (rule Px0)
next
  case (Suc i)
  have i: "i < length fs - 1" using Suc by linarith
  show ?case 
    apply (subst ext_seq'_take_Suc)
    using i apply simp
    apply (rule QP)
    using i apply simp
    apply (subst ext_seq_last)
    using i f_wf apply simp
    apply (rule PQ)
    using i apply simp
    using Suc by linarith
qed

lemma ext_seq'_pre_post_induct_steps_post:
  assumes i: "i < length fs"
      and Px0: "P 0 (last xs)"
    shows "Q i (last (ext_seq (fs ! i) (ext_seq' (take i fs) xs)))"
  apply (subst ext_seq_last)
  using i f_wf apply simp
  apply (rule PQ[OF i])
  by (rule ext_seq'_pre_post_induct_steps_pre[OF assms])

lemma ext_seq'_pre_post_induct_length_post:
  assumes l: "0 < length fs"
      and Px0: "P 0 (last xs)"
    shows "Q (length fs - 1) (last (ext_seq' fs xs))"
  apply (subst (2) take_all[symmetric, where n = "Suc (length fs - 1)"])
  using l apply simp
  apply (subst ext_seq'_take_Suc)
  using l apply simp
  apply (rule ext_seq'_pre_post_induct_steps_post)
  using assms
  by simp+

lemma ext_seq'_pre_post_induct_weaken_pre_strengthen_post:
  assumes Rx0: "R (last xs)"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. Q (length fs - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. 0 = length fs \<Longrightarrow> R x \<Longrightarrow> S x"
    shows "S (last (ext_seq' fs xs))"
  apply (cases fs)
  subgoal
    apply (rule ssubst[of fs], assumption)
    apply (subst ext_seq'_with_Nil)
    apply (rule RS0)
     apply simp
    by (rule Rx0)
  subgoal for f fs'
    apply (rule QSl)
    apply (rule ext_seq'_pre_post_induct_length_post)
     apply simp
    apply (rule RP0)
     apply simp
    by (rule Rx0)
  done

lemma ext_seq'_take_induct_list_prop:
  assumes step: "\<And>xs ys. LP xs \<Longrightarrow> LP (last xs # ys) \<Longrightarrow> LP (xs @ ys)"
      and LPxs: "LP xs"
      and Rx0: "R (last xs)"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and r: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> LP (s#(fs ! i) s)"
      and i: "i \<le> length fs"
    shows "LP (ext_seq' (take i fs) xs)"
proof -
  { assume "0 < length fs" "i \<le> length fs"
    hence "LP (ext_seq' (take i fs) xs)"
      apply (induction i)
       apply (subst ext_seq'_take_0)
       apply (rule LPxs)
      subgoal for i'
        apply (subst ext_seq'_take_Suc)
         apply simp
        apply (subst ext_seq_def)
        apply (rule step)
         apply simp
        apply (rule r)
         apply simp
        apply (rule ext_seq'_pre_post_induct_steps_pre)
         apply simp
        apply (rule RP0)
         apply simp
        by (rule Rx0)
      done
  } note not_Nil = this

  show ?thesis
  proof (cases "length fs")
    case 0
    hence i: "i = 0" using i by simp
    show ?thesis 
      apply (subst i) 
      apply (subst ext_seq'_take_0)
      by (rule LPxs)
  next
    case (Suc nat)
    then show ?thesis using i not_Nil by simp
  qed
qed

lemma ext_seq'_induct_list_prop:
  assumes step: "\<And>xs ys. LP xs \<Longrightarrow> LP (last xs # ys) \<Longrightarrow> LP (xs @ ys)"
      and LPxs: "LP xs"
      and Rx0: "R (last xs)"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and r: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> LP (s#(fs ! i) s)"
    shows "LP (ext_seq' fs xs)"
  apply (subst take_all[symmetric])
   apply (rule order.refl)
  apply (rule ext_seq'_take_induct_list_prop)
  using assms by simp+

lemma seq_apply'_pre_post_induct_weaken_pre_strengthen_post:
    assumes Rx0: "R x"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. Q (length fs - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. 0 = length fs \<Longrightarrow> R x \<Longrightarrow> S x"
      and l: "0 < length fs"
    shows "S (last (seq_apply' fs x))"
  apply (subst last_ConsR[symmetric, of _ x])
   apply (subst seq_apply'_not_Nil)
  using f_wf apply simp
  using l apply simp
   apply simp
  apply (subst ext_seq'_as_seq_apply'[symmetric, of "[x]", simplified])
  apply (rule ext_seq'_pre_post_induct_weaken_pre_strengthen_post)
  using assms by simp+

lemma seq_apply'_induct_list_prop:
  assumes base: "\<And>x. LP [x]"
      and step: "\<And>xs ys. LP xs \<Longrightarrow> LP (last xs # ys) \<Longrightarrow> LP (xs @ ys)"
      and Rx0: "R x"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and r: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> LP (s#(fs ! i) s)"
    shows "LP (x#seq_apply' fs x)"
  apply (subst ext_seq'_as_seq_apply'[symmetric, of "[x]", simplified])
  apply (rule ext_seq'_induct_list_prop)
  using assms by simp_all
  
end
end
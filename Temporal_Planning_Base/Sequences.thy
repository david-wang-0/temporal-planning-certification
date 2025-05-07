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

lemma seq_apply_nth:
  assumes "i < length fs"
  shows "(seq_apply fs x) ! i = fold id (take (Suc i) fs) x"
  unfolding seq_apply_def
  apply (subst nth_map)
  using assms apply simp
  apply (subst nth_upt)
  using assms apply simp
  by auto

lemma seq_apply_nth_Suc:
  assumes "Suc i < length fs"
  shows "(seq_apply fs s) ! (Suc i) = (fs ! (Suc i)) ((seq_apply fs s) ! i)"
  apply (subst seq_apply_nth)
  using assms apply simp
  apply (subst seq_apply_nth)
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
    apply (subst seq_apply_nth)
    using assms by simp+
  done   

lemma seq_apply_Cons_nth_Suc:
  assumes "i < length fs"
  shows "(x#(seq_apply fs x)) ! (Suc i) = (fs ! i) ((x#(seq_apply fs x)) ! i)"
  apply (subst nth_Cons_Suc)
  apply (subst seq_apply_Cons_nth)
  using assms apply simp
  apply (subst seq_apply_nth)
  using assms apply simp
  apply (subst take_Suc_conv_app_nth[OF assms])
  by simp

lemma seq_apply_not_Nil:
  assumes "fs \<noteq> []"
  shows "seq_apply fs x \<noteq> []"
  apply (subst length_greater_0_conv[symmetric])
  using assms length_seq_apply 
  by simp

lemma seq_apply_Nil: "seq_apply [] x = []"
  unfolding seq_apply_def by auto

lemma last_seq_apply: 
  assumes "fs \<noteq> []"
  shows "last (seq_apply fs x) = fold id fs x"
  apply (subst last_conv_nth)
  using assms[THEN seq_apply_not_Nil] apply simp
  apply (subst seq_apply_nth)
  using assms apply simp
  apply (subst take_all)
  by simp+


(* Precondition: the 0th state x must satisfy P *)
(* The first state Q (fs ! 0) x must satisfy Q 0 *)
(* Assuming the length of fs is 0, this is the final state *)
(* Assuming the length of fs is greater than 0, this state satisfies P 1 *)
(* the ith state (x#seq_apply fs x) ! i assuming i \<le> length fs*)
(* Does the post-condition only have to hold when Suc i < length fs? Yes. We do not want 
a vacuous post-condition to hold *)
(* The pre to post condition. The final state is (fs ! (length fs - 1)) s 
  For this, we want *)
context
  fixes fs::"('a \<Rightarrow> 'a) list"
    and P Q::"nat \<Rightarrow>'a \<Rightarrow> bool"
    and R::"'a \<Rightarrow> bool"
    and S::"'a \<Rightarrow> bool"
  assumes PQ: "\<And>i s. i < length fs \<Longrightarrow> P i s \<Longrightarrow> (Q i ((fs ! i) s))"
      and QP: "\<And>i s. Suc i < length fs \<Longrightarrow> Q i s \<Longrightarrow> P (Suc i) s"
begin

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
    apply (subst last_conv_nth)
     apply simp
    apply (subst seq_apply_Cons_nth)
    using assms apply simp
    apply (subst take_all)
     apply simp
    apply (subst (asm) take_all)
    by simp+
qed
 
lemma seq_apply_pre_post_induct_weaken_pre_strengthen_post:
  assumes i: "i \<le> length fs"
      and Rx0: "R x"
      and RP0: "\<And>x. 0 < length fs \<Longrightarrow> R x \<Longrightarrow> P 0 x"
      and QSl: "\<And>x. Q (length fs - 1) x \<Longrightarrow> S x"
      and RS0: "\<And>x. 0 = length fs \<Longrightarrow> R x \<Longrightarrow> S x"
    shows "S (last (x#seq_apply fs x))"
  apply (cases fs)
  subgoal 
    apply (rule ssubst[of fs], assumption)
    apply (subst seq_apply_Nil)
    using RS0 Rx0 by simp
  subgoal for f fs'
    apply (rule QSl)
    apply (rule seq_apply_pre_post_induct_length_post)
     apply simp
    apply (rule RP0)
     apply simp
    by (rule Rx0)
  done

end

context
  fixes fs::"('a \<Rightarrow> 'a list) list"
  assumes f_wf: "\<And>f x. f \<in> set fs \<Longrightarrow> f x \<noteq> []"
begin
thm ext_seq'_def

end

context 
  fixes fs::"('a \<Rightarrow> 'a list) list"
      and P Q::"nat \<Rightarrow>'a \<Rightarrow> bool"
      and R::"'a \<Rightarrow> bool"
      and S::"'a \<Rightarrow> bool"
  assumes f_wf: "\<forall>f \<in> set fs. \<forall>x. f x \<noteq> []"
      and PQ: "\<forall>i < length fs. \<forall>s. P i s \<longrightarrow> (Q i (last ((fs ! i) s)))"
      and QP: "\<forall>i < length fs - 1. \<forall>s. Q i s\<longrightarrow> P (Suc i) s"
begin

end
end
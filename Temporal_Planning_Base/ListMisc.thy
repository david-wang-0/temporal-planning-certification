theory ListMisc
  imports "Automatic_Refinement.Misc"
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
end

end
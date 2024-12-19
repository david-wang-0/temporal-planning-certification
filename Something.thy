theory Something
  imports Compilation
begin
  context temporal_plan
  begin

text \<open>Numbering for snap_actions. This is hard to work with.\<close>
definition snap::"nat \<Rightarrow> 'snap_action" where
"snap n \<equiv> if (n mod 2 = 0) then (at_start (act (n div 2))) else (at_end (act (n div 2)))"

lemma "bij_betw snap {n. n < 2 * M} (at_start ` actions \<union> at_end ` actions)"
proof -
  have 1: "bij_betw snap {n. n < 2 * M \<and> n mod 2 = 0} (at_start ` actions)"
  proof -
    have "inj_on snap {n. n < 2 * M \<and> n mod 2 = 0}"
    proof (rule inj_onI)
      fix x y
      assume a: "x \<in> {n. n < 2 * M \<and> n mod 2 = 0}" 
             "y \<in> {n. n < 2 * M \<and> n mod 2 = 0}" 
             "snap x = snap y" 
      
      hence 0: "x div 2 \<in> {m. m < M}"
            "y div 2 \<in> {m. m < M}" by auto
      
      from this[simplified ] action_numbering[THEN bij_betw_apply]
      have 1: "act (x div 2) \<in> actions"
           "act (y div 2) \<in> actions"
        by blast+
      
      from a
      have 2: "at_start (act (x div 2)) = at_start (act (y div 2))"  
        using snap_def by auto
      
      from 1 2
      have "act (x div 2) = act (y div 2)" 
        using at_start_inj_on
        by (blast dest: inj_onD)
      hence "x div 2 = y div 2" using act_inj_on[simplified inj_on_def] 0[simplified ] by blast
      moreover
      from a
      have "x mod 2 = y mod 2" by simp
      ultimately
      show "x = y" by (metis div_mod_decomp)
    qed
    moreover
    have "snap ` {n. n < 2 * M \<and> n mod 2 = 0} = (at_start ` actions)"
    proof (rule equalityI; rule subsetI)
      fix x
      assume "x \<in> snap ` {n. n < 2 * M \<and> n mod 2 = 0}"
      then obtain n where
        n: "n \<in> {n. n < 2 * M}"
        "n mod 2 = 0"
        "snap n = x"  by auto
      hence "n div 2 \<in> {n. n < M}" by auto
      hence "act (n div 2) \<in> actions" using act_img_actions by blast
      with n(2, 3)[simplified snap_def]
      show "x \<in> at_start ` actions" using action_numbering
        by auto
    next
      fix x
      assume "x \<in> at_start ` actions"
      then obtain a where
        xa: "x = at_start a"
        "a \<in> actions"
        by force
      
      hence 1: "a \<in> act ` {n. n < M}" using act_img_actions
        by simp
      
      have 2: "(\<lambda>n. n div 2) ` {n. n < 2 * M} = {n. n < M}"
      proof (rule equalityI; rule subsetI)
        fix x 
        assume "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * M}"
        then obtain n where
          "x = n div 2"
          "n < 2 * M"
          by blast
        hence "x < M" by linarith
        thus "x \<in> {n. n < M}"
          by simp
      next 
        fix x
        assume "x \<in> {n. n < M}"
        hence "x < M" by simp
        hence "2 * x < 2 * M" by simp
        then obtain n where
          "n div 2 = x"
          "n < 2 * M"
          using div_mult_self1_is_m zero_less_numeral by blast
        thus "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * M}"
          by blast
      qed
      
      have 3: "{n div 2 | n. n < 2 * M \<and> n mod 2 = 0} = {n div 2 | n. n < 2 * M}"
      proof (rule equalityI; rule subsetI)
        show "\<And>x. x \<in> {n div 2 |n. n < 2 * M \<and> n mod 2 = 0} \<Longrightarrow> x \<in> {n div 2 |n. n < 2 * M}" by blast
      next
        fix x
        assume "x \<in> {n div 2 |n. n < 2 * M}" 
        then obtain n where
          n: "n < 2 * M"
          "n div 2 = x" by blast
        have "\<exists>m. m < 2 * M \<and> m mod 2 = 0 \<and> m div 2 = x"
        proof (cases "n mod 2 = 0")
          case True
          with n
          show ?thesis by metis
        next
          case False
          then have "n mod 2 = 1" by auto
          hence "(n - 1) div 2 = n div 2" "(n - 1) mod 2 = 0" by presburger+
          moreover
          have "n - 1 < 2 * M" using n(1) by linarith
          ultimately
          show ?thesis using n(2) by meson
        qed
        thus "x \<in> {n div 2 |n. n < 2 * M \<and> n mod 2 = 0}" by auto
      qed
      
      have "a \<in> act ` {n div 2 | n. n < 2 * M \<and> n mod 2 = 0}"  
        using 1[simplified 2[symmetric]]
        by (subst 3, blast)
      with xa
      show "x \<in> snap ` {n. n < 2 * M \<and> n mod 2 = 0}"
        unfolding snap_def by auto
    qed
    ultimately
    show "bij_betw snap {n. n < 2 * M \<and> n mod 2 = 0} (at_start ` actions)"
      using bij_betw_imageI by blast
  qed
  have 2: "bij_betw snap {n. n < 2 * M \<and> n mod 2 = 1} (at_end ` actions)"
  proof -
    have "inj_on snap {n. n < 2 * M \<and> n mod 2 = 1}"
    proof (rule inj_onI)
      fix x y
      assume a: "x \<in> {n. n < 2 * M \<and> n mod 2 = 1}" 
             "y \<in> {n. n < 2 * M \<and> n mod 2 = 1}" 
             "snap x = snap y" 
      
      hence 0: "x div 2 \<in> {m. m < M}"
            "y div 2 \<in> {m. m < M}" by auto
      
      from this[simplified ] action_numbering[THEN bij_betw_apply]
      have 1: "act (x div 2) \<in> actions"
           "act (y div 2) \<in> actions"
        by blast+
      
      from a
      have 2: "at_end (act (x div 2)) = at_end (act (y div 2))"  
        using snap_def by auto
      
      from 1 2
      have "act (x div 2) = act (y div 2)" 
        using at_end_inj_on
        by (blast dest: inj_onD)
      hence "x div 2 = y div 2" using act_inj_on[simplified inj_on_def] 0[simplified ] by blast
      moreover
      from a
      have "x mod 2 = y mod 2" by simp
      ultimately
      show "x = y" by (metis div_mod_decomp)
    qed
    moreover
    have "snap ` {n. n < 2 * M \<and> n mod 2 = 1} = (at_end ` actions)"
    proof (rule equalityI; rule subsetI)
      fix x
      assume "x \<in> snap ` {n. n < 2 * M \<and> n mod 2 = 1}"
      then obtain n where
        n: "n \<in> {n. n < 2 * M}"
        "n mod 2 = 1"
        "snap n = x" by auto
      hence "n div 2 \<in> {n. n < M}" by auto
      hence "act (n div 2) \<in> actions" using act_img_actions by blast
      with n(2, 3)[simplified snap_def]
      show "x \<in> at_end ` actions" using action_numbering
        by auto
    next
      fix x
      assume "x \<in> at_end ` actions"
      then obtain a where
        xa: "x = at_end a"
        "a \<in> actions"
        by force
      
      hence 1: "a \<in> act ` {n. n < M}" using act_img_actions by simp
      
      have 2: "(\<lambda>n. n div 2) ` {n. n < 2 * M} = {n. n < M}"
      proof (rule equalityI; rule subsetI)
        fix x 
        assume "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * M}"
        then obtain n where
          "x = n div 2"
          "n < 2 * M"
          by blast
        hence "x < M" by linarith
        thus "x \<in> {n. n < M}"
          by simp
      next 
        fix x
        assume "x \<in> {n. n < M}"
        hence "x < M" by simp
        hence "2 * x < 2 * M" by simp
        then obtain n where
          "n div 2 = x"
          "n < 2 * M"
          using div_mult_self1_is_m zero_less_numeral by blast
        thus "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * M}"
          by blast
      qed
      
      have 3: "{n div 2 | n. n < 2 * M \<and> n mod 2 = 1} = {n div 2 | n. n < 2 * M}"
      proof (rule equalityI; rule subsetI)
        show "\<And>x. x \<in> {n div 2 |n. n < 2 * M \<and> n mod 2 = 1} \<Longrightarrow> x \<in> {n div 2 |n. n < 2 * M}" by blast
      next
        fix x
        assume "x \<in> {n div 2 |n. n < 2 * M}" 
        then obtain n where
          n: "n < 2 * M"
          "n div 2 = x" by blast
        have "\<exists>m. m < 2 * M \<and> m mod 2 = 1 \<and> m div 2 = x"
        proof (cases "n mod 2 = 1")
          case True
          with n
          show ?thesis by metis
        next
          case False
          then have nm2: "n mod 2 = 0" by auto
          hence "(Suc n) div 2 = n div 2" "(Suc n) mod 2 = 1" by presburger+
          moreover
          have "Suc n < 2 * M" using n(1) nm2 by auto
          ultimately
          show ?thesis using n(2) by meson
        qed
        thus "x \<in> {n div 2 |n. n < 2 * M \<and> n mod 2 = 1}" by auto
      qed
      
      have "a \<in> act ` {n div 2 | n. n < 2 * M \<and> n mod 2 = 1}"  
        using 1[simplified 2[symmetric]]
        by (subst 3, blast)
      with xa
      show "x \<in> snap ` {n. n < 2 * M \<and> n mod 2 = 1}"
        unfolding snap_def by auto
    qed
    ultimately
    show "bij_betw snap {n. n < 2 * M \<and> n mod 2 = 1} (at_end ` actions)"
      using bij_betw_imageI by blast
  qed
  have 3: \<open>{n. n < 2 * M \<and> n mod 2 = 0} \<union> {n. n < 2 * M \<and> n mod 2 = 1} = {n. n < 2 * M}\<close>
  proof (rule equalityI; rule subsetI) 
    fix x
    assume "x \<in> {n. n < 2 * M \<and> n mod 2 = 0} \<union> {n. n < 2 * M \<and> n mod 2 = 1}"
    thus "x \<in> {n. n < 2 * M}" by blast
  next
    fix x
    assume "x \<in> {n. n < 2 * M}"
    moreover
    have "x mod 2 = 1 \<or> x mod 2 = 0" by presburger
    ultimately
    show "x \<in> {n. n < 2 * M \<and> n mod 2 = 0} \<union> {n. n < 2 * M \<and> n mod 2 = 1}" by blast
  qed
  show "bij_betw snap {n. n < 2 * M} (at_start ` actions \<union> at_end ` actions)"
    using bij_betw_combine[OF 1 2 snaps_disj] 3 by simp
qed

definition interfering_snaps::"'snap_action \<Rightarrow> 'snap_action list" where
"interfering_snaps a = sorted_key_list_of_set (inv snap) {b. a \<noteq> b \<and> mutex_snap_action a b}"
  end 
end
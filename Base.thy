theory Base
  imports Main Containers.Containers
begin

section \<open>Time\<close>

find_theorems name: "zero_le"

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

find_theorems name: "GreatestI"

lemma GreatestI_time:
  assumes "P k" and minor: "\<And>y. P y \<Longrightarrow> y \<le> k"
  shows GreatestI_nat: "P (Greatest P)"
  using assms GreatestI2_order by blast

  
end

lemma list_all2_twist: "list_all2 P xs ys \<longleftrightarrow> list_all2 (\<lambda>y x. P x y) ys xs" for xs ys P
    apply (subst list_all2_iff)+
    apply (rule iffI; rule conjI; simp; drule conjunct2)
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

lemma distinct_inj_map: "distinct xs \<Longrightarrow> inj f \<Longrightarrow> distinct (map f xs)"
  apply (induction xs)
  unfolding inj_def
  by auto

end
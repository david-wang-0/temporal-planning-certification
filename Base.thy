theory Base
  imports Main
begin
  
section \<open>Time\<close>

class time = wellorder + ordered_ab_group_add + one +
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


lemma least_time_gt_0: "(LEAST n. n > 0) > 0"
proof -
  have "Ex (\<lambda>x. 0 < x)" using diff_gt_0_iff_gt non_trivial_neg by blast
  thus ?thesis using LeastI_ex by auto
qed

lemma "0 < x \<Longrightarrow> (LEAST n. 0 < n) \<le> x" using Least_le by simp
lemma ge_least_gt_0: "Least ((<) 0) \<le> x \<Longrightarrow> 0 < x" using least_time_gt_0 by auto


lemma GreatestI_ex_time: "\<exists>t. P t \<Longrightarrow> P (Greatest P)"
  using least_time_gt_0 local.dense local.not_less_Least by auto


end

end
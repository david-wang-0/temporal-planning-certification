theory Base
  imports Main
begin
  
section \<open>Time\<close>

class time = linordered_ab_group_add + one +
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
end

definition restr_set::"(nat \<Rightarrow> 't) \<Rightarrow> nat \<Rightarrow> 't set" where
"restr_set f n = f ` {..<n}"

lemma restr_set_bij: "bij_betw f {..<n} S \<Longrightarrow> restr_set f n = S"
  apply (subst restr_set_def)
  apply (subst (asm) bij_betw_def)
  by (drule conjunct2)

lemma lt_in_restr: "n < m \<Longrightarrow> f n \<in> restr_set f m"
  using restr_set_def by fast

end
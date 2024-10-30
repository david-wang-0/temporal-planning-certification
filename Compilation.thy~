theory Compilation
  imports Prop_Plans Diagonal_Timed_Automata
begin

text \<open>This formalisation follows the pen-and-paper compilation defined by Gigante, et al.\<close>

datatype ('proposition, 'action, 'snap_action) state =
  Init 
  | Goal
  | Main
  | PropDecoding 'proposition 
  | ExecDecoding 'action
  | Decision 'snap_action
  | Execution 'snap_action


datatype ('proposition, 'action) clock =
  Delta
  | Stop
  | PropClock 'proposition
  | Running 'action
  | Start 'action
  | End 'action
  | ExecStart 'action
  | ExecEnd 'action

datatype alpha = Unit

context temp_planning_problem
begin

definition prop_numbers ("p\<^sub>_" 65) where "prop_numbers \<equiv> p"

definition "N = card props"

definition A ("A\<^sub>_" 65) where "A \<equiv> act"

definition "M = card actions"

definition "true_const \<equiv> GE Stop 0"

text \<open>Preventing time from passing in any location other than the main location.\<close>
fun invs::"(('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) invassn" where
  "invs Main  = GE Stop 0"
| "invs _     = EQ Stop 0"

text \<open>The transition from the initial location \<open>l\<^sub>I\<close> to the main location \<open>l\<^sub>\<delta>\<close>\<close>
definition init_pos::"'proposition list" where
"init_pos \<equiv> sorted_key_list_of_set (inv p) init"

definition init_asmt::"(('proposition, 'action) clock, 't) clkassn list" where
"init_asmt \<equiv> map (\<lambda>x. (PropClock x, 1)) init_pos"

definition initial_transition::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"initial_transition \<equiv> (Init, true_const, Unit, init_asmt, Main)"

text \<open>The transition from the main location \<open>l\<^sub>\<delta>\<close> to the \<open>0\<^sup>t\<^sup>h\<close> location of the state decoding path \<open>s\<^sub>0\<close>.\<close>
definition main_to_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"main_to_decoding \<equiv> (Main, true_const, Unit, [(Stop, 0)], PropDecoding (p 0))"

subsubsection \<open>State decoding\<close>

text \<open>The transitions between the decoding locations for the propositional clocks \<open>cp\<^sub>i\<close>\<close>
definition prop_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition set" where
"prop_decoding \<equiv> {(PropDecoding (p n), CEQ (PropClock (p n)) Delta 1, Unit, [(PropClock (p n), 1)], PropDecoding (p (n + 1))) | n. n < N}
  \<union> {(PropDecoding (p n), CEQ (PropClock (p n)) Delta 0, Unit, [(PropClock (p n), 0)], PropDecoding (p (n + 1))) | n. n < N}"

text \<open>A transition from the decoding locations for propositional clocks to the decoding locations for
the execution clocks\<close>
definition prop_decoding_to_exec_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"prop_decoding_to_exec_decoding \<equiv> (PropDecoding (p N), true_const, Unit, [], ExecDecoding (act 0))"

text \<open>The transitions between the decoding locations for the execution clocks \<open>cr\<^sub>a\<close>\<close>
definition exec_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition set" where
"exec_decoding \<equiv> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 1, Unit, [(Running (act m), 1)], ExecDecoding (act (m + 1))) | m. m < M}
  \<union> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 0, Unit, [(Running (act m), 0)], ExecDecoding (act (m + 1))) | m. m < M}"

text \<open>The transition from the execution decoding locations to the decision-making locations\<close>
definition exec_decoding_to_decision_making::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"exec_decoding_to_decision_making \<equiv> (ExecDecoding (act M), true_const, Unit, [], Decision (at_start (act 0)))"

subsubsection \<open>Decision-making\<close>
definition AND_ALL::"(('proposition, 'action) clock, 't) dconstraint list \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"AND_ALL xs = fold AND xs (true_const)"

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
      
      from this[simplified M_def] action_numbering[THEN bij_betw_apply]
      have 1: "act (x div 2) \<in> actions"
           "act (y div 2) \<in> actions"
        by blast+
      
      from a
      have 2: "at_start (act (x div 2)) = at_start (act (y div 2))"  
        using snap_def by auto
      
      from 1 2
      have "act (x div 2) = act (y div 2)" 
        using at_start_inj
        by (blast dest: inj_onD)
      hence "x div 2 = y div 2" using act_inj_on[simplified inj_on_def] 0[simplified M_def] by blast
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
        n: "n \<in> {n. n < 2 * (card actions)}"
        "n mod 2 = 0"
        "snap n = x" using M_def by auto
      hence "n div 2 \<in> {n. n < card actions}" by auto
      hence "act (n div 2) \<in> actions" using act_img_action by blast
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
      
      hence 1: "a \<in> act ` {n. n < card actions}" using act_img_action
        by simp
      
      have 2: "(\<lambda>n. n div 2) ` {n. n < 2 * card actions} = {n. n < card actions}"
      proof (rule equalityI; rule subsetI)
        fix x 
        assume "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * card actions}"
        then obtain n where
          "x = n div 2"
          "n < 2 * card actions"
          by blast
        hence "x < card actions" by linarith
        thus "x \<in> {n. n < card actions}"
          by simp
      next 
        fix x
        assume "x \<in> {n. n < card actions}"
        hence "x < card actions" by simp
        hence "2 * x < 2 * card actions" by simp
        then obtain n where
          "n div 2 = x"
          "n < 2 * card actions"
          using div_mult_self1_is_m zero_less_numeral by blast
        thus "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * card actions}"
          by blast
      qed
      
      have 3: "{n div 2 | n. n < 2 * (card actions) \<and> n mod 2 = 0} = {n div 2 | n. n < 2 * (card actions)}"
      proof (rule equalityI; rule subsetI)
        show "\<And>x. x \<in> {n div 2 |n. n < 2 * card actions \<and> n mod 2 = 0} \<Longrightarrow> x \<in> {n div 2 |n. n < 2 * card actions}" by blast
      next
        fix x
        assume "x \<in> {n div 2 |n. n < 2 * card actions}" 
        then obtain n where
          n: "n < 2 * card actions"
          "n div 2 = x" by blast
        have "\<exists>m. m < 2 * card actions \<and> m mod 2 = 0 \<and> m div 2 = x"
        proof (cases "n mod 2 = 0")
          case True
          with n
          show ?thesis by metis
        next
          case False
          then have "n mod 2 = 1" by auto
          hence "(n - 1) div 2 = n div 2" "(n - 1) mod 2 = 0" by presburger+
          moreover
          have "n - 1 < 2 * card actions" using n(1) by linarith
          ultimately
          show ?thesis using n(2) by meson
        qed
        thus "x \<in> {n div 2 |n. n < 2 * card actions \<and> n mod 2 = 0}" by auto
      qed
      
      have "a \<in> act ` {n div 2 | n. n < 2 * M \<and> n mod 2 = 0}" unfolding M_def 
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
      
      from this[simplified M_def] action_numbering[THEN bij_betw_apply]
      have 1: "act (x div 2) \<in> actions"
           "act (y div 2) \<in> actions"
        by blast+
      
      from a
      have 2: "at_end (act (x div 2)) = at_end (act (y div 2))"  
        using snap_def by auto
      
      from 1 2
      have "act (x div 2) = act (y div 2)" 
        using at_end_inj
        by (blast dest: inj_onD)
      hence "x div 2 = y div 2" using act_inj_on[simplified inj_on_def] 0[simplified M_def] by blast
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
        n: "n \<in> {n. n < 2 * (card actions)}"
        "n mod 2 = 1"
        "snap n = x" using M_def by auto
      hence "n div 2 \<in> {n. n < card actions}" by auto
      hence "act (n div 2) \<in> actions" using act_img_action by blast
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
      
      hence 1: "a \<in> act ` {n. n < card actions}" using act_img_action
        by simp
      
      have 2: "(\<lambda>n. n div 2) ` {n. n < 2 * card actions} = {n. n < card actions}"
      proof (rule equalityI; rule subsetI)
        fix x 
        assume "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * card actions}"
        then obtain n where
          "x = n div 2"
          "n < 2 * card actions"
          by blast
        hence "x < card actions" by linarith
        thus "x \<in> {n. n < card actions}"
          by simp
      next 
        fix x
        assume "x \<in> {n. n < card actions}"
        hence "x < card actions" by simp
        hence "2 * x < 2 * card actions" by simp
        then obtain n where
          "n div 2 = x"
          "n < 2 * card actions"
          using div_mult_self1_is_m zero_less_numeral by blast
        thus "x \<in> (\<lambda>n. n div 2) ` {n. n < 2 * card actions}"
          by blast
      qed
      
      have 3: "{n div 2 | n. n < 2 * (card actions) \<and> n mod 2 = 1} = {n div 2 | n. n < 2 * (card actions)}"
      proof (rule equalityI; rule subsetI)
        show "\<And>x. x \<in> {n div 2 |n. n < 2 * card actions \<and> n mod 2 = 1} \<Longrightarrow> x \<in> {n div 2 |n. n < 2 * card actions}" by blast
      next
        fix x
        assume "x \<in> {n div 2 |n. n < 2 * card actions}" 
        then obtain n where
          n: "n < 2 * card actions"
          "n div 2 = x" by blast
        have "\<exists>m. m < 2 * card actions \<and> m mod 2 = 1 \<and> m div 2 = x"
        proof (cases "n mod 2 = 1")
          case True
          with n
          show ?thesis by metis
        next
          case False
          then have nm2: "n mod 2 = 0" by auto
          hence "(Suc n) div 2 = n div 2" "(Suc n) mod 2 = 1" by presburger+
          moreover
          have "Suc n < 2 * card actions" using n(1) nm2 by auto
          ultimately
          show ?thesis using n(2) by meson
        qed
        thus "x \<in> {n div 2 |n. n < 2 * card actions \<and> n mod 2 = 1}" by auto
      qed
      
      have "a \<in> act ` {n div 2 | n. n < 2 * M \<and> n mod 2 = 1}" unfolding M_def 
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

text \<open>This is easier to work with.\<close>

definition interfering_at_start::"'snap_action \<Rightarrow> nat list" where
"interfering_at_start a = sorted_list_of_set {n. at_start (act n) \<noteq> a \<and> mutex_snap_action a (at_start (act n))}"

definition start_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint list" where
"start_constraints a = map (\<lambda>b. GT (Start (act b)) \<epsilon>) (interfering_at_start a)"

definition interfering_at_end::"'snap_action \<Rightarrow> nat list" where
"interfering_at_end a = sorted_list_of_set {n. at_end (act n) \<noteq> a \<and> mutex_snap_action a (at_end (act n))}"

definition end_constraints::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint list" where
"end_constraints a = map (\<lambda>b. GT (End (act b)) \<epsilon>) (interfering_at_end a)"

definition sep::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"sep a \<equiv> AND_ALL (start_constraints a @ end_constraints a)"

text \<open>The clock constraints for the precondition\<close>
definition pre_clocks::"'snap_action \<Rightarrow> ('proposition, 'action) clock list" where
"pre_clocks a \<equiv> map PropClock (sorted_key_list_of_set (inv p) (pre a))"

definition pre_constraint::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"pre_constraint a \<equiv> AND_ALL (map (\<lambda>c. EQ c 1) (pre_clocks a))"

text \<open>The guard constraints\<close>
definition guard::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"guard a \<equiv> AND (sep a) (pre_constraint a)"

definition guard_at_start::"'action \<Rightarrow> (('proposition, 'action) clock, 't::time) dconstraint" where
"guard_at_start a \<equiv> AND (guard (at_start a)) (EQ (Running a) 0)"

definition guard_at_end::"'action \<Rightarrow> (('proposition, 'action) clock, 't::time) dconstraint" where
"guard_at_end a \<equiv> 
  let l = case (lower a) of 
    (lower_bound.GT t) \<Rightarrow> GT (Start a) t
  | (lower_bound.GE t) \<Rightarrow> GE (Start a) t;
  u = case (upper a) of 
    (upper_bound.LT t) \<Rightarrow> LT (Start a) t
  | (upper_bound.LE t) \<Rightarrow> LE (Start a) t
  in
AND (AND (guard (at_end a)) (EQ (Running a) 1)) (AND l u)"

definition decision_making::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition set" where
"decision_making \<equiv> 
  {(Decision (at_start (act m)), guard (at_start (act m)), Unit, [(ExecStart (act m), 1)], Decision (at_end (act m))) | m. m < M}
  \<union> {(Decision (at_start (act m)), true_const, Unit, [(ExecStart (act m), 0)], Decision (at_end (act m))) | m. m < M}
  \<union> {(Decision (at_end (act m)), guard (at_end (act m)), Unit, [(ExecEnd (act m), 1)], Decision (at_start (act (Suc m)))) | m. Suc m < M}
  \<union> {(Decision (at_end (act m)), true_const, Unit, [(ExecEnd (act m), 0)], Decision (at_start (act (Suc m)))) | m. Suc m < M}"

definition dm_to_exec::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"dm_to_exec \<equiv> (Decision (at_end (act M)), true_const, Unit, [], Execution (at_start (act 0)))"

subsubsection \<open>Execution\<close>

definition add_effects::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) clkassn list" where
"add_effects s \<equiv> map (\<lambda>p. (PropClock p, 1)) (sorted_key_list_of_set (inv p) (adds s))"

definition del_effects::"'snap_action  \<Rightarrow> (('proposition, 'action) clock, 't) clkassn list" where
"del_effects s \<equiv> map (\<lambda>p. (PropClock p, 1)) (sorted_key_list_of_set (inv p) ((dels s) - (adds s)))"

definition effects::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) clkassn list" where
"effects s \<equiv> del_effects s @ add_effects s"

definition at_start_effects::"'action \<Rightarrow> (('proposition, 'action) clock, 't) clkassn list" where
"at_start_effects a \<equiv> (Running a, 1) # (ExecStart a, 0) # effects (at_start a)"

definition at_end_effects::"'action \<Rightarrow> (('proposition, 'action) clock, 't) clkassn list" where
"at_end_effects a \<equiv> (Running a, 0) # (ExecEnd a, 0) # effects (at_start a)"

definition execution::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition set" where
"execution \<equiv> 
  {(Execution (at_start (act m)), EQ (ExecStart (act m)) 1, Unit, at_start_effects (act m), Execution (at_end (act m))) | m. m < M}
  \<union> {(Execution (at_start (act m)), true_const, Unit, [], Execution (at_end (act m))) | m. m < M}
  \<union> {(Execution (at_end (act m)), EQ (ExecEnd (act m)) 1, Unit, at_end_effects (act m), Execution (at_end (act (Suc m)))) | m. Suc m < M}
  \<union> {(Execution (at_end (act m)), true_const, Unit, [], Decision (at_start (act (Suc m)))) | m. Suc m < M}"


subsubsection \<open>Over-all conditions\<close>
definition over_all_clocks::"'action \<Rightarrow> ('proposition, 'action) clock list" where
"over_all_clocks a \<equiv> map PropClock (sorted_key_list_of_set (inv p) (over_all a))"

definition action_over_all::"'action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"action_over_all a \<equiv> AND_ALL (map (\<lambda>c. CLE (Running a) c 0) (over_all_clocks a))"

definition over_all_conds::"(('proposition, 'action) clock, 't) dconstraint" where
"over_all_conds \<equiv> AND_ALL (map (\<lambda>m. action_over_all (act m)) (sorted_list_of_set {m. m < M}))"

definition exec_to_main::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"exec_to_main \<equiv> (Execution (at_end (act M)), over_all_conds, Unit, [(Delta, 0)], Main)"

subsubsection \<open>The goal\<close>
definition none_running::"(('proposition, 'action) clock, 't) dconstraint" where
"none_running \<equiv> AND_ALL (map (\<lambda>m. EQ (Running (act m)) 0) (sorted_list_of_set {m. m < M}))"

definition goal_satisfied::"(('proposition, 'action) clock, 't) dconstraint" where
"goal_satisfied \<equiv> AND_ALL (map (\<lambda>p. EQ (PropClock p) 1) (sorted_key_list_of_set (inv p) goal))"

definition goal_constraint::"(('proposition, 'action) clock, 't) dconstraint" where
"goal_constraint \<equiv> AND none_running goal_satisfied"

definition goal_trans::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"goal_trans \<equiv> (ExecDecoding (act M), goal_constraint, Unit, [], Goal)"

subsubsection \<open>The automaton\<close>
definition plan_automaton::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) ta" where
"plan_automaton \<equiv> ({initial_transition} \<union> {main_to_decoding} \<union> prop_decoding 
  \<union> {prop_decoding_to_exec_decoding} \<union> exec_decoding \<union> {exec_decoding_to_decision_making}
  \<union> decision_making \<union> {dm_to_exec} \<union> execution \<union> {exec_to_main} \<union> {goal_trans}, invs)"
end

end
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

definition P ("P\<^sub>_" 65) where "P \<equiv> p"

definition "N = card props"

definition A ("A\<^sub>_" 65) where "A \<equiv> act"

definition "M = card actions"

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
"initial_transition \<equiv> (Init, GE Stop 0, Unit, init_asmt, Main)"

text \<open>The transition from the main location \<open>l\<^sub>\<delta>\<close> to the \<open>0\<^sup>t\<^sup>h\<close> location of the state decoding path \<open>s\<^sub>0\<close>.\<close>
definition main_to_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"main_to_decoding \<equiv> (Main, GE Stop 0, Unit, [(Stop, 0)], PropDecoding (p 0))"

text \<open>The transitions between the decoding locations for the propositional clocks \<open>cp\<^sub>i\<close>\<close>
definition prop_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition set" where
"prop_decoding \<equiv> {(PropDecoding (p n), CEQ (PropClock (p n)) Delta 1, Unit, [(PropClock (p n), 1)], PropDecoding (p (n + 1))) | n. n < N}
  \<union> {(PropDecoding (p n), CEQ (PropClock (p n)) Delta 0, Unit, [(PropClock (p n), 0)], PropDecoding (p (n + 1))) | n. n < N}"

text \<open>A transition from the decoding locations for propositional clocks to the decoding locations for
the execution clocks\<close>
definition prop_decoding_to_exec_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"prop_decoding_to_exec_decoding \<equiv> (PropDecoding (p N), GE Stop 0, Unit, [], ExecDecoding (act 0))"

text \<open>The transitions between the decoding locations for the execution clocks \<open>cr\<^sub>a\<close>\<close>
definition exec_decoding::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition set" where
"exec_decoding \<equiv> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 1, Unit, [(Running (act m), 1)], ExecDecoding (act (m + 1))) | m. m < M}
  \<union> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 0, Unit, [(Running (act m), 0)], ExecDecoding (act (m + 1))) | m. m < M}"

text \<open>The transition from the execution decoding locations to the decision-making locations\<close>
definition exec_decoding_to_decision_making::"(alpha, ('proposition, 'action) clock, 't, ('proposition, 'action, 'snap_action) state) transition" where
"exec_decoding_to_decision_making \<equiv> (ExecDecoding (act M), GE Stop 0, Unit, [], Decision (at_start (act 0)))"

text \<open>The transitions between the decision-making locations\<close>
definition AND_ALL::"(('proposition, 'action) clock, 't) dconstraint list \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"AND_ALL xs = fold AND xs (GE Stop 0)"

text \<open>Numbering for snap_actions\<close>
definition s::"nat \<Rightarrow> 'snap_action" where
"s n \<equiv> if (n mod 2 = 0) then (at_start (act (n div 2))) else (at_end (act ((n - 1) div 2)))"

lemma "x mod 2 = Suc n \<Longrightarrow> n = 0"
  by auto

lemma "bij_betw s {n. n < 2 * M} (at_start ` actions \<union> at_end ` actions)"
proof -
  have 1: "bij_betw s {n. n < 2 * M \<and> n mod 2 = 0} (at_start ` actions)"
  proof -
    have "inj_on s {n. n < 2 * M \<and> n mod 2 = 0}"
    proof (rule inj_onI)
      fix x y
      assume a: "x \<in> {n. n < 2 * M \<and> n mod 2 = 0}" 
             "y \<in> {n. n < 2 * M \<and> n mod 2 = 0}" 
             "s x = s y" 
      
      hence 0: "x div 2 \<in> {m. m < M}"
            "y div 2 \<in> {m. m < M}" by auto
      
      from this[simplified M_def] action_numbering[THEN bij_betw_apply]
      have 1: "act (x div 2) \<in> actions"
           "act (y div 2) \<in> actions"
        by blast+
      
      from a
      have 2: "at_start (act (x div 2)) = at_start (act (y div 2))"  
        using s_def by auto
      
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
    have "s ` {n. n < 2 * M \<and> n mod 2 = 0} = (at_start ` actions)"
    proof (rule equalityI; rule subsetI)
      fix x
      assume "x \<in> s ` {n. n < 2 * M \<and> n mod 2 = 0}"
      then obtain n where
        n: "n \<in> {n. n < 2 * (card actions)}"
        "n mod 2 = 0"
        "s n = x" using M_def by auto
      hence "n div 2 \<in> {n. n < card actions}" by auto
      hence "act (n div 2) \<in> actions" using action_numbering[simplified bij_betw_def] by blast
      with n(2, 3)[simplified s_def]
      show "x \<in> at_start ` actions" using action_numbering
        by auto
    next
      fix x
      assume "x \<in> at_start ` actions"
      show "x \<in> s ` {n. n < 2 * M \<and> n mod 2 = 0}"
        unfolding s_def
        apply simp
    qed
  qed
  have 2: "bij_betw s {n. n < 2 * N \<and> n mod 2 = 1} (at_end ` actions)"
    sorry
  
  have 3: \<open>{n. n < 2 * N \<and> n mod 2 = 0} \<union> {n. n < 2 * N \<and> n mod 2 = 1} = {n. n < 2 * N}\<close>
  proof (rule equalityI; rule subsetI) 
    fix x
    assume "x \<in> {n. n < 2 * N \<and> n mod 2 = 0} \<union> {n. n < 2 * N \<and> n mod 2 = 1}"
    thus "x \<in> {n. n < 2 * N}" by blast
  next
    fix x
    assume "x \<in> {n. n < 2 * N}"
    moreover
    have "x mod 2 = 1 \<or> x mod 2 = 0" by presburger
    ultimately
    show "x \<in> {n. n < 2 * N \<and> n mod 2 = 0} \<union> {n. n < 2 * N \<and> n mod 2 = 1}"by blast
  qed
  show "bij_betw s {n. n < 2 * N} (at_start ` actions \<union> at_end ` actions)"
    using bij_betw_combine[OF 1 2 snaps_disj] 3 by simp
qed


definition sep::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"sep s \<equiv> sorted_key_list_of_set f {b. a \<noteq> b \<and> mutex_snap_action a b}"

definition guard::"'snap_action \<Rightarrow> (('proposition, 'action) clock, 't) dconstraint" where
"guard s \<equiv> undefined"

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
  {(Decision (at_start (act m)), CEQ (Running (act m)) Delta 1, Unit, [(Running (act m), 1)], ExecDecoding (act (m + 1))) | m. m < M}
  \<union> {(ExecDecoding (act m), CEQ (Running (act m)) Delta 0, Unit, [(Running (act m), 0)], ExecDecoding (act (m + 1))) | m. m < M}"

end

end
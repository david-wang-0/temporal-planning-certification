theory Ground_PDDL_Plan_Defs
  imports
    Ground_PDDL_Problem_Defs
    "Temporal_Planning_Discrete.Temporal_State_Sequence_Semantics"
begin

text \<open>The new \<open>Temporal_State_Sequence_Semantics\<close> import re-introduces the duplicate
  \<open>Syntax_Utils.app\<close> \<open>|>\<close> notation (identical to Munta's \<open>Error_List_Monad.app\<close> already used
  here, and suppressed in \<open>Ground_PDDL_Problem_Defs\<close>).  Re-suppress it so \<open>|>\<close> resolves uniquely.\<close>
no_notation Syntax_Utils.app (infixl "|>" 59)

instantiation real::infinity
begin
instance ..
end

text \<open>Re-point: the project-local \<open>list_pairwise\<close> (formerly in \<open>ListMisc\<close>) was removed in favour of
  Formal-PDDL-Semantics' \<open>Utils.list_pairwise\<close> (the one \<open>valid_temporal_state_seq\<close> uses).  The
  two \<open>list_pairwise\<close>-specific lemmas the development relies on (\<open>list_pairwise_nth_refl\<close>,
  \<open>list_pairwise_map\<close>) are re-established here on the FPS constant.  FPS' \<open>list_pairwise\<close> is already
  symmetric, so the index characterisation needs no symmetry side condition (the \<open>refl\<close> assumption is
  kept only for call compatibility with the existing use sites).  The generic \<open>count_list\<close> index
  helpers (\<open>count_list_gt1_two_indices\<close>, \<open>two_indices_count_list_gt1\<close>) those proofs use live in
  \<open>Temporal_Planning_Common.ListMisc\<close> (imported transitively).\<close>


text \<open>Re-point: numeric-free duration-constraint satisfaction, replacing the old submodule's
  \<open>duration_matches\<close> / \<open>is_Func_Const\<close> over the retired 3-constructor \<open>duration_constraint\<close>.
  \<open>is_Func_Const\<close> is the negation of \<^const>\<open>dc_no_func\<close>; \<open>duration_matches\<close> evaluates the (constant)
  bound exactly as the duration atom \<^const>\<open>duration_constraint_as_formula\<close> does inside a snap
  precondition (\<open>EQ\<close> \<rightarrow> \<open>d = x\<close>, \<open>LEQ\<close> \<rightarrow> \<open>d \<le> x\<close>, \<open>GEQ\<close> \<rightarrow> \<open>d \<ge> x\<close>).  The \<open>ps\<close>/\<open>as\<close> arguments
  are vestigial in the numeric-free phase (durations are constants), kept for call compatibility.\<close>

definition is_Func_Const :: "term duration_constraint \<Rightarrow> bool" where
  "is_Func_Const dc \<equiv> \<not> dc_no_func dc"

fun duration_matches :: "rat \<Rightarrow> term duration_constraint \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> bool" where
  "duration_matches d (DurationConstraint duration_op.EQ (ConstantExpr x)) ps as = (d = x)"
| "duration_matches d (DurationConstraint duration_op.LEQ (ConstantExpr x)) ps as = (d \<le> x)"
| "duration_matches d (DurationConstraint duration_op.GEQ (ConstantExpr x)) ps as = (d \<ge> x)"
| "duration_matches d _ ps as = False"

definition durations_match :: "rat \<Rightarrow> term duration_constraint list \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> bool" where
  "durations_match d dcs ps as \<equiv> list_all (\<lambda>dc. duration_matches d dc ps as) dcs"

context ground_ast_problem_defs
begin

lemma in_acts_of_temporal_plan_atE:
  assumes "a \<in> set (acts_of_temporal_plan_at t p)"
      and "\<And>\<pi>. (t, \<pi>) \<in> simple_acts p \<Longrightarrow> a = the (res_inst \<pi>) \<Longrightarrow> Q a t p"
          "\<And>\<pi>. (t, \<pi>) \<in> durative_acts p \<Longrightarrow> a = the (res_inst_snap_action \<pi> At_Start) \<Longrightarrow> Q a t p"
          "\<And>t' \<pi>. (t', \<pi>) \<in> durative_acts p \<Longrightarrow> t = t' + duration \<pi> \<Longrightarrow> a = the (res_inst_snap_action \<pi> At_End) \<Longrightarrow> Q a t p"
  shows "Q a t p"
proof -
  from assms(1) obtain t\<^sub>\<pi> \<pi> where
    mem: "(t\<^sub>\<pi>, \<pi>) \<in> set p"
    and a_in: "a \<in> set (simplified_res_inst_temporal_plan_action_at t (t\<^sub>\<pi>, \<pi>))"
    unfolding acts_of_temporal_plan_at_def by auto
  show ?thesis
  proof (cases \<pi>)
    case (SimplePlanAction n args)
    hence "t = t\<^sub>\<pi>" and "a = the (res_inst \<pi>)"
      using a_in by (auto split: if_splits)
    moreover have "(t, \<pi>) \<in> simple_acts p"
      using mem \<open>t = t\<^sub>\<pi>\<close> SimplePlanAction
      unfolding simple_acts_def is_act_simple_def by force
    ultimately show ?thesis using assms(2) by blast
  next
    case (DurativePlanAction n args dur)
    have dur_mem: "(t\<^sub>\<pi>, \<pi>) \<in> durative_acts p"
      using mem DurativePlanAction
      unfolding durative_acts_def is_act_simple_def by force
    consider "t = t\<^sub>\<pi> \<and> a = the (res_inst_snap_action \<pi> At_Start)"
      | "t = t\<^sub>\<pi> + dur \<and> a = the (res_inst_snap_action \<pi> At_End)"
      using a_in DurativePlanAction by (auto split: if_splits)
    thus ?thesis
    proof cases
      case 1
      thus ?thesis using assms(3) dur_mem by blast
    next
      case 2
      thus ?thesis using assms(4) dur_mem DurativePlanAction by force
    qed
  qed
qed



lemma fst_apply_eff_mem_or_del:
  assumes "p \<in> fst M"
  shows "p \<in> fst (apply_eff A M)
         \<or> p \<in> \<Union> (set (map (set o dels o effect) A))"
  using assms unfolding apply_eff_unfold by auto

lemma valid_temporal_state_seq_prop_pred_final:
  assumes "valid_temporal_state_seq M ts \<pi> M'"
      and "\<forall>p \<in> fst M'. Q p"
      and "\<forall>t \<in> set ts. \<forall>a \<in> set (acts_of_temporal_plan_at t \<pi>). 
            \<forall>p \<in> set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). Q p"
  shows "\<forall>p \<in> fst M. Q p"
  using assms
proof (induction M ts \<pi> M' arbitrary: M rule: valid_temporal_state_seq.induct)
  case (1 M \<pi>s M')
  then show ?case by simp
next
  case (2 M t\<^sub>i \<pi>s M')
  have effQ: "\<forall>a\<in>set (acts_of_temporal_plan_at t\<^sub>i \<pi>s).
      \<forall>p\<in>set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). Q p"
    using 2 by simp
  have post: "\<forall>p\<in>fst (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M). Q p"
    using 2 by (simp add: Let_def)
  have "Q p" if "p \<in> fst M" for p
  proof -
    have "p \<in> fst (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M)
          \<or> p \<in> \<Union> (set (map (set o dels o effect) (acts_of_temporal_plan_at t\<^sub>i \<pi>s)))"
      using fst_apply_eff_mem_or_del[OF that] .
    thus ?thesis using post effQ by auto
  qed
  thus ?case by blast
next
  case (3 M t\<^sub>i t\<^sub>j ts \<pi>s M')
  have effQ: "\<forall>a\<in>set (acts_of_temporal_plan_at t\<^sub>i \<pi>s).
      \<forall>p\<in>set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). Q p"
    using 3 by simp
  have rec: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M) (t\<^sub>j # ts) \<pi>s M'"
    using 3(2) by (simp add: Let_def)
  have tail: "\<forall>t\<in>set (t\<^sub>j # ts). \<forall>a\<in>set (acts_of_temporal_plan_at t \<pi>s).
      \<forall>p\<in>set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). Q p"
    using 3(4) by simp
  have post: "\<forall>p\<in>fst (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M). Q p"
    using 3(1) rec 3(3) tail by blast
  have "Q p" if "p \<in> fst M" for p
  proof -
    have "p \<in> fst (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M)
          \<or> p \<in> \<Union> (set (map (set o dels o effect) (acts_of_temporal_plan_at t\<^sub>i \<pi>s)))"
      using fst_apply_eff_mem_or_del[OF that] .
    thus ?thesis using post effQ by auto
  qed
  thus ?case by blast
qed

lemma fst_apply_eff_Q_forward:
  assumes "\<forall>p \<in> fst M. Q p"
      and "\<forall>a\<in>set A. \<forall>p\<in>set (adds (ground_action.effect a)). Q p"
  shows "\<forall>p \<in> fst (apply_eff A M). Q p"
  using assms unfolding apply_eff_unfold by auto

lemma valid_temporal_state_seq_prop_pred_initial:
  assumes "valid_temporal_state_seq M ts \<pi> M'"
      and "\<forall>p \<in> fst M. Q p"
      and "\<forall>t \<in> set ts. \<forall>a \<in> set (acts_of_temporal_plan_at t \<pi>). 
        \<forall>p \<in> set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). Q p"
  shows "\<forall>p \<in> fst M'. Q p"
  using assms
proof (induction M ts \<pi> M' rule: valid_temporal_state_seq.induct)
  case (1 M \<pi>s M')
  then show ?case by simp
next
  case (2 M t\<^sub>i \<pi>s M')
  have adds: "\<forall>a\<in>set (acts_of_temporal_plan_at t\<^sub>i \<pi>s).
      \<forall>p\<in>set (adds (ground_action.effect a)). Q p"
    using 2(3) by simp
  have post: "\<forall>p \<in> fst (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M). Q p"
    using fst_apply_eff_Q_forward[OF 2(2) adds] .
  have "apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M = M'"
    using 2(1) by (simp add: Let_def)
  thus ?case using post by simp
next
  case (3 M t\<^sub>i t\<^sub>j ts \<pi>s M')
  have adds: "\<forall>a\<in>set (acts_of_temporal_plan_at t\<^sub>i \<pi>s).
      \<forall>p\<in>set (adds (ground_action.effect a)). Q p"
    using 3(4) by simp
  have post: "\<forall>p \<in> fst (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M). Q p"
    using fst_apply_eff_Q_forward[OF 3(3) adds] .
  have rec: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M) (t\<^sub>j # ts) \<pi>s M'"
    using 3(2) by (simp add: Let_def)
  have tail: "\<forall>t\<in>set (t\<^sub>j # ts). \<forall>a\<in>set (acts_of_temporal_plan_at t \<pi>s).
      \<forall>p\<in>set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). Q p"
    using 3(4) by simp
  show ?case
    using 3(1) post rec tail by (simp add: Let_def)
qed




lemma wf_apply_eff:
  assumes "wf_world_model M"
      and "\<forall>h \<in> set A. wf_ground_action h"
    shows "wf_world_model (apply_eff A M)"
proof -
  have "\<forall>f \<in> fst (apply_eff A M). wf_fmla_atom objT f"
  proof
    fix f
    assume "f \<in> fst (apply_eff A M)"
    hence "f \<in> (fst M - \<Union> (set (map (set o dels o effect) A)))
            \<or> f \<in> \<Union> (set (map (set o adds o effect) A))"
      unfolding apply_eff_unfold by auto
    thus "wf_fmla_atom objT f"
    proof
      assume "f \<in> (fst M - \<Union> (set (map (set o dels o effect) A)))"
      thus "wf_fmla_atom objT f"
        using assms(1) by (cases M) auto
    next
      assume "f \<in> \<Union> (set (map (set o adds o effect) A))"
      then obtain a where a_mem: "a \<in> set A" and f_add: "f \<in> set (adds (effect a))"
        by auto
      have "wf_ground_action a" using a_mem assms(2) by blast
      hence "wf_effect objT (effect a)" by (cases a) auto
      thus "wf_fmla_atom objT f"
        using f_add by (cases "effect a") auto
    qed
  qed
  thus ?thesis by (cases "apply_eff A M") auto
qed

lemma valid_temporal_state_seq_list_pairwise_acts:
  assumes "valid_temporal_state_seq M ts \<pi> M'"
      and "t \<in> set ts"
    shows "list_pairwise acts_non_intrf (acts_of_temporal_plan_at t \<pi>)"
  using assms
proof (induction M ts \<pi> M' rule: valid_temporal_state_seq.induct)
  case (1 M \<pi>s M')
  then show ?case by simp
next
  case (2 M t\<^sub>i \<pi>s M')
  have "t = t\<^sub>i" using 2(2) by simp
  thus ?case using 2(1) by (simp add: Let_def)
next
  case (3 M t\<^sub>i t\<^sub>j ts \<pi>s M')
  have here: "list_pairwise acts_non_intrf (acts_of_temporal_plan_at t\<^sub>i \<pi>s)"
    using 3(2) by (simp add: Let_def)
  have rec: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M) (t\<^sub>j # ts) \<pi>s M'"
    using 3(2) by (simp add: Let_def)
  show ?case
  proof (cases "t = t\<^sub>i")
    case True
    thus ?thesis using here by simp
  next
    case False
    hence "t \<in> set (t\<^sub>j # ts)" using 3(3) by simp
    thus ?thesis using 3(1) rec by blast
  qed
qed

lemma valid_temporal_state_seq_head_precond:
  assumes "valid_temporal_state_seq M (t\<^sub>i # ts) \<pi> M'"
      and "a \<in> set (acts_of_temporal_plan_at t\<^sub>i \<pi>)"
    shows "valuation M \<Turnstile>\<^sub>m ground_action.precondition a"
  using assms
  by (cases ts) (simp_all add: Let_def)

lemma valid_temporal_state_seq_head_inv:
  assumes "valid_temporal_state_seq M (t\<^sub>i # t\<^sub>j # ts) \<pi> M'"
      and "\<phi> \<in> set (invs_of_temporal_plan_in_interval (t\<^sub>i, t\<^sub>j) \<pi>)"
    shows "valuation (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M) \<Turnstile>\<^sub>m \<phi>"
  using assms
  by (simp add: Let_def)

lemma list_pairwise_acts_distinctD:
  assumes "list_pairwise acts_non_intrf (acts_of_temporal_plan_at t \<pi>)"
      and "a \<in> set (acts_of_temporal_plan_at t \<pi>)"
      and "b \<in> set (acts_of_temporal_plan_at t \<pi>)"
      and "a \<noteq> b"
    shows "acts_non_intrf a b"
  using assms unfolding list_pairwise_as_nonrec by blast

end

context ground_ast_problem_core
begin

lemma wf_acts_of_temporal_plan_at:
  assumes wfp: "wf_plan p"
      and "a \<in> set (acts_of_temporal_plan_at t p)"
    shows "wf_ground_action a"
proof (rule in_acts_of_temporal_plan_atE[OF assms(2)], goal_cases)
  case (1 \<pi>)
  obtain n args where \<pi>: "\<pi> = SimplePlanAction n args"
    using 1 unfolding simple_acts_def is_act_simple_def by (cases \<pi>) auto
  have mem: "(t, \<pi>) \<in> set p"
    using 1 unfolding simple_acts_def by auto
  hence wfpa: "wf_plan_action \<pi>" using wfp unfolding wf_plan_def by blast
  then obtain h b where
    res: "resolve_temporal_action_schema n = Some (SimpleActionSchema h b)"
    using \<pi> by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  have wfsch: "wf_temporal_action_schema (SimpleActionSchema h b)"
    using resolve_temporal_action_wf res by blast
  have pm: "action_params_match h args"
    using wf_plan_action_params_match[OF wfp mem] \<pi> res by simp
  have "wf_ground_action (instantiate_temporal_action_schema (SimpleActionSchema h b) args)"
    using wf_inst_temporal_action_schema[OF pm wfsch] .
  thus ?case
    using 1 \<pi> res by simp
next
  case (2 \<pi>)
  obtain n args d where \<pi>: "\<pi> = DurativePlanAction n args d"
    using 2 unfolding durative_acts_def is_act_simple_def by (cases \<pi>) auto
  have mem: "(t, \<pi>) \<in> set p"
    using 2 unfolding durative_acts_def by auto
  hence wfpa: "wf_plan_action \<pi>" using wfp unfolding wf_plan_def by blast
  then obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using \<pi> by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  have wfsch: "wf_temporal_action_schema (DurativeActionSchema h b)"
    using resolve_temporal_action_wf res by blast
  have pm: "action_params_match h args"
    using wf_plan_action_params_match[OF wfp mem] \<pi> res by simp
  have "wf_ground_action (inst_temporal_snap_action (DurativeActionSchema h b) d args At_Start)"
    using wf_inst_durative_action_schema[OF pm wfsch] .
  thus ?case
    using 2 \<pi> res by simp
next
  case (3 t' \<pi>)
  obtain n args d where \<pi>: "\<pi> = DurativePlanAction n args d"
    using 3 unfolding durative_acts_def is_act_simple_def by (cases \<pi>) auto
  have mem: "(t', \<pi>) \<in> set p"
    using 3 unfolding durative_acts_def by auto
  hence wfpa: "wf_plan_action \<pi>" using wfp unfolding wf_plan_def by blast
  then obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using \<pi> by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  have wfsch: "wf_temporal_action_schema (DurativeActionSchema h b)"
    using resolve_temporal_action_wf res by blast
  have pm: "action_params_match h args"
    using wf_plan_action_params_match[OF wfp mem] \<pi> res by simp
  have "wf_ground_action (inst_temporal_snap_action (DurativeActionSchema h b) d args At_End)"
    using wf_inst_durative_action_schema[OF pm wfsch] .
  thus ?case
    using 3 \<pi> res by simp
qed

lemma valid_temporal_state_seq_wf_world_model:
  assumes "wf_world_model M"
      and "valid_temporal_state_seq M ts \<pi> M'"
      and "wf_plan \<pi>"
      and "\<forall>t \<in>set ts. is_htp \<pi> t"
    shows "wf_world_model M'"
  using assms 
proof (induction M ts \<pi> M' rule: valid_temporal_state_seq.induct)
  case (1 M \<pi>s M')
  then show ?case by auto
next
  case (2 M t\<^sub>i \<pi>s M')

  have wf: "\<forall>a \<in> set (acts_of_temporal_plan_at t\<^sub>i \<pi>s). wf_ground_action a"
    using wf_acts_of_temporal_plan_at 2 by blast

  have wf_M1: "wf_world_model (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M)"
    using wf_apply_eff wf 2 by blast

  show ?case using 2 wf_M1 by (simp add: Let_def)
next
  case (3 M t\<^sub>i t\<^sub>j ts \<pi>s M')

  have wf: "\<forall>a \<in> set (acts_of_temporal_plan_at t\<^sub>i \<pi>s). wf_ground_action a"
    using wf_acts_of_temporal_plan_at 3 by blast

  have wf_M1: "wf_world_model (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M)"
    using wf_apply_eff wf 3 by blast

  have rec: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M) (t\<^sub>j # ts) \<pi>s M'"
    using 3 by (simp add: Let_def)

  show ?case
    using 3 wf_M1 rec by simp
qed
  (* Obtain some induced happening sequence, from a valid plan *)
  (* Every ground action of a plan at a time point is in the induced happening sequence *)
  (* The induced happening sequence is well formed *)
  (* The actions at the time point are well formed *)
  (* Application of well formed ground actions resutls in a well formed world model *)
  (* Induction *)

end

locale ground_plan_defs = 
  ground_ast_problem_defs P 
  for P::ast_temporal_problem +
  fixes tp::"(rat \<times> plan_action) list"
begin

fun timed_plan_action_to_ref_plan_action::"rat \<times> plan_action \<Rightarrow> ast_temporal_action_schema \<times> int \<times> int" where
"timed_plan_action_to_ref_plan_action (t, SimplePlanAction n as) = (the (resolve_temporal_action_schema n), floor t, 0)" |
"timed_plan_action_to_ref_plan_action (t, DurativePlanAction n as d) = (the (resolve_temporal_action_schema n), floor t, floor d)"

definition ref_plan where
"ref_plan \<equiv> (map timed_plan_action_to_ref_plan_action tp)"


definition plan_imp where
"plan_imp \<equiv> 
  ref_plan
  |> nth_opt"

text \<open>Simple properties\<close>

lemma dom_plan_imp: 
  "dom plan_imp = {i. i < length tp}"
  unfolding plan_imp_def dom_nth_opt ref_plan_def by auto

lemma ran_plan_imp:
  "ran plan_imp = timed_plan_action_to_ref_plan_action ` set tp"
  unfolding plan_imp_def ran_nth_opt ref_plan_def by auto

lemma in_set_ref_planE:
  assumes "(a, t, d) \<in> set ref_plan"
      and "\<And>t n as. (t, SimplePlanAction n as) \<in> set tp 
            \<Longrightarrow> Q (the (resolve_temporal_action_schema n)) (floor t) 0"
      and "\<And>t n as d. (t, DurativePlanAction n as d) \<in> set tp 
            \<Longrightarrow> Q (the (resolve_temporal_action_schema n)) (floor t) (floor d)"
  shows "Q a t d"
  using assms(1) unfolding ref_plan_def set_map
  apply (elim imageE)
  subgoal for x
    apply (cases x)
    subgoal for t' b
      apply (cases b)
      using assms(2, 3)
      by auto
    done
  done

lemma in_set_ref_planI:
  "(t, SimplePlanAction n as) \<in> set tp \<Longrightarrow> (the (resolve_temporal_action_schema n), floor t, 0) \<in> set ref_plan"
  "(t, DurativePlanAction n as d) \<in> set tp \<Longrightarrow> (the (resolve_temporal_action_schema n), floor t, floor d) \<in> set ref_plan"
  unfolding ref_plan_def by force+

lemma ref_plan_pairwise_if:
  assumes "list_pairwise (\<lambda>a b. Q (timed_plan_action_to_ref_plan_action a) (timed_plan_action_to_ref_plan_action b)) tp"
  shows "list_pairwise Q ref_plan"
  using assms unfolding ref_plan_def by (rule list_pairwise_map)

text \<open>Properties specific to later proofs\<close>
fun plan_act_no_args where
"plan_act_no_args (SimplePlanAction n []) = True" |
"plan_act_no_args (DurativePlanAction n [] d) = True" |
"plan_act_no_args _ = False"

fun timed_plan_action_durs_integer::"rat \<times> plan_action \<Rightarrow> bool" where
"timed_plan_action_durs_integer (t, SimplePlanAction n as) = (is_integer t)" |
"timed_plan_action_durs_integer (t, DurativePlanAction n as d) = (is_integer t \<and> is_integer d)"

fun PDDL_no_self_overlap::"(rat \<times> plan_action) \<Rightarrow> (rat \<times> plan_action) \<Rightarrow> bool" where
"PDDL_no_self_overlap (t, SimplePlanAction x _) (u, SimplePlanAction y _) = (x = y \<longrightarrow> t \<noteq> u)" |
"PDDL_no_self_overlap (_, SimplePlanAction _ _) (_, DurativePlanAction _ _ _) = True" |
"PDDL_no_self_overlap (_, DurativePlanAction _ _ _) (_, SimplePlanAction _ _) = True" |
"PDDL_no_self_overlap (t, DurativePlanAction x _ d) (u, DurativePlanAction y _ e) =
  (x = y \<longrightarrow> \<not>((t \<le> u \<and> u \<le> t + d) \<or> (u \<le> t \<and> t \<le> u + e)))"

definition "PDDL_plan_no_self_overlap \<equiv> list_pairwise PDDL_no_self_overlap tp"

fun ref_no_self_overlap::"(ast_temporal_action_schema \<times> int \<times> int) \<Rightarrow> (ast_temporal_action_schema \<times> int \<times> int) \<Rightarrow> bool" where
"ref_no_self_overlap (a, t, d) (b, u, e) = ((a = b) \<longrightarrow> \<not>((t \<le> u \<and> u \<le> t + d) \<or> (u \<le> t \<and> t \<le> u + e)))"

definition "ref_plan_no_self_overlap \<equiv> list_pairwise ref_no_self_overlap ref_plan"

lemma ref_no_self_overlap_refl:
  "\<forall>x y. ref_no_self_overlap x y \<longleftrightarrow> ref_no_self_overlap y x"
  by auto


text \<open>The abstract plan that can be obtained from this plan\<close>
sublocale imp_defs: temp_plan_for_problem_list_defs_int
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  init_spec goal_spec 0 props_spec actions_spec plan_imp  
  by unfold_locales simp

(* leaky abstraction? 
To do (low prio): move into other locale that converts a plan from a list into a function. *)
sublocale temp_plan_finite at_start_spec at_end_spec "set o over_all_spec"
  "(map_option (map_lower_bound rat_of_int)) o lower_spec" 
  "(map_option (map_upper_bound rat_of_int)) o upper_spec" 
  "set o pre_spec" "set o adds_spec" "set o dels_spec"
  "set init_spec" "set goal_spec" "rat_of_int 0" 
  "map_option (map_prod id (map_prod rat_of_int rat_of_int)) o plan_imp"
  apply unfold_locales 
  unfolding imp_defs.rat_impl.finite_plan_def
  unfolding comp_def
  unfolding dom_map_option
  unfolding plan_imp_def
  unfolding dom_nth_opt
  by blast
  

definition "abstr_plan \<equiv> (map_option (map_prod id (map_prod rat_of_int rat_of_int))) o plan_imp"

lemma ran_abstr_plan_ref_planE:
  assumes "(a, t, d) \<in> ran abstr_plan"
      and "\<And>a t d. (a, t, d) \<in> set ref_plan \<Longrightarrow> Q a (rat_of_int t) (rat_of_int d)"
    shows "Q a t d"
  using assms unfolding abstr_plan_def plan_imp_def ran_map_option comp_def ran_nth_opt 
  by auto

lemma ran_abstr_planI:
  "(a, t, d) \<in> set ref_plan \<Longrightarrow> (a, rat_of_int t, rat_of_int d) \<in> ran abstr_plan"
  unfolding abstr_plan_def plan_imp_def ran_map_option comp_def ran_nth_opt by force

lemma abstr_plan_binary_prop':
  assumes secondary:
    "i \<in> dom abstr_plan" 
    "j \<in> dom abstr_plan" 
    "i \<noteq> j"
    "abstr_plan i = Some (a, ta, da)"
    "abstr_plan j = Some (b, tb, db)"
  and refl:
    "\<forall>a ta da b tb db. Q a ta da b tb db = Q b tb db a ta da"
  and primary: "(\<forall>i j a ta da b tb db. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j 
      \<longrightarrow> (ref_plan ! i) = (a, ta, da) \<longrightarrow> (ref_plan ! j) = (b, tb, db)
      \<longrightarrow> Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db))"
shows "Q a ta da b tb db"
proof -
  show ?thesis
    using secondary 
    unfolding abstr_plan_def plan_imp_def 
    unfolding ran_map_option comp_def ran_nth_opt 
    unfolding dom_map_option comp_def dom_nth_opt
    unfolding map_option_eq_Some
    apply -
    apply (elim exE conjE)
    subgoal for x y
      apply (drule nth_opt_Some)+
      apply (induction x; induction y)
      unfolding map_prod_simp using primary by auto
    done
qed

lemma abstr_plan_binary_prop:
  assumes secondary:
    "i \<in> dom abstr_plan" 
    "j \<in> dom abstr_plan" 
    "i \<noteq> j"
    "abstr_plan i = Some (a, ta, da)"
    "abstr_plan j = Some (b, tb, db)"
  and refl:
    "\<forall>a ta da b tb db. Q a ta da b tb db = Q b tb db a ta da"
  and primary: "list_pairwise (\<lambda>(a, ta, da) (b, tb, db). Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)) ref_plan"
shows "Q a ta da b tb db"
proof -
  have "list_pairwise (\<lambda>(a, ta, da) (b, tb, db). Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)) ref_plan =
     (\<forall>i j. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j \<longrightarrow> 
      (case ref_plan ! i of (a, ta, da) \<Rightarrow> \<lambda>(b, tb, db). 
      Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)) (ref_plan ! j))" 
    using list_pairwise_nth_refl[of "\<lambda>(a, ta, da) (b, tb, db). Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)",
        where xs = ref_plan] using refl by simp
  hence 1: "(\<forall>i j a ta da b tb db. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j 
      \<longrightarrow> (ref_plan ! i) = (a, ta, da) \<longrightarrow> (ref_plan ! j) = (b, tb, db)
      \<longrightarrow> Q a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db))"
    using primary by fastforce
  show ?thesis using assms abstr_plan_binary_prop' 1 by blast
qed

(* --- *)
lemma duration_matches_imp_sat_lb: 
  assumes "duration_matches d dc ps as"
      and "\<not>is_Func_Const dc"
  shows "imp_defs.rat_impl.satisfies_lower_bound (dc_to_lb dc) d"
proof -
  have nf: "dc_no_func dc" using assms(2) unfolding is_Func_Const_def by simp
  obtain dop e where de: "dc = DurationConstraint dop e" by (cases dc) auto
  have "dc_no_func (DurationConstraint dop e)" using nf de by simp
  then obtain x where e: "e = ConstantExpr x" by (cases e) auto
  show ?thesis using assms(1) unfolding de e by (cases dop) auto
qed

lemma durations_match_imp_sat_lb:
  assumes "durations_match d dcs ps as"
      and "list_all (\<lambda>x. \<not>is_Func_Const x) dcs"
    shows "imp_defs.rat_impl.satisfies_lower_bound (dc_list_lower dcs) d"
proof (rule dc_list_lower_propI)
  show "list_all (\<lambda>lb. imp_defs.rat_impl.satisfies_lower_bound lb d) (map dc_to_lb dcs)"
    unfolding list_all_iff
  proof (intro ballI)
    fix lb assume "lb \<in> set (map dc_to_lb dcs)"
    then obtain dc where dc: "dc \<in> set dcs" and lb: "lb = dc_to_lb dc" by auto
    have "duration_matches d dc ps as"
      using assms(1) dc unfolding durations_match_def list_all_iff by blast
    moreover have "\<not> is_Func_Const dc" using assms(2) dc unfolding list_all_iff by blast
    ultimately show "imp_defs.rat_impl.satisfies_lower_bound lb d"
      unfolding lb by (rule duration_matches_imp_sat_lb)
  qed
qed simp

lemma duration_matches_imp_sat_ub: 
  assumes "duration_matches d dc ps as"
      and "\<not>is_Func_Const dc"
  shows "imp_defs.rat_impl.satisfies_upper_bound (dc_to_ub dc) d"
proof -
  have nf: "dc_no_func dc" using assms(2) unfolding is_Func_Const_def by simp
  obtain dop e where de: "dc = DurationConstraint dop e" by (cases dc) auto
  have "dc_no_func (DurationConstraint dop e)" using nf de by simp
  then obtain x where e: "e = ConstantExpr x" by (cases e) auto
  show ?thesis using assms(1) unfolding de e by (cases dop) auto
qed

lemma durations_match_imp_sat_ub:
  assumes "durations_match d dcs ps as"
      and "list_all (\<lambda>x. \<not>is_Func_Const x) dcs"
    shows "imp_defs.rat_impl.satisfies_upper_bound (dc_list_upper dcs) d"
proof (rule dc_list_upper_propI)
  show "list_all (\<lambda>ub. imp_defs.rat_impl.satisfies_upper_bound ub d) (map dc_to_ub dcs)"
    unfolding list_all_iff
  proof (intro ballI)
    fix ub assume "ub \<in> set (map dc_to_ub dcs)"
    then obtain dc where dc: "dc \<in> set dcs" and ub: "ub = dc_to_ub dc" by auto
    have "duration_matches d dc ps as"
      using assms(1) dc unfolding durations_match_def list_all_iff by blast
    moreover have "\<not> is_Func_Const dc" using assms(2) dc unfolding list_all_iff by blast
    ultimately show "imp_defs.rat_impl.satisfies_upper_bound ub d"
      unfolding ub by (rule duration_matches_imp_sat_ub)
  qed
qed simp

lemma integers_sat_lower_bounds:
  assumes "imp_defs.rat_impl.satisfies_lower_bound x d"
      and "pred_option (pred_lower_bound is_integer) x"
      and "is_integer d"
    shows "imp_defs.rat_impl.satisfies_lower_bound (map_option (map_lower_bound (\<lambda>x. rat_of_int \<lfloor>x\<rfloor>)) x) (rat_of_int \<lfloor>d\<rfloor>)"
  using assms apply (cases x)
   apply simp
  subgoal for a
    apply (cases a)
    using is_integer_floor_less Archimedean_Field.floor_mono
    by auto
  done

lemma integers_sat_upper_bounds:
  assumes "imp_defs.rat_impl.satisfies_upper_bound x d"
      and "pred_option (pred_upper_bound is_integer) x"
      and "is_integer d"
    shows "imp_defs.rat_impl.satisfies_upper_bound (map_option (map_upper_bound (\<lambda>x. rat_of_int \<lfloor>x\<rfloor>)) x) (rat_of_int \<lfloor>d\<rfloor>)"
  using assms apply (cases x)
   apply simp
  subgoal for a
    apply (cases a)
    using is_integer_floor_less Archimedean_Field.floor_mono
    by auto
  done

lemmas integers_sat_bounds = integers_sat_lower_bounds integers_sat_upper_bounds

lemma ground_act_pres_conv_pre_spec:
  assumes "ground_act_pres_pos a"
  shows "to_predicate ` Atom `(atoms (ground_action.precondition a)) = set (pre_spec a)"
  using assms
proof (induction a)
  case (GroundAction pre eff)
  hence "pos_conj_form pre" by simp
  then show ?case using pos_conj_form_predicates by simp
qed

lemma add_preds: "to_predicate ` set (adds (ground_action.effect a)) = set (adds_spec a)"
  apply (cases a) by simp

lemma del_preds: "to_predicate ` set (dels (ground_action.effect a)) = set (dels_spec a)"
  apply (cases a) by simp

lemma acts_non_intrf_imp_mutex_snap_action:
  assumes non_int: "acts_non_intrf a b"
      and pres_pos: "ground_act_pres_pos a" "ground_act_pres_pos b"
      and wf: "wf_ground_action a" "wf_ground_action b"
      and no_args: "ground_act_no_args a" "ground_act_no_args b"
  shows "\<not> imp_defs.rat_impl.set_impl.mutex_snap_action a b"
proof -
  have "to_predicate ` Atom `(atoms (ground_action.precondition a)) = set (pre_spec a)"
    using ground_act_pres_conv_pre_spec pres_pos by auto
  moreover
  have "to_predicate ` set (adds (ground_action.effect a)) = set (adds_spec a)"
    using add_preds by simp
  moreover
  have "to_predicate ` set (dels (ground_action.effect a)) = set (dels_spec a)"
    using del_preds by simp
  moreover
  have "to_predicate ` Atom `(atoms (ground_action.precondition b)) = set (pre_spec b)"
    using ground_act_pres_conv_pre_spec pres_pos by auto
  moreover
  have "to_predicate ` set (adds (ground_action.effect b)) = set (adds_spec b)"
    using add_preds by simp
  moreover
  have "to_predicate ` set (dels (ground_action.effect b)) = set (dels_spec b)"
    using del_preds by simp
  moreover
  note pad_alt = calculation[symmetric]
  
  ultimately have True by simp (* clearing calculation *)

  have x: "(\<not> x \<noteq> y) = (x = y)" for x y by simp (* SMT.smt_arith_simplify(277) *)
                           
  have inj_to_predicate: "inj_on to_predicate {x. is_predAtom x \<and> form_preds_no_args x}" (is "inj_on to_predicate ?S")
    apply (rule inj_onI)
    apply (elim CollectE conjE is_predAtom.elims)
    unfolding form_preds_no_args_def 
    apply (drule bspec, simp)+
    apply (erule atom_no_args.elims)+
    by auto
    
  have "Atom ` atoms (ground_action.precondition a) \<subseteq> ?S" 
    using is_pos_conj_atoms_preds pres_pos no_args
    apply (induction a)
    using form_preds_no_args_imp_atoms_no_args by auto
  moreover
  have "set (adds (ground_action.effect a)) \<subseteq> ?S" 
    using no_args wf apply (induction a)
    unfolding ground_action.sel
    subgoal for pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  have "set (dels (ground_action.effect a)) \<subseteq> ?S" 
    using no_args wf apply (induction a)
    unfolding ground_action.sel
    subgoal for pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  have "Atom ` atoms (ground_action.precondition b) \<subseteq> ?S" 
    using is_pos_conj_atoms_preds pres_pos no_args
    apply (induction b)
    using form_preds_no_args_imp_atoms_no_args by auto
  moreover
  have "set (adds (ground_action.effect b)) \<subseteq> ?S" 
    using no_args wf apply (induction b)
    unfolding ground_action.sel
    subgoal for pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  have "set (dels (ground_action.effect b)) \<subseteq> ?S" 
    using no_args wf apply (induction b)
    unfolding ground_action.sel
    subgoal for pre eff
      apply (induction eff)
      unfolding ground_act_no_args.simps list_all_iff 
      using wf_fmla_atom_imp_is_predAtom by fastforce
    done
  moreover
  note in_set = calculation
  ultimately have True by simp (* clearing calculation *)

  

  show ?thesis
    unfolding imp_defs.rat_impl.set_impl.mutex_snap_action_def
    unfolding comp_def pad_alt
    unfolding de_Morgan_disj x 
    unfolding image_Un[symmetric]
    apply (intro conjI)
    using non_int 
    unfolding acts_non_intrf_def Let_def
    using inj_on_image_Int[symmetric, OF inj_to_predicate] in_set 
    by simp+
qed

lemma ground_non_action_not_mutex:
  shows "\<not>imp_defs.rat_impl.set_impl.mutex_snap_action ground_non_action b"
        "\<not>imp_defs.rat_impl.set_impl.mutex_snap_action b ground_non_action"
  unfolding ground_non_action_def imp_defs.rat_impl.set_impl.mutex_snap_action_def by simp+

lemma ground_non_action_non_intrf:
  shows "acts_non_intrf ground_non_action b"
        "acts_non_intrf b ground_non_action"
  unfolding ground_non_action_def acts_non_intrf_def lvalues_def additive_lvalues_def rvalues_def by simp+


lemma ground_non_action_no_effs:
  assumes "T \<subseteq> {ground_non_action}"
  shows "imp_defs.rat_impl.apply_effects (S \<union> T) q = imp_defs.rat_impl.apply_effects S q"
proof -
  have "(\<Union>x\<in>T. set (dels_spec x)) = {}"
    using assms ground_non_action_dels by fastforce
  moreover
  have "(\<Union>x\<in>T. set (adds_spec x)) = {}"  
    using assms ground_non_action_adds by fastforce
  ultimately
  show ?thesis unfolding imp_defs.rat_impl.apply_effects_def
    unfolding comp_def unfolding UN_Un by blast
qed

lemma ground_non_action_no_pres:
  assumes "T \<subseteq> {ground_non_action}"
  shows "\<Union> ((set \<circ> pre_spec) ` (S \<union> T)) = \<Union> ((set \<circ> pre_spec) ` S)"
proof -
  have "(\<Union>x\<in>T. set (pre_spec x)) = {}"
    using assms ground_non_action_pre by fastforce
  thus ?thesis 
    unfolding comp_def unfolding UN_Un 
    by blast
qed

end

locale valid_ground_plan =
  ground_ast_problem P +
  ground_plan_defs P tp
  for P::ast_temporal_problem 
  and tp::"(rat \<times> plan_action) list" +
assumes valid_temporal_state_seq_plan: "valid_temporal_state_seq_plan tp"
    and pddl_nso: "PDDL_plan_no_self_overlap"
    and plan_acts_durs_integer: "list_all (timed_plan_action_durs_integer) tp"
begin

lemma wf_plan: "wf_plan tp" using valid_temporal_state_seq_plan valid_temporal_state_seq_plan_def valid_temporal_state_seq_plan_from_def by simp

text \<open>We obtain some other constants\<close>
definition "htps_and_final_state \<equiv> 
  let
    (htps, final_state) = (SOME hm. (\<lambda>(htps, M'). htps_seq tp htps \<and> valid_temporal_state_seq I htps tp M' \<and> valuation M' \<Turnstile>\<^sub>m (goal P)) hm)
  in
  (htps, final_state)"

thm Hilbert_Choice.someI

definition "htps = fst htps_and_final_state"
definition "final_state = snd htps_and_final_state"

lemma htps_seq_htps: "htps_seq tp htps"
  and valid_temporal_state_seq_final_state: "valid_temporal_state_seq I htps tp final_state" 
  and final_state_sat_goal: "valuation final_state \<Turnstile>\<^sub>m (goal P)"
proof -
  let ?P = "(\<lambda>(htps, M'). htps_seq tp htps \<and> valid_temporal_state_seq I htps tp M' \<and> valuation M' \<Turnstile>\<^sub>m (goal P))"
  have P: "\<exists>x. (\<lambda>(htps, M'). htps_seq tp htps \<and> valid_temporal_state_seq I htps tp M' \<and> valuation M' \<Turnstile>\<^sub>m (goal P)) x"
    using valid_temporal_state_seq_plan unfolding valid_temporal_state_seq_plan_def valid_temporal_state_seq_plan_from_def by auto
  have "?P htps_and_final_state" using Hilbert_Choice.someI_ex[of ?P, OF P]  htps_and_final_state_def by auto
  thus "htps_seq tp htps"
       "valid_temporal_state_seq I htps tp final_state"
       "valuation final_state \<Turnstile>\<^sub>m goal P"
    unfolding htps_def final_state_def by auto
qed


text \<open>Mutex re-bridge.  The new state-sequence validity carries, at every happening
  time point \<open>t\<^sub>i\<close>, the position-based @{term "list_pairwise acts_non_intrf
  (acts_of_temporal_plan_at t\<^sub>i tp)"}.  We restate it as the per-snap-pair non-interference
  form consumed by the NTA reduction's mutex machinery.  Since @{term acts_non_intrf} is
  reflexively false (a snap interferes with itself), two \<^emph>\<open>distinct\<close> snaps occurring at the
  same htp are necessarily at distinct list positions and hence non-interfering; this is the
  content of @{thm list_pairwise_as_nonrec} (no separation / no-self-overlap collapses the
  list-position mutex to plan-entry-pair non-interference).\<close>

lemma htps_acts_list_pairwise:
  assumes "t\<^sub>i \<in> set htps"
  shows "list_pairwise acts_non_intrf (acts_of_temporal_plan_at t\<^sub>i tp)"
  using valid_temporal_state_seq_list_pairwise_acts[OF valid_temporal_state_seq_final_state assms] .

lemma all_htps_acts_non_intrf:
  assumes "t\<^sub>i \<in> set htps"
  shows "(\<forall>a \<in> set (acts_of_temporal_plan_at t\<^sub>i tp).
            \<forall>b \<in> set (acts_of_temporal_plan_at t\<^sub>i tp). a \<noteq> b \<longrightarrow> acts_non_intrf a b)"
  using list_pairwise_acts_distinctD[OF htps_acts_list_pairwise[OF assms]] by blast

lemma all_htps_acts_non_intrf':
  assumes "t\<^sub>i \<in> set htps"
      and "a \<in> set (acts_of_temporal_plan_at t\<^sub>i tp)"
      and "b \<in> set (acts_of_temporal_plan_at t\<^sub>i tp)"
      and "a \<noteq> b"
  shows "acts_non_intrf a b"
  using list_pairwise_acts_distinctD[OF htps_acts_list_pairwise[OF assms(1)] assms(2,3,4)] .

(* Needs an assumption that durations are integers. *)

lemma wf_plan_actions:
  assumes "(t, a) \<in> set tp"
  shows "wf_plan_action a" 
  using assms valid_temporal_state_seq_plan 
  unfolding valid_temporal_state_seq_plan_def valid_temporal_state_seq_plan_from_def wf_plan_def 
  by blast

lemma simple_acts_in_plan:  
  assumes "(t, a) \<in> simple_acts tp"
  shows "(t, a) \<in> set tp" using assms unfolding simple_acts_def by simp

lemma durative_acts_in_plan:
  assumes "(t, a) \<in> durative_acts tp"
  shows "(t, a) \<in> set tp" using assms unfolding durative_acts_def by simp

lemma resolve_schema_name:
  assumes "resolve_temporal_action_schema n = Some a"
  shows "ast_temporal_action_schema_name a = n"
  using assms unfolding resolve_temporal_action_schema_def
  by (auto dest: index_by_eq_SomeD)

lemma simple_plan_action_schema_type1:
  assumes "wf_plan_action (SimplePlanAction n args)"
  shows "\<exists>params pre eff. resolve_temporal_action_schema n
            = Some (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff))"
proof -
  obtain a where res: "resolve_temporal_action_schema n = Some a"
    using assms by (cases "resolve_temporal_action_schema n") auto
  obtain h b where a: "a = SimpleActionSchema h b"
    using assms res by (cases a) auto
  have nm: "ast_action_head.name h = n"
    using resolve_schema_name[OF res] unfolding a by simp
  obtain params where h: "h = ActionHead n params"
    using nm by (cases h) simp
  obtain pre eff where b: "b = SimpleActionBody pre eff"
    by (cases b) simp
  show ?thesis using res unfolding a h b by blast
qed

lemma durative_plan_action_schema_type1:
  assumes "wf_plan_action (DurativePlanAction n args d)"
  shows "\<exists>params dcs pre eff. resolve_temporal_action_schema n
            = Some (DurativeActionSchema (ActionHead n params) (DurativeActionBody dcs pre eff))"
proof -
  obtain a where res: "resolve_temporal_action_schema n = Some a"
    using assms by (cases "resolve_temporal_action_schema n") auto
  obtain h b where a: "a = DurativeActionSchema h b"
    using assms res by (cases a) auto
  have nm: "ast_action_head.name h = n"
    using resolve_schema_name[OF res] unfolding a by simp
  obtain params where h: "h = ActionHead n params"
    using nm by (cases h) simp
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff"
    by (cases b) simp
  show ?thesis using res unfolding a h b by blast
qed

lemma durative_plan_action_durs:
  assumes "wf_plan_action (DurativePlanAction n as d)"
  shows "0 \<le> d"
  using assms by (auto split: option.splits)

lemma simple_act_ex_simple_plan_act:
  assumes "(t, a) \<in> simple_acts tp"
  shows "\<exists>n as. a = SimplePlanAction n as"
  using assms unfolding simple_acts_def is_act_simple apply (cases a) by auto

lemma res_simple_act_name:
  assumes "(t, a) \<in> simple_acts tp"
  shows "\<exists>ps pre eff. resolve_temporal_action_schema (plan_action.name a) = Some (SimpleActionSchema (ActionHead (plan_action.name a) ps) (SimpleActionBody pre eff))"
proof -
  obtain n as where a: "a = SimplePlanAction n as"
    using assms[THEN simple_act_ex_simple_plan_act] by blast
  have "wf_plan_action a" using wf_plan_actions assms[THEN simple_acts_in_plan] by blast
  then obtain params pre eff
    where "resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff))"
    using simple_plan_action_schema_type1 unfolding a by blast
  thus ?thesis unfolding a by auto
qed

lemma durative_act_ex_durative_plan_act:
  assumes "(t, a) \<in> durative_acts tp"
  shows "\<exists>n as d. a = DurativePlanAction n as d"
  using assms unfolding durative_acts_def is_act_simple 
  apply (cases a) by auto

lemma res_durative_act_name:
  assumes "(t, a) \<in> durative_acts tp"
  shows "\<exists>ps dcs pre eff. resolve_temporal_action_schema (plan_action.name a) = Some (DurativeActionSchema (ActionHead (plan_action.name a) ps) (DurativeActionBody dcs pre eff))"
proof -
  obtain n as d where a: "a = DurativePlanAction n as d"
    using assms[THEN durative_act_ex_durative_plan_act] by blast
  have "wf_plan_action a" using wf_plan_actions assms[THEN durative_acts_in_plan] by blast
  then obtain params dcs pre eff
    where "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n params) (DurativeActionBody dcs pre eff))"
    using durative_plan_action_schema_type1 unfolding a by blast
  thus ?thesis unfolding a by auto
qed

lemma in_simple_actsE:
  assumes "(t, a) \<in> simple_acts tp"
      and "\<And>n as. (t, SimplePlanAction n as) \<in> set tp \<Longrightarrow> Q (SimplePlanAction n as) t tp"
    shows "Q a t tp"
  using assms unfolding simple_acts_def is_act_simple 
  apply (cases a)
  by auto

lemma in_simple_actsE':
  assumes "(t, a) \<in> simple_acts tp"
      and "\<And>n as. (t, SimplePlanAction n as) \<in> set tp \<Longrightarrow> thesis"
    shows "thesis"
proof -
  have mem: "(t, a) \<in> set tp" and "is_act_simple a"
    using assms(1) unfolding simple_acts_def by auto
  then obtain n as where "a = SimplePlanAction n as"
    unfolding is_act_simple_def by (cases a) auto
  thus thesis using mem assms(2) by blast
qed

lemma in_durative_actsE:
  assumes "(t, a) \<in> durative_acts tp"
      and "\<And>n as d. (t, DurativePlanAction n as d) \<in> set tp \<Longrightarrow> Q (DurativePlanAction n as d) t tp"
    shows "Q a t tp"
proof -
  have mem: "(t, a) \<in> set tp" and "\<not> is_act_simple a"
    using assms(1) unfolding durative_acts_def by auto
  then obtain n as d where "a = DurativePlanAction n as d"
    unfolding is_act_simple_def by (cases a) auto
  thus ?thesis using mem assms(2) by blast
qed

lemma in_durative_actsE':
  assumes "(t, a) \<in> durative_acts tp"
      and "\<And>n as d. (t, DurativePlanAction n as d) \<in> set tp \<Longrightarrow> thesis"
    shows "thesis"
proof -
  have mem: "(t, a) \<in> set tp" and "\<not> is_act_simple a"
    using assms(1) unfolding durative_acts_def by auto
  then obtain n as d where "a = DurativePlanAction n as d"
    unfolding is_act_simple_def by (cases a) auto
  thus thesis using mem assms(2) by blast
qed



text \<open>The acts of a plan at a time point are wf\<close>

lemma acts_of_temporal_plan_at_wf:
  assumes "a \<in> set (acts_of_temporal_plan_at t tp)"
  shows "wf_ground_action a"
  using wf_acts_of_temporal_plan_at[OF wf_plan assms] .

text \<open>Plan actions provide no arguments\<close>

lemma plan_acts_no_args: "list_all (\<lambda>x. plan_act_no_args (snd x)) tp"
proof -
  { fix t a 
    assume "(t, a) \<in> set tp"
    hence wf: "wf_plan_action a" using wf_plan_actions by auto
    have "plan_act_no_args a"
    proof (cases a)
      case a: (SimplePlanAction n ps)
      hence wf: "wf_plan_action (SimplePlanAction n ps)" using wf by auto
      then obtain pre eff as  where
        res: "resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n as) (SimpleActionBody pre eff))"
        using simple_plan_action_schema_type1 by blast
      have pm: "action_params_match (ActionHead n as) ps" using wf res by auto
      have "as = []" using resolve_temporal_action_schema_def index_by_eq_SomeD acts_no_params res
        unfolding list_all_iff by fastforce
      then show ?thesis using pm a action_params_match_def by simp
    next
      case a: (DurativePlanAction n ps d)
      hence wf: "wf_plan_action (DurativePlanAction n ps d)" using wf by auto
      then obtain pre eff as dcs where
        res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n as) (DurativeActionBody pre eff dcs))"
        using durative_plan_action_schema_type1 by blast
      have pm: "action_params_match (ActionHead n as) ps" using wf res by auto
      have "as = []" using resolve_temporal_action_schema_def index_by_eq_SomeD acts_no_params res
        unfolding list_all_iff by fastforce
      then show ?thesis using pm a action_params_match_def by simp
    qed
  }
  thus ?thesis unfolding list_all_iff by fastforce
qed

text \<open>Duration-fold bridge: the FPS @{const acts_of_temporal_plan_at} resolves the plan actions
  through @{const res_inst}/@{const res_inst_snap_action}, whose durative snaps
  @{term "the (res_inst_snap_action \<pi> At_Start)"} fold the duration constraints into the
  snap precondition as numeric duration atoms and carry the concrete duration through
  @{const inst_formula}/@{const inst_duration_in_ast_effect}.  The NTA-target snaps
  @{const at_start_spec}/@{const at_end_spec} are the same instantiation stripped of the
  duration constraints (\<open>dc = []\<close>, \<open>dur = 0\<close>) — those are carried separately by the network's
  clock bounds, not the precondition.  We introduce a \<^emph>\<open>simplified\<close> actions-at-a-time list that
  mirrors @{const acts_of_temporal_plan_at}'s membership structure but with the durative snaps
  replaced by the project snaps, and bridge the two through @{const to_literals} (which drops the
  numeric duration atoms) and @{const ast_effect.adds}/@{const ast_effect.dels} (which ignore the
  numeric effect component).  A simple action's start snap already \<^emph>\<open>is\<close> its project snap, so
  @{const res_inst} is reused verbatim there.\<close>

definition snap_of_plan_action_at_simplified :: "time \<Rightarrow> (time \<times> plan_action) \<Rightarrow> ground_action list" where
  "snap_of_plan_action_at_simplified t p \<equiv> (case p of
      (t\<^sub>\<pi>, SimplePlanAction n args) \<Rightarrow>
        (if t = t\<^sub>\<pi> then [the (res_inst (SimplePlanAction n args))] else [])
    | (t\<^sub>\<pi>, DurativePlanAction n args dur) \<Rightarrow>
        (if t = t\<^sub>\<pi> then [at_start_spec (the (resolve_temporal_action_schema n))] else []) @
        (if t = t\<^sub>\<pi> + dur then [at_end_spec (the (resolve_temporal_action_schema n))] else []))"

definition acts_of_plan_at_simplified :: "time \<Rightarrow> plan \<Rightarrow> ground_action list" where
  "acts_of_plan_at_simplified t\<^sub>i \<pi>s = concat (map (snap_of_plan_action_at_simplified t\<^sub>i) \<pi>s)"

lemma snap_of_plan_action_at_simplified_simps:
  "snap_of_plan_action_at_simplified t (t\<^sub>\<pi>, SimplePlanAction n args) =
     (if t = t\<^sub>\<pi> then [the (res_inst (SimplePlanAction n args))] else [])"
  "snap_of_plan_action_at_simplified t (t\<^sub>\<pi>, DurativePlanAction n args dur) =
     (if t = t\<^sub>\<pi> then [at_start_spec (the (resolve_temporal_action_schema n))] else []) @
     (if t = t\<^sub>\<pi> + dur then [at_end_spec (the (resolve_temporal_action_schema n))] else [])"
  unfolding snap_of_plan_action_at_simplified_def by simp_all

lemma in_acts_of_plan_at_simplifiedE:
  assumes "a \<in> set (acts_of_plan_at_simplified t p)"
      and "\<And>n args. (t, SimplePlanAction n args) \<in> set p \<Longrightarrow> a = the (res_inst (SimplePlanAction n args)) \<Longrightarrow> Q a t p"
          "\<And>n args dur. (t, DurativePlanAction n args dur) \<in> set p \<Longrightarrow> a = at_start_spec (the (resolve_temporal_action_schema n)) \<Longrightarrow> Q a t p"
          "\<And>t' n args dur. (t', DurativePlanAction n args dur) \<in> set p \<Longrightarrow> t = t' + dur \<Longrightarrow> a = at_end_spec (the (resolve_temporal_action_schema n)) \<Longrightarrow> Q a t p"
  shows "Q a t p"
proof -
  from assms(1) obtain t\<^sub>\<pi> \<pi> where
    mem: "(t\<^sub>\<pi>, \<pi>) \<in> set p"
    and a_in: "a \<in> set (snap_of_plan_action_at_simplified t (t\<^sub>\<pi>, \<pi>))"
    unfolding acts_of_plan_at_simplified_def by auto
  show ?thesis
  proof (cases \<pi>)
    case (SimplePlanAction n args)
    hence "t = t\<^sub>\<pi>" and "a = the (res_inst (SimplePlanAction n args))"
      using a_in unfolding SimplePlanAction snap_of_plan_action_at_simplified_simps
      by (auto split: if_splits)
    thus ?thesis using assms(2) mem SimplePlanAction by blast
  next
    case (DurativePlanAction n args dur)
    consider "t = t\<^sub>\<pi> \<and> a = at_start_spec (the (resolve_temporal_action_schema n))"
      | "t = t\<^sub>\<pi> + dur \<and> a = at_end_spec (the (resolve_temporal_action_schema n))"
      using a_in unfolding DurativePlanAction snap_of_plan_action_at_simplified_simps
      by (auto split: if_splits)
    thus ?thesis
    proof cases
      case 1 thus ?thesis using assms(3) mem DurativePlanAction by blast
    next
      case 2 thus ?thesis using assms(4) mem DurativePlanAction by blast
    qed
  qed
qed

lemma acts_of_plan_at_simplified_res_instI:
  assumes "(t, SimplePlanAction n args) \<in> set p"
  shows "the (res_inst (SimplePlanAction n args)) \<in> set (acts_of_plan_at_simplified t p)"
  unfolding acts_of_plan_at_simplified_def set_concat set_map
  apply (rule UN_I[OF imageI[OF assms]])
  unfolding snap_of_plan_action_at_simplified_simps by simp

lemma acts_of_plan_at_simplified_startI:
  assumes "(t, DurativePlanAction n args dur) \<in> set p"
  shows "at_start_spec (the (resolve_temporal_action_schema n)) \<in> set (acts_of_plan_at_simplified t p)"
  unfolding acts_of_plan_at_simplified_def set_concat set_map
  apply (rule UN_I[OF imageI[OF assms]])
  unfolding snap_of_plan_action_at_simplified_simps by simp

lemma acts_of_plan_at_simplified_endI:
  assumes "(t', DurativePlanAction n args dur) \<in> set p"
      and "t = t' + dur"
  shows "at_end_spec (the (resolve_temporal_action_schema n)) \<in> set (acts_of_plan_at_simplified t p)"
  unfolding acts_of_plan_at_simplified_def set_concat set_map
  apply (rule UN_I[OF imageI[OF assms(1)]])
  unfolding snap_of_plan_action_at_simplified_simps using assms(2) by simp

text \<open>Effect bridge.  The effect component of @{const inst_snap_action_body_elements} is
  @{term "inst_duration_in_ast_effect (map_ast_effect f (\<And>\<^sub>e\<^sub>f\<^sub>f (filter_time_spec ta eff))) dur"};
  @{const inst_duration_in_ast_effect} only rewrites the numeric-effect component
  (@{const ast_effect.adds}/@{const ast_effect.dels} are untouched), and the duration
  constraints @{term dc} do not appear in the effect at all.  Hence the FPS durative snap
  (built at @{term dc} and the concrete duration) and the project snap (built at \<open>dc = []\<close>,
  \<open>dur = 0\<close>) have literally identical @{const ast_effect.adds} and @{const ast_effect.dels}.\<close>

lemma inst_snap_action_body_elements_adds_indep:
  "ast_effect.adds (ground_action.effect (inst_snap_action_body_elements dc cond eff f dur ta))
     = ast_effect.adds (ground_action.effect (inst_snap_action_body_elements dc' cond' eff f dur' ta))"
  for f :: "term \<Rightarrow> object"
  by (cases "\<And>\<^sub>e\<^sub>f\<^sub>f (filter_time_spec ta eff)")
     (simp add: inst_snap_action_body_elements.simps)

lemma inst_snap_action_body_elements_dels_indep:
  "ast_effect.dels (ground_action.effect (inst_snap_action_body_elements dc cond eff f dur ta))
     = ast_effect.dels (ground_action.effect (inst_snap_action_body_elements dc' cond' eff f dur' ta))"
  for f :: "term \<Rightarrow> object"
  by (cases "\<And>\<^sub>e\<^sub>f\<^sub>f (filter_time_spec ta eff)")
     (simp add: inst_snap_action_body_elements.simps)

text \<open>The FPS durative snap and the project snap thus have identical
  @{const ast_effect.adds}/@{const ast_effect.dels}.\<close>

lemma res_inst_snap_start_adds:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "ast_effect.adds (ground_action.effect (the (res_inst_snap_action (DurativePlanAction n [] dur) At_Start)))
       = ast_effect.adds (ground_action.effect (at_start_spec (the (resolve_temporal_action_schema n))))"
  using assms inst_snap_action_body_elements_adds_indep by simp

lemma res_inst_snap_start_dels:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "ast_effect.dels (ground_action.effect (the (res_inst_snap_action (DurativePlanAction n [] dur) At_Start)))
       = ast_effect.dels (ground_action.effect (at_start_spec (the (resolve_temporal_action_schema n))))"
  using assms inst_snap_action_body_elements_dels_indep by simp

lemma res_inst_snap_end_adds:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "ast_effect.adds (ground_action.effect (the (res_inst_snap_action (DurativePlanAction n [] dur) At_End)))
       = ast_effect.adds (ground_action.effect (at_end_spec (the (resolve_temporal_action_schema n))))"
  using assms inst_snap_action_body_elements_adds_indep by simp

lemma res_inst_snap_end_dels:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "ast_effect.dels (ground_action.effect (the (res_inst_snap_action (DurativePlanAction n [] dur) At_End)))
       = ast_effect.dels (ground_action.effect (at_end_spec (the (resolve_temporal_action_schema n))))"
  using assms inst_snap_action_body_elements_dels_indep by simp


text \<open>The ground actions of the plan at a timepoint have no arguments\<close>

lemma acts_of_temporal_plan_at_no_args:
  assumes "a \<in> set (acts_of_plan_at_simplified t tp)"
  shows "ground_act_no_args a"
proof (rule in_acts_of_plan_at_simplifiedE[OF assms], goal_cases)
  case (1 n as)
  have mem: "(t, SimplePlanAction n as) \<in> set tp" using 1 by simp
  hence wfpa: "wf_plan_action (SimplePlanAction n as)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (SimpleActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain pre eff where bb: "b = SimpleActionBody pre eff"
    by (cases b)
  have sch: "SimpleActionSchema h (SimpleActionBody pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] bb by simp
  have "ground_act_no_args (instantiate_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff)) as)"
    using instantiate_action_schema_no_params[OF act_no_params[OF sch] 
        resolve_temporal_action_wf[OF res[unfolded bb]] 
        act_pres_pos_spec[OF sch] act_conds_no_args_spec[OF sch]] .
  thus ?case
    using 1 res bb by simp
next
  case (2 n as dur)
  have mem: "(t, DurativePlanAction n as dur) \<in> set tp" using 2 by simp
  hence wfpa: "wf_plan_action (DurativePlanAction n as dur)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff"
    by (cases b)
  have sch: "DurativeActionSchema h (DurativeActionBody dcs pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] b by simp
  have "ground_act_no_args (at_start_spec (DurativeActionSchema h (DurativeActionBody dcs pre eff)))"
    unfolding at_start_spec.simps
    using inst_snap_action_no_params[OF act_no_params[OF sch] resolve_temporal_action_wf[OF res[unfolded b]] act_pres_pos_spec[OF sch] act_conds_no_args_spec[OF sch]] .
  thus ?case
    using 2 res b by simp
next
  case (3 t' n as dur)
  have mem: "(t', DurativePlanAction n as dur) \<in> set tp" using 3 by simp
  hence wfpa: "wf_plan_action (DurativePlanAction n as dur)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff"
    by (cases b)
  have sch: "DurativeActionSchema h (DurativeActionBody dcs pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] b by simp
  have "ground_act_no_args (at_end_spec (DurativeActionSchema h (DurativeActionBody dcs pre eff)))"
    unfolding at_end_spec.simps
    using inst_snap_action_no_params[OF act_no_params[OF sch] resolve_temporal_action_wf[OF res[unfolded b]] act_pres_pos_spec[OF sch] act_conds_no_args_spec[OF sch]] .
  thus ?case
    using 3 res b by simp
qed

text \<open>The ground actions of the simplified plan at a timepoint are well-formed.\<close>

lemma acts_of_plan_at_simplified_wf:
  assumes "a \<in> set (acts_of_plan_at_simplified t tp)"
  shows "wf_ground_action a"
proof (rule in_acts_of_plan_at_simplifiedE[OF assms], goal_cases)
  case (1 n as)
  have mem: "(t, SimplePlanAction n as) \<in> set tp" using 1 by simp
  hence wfpa: "wf_plan_action (SimplePlanAction n as)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (SimpleActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain pre eff where bb: "b = SimpleActionBody pre eff" by (cases b)
  have sch: "SimpleActionSchema h (SimpleActionBody pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] bb by simp
  have wfsch: "wf_temporal_action_schema (SimpleActionSchema h b)"
    using resolve_temporal_action_wf res by blast
  have pm: "action_params_match h as"
    using wf_plan_action_params_match[OF wf_plan mem] res by simp
  have "wf_ground_action (instantiate_temporal_action_schema (SimpleActionSchema h b) as)"
    using wf_inst_temporal_action_schema[OF pm wfsch] .
  thus ?case using 1 res by simp
next
  case (2 n as dur)
  have mem: "(t, DurativePlanAction n as dur) \<in> set tp" using 2 by simp
  hence wfpa: "wf_plan_action (DurativePlanAction n as dur)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff" by (cases b)
  have sch: "DurativeActionSchema h (DurativeActionBody dcs pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] b by simp
  show ?case using 2 start_snaps_wf[OF sch] res b by simp
next
  case (3 t' n as dur)
  have mem: "(t', DurativePlanAction n as dur) \<in> set tp" using 3 by simp
  hence wfpa: "wf_plan_action (DurativePlanAction n as dur)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff" by (cases b)
  have sch: "DurativeActionSchema h (DurativeActionBody dcs pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] b by simp
  show ?case using 3 end_snaps_wf[OF sch] res b by simp
qed

text \<open>Plan actions have no arguments\<close>

lemma simple_action_in_ref_plan:
  assumes "(SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff), t, d) \<in> set ref_plan"
  shows "\<exists>as. (rat_of_int t, SimplePlanAction n as) \<in> set tp \<and> resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
proof -
  obtain t' a where
    a: "(t', a) \<in> set tp"
    "timed_plan_action_to_ref_plan_action (t', a) = (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff), t, d)"
    "wf_plan_action a"
    using assms wf_plan_actions unfolding ref_plan_def set_map by auto
  hence "\<exists>as'. a = SimplePlanAction n as' \<and> resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
  proof (cases a)
    case x: (SimplePlanAction n' as)
    have "n' = n" using a unfolding x using simple_plan_action_schema_type1 by fastforce
    then show ?thesis using x a using simple_plan_action_schema_type1 by fastforce
  next
    case (DurativePlanAction n' as d')
    then show ?thesis using durative_plan_action_schema_type1 a by fastforce
  qed
  moreover
  { have "is_integer t'" using plan_acts_durs_integer using a apply (cases a) unfolding list_all_iff by auto
    moreover
    have "t = floor t'" using a apply (cases a) by auto
    ultimately
    have "rat_of_int t = t'" using is_integer_of_int by blast
  }
  ultimately
  show ?thesis using a(1) by fast
qed

lemma durative_action_in_ref_plan:
  assumes "(DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, d) \<in> set ref_plan"
  shows "\<exists>as. (rat_of_int t, DurativePlanAction n as (rat_of_int d)) \<in> set tp 
        \<and> resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
proof -
  obtain t' a where
    a: "(t', a) \<in> set tp"
    "timed_plan_action_to_ref_plan_action (t', a) = (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, d)"
    "wf_plan_action a"
    using assms wf_plan_actions unfolding ref_plan_def set_map by auto
  hence "\<exists>as' d'. a = DurativePlanAction n as' d' \<and> resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  proof (cases a)
    case x: (SimplePlanAction n' as)
    have "n' = n" using a unfolding x using simple_plan_action_schema_type1 by fastforce
    then show ?thesis using x a using simple_plan_action_schema_type1 by fastforce
  next
    case x: (DurativePlanAction n' as d')
    have "n' = n" using a unfolding x using durative_plan_action_schema_type1 by fastforce
    then show ?thesis using durative_plan_action_schema_type1 a x by fastforce
  qed
  then obtain as' d' where
    wit: "a = DurativePlanAction n as' d'" 
    "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))" by auto
  moreover
  { have "is_integer t'" using plan_acts_durs_integer using a apply (cases a) unfolding list_all_iff by auto
    moreover
    have "t = floor t'" using a apply (cases a) by auto
    ultimately
    have "rat_of_int t = t'" using is_integer_of_int by blast
  }
  moreover
  { have "is_integer d'" using plan_acts_durs_integer using wit a apply (cases a) unfolding list_all_iff by auto
    moreover
    have "d = floor d'" using wit a apply (cases a) by auto
    ultimately
    have "rat_of_int d = d'" using is_integer_of_int by blast
  }
  ultimately
  show ?thesis using a(1) by fast
qed


lemma resolve_temporal_action_schema_inj_on_dom:
  assumes "resolve_temporal_action_schema x = resolve_temporal_action_schema y"
      and "resolve_temporal_action_schema x = Some a"
      and "resolve_temporal_action_schema y = Some b"
  shows "x = y"
proof -
  have "ast_temporal_action_schema_name a = x"
    using assms(2) index_by_eq_SomeD unfolding resolve_temporal_action_schema_def by fastforce
  moreover
  have "ast_temporal_action_schema_name b = y"
    using assms(3) index_by_eq_SomeD unfolding resolve_temporal_action_schema_def by fastforce
  moreover
  have "a = b" using assms(1,2,3) by simp
  ultimately show "x = y" by simp
qed

text \<open>Well-formedness and properties of the refined plan.\<close>
(* 
- Every action in the refined plan belongs to the set of actions. 
- The duration of every action in the refined plan is greater than or equal to 0.
- The actions' starts and ends are pairwise non-interfering
- The actions' 
*)

lemma ref_plan_acts_in_actions:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "a \<in> set actions_spec"
  apply (rule in_set_ref_planE[OF assms])
  using simple_plan_action_schema_type1 resolve_action_in_actions  wf_plan_actions
   apply fastforce
  using durative_plan_action_schema_type1 resolve_action_in_actions wf_plan_actions
  by fastforce

lemma ref_plan_acts_wf:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "wf_temporal_action_schema a"
  using acts_wf[OF ref_plan_acts_in_actions[OF assms]] .

lemma ref_plan_durs:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "0 \<le> d"
  apply (rule in_set_ref_planE[OF assms])
  using durative_plan_action_durs wf_plan_actions 
  by fastforce+ 

lemma ref_plan_start_is_htp:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "is_htp tp (rat_of_int t)"
  using assms
proof (cases a rule: ast_temporal_action_schema_cases_unfold)
  case (SimpleActionSchema n params pre eff)
  thus ?thesis
    using assms simple_action_in_ref_plan unfolding is_htp_def by blast
next
  case (DurativeActionSchema n params dc cond deff)
  thus ?thesis
    using assms durative_action_in_ref_plan unfolding is_htp_def by blast
qed

lemma ref_plan_end_is_htp_if_durative:
  assumes "(DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, d) \<in> set ref_plan"
  shows "is_htp tp (rat_of_int (t + d))"
  using durative_action_in_ref_plan[OF assms]
  unfolding is_htp_def durative_acts_def is_act_simple_def by fastforce

lemma ref_plan_start_in_htps:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "(rat_of_int t) \<in> set htps"
  using ref_plan_start_is_htp[OF assms] htps_seq_htps htps_seq_def by blast

lemma ref_plan_end_in_htps_if_durative:
  assumes "(DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, d) \<in> set ref_plan"
  shows "rat_of_int (t + d) \<in> set htps"
  using ref_plan_end_is_htp_if_durative[OF assms] 
    htps_seq_htps htps_seq_def by blast
  

(* Hence, we know that the starts and ends are well-formed *)

lemma ref_plan_snaps_wf:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "wf_ground_action (at_start_spec a)"
        "wf_ground_action (at_end_spec a)"
        "wf_ground_action (over_all_snap a)"
  using assms ref_plan_acts_in_actions 
  by (blast intro: start_snaps_wf end_snaps_wf over_all_snap_wf)+


(* Prove that these are in the acts_of_temporal_plan_at *)


(* acts_of_temporal_plan_at are only guaranteed not to interfere, if they are not equal, but
equality is asserted on the ground action, which means that a can interfere with b
if dels b = {x}, pre b = {x}, adds b = {}, dels a = {x}, pre a = {x}, adds a = {x}. *)


(* To do: remove the name *)

lemma at_start_snap_at_t:
  assumes "(a, t, d) \<in> set ref_plan"
  shows "at_start_spec a \<in> set (acts_of_plan_at_simplified (rat_of_int t) tp)"
  using assms
proof (induction a rule: ast_temporal_action_schema_induct_unfold)
  case (SimpleActionSchema n ps pre eff)
  then obtain as where
    x: "(rat_of_int t, SimplePlanAction n as) \<in> set tp" 
    and y: "resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
    using simple_action_in_ref_plan by blast
  hence z: "SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff) = the (resolve_temporal_action_schema n)" by simp
  have as_Nil: "as = []" using x plan_acts_no_args unfolding list_all_iff by (cases as) auto
  have "the (res_inst (SimplePlanAction n as)) \<in> set (acts_of_plan_at_simplified (rat_of_int t) tp)"
    using acts_of_plan_at_simplified_res_instI[OF x] .
  moreover
  have "the (res_inst (SimplePlanAction n as)) = at_start_spec (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
    unfolding as_Nil res_inst.simps at_start_spec.simps z[symmetric] by simp
  ultimately show ?case by simp
next
  case (DurativeActionSchema n ps dcs pre eff)
  then obtain as d where
    x: "(rat_of_int t, DurativePlanAction n as d) \<in> set tp" 
    and y: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using durative_action_in_ref_plan by blast
  hence z: "DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff) = the (resolve_temporal_action_schema n)" by simp
  have "at_start_spec (the (resolve_temporal_action_schema n)) \<in> set (acts_of_plan_at_simplified (rat_of_int t) tp)"
    using acts_of_plan_at_simplified_startI[OF x] .
  thus ?case unfolding z[symmetric] by simp
qed

lemma at_end_snap_at_t_if_durative:
  assumes "((DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)), t, d) \<in> set ref_plan"
  shows "at_end_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)) \<in> set (acts_of_plan_at_simplified (rat_of_int (t + d)) tp)"
proof -
  obtain as where
    x: "(rat_of_int t, DurativePlanAction n as (rat_of_int d)) \<in> set tp"
    and y: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using assms durative_action_in_ref_plan by blast
  hence z: "DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff) = the (resolve_temporal_action_schema n)" by simp
  have "at_end_spec (the (resolve_temporal_action_schema n)) \<in> set (acts_of_plan_at_simplified (rat_of_int t + rat_of_int d) tp)"
    by (rule acts_of_plan_at_simplified_endI[OF x]) simp
  thus ?thesis unfolding z[symmetric] by simp
qed

(* The above is needed for non-interference of starting snaps.
Ending snaps for durative (but not simple) actions need a similar one.
Simple actions' ends need to be considered separately *)

lemma simple_act_in_ref_plan_durs:
  assumes "(SimpleActionSchema (ActionHead n as) (SimpleActionBody pre eff), t, d) \<in> set ref_plan"
  shows "d = 0"using assms unfolding ref_plan_def set_map
    apply -
    apply (erule imageE)
    subgoal for x
      apply (cases x)
      subgoal for a b apply (cases b)
         apply simp
        using durative_plan_action_schema_type1[OF wf_plan_actions]
        by fastforce
      done
    done

find_theorems "inst_of_plan_action"

text \<open>We obtain a placeholder for the valid state_sequence\<close>

lemma PDDL_no_self_overlap_imp_ref_no_self_overlap:
  assumes "PDDL_no_self_overlap a b"
      and "wf_plan_action (snd a)"
      and "wf_plan_action (snd b)"
      and "plan_act_no_args (snd a)"
      and "plan_act_no_args (snd b)"
      and "timed_plan_action_durs_integer a"
      and "timed_plan_action_durs_integer b"
  shows "ref_no_self_overlap (timed_plan_action_to_ref_plan_action a) (timed_plan_action_to_ref_plan_action b)"
  using assms
proof (induction rule: PDDL_no_self_overlap.induct)
  case (1 t x as u y bs)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" using 1 by auto

  have a: "x = y \<longrightarrow> t \<noteq> u" using 1 unfolding PDDL_no_self_overlap.simps by auto

  have wf_acts: 
    "wf_plan_action (SimplePlanAction x as)"
    "wf_plan_action (SimplePlanAction y bs)" using 1 by auto

  hence res_some: 
    "\<exists>a. resolve_temporal_action_schema x = Some a"
    "\<exists>b. resolve_temporal_action_schema y = Some b" using simple_plan_action_schema_type1 by blast+

  have res_iff: "the (resolve_temporal_action_schema x) = the (resolve_temporal_action_schema y) \<longleftrightarrow> x = y"
    using res_some resolve_temporal_action_schema_inj_on_dom by auto 

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    apply (subst res_iff)
    using a is_integer_floor_ne t_integer u_integer 
    by auto
next
  case (2 t x as u y d bs)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" using 2 by auto


  have wf_acts: 
    "wf_plan_action (SimplePlanAction x as)"
    "wf_plan_action (DurativePlanAction y d bs)" using 2 by auto

  hence res_some: 
    "\<exists>a. resolve_temporal_action_schema x = Some a"
    "\<exists>b. resolve_temporal_action_schema y = Some b" 
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 by blast+

  have res_neq: "the (resolve_temporal_action_schema x) \<noteq> the (resolve_temporal_action_schema y)"
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 wf_acts by fastforce

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    using res_neq by auto
next
  case (3 t x d as u y bs)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" using 3 by auto

  have wf_acts: 
    "wf_plan_action (DurativePlanAction x d as)"
    "wf_plan_action (SimplePlanAction y bs)" using 3 by auto

  hence res_some: 
    "\<exists>a. resolve_temporal_action_schema x = Some a"
    "\<exists>b. resolve_temporal_action_schema y = Some b" 
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 by blast+

  have res_neq: "the (resolve_temporal_action_schema x) \<noteq> the (resolve_temporal_action_schema y)"
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 wf_acts by fastforce

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    using res_neq by auto
next
  case (4 t x as d u y bs e)

  have t_integer: "is_integer t" 
   and u_integer: "is_integer u" 
   and d_integer: "is_integer d"
   and e_integer: "is_integer e" using 4 by auto

  note vs_integer = t_integer u_integer d_integer e_integer
  
  have wf_acts: 
    "wf_plan_action (DurativePlanAction x as d)"
    "wf_plan_action (DurativePlanAction y bs e)" using 4 by auto

  have res_iff: "the (resolve_temporal_action_schema x) = the (resolve_temporal_action_schema y) \<longleftrightarrow> x = y"
    using durative_plan_action_schema_type1[OF wf_acts(1)] durative_plan_action_schema_type1[OF wf_acts(2)]
    by auto

  {
    assume "x = y"
    hence " \<not> (t \<le> u \<and> u \<le> t + d \<or> u \<le> t \<and> t \<le> u + e)" using 4 by simp
    hence "(u < t \<or> t + d < u) \<and> (t < u \<or> u + e < t)" by linarith
    moreover
    { assume "u < t"
      hence "floor u < floor t" using vs_integer is_integer_floor_less by auto
    }
    moreover
    { assume "t + d < u"
      hence "floor (t + d) < floor u" 
        by (intro vs_integer is_integer_floor_less is_integer_add)
      hence "floor t + floor d < floor u" by linarith
    }
    moreover
    { assume "t < u"
      hence "floor t < floor u" using vs_integer is_integer_floor_less by auto
    }
    moreover
    { assume "u + e < t"
      hence "floor (u + e) < floor t" 
        by (intro vs_integer is_integer_floor_less is_integer_add)
      hence "floor u + floor e < floor t" by linarith 
    }
    ultimately
    have " \<not> (\<lfloor>t\<rfloor> \<le> \<lfloor>u\<rfloor> \<and> \<lfloor>u\<rfloor> \<le> plus_int \<lfloor>t\<rfloor> \<lfloor>d\<rfloor> \<or> \<lfloor>u\<rfloor> \<le> \<lfloor>t\<rfloor> \<and> \<lfloor>t\<rfloor> \<le> plus_int \<lfloor>u\<rfloor> \<lfloor>e\<rfloor>)" 
      unfolding de_Morgan_disj de_Morgan_conj not_le by linarith
  } note r = this

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    apply (subst res_iff) 
    using r
    by blast
qed 


lemma ref_plan_no_self_overlap: "ref_plan_no_self_overlap"
proof -
  have "wf_plan tp" using valid_temporal_state_seq_plan unfolding valid_temporal_state_seq_plan_def valid_temporal_state_seq_plan_from_def by blast
  hence "list_all (\<lambda>x. wf_plan_action (snd x)) tp" unfolding wf_plan_def list_all_iff by auto
  thus ?thesis
    using pddl_nso plan_acts_no_args plan_acts_durs_integer
    unfolding PDDL_plan_no_self_overlap_def ref_plan_no_self_overlap_def ref_plan_def
  proof (induction tp)
    case Nil
    then show ?case by simp
  next
    case (Cons pa pas)
    have 1: "list_pairwise ref_no_self_overlap (map timed_plan_action_to_ref_plan_action pas)" using Cons by simp

    have nso: "list_all (PDDL_no_self_overlap pa) pas" using Cons.prems unfolding list_all_iff by auto
    have wf: "list_all (\<lambda>x. wf_plan_action (snd x)) (pa # pas)" using Cons by blast
    have no_args: "list_all (\<lambda>x. plan_act_no_args (snd x)) (pa # pas)" using Cons by blast
    have are_integer: "list_all timed_plan_action_durs_integer (pa # pas)" using Cons by blast

    have 2: "list_all (ref_no_self_overlap (timed_plan_action_to_ref_plan_action pa)) (map timed_plan_action_to_ref_plan_action pas)"
      using nso wf no_args are_integer PDDL_no_self_overlap_imp_ref_no_self_overlap unfolding list_all_iff by simp

    have "ref_no_self_overlap (timed_plan_action_to_ref_plan_action pa) y'
          \<and> ref_no_self_overlap y' (timed_plan_action_to_ref_plan_action pa)"
      if "y' \<in> set (map timed_plan_action_to_ref_plan_action pas)" for y'
      using that 2 ref_no_self_overlap_refl unfolding list_all_iff by blast
    thus ?case using 1 by simp
  qed
qed

lemma ref_plan_actions_in_actions:
  "set (map fst ref_plan) \<subseteq> set actions_spec"
proof -
  have "\<forall>a \<in> fst ` set ref_plan. a \<in> set actions_spec"
  proof (rule ballI)
    fix a 
    assume a: "a \<in> fst ` set ref_plan" 
    obtain t d where
      t: "(a, t, d) \<in> set ref_plan"  using a by auto
    then obtain t' a' where
      t': "(t', a') \<in> set tp"
          "(a, t, d) = timed_plan_action_to_ref_plan_action (t', a')" 
      using t unfolding ref_plan_def by auto
    have wf: "wf_plan_action a'" using t' valid_temporal_state_seq_plan unfolding valid_temporal_state_seq_plan_def valid_temporal_state_seq_plan_from_def wf_plan_def list_all_iff by auto
    show "a \<in> set actions_spec" 
    proof (cases a')
      case (SimplePlanAction n as)
      thus "a \<in> set actions_spec" using t' wf unfolding actions_spec_def
        apply (cases "resolve_temporal_action_schema n")
         apply simp (* apply simp *)
        (* unfolding *) using resolve_temporal_action_schema_def
        by (auto dest: index_by_eq_SomeD)
    next
      case (DurativePlanAction n as d)
      thus ?thesis using t' wf unfolding actions_spec_def
        apply (cases "resolve_temporal_action_schema n")
        by (auto dest: index_by_eq_SomeD simp: resolve_temporal_action_schema_def)
    qed
  qed
  thus ?thesis by auto
qed


text \<open>Properties of the abstract plan used for the proof\<close>

lemma temp_plan_no_self_overlap:
  "imp_defs.rat_impl.no_self_overlap"
proof -
  define \<pi> where "\<pi> \<equiv> (map_option (map_prod id (map_prod rat_of_int rat_of_int))) o plan_imp"
  have "list_pairwise ref_no_self_overlap ref_plan" 
    using ref_plan_no_self_overlap unfolding ref_plan_no_self_overlap_def by simp
  hence "(\<forall>i j. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j 
    \<longrightarrow> ref_no_self_overlap (ref_plan ! i) (ref_plan ! j))" 
    using list_pairwise_nth_refl ref_no_self_overlap_refl by blast
  hence "(\<forall>i j. i \<in> dom plan_imp \<longrightarrow> j \<in> dom plan_imp \<longrightarrow> i \<noteq> j 
    \<longrightarrow> ref_no_self_overlap (ref_plan ! i) (ref_plan ! j))" 
    unfolding plan_imp_def dom_nth_opt by blast
  hence "(\<forall>i j a t d b u e. i \<in> dom plan_imp \<longrightarrow> j \<in> dom plan_imp \<longrightarrow> i \<noteq> j 
    \<longrightarrow> Some (a, t, d) = plan_imp i \<longrightarrow> Some (b, u, e) = plan_imp j
    \<longrightarrow> ref_no_self_overlap (a, t, d) (b, u, e))" unfolding plan_imp_def 
    apply (intro strip)
    apply (drule nth_opt_Some)+
    by simp
  hence "\<forall>i j a t d u e.  i \<noteq> j \<and> i \<in> dom \<pi> \<and> j \<in> dom \<pi> 
    \<and> Some (a, t, d) = \<pi> i \<and> Some (a, u, e) = \<pi> j 
    \<longrightarrow> \<not>(t \<le> u \<and> u \<le> t + d)"
    unfolding \<pi>_def by fastforce
  thus ?thesis 
    unfolding imp_defs.rat_impl.no_self_overlap_def \<pi>_def by blast
qed

lemma temp_plan_actions_in_actions:
  "imp_defs.rat_impl.plan_actions_in_problem"
proof -
  have "ran (nth_opt ref_plan) = set ref_plan" using ran_nth_opt by fast
  hence 1: "ran ((map_option (map_prod id (map_prod rat_of_int rat_of_int)) \<circ>\<circ> nth_opt) ref_plan) = 
      (map_prod id (map_prod rat_of_int rat_of_int)) ` set ref_plan" 
    unfolding comp_def ran_map_option  by simp
  show ?thesis
  unfolding imp_defs.rat_impl.plan_actions_in_problem_def
  unfolding imp_defs.rat_impl.plan_actions_def
  unfolding plan_imp_def 
  apply (rule subsetI)
  apply (elim CollectE exE conjE)
  apply simp
  apply (subst (asm) 1)
  using ref_plan_actions_in_actions by force
qed

definition "is_state_at \<pi> ts initial final t M \<equiv> 
  valid_temporal_state_seq initial (takeWhile (\<lambda>x. x < t) ts) \<pi> M 
  \<and> valid_temporal_state_seq M (dropWhile (\<lambda>x. x < t) ts) \<pi> final"

definition "state_at \<pi> ts initial final t \<equiv> SOME M. is_state_at \<pi> ts initial final t M"

definition "time_after_all ts \<equiv> SOME t. \<forall>t' \<in> set ts. t' < t"

definition "add_final_time_point ts \<equiv> ts @ [time_after_all ts]" 

definition "abstr_state_list \<equiv> (map (state_at tp htps I final_state) (add_final_time_point htps))"

definition "plan_state_list \<equiv> abstr_state_list 
  |> map (\<lambda>M. \<Union>f \<in> fst M. set (map to_predicate (to_literals f)))"


lemma length_add_final_time_point:
  "length (add_final_time_point ts) = Suc (length ts)"
  unfolding add_final_time_point_def by auto

lemma length_abstr_state_list:
  "length abstr_state_list = Suc (length htps)"
  unfolding abstr_state_list_def length_map
  using length_add_final_time_point by blast

lemma length_plan_state_list:
  "length plan_state_list = Suc (length htps)"
  unfolding plan_state_list_def 
  using length_abstr_state_list by simp

lemma plan_state_list_nth_conv_abstr_state_list_nth:
  assumes "n < length plan_state_list"
  shows "plan_state_list ! n = (\<Union>x\<in>fst (abstr_state_list ! n). to_predicate ` set (to_literals x))"
  using assms unfolding plan_state_list_def
  by auto

lemma time_after_all_is_after_all:
  "\<forall>t \<in> set ts. t < time_after_all (ts::rat list)"
  unfolding time_after_all_def
  apply (rule someI_ex)
  apply (induction ts)
   apply simp
  subgoal for t ts
    apply (erule exE)
    subgoal for x
      apply (cases "x < t")
       apply (intro exI[of _ "t+1"] ballI)
       apply auto[1]
      apply (intro exI[of _ "x + 1"])
      by auto
    done
  done
      


lemma nth_add_final_time_point_length:
  "add_final_time_point ts ! (length ts) = (time_after_all ts)"
  unfolding add_final_time_point_def by simp

lemma nth_add_final_time_point:
  assumes "n < length ts"
  shows "add_final_time_point ts ! n = ts ! n"
  using assms
  unfolding add_final_time_point_def by auto


lemma strict_sorted_add_final_time_point:
  assumes "strict_sorted (ts::rat list)"
  shows "strict_sorted (add_final_time_point ts)"
  unfolding add_final_time_point_def
  apply (rule sorted_wrt_append)
  using assms time_after_all_is_after_all[of ts] by auto

lemma abstr_state_list_nth_length:
  "abstr_state_list ! length htps = (state_at tp htps I final_state (time_after_all htps))" 
  unfolding abstr_state_list_def apply (subst nth_map, subst length_add_final_time_point, blast)
  apply (subst nth_add_final_time_point_length)
  by simp

text \<open>Forward decomposition of a valid state sequence at an arbitrary split point.  Unlike the
  old two-case @{text valid_state_seq} (where the invariants were a per-happening precondition and
  the split was a clean iff), the new three-case @{const valid_temporal_state_seq} checks an
  \<^emph>\<open>interval\<close> invariant @{term \<open>invs_of_temporal_plan_in_interval (t\<^sub>i, t\<^sub>j)\<close>} across each consecutive
  pair, so the converse glue is unavailable at a non-shared boundary.  Only the forward direction
  (which \<^emph>\<open>drops\<close> the straddling interval invariant) holds, and that is all our @{const state_at}
  proofs consume.\<close>
lemma valid_temporal_state_seq_app_decompose:
  assumes "valid_temporal_state_seq M (xs @ ys) \<pi> M'"
  shows "\<exists>Mm. valid_temporal_state_seq M xs \<pi> Mm \<and> valid_temporal_state_seq Mm ys \<pi> M'"
  using assms
proof (induction M xs \<pi> M' arbitrary: ys rule: valid_temporal_state_seq.induct)
  case (1 M \<pi> M')
  then show ?case by auto
next
  case (2 M t\<^sub>i \<pi> M')
  show ?case
  proof (cases ys)
    case Nil
    hence "valid_temporal_state_seq M [t\<^sub>i] \<pi> M'" using 2 by simp
    moreover
    have "valid_temporal_state_seq M' ys \<pi> M'" using Nil by simp
    ultimately
    show ?thesis by blast
  next
    case (Cons t\<^sub>j ys')
    have "valid_temporal_state_seq M [t\<^sub>i] \<pi> (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M)"
      using 2 Cons by (simp add: Let_def)
    moreover
    have "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M) ys \<pi> M'"
      using 2 Cons by (simp add: Let_def)
    ultimately
    show ?thesis by blast
  qed
next
  case (3 M t\<^sub>i t\<^sub>j ts \<pi> M')
  have rec: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M) (t\<^sub>j # ts @ ys) \<pi> M'"
    using 3 by (simp add: Let_def)
  have "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M) ((t\<^sub>j # ts) @ ys) \<pi> M'"
    using rec by simp
  hence "\<exists>Mm. valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M) (t\<^sub>j # ts) \<pi> Mm
           \<and> valid_temporal_state_seq Mm ys \<pi> M'"
    using "3.IH" by blast
  then obtain Mm where
    pre: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>) M) (t\<^sub>j # ts) \<pi> Mm"
    and suf: "valid_temporal_state_seq Mm ys \<pi> M'"
    by blast
  have "valid_temporal_state_seq M (t\<^sub>i # t\<^sub>j # ts) \<pi> Mm"
    using 3 pre by (simp add: Let_def)
  thus ?case using suf by blast
qed

lemma state_at_is_state_at:
  assumes "valid_temporal_state_seq M ts \<pi> M'"
      and "strict_sorted ts"
  shows "is_state_at \<pi> ts M M' t (state_at \<pi> ts M M' t)"
proof -
  have "valid_temporal_state_seq M (takeWhile (\<lambda>x. x < t) ts @ dropWhile (\<lambda>x. x < t) ts) \<pi> M'"
    using assms(1) by simp
  hence "\<exists>M\<^sub>m. is_state_at \<pi> ts M M' t M\<^sub>m"
    unfolding is_state_at_def using valid_temporal_state_seq_app_decompose by blast
  thus ?thesis
    unfolding state_at_def by (rule someI_ex)
qed

lemma is_state_at_unique:
  fixes X Y
  assumes "is_state_at \<pi> ts M M' t X"
     and "is_state_at \<pi> ts M M' t Y"
  shows "X = Y" 
  using assms valid_temporal_state_seq_state_unique is_state_at_def by blast


lemma abstr_state_list_nth_valid:
  assumes "n \<le> length htps"
  shows "is_state_at tp htps I final_state ((add_final_time_point htps) ! n) (abstr_state_list ! n)"
  unfolding abstr_state_list_def
   apply (subst nth_map)
    apply (subst length_add_final_time_point)
  using assms apply simp
   apply (rule state_at_is_state_at)
  using valid_temporal_state_seq_final_state 
  using htps_seq_htps unfolding htps_seq_def 
  by blast+

lemma abstr_state_list_nth_length_is_final:
  "abstr_state_list ! (length htps) = final_state"
proof -
  have "is_state_at tp htps I final_state ((add_final_time_point htps) ! length htps) (abstr_state_list ! length htps)"
    using abstr_state_list_nth_valid by blast
  hence "valid_temporal_state_seq I (takeWhile (\<lambda>x. x < add_final_time_point htps ! length htps) htps) tp (abstr_state_list ! length htps)" 
    unfolding is_state_at_def by auto
  moreover
  have "takeWhile (\<lambda>x. x < add_final_time_point htps ! length htps) htps = htps"
    apply (subst nth_add_final_time_point_length)
    using time_after_all_is_after_all by simp
  ultimately
  have "valid_temporal_state_seq I htps tp (abstr_state_list ! length htps)"
    by simp
  moreover
  have "valid_temporal_state_seq I htps tp final_state" using valid_temporal_state_seq_final_state by simp
  ultimately
  show ?thesis using valid_temporal_state_seq_state_unique by simp
qed

lemma abstr_state_list_nth_0_is_init:
  "abstr_state_list ! 0 = I"
proof -
  have "is_state_at tp htps I final_state ((add_final_time_point htps) ! 0) (abstr_state_list ! 0)"
    using abstr_state_list_nth_valid by blast
  hence "valid_temporal_state_seq I (takeWhile (\<lambda>x. x < add_final_time_point htps ! 0) htps) tp (abstr_state_list ! 0)" 
    unfolding is_state_at_def by auto
  moreover
  have "takeWhile (\<lambda>x. x < add_final_time_point htps ! 0) htps = []"
  proof (cases "length htps")
    case 0
    then show ?thesis by auto
  next
    case (Suc nat)
    then show ?thesis 
      apply (subst nth_add_final_time_point)
       apply simp
      apply (subst strict_sorted_takeWhile_nth)
      using htps_seq_htps unfolding htps_seq_def
      by auto
  qed
  ultimately
  have "valid_temporal_state_seq I [] tp (abstr_state_list ! 0)"
    by auto
  thus ?thesis using valid_temporal_state_seq_state_unique by simp
qed

lemma valid_temporal_state_seq_abstr_state_list_f:
  assumes "i \<le> length htps"
  shows "valid_temporal_state_seq (abstr_state_list ! i) (drop i htps) tp final_state"
proof (cases "i < length htps")
  case True
  have htps_sorted: "sorted_wrt (<) htps" using htps_seq_htps unfolding htps_seq_def by blast
  have state_at_i: "is_state_at tp htps I final_state ((add_final_time_point htps) ! i) (abstr_state_list ! i)"
    apply (rule abstr_state_list_nth_valid)
    using True abstr_state_list_nth_valid by simp 
  hence "valid_temporal_state_seq (abstr_state_list ! i) (dropWhile (\<lambda>x. x < add_final_time_point htps ! i) htps) tp final_state" 
    unfolding is_state_at_def by blast
  thus "valid_temporal_state_seq (abstr_state_list ! i) (drop i htps) tp final_state"
    apply (subst (asm) nth_add_final_time_point)
    using True apply simp
    using strict_sorted_dropWhile_nth[OF True htps_sorted] by simp
next
  case False
  hence i: "i = length htps" using assms by auto
  have "drop i htps = []" using i by auto
  moreover
  have "abstr_state_list ! i = final_state" using abstr_state_list_nth_length_is_final i by simp
  ultimately 
  show ?thesis by auto
qed

lemma valid_temporal_state_seq_abstr_state_list_i:
  assumes "i \<le> length htps"
  shows "valid_temporal_state_seq I (take i htps) tp (abstr_state_list ! i)"
proof (cases "i < length htps")
  case True
  have htps_sorted: "strict_sorted htps"  using htps_seq_htps unfolding htps_seq_def by blast
  have n: "is_state_at tp htps I final_state ((add_final_time_point htps) ! i) (abstr_state_list ! i)" 
    using True htps_sorted abstr_state_list_nth_valid by auto
  hence "valid_temporal_state_seq I (takeWhile (\<lambda>x. x < add_final_time_point htps ! i) htps) tp (abstr_state_list ! i)" 
    unfolding is_state_at_def by blast
  thus "valid_temporal_state_seq I (take i htps) tp (abstr_state_list ! i)"
    apply (subst (asm) nth_add_final_time_point)
    using True apply simp
    using strict_sorted_takeWhile_nth[OF True htps_sorted] by simp
next
  case False
  hence i: "i = length htps" using assms by auto
  have "take i htps = htps" using i by auto
  moreover
  have "abstr_state_list ! i = final_state" using abstr_state_list_nth_length_is_final i by simp
  ultimately 
  show ?thesis using valid_temporal_state_seq_final_state by presburger
qed

text \<open>The temporal wf-problem locale does not assume @{term \<open>wf_world_model I\<close>} directly
  (the \<open>wf_world_model (set (init P))\<close> clause is commented out of @{const wf_temporal_problem});
  we recover it from the per-fact clause
  \<open>\<forall>f\<in>set (init P). wf_fmla_atom objT f \<or> wf_func_assign f\<close>, since for a predAtom
  @{term \<open>wf_func_assign f\<close>} is always false.\<close>
lemma wf_I: "wf_world_model I"
proof -
  have "wf_fmla_atom objT f" if "f \<in> set (init P)" and "is_predAtom f" for f
    using that wf_temporal_problem
    unfolding wf_temporal_problem_def
    by (metis is_predAtom.elims(2) wf_func_assign.simps)
  thus ?thesis
    using wf_temporal_problem
    unfolding I_def wf_temporal_problem_def
    by auto
qed


lemma abstr_state_list_nth_wf_world_model:
  assumes "i \<le> length htps"
  shows "wf_world_model (abstr_state_list ! i)"
proof (rule valid_temporal_state_seq_wf_world_model)
  show "wf_world_model I" using wf_I by simp
  show "valid_temporal_state_seq I (take i htps) tp (abstr_state_list ! i)" 
    using assms valid_temporal_state_seq_abstr_state_list_i by simp
  show "wf_plan tp" using wf_plan by simp
  show "\<forall>t\<in>set (take i htps). is_htp tp t"
    using set_take_subset htps_seq_htps unfolding htps_seq_def by fast
qed

lemma abstr_state_list_nth_Suc:
  assumes "n < length htps"
  shows "(abstr_state_list ! (Suc n)) = apply_eff (acts_of_temporal_plan_at (htps ! n) tp) (abstr_state_list ! n)"
proof -
  have 1: "sorted_wrt (<) htps" using htps_seq_htps unfolding htps_seq_def by blast

  have take_Sn: "take (Suc n) htps = take n htps @ [htps ! n]" using take_Suc_conv_app_nth assms by auto
  
  
  have sn: "is_state_at tp htps I final_state ((add_final_time_point htps) ! (Suc n)) (abstr_state_list ! (Suc n))" 
    using assms 1 abstr_state_list_nth_valid by auto
  hence 2: "valid_temporal_state_seq I (takeWhile (\<lambda>x. x < add_final_time_point htps ! Suc n) htps) tp (abstr_state_list ! Suc n)" 
    unfolding is_state_at_def by simp
  have "valid_temporal_state_seq I (take (Suc n) htps) tp (abstr_state_list ! Suc n)" 
  proof (cases "Suc n < length htps")
    case True
    show ?thesis 
      apply (insert 2 True)
      apply (subst (asm) nth_add_final_time_point, simp)
     apply (subst (asm) strict_sorted_takeWhile_nth)
    using 1 by simp+
  next
    case False
    hence n': "Suc n = length htps" using assms by simp
    show ?thesis
      apply (insert 2)
      unfolding n' 
      apply (subst (asm) nth_add_final_time_point_length)
      apply (subst (asm) takeWhile_all)
      using time_after_all_is_after_all
      by auto
  qed 
  hence "\<exists>Mj. valid_temporal_state_seq I (take n htps) tp Mj \<and> valid_temporal_state_seq Mj [htps ! n] tp (abstr_state_list ! Suc n)" 
    unfolding take_Sn using valid_temporal_state_seq_app_decompose by blast
  then obtain Mj where
    Ij: "valid_temporal_state_seq I (take n htps) tp Mj" 
    and jSn: "valid_temporal_state_seq Mj [htps ! n] tp (abstr_state_list ! Suc n)" by auto

  have Mj_eff_Sn: "apply_eff (acts_of_temporal_plan_at (htps ! n) tp) Mj = abstr_state_list ! Suc n" 
    using jSn unfolding valid_temporal_state_seq.simps Let_def by auto

  have In: "valid_temporal_state_seq I (take n htps) tp (abstr_state_list ! n)" 
    using valid_temporal_state_seq_abstr_state_list_i assms by simp
  have eq: "Mj = (abstr_state_list ! n)" using Ij In valid_temporal_state_seq_state_unique by blast

  show ?thesis using Mj_eff_Sn eq by simp
qed

lemma ref_htpl_eq_htps: "imp_defs.rat_impl.htpl = htps"
proof (rule strict_sorted_equal)
  have "htps_seq tp htps" using htps_seq_htps by blast
  hence htps_prop: "(\<forall>t. (t \<in> set htps) = ((\<exists>\<pi>. (t, \<pi>) \<in> set tp) \<or> (\<exists>(t\<^sub>\<pi>, \<pi>)\<in>durative_acts tp. t = t\<^sub>\<pi> + duration \<pi>)))"
    unfolding htps_seq_def is_htp_def by argo

  show "strict_sorted htps"
    using htps_seq_htps htps_seq_def by blast
  show "strict_sorted imp_defs.rat_impl.htpl" 
    using imp_defs.rat_impl.sorted_htpl by simp
  show "set imp_defs.rat_impl.htpl = set htps"
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> set imp_defs.rat_impl.htpl"
    hence "x \<in> imp_defs.rat_impl.htps" using htps_set_htpl by simp
    thus "x \<in> set htps" 
      apply (elim imp_defs.rat_impl.htpsE ssubst)
      unfolding abstr_plan_def[symmetric]
    proof goal_cases
      fix a t d
      assume "(a, t, d) \<in> ran abstr_plan"
      thus "t + d \<in> set htps" 
      proof (elim ran_abstr_plan_ref_planE)
        fix a t d
        assume "(a, t, d) \<in> set ref_plan" 
        thus "rat_of_int t + rat_of_int d \<in> set htps"
        proof (elim in_set_ref_planE)
          fix t n as
          assume a: "(t, SimplePlanAction n as) \<in> set tp" 
          have "is_integer t" using plan_acts_durs_integer a unfolding list_all_iff by fastforce
          moreover
          have "t \<in> set htps" using a htps_prop by blast
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> + rat_of_int 0 \<in> set htps" 
            using is_integer_of_int by fastforce
        next
          fix t n as d
          assume a: "(t, DurativePlanAction n as d) \<in> set tp"
          have "is_integer t" "is_integer d" using plan_acts_durs_integer a 
            unfolding list_all_iff by fastforce+
          moreover
          {
            have "(t, DurativePlanAction n as d) \<in> (durative_acts tp)" using a 
              unfolding durative_acts_def comp_def set_filter is_act_simple by auto
            hence "t + d \<in> set htps" using htps_prop by fastforce
          }
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> + rat_of_int \<lfloor>d\<rfloor> \<in> set htps" 
            by(fastforce simp: is_integer_of_int)
        qed
      qed
    next
      fix a t d
      assume "(a, t, d) \<in> ran abstr_plan"
      thus "t \<in> set htps"
      proof (elim ran_abstr_plan_ref_planE)
        fix a t d
        assume "(a, t, d) \<in> set ref_plan" 
        thus "rat_of_int t \<in> set htps"
        proof (elim in_set_ref_planE)
          fix t n as
          assume a: "(t, SimplePlanAction n as) \<in> set tp" 
          have "is_integer t" using plan_acts_durs_integer a unfolding list_all_iff by fastforce
          moreover
          have "t \<in> set htps" using a htps_prop by blast
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> \<in> set htps" 
            using is_integer_of_int by fastforce
        next
          fix t n as d
          assume a: "(t, DurativePlanAction n as d) \<in> set tp"
          have "is_integer t"  using plan_acts_durs_integer a 
            unfolding list_all_iff by fastforce+
          moreover
          have "t \<in> set htps" using htps_prop a by fastforce
          ultimately
          show "rat_of_int \<lfloor>t\<rfloor> \<in> set htps" 
            by (fastforce simp: is_integer_of_int)
        qed
      qed
    qed
  next
    fix x
    assume "x \<in> set htps" 
    hence "((\<exists>\<pi>. (x, \<pi>) \<in> set tp) \<or> (\<exists>(t\<^sub>\<pi>, \<pi>)\<in>durative_acts tp. x = t\<^sub>\<pi> + duration \<pi>))"
      using htps_prop by blast
    then consider 
          a where "(x, a) \<in> set tp" 
      | t a where "(t, a) \<in> durative_acts tp" "x = t + duration a"
      by blast
    then consider
        n as  where "(x, (SimplePlanAction n as)) \<in> set tp" 
      | n as d where "(x, (DurativePlanAction n as d)) \<in> set tp" 
      | t n as d where "(t, (DurativePlanAction n as d)) \<in> set tp" 
        "x = t + d"
      apply cases
      subgoal for a apply (cases a)
        by auto
      subgoal for t a
        apply (cases a)
        unfolding durative_acts_def is_act_simple 
        by auto
      done
    hence "x \<in> imp_defs.rat_impl.htps"
    proof (cases)
      case 1
      have 2: "(the (resolve_temporal_action_schema n), \<lfloor>x\<rfloor>, 0) \<in> set ref_plan" 
        using in_set_ref_planI 1 by simp
      {
        have "(the (resolve_temporal_action_schema n), rat_of_int \<lfloor>x\<rfloor>, rat_of_int 0) \<in> ran abstr_plan" 
          using ran_abstr_planI 2 by blast
        moreover
        have "is_integer x" using plan_acts_durs_integer 1
            unfolding list_all_iff by fastforce+
        ultimately
        have "(the (resolve_temporal_action_schema n), x, rat_of_int 0) \<in> ran abstr_plan" 
          using is_integer_of_int by fastforce
      }
      then show ?thesis using imp_defs.rat_impl.htpsI 
        unfolding abstr_plan_def by auto
    next
      case 2
      have 3: "(the (resolve_temporal_action_schema n), \<lfloor>x\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
        using in_set_ref_planI 2 by blast
      {
        have "(the (resolve_temporal_action_schema n), rat_of_int \<lfloor>x\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
          using ran_abstr_planI 3 by blast
        moreover
        have "is_integer x" "is_integer d" using plan_acts_durs_integer 2
            unfolding list_all_iff by fastforce+
        ultimately
        have "(the (resolve_temporal_action_schema n), x, d) \<in> ran abstr_plan" 
          using is_integer_of_int by fastforce
      }
      then show ?thesis using imp_defs.rat_impl.htpsI 
        unfolding abstr_plan_def by auto
    next
      case 3
      have 4: "(the (resolve_temporal_action_schema n), \<lfloor>t\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
        using in_set_ref_planI 3 by blast
      {
        have "(the (resolve_temporal_action_schema n), rat_of_int \<lfloor>t\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
          using ran_abstr_planI 4 by blast
        moreover
        have "is_integer t" "is_integer d" using plan_acts_durs_integer 3
            unfolding list_all_iff by fastforce+
        ultimately
        have "(the (resolve_temporal_action_schema n), t, d) \<in> ran abstr_plan" 
          using is_integer_of_int by fastforce
      }
      then show ?thesis using imp_defs.rat_impl.htpsI 
        unfolding abstr_plan_def 3 by auto
    qed
    thus "x \<in> set imp_defs.rat_impl.htpl" using htps_set_htpl by simp
  qed
qed


(* What needs to be added to the actions of the plan at a time_point to include all snap actions? *)
(* Every instantaneous action (simple action) needs an empty snap action paired with its start *)

definition "missing_ends t \<pi> \<equiv> {s. \<exists>a. (t,a) \<in> simple_acts \<pi> \<and> Some s = map_option at_end_spec (resolve_temporal_action_schema (name a))}"  

lemma plan_happ_seq_alt': "\<forall>s. s \<in> (imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq t)  \<longleftrightarrow> 
  ((s \<in> set (acts_of_plan_at_simplified t tp)) 
    \<or> s \<in> missing_ends t tp)"
  unfolding missing_ends_def
proof (intro strip iffI CollectI; (elim disjE CollectE exE conjE)?)
  fix s
  assume a: "(t, s) \<in> imp_defs.rat_impl.plan_happ_seq" 
  show "s \<in> set (acts_of_plan_at_simplified t tp) \<or> s \<in> {s. \<exists>a. (t, a) \<in> simple_acts tp \<and> Some s = map_option at_end_spec (resolve_temporal_action_schema (plan_action.name a))}"
  proof ((rule imp_defs.rat_impl.in_happ_seq_propE[OF a]; subst (asm) abstr_plan_def[symmetric]); elim ran_abstr_plan_ref_planE)
    show "\<And>a t d aa ta da. (aa, ta, da) \<in> set ref_plan 
      \<Longrightarrow> at_start_spec aa \<in> set (acts_of_plan_at_simplified (rat_of_int ta) tp) \<or> 
          at_start_spec aa \<in> {s. \<exists>a. (rat_of_int ta, a) \<in> simple_acts tp 
            \<and> Some s = map_option at_end_spec (resolve_temporal_action_schema (plan_action.name a))}"
      using at_start_snap_at_t by simp
  next
    fix a t d
    assume a: "(a, t, d) \<in> set ref_plan"
    thus "at_end_spec a \<in> set (acts_of_plan_at_simplified (rat_of_int t + rat_of_int d) tp) 
            \<or> at_end_spec a \<in> {s. \<exists>a. (rat_of_int t + rat_of_int d, a) \<in> simple_acts tp 
              \<and> Some s = map_option at_end_spec (resolve_temporal_action_schema (plan_action.name a))}"
    proof (induction a rule: ast_temporal_action_schema_induct_unfold)
      case (SimpleActionSchema n ps pre eff)
      hence b: "(SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff), t, d) \<in> set ref_plan" by simp
      have d: "d = 0" using b simple_act_in_ref_plan_durs by auto
      obtain as where
        as: "(rat_of_int t, SimplePlanAction n as) \<in> set tp \<and> resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))" using simple_action_in_ref_plan b by blast
      have "at_end_spec (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))
              \<in> {s. \<exists>a. (rat_of_int t + rat_of_int d, a) \<in> simple_acts tp \<and> Some s = map_option at_end_spec (resolve_temporal_action_schema (plan_action.name a))}"
      proof -
        have "(rat_of_int t + rat_of_int d, SimplePlanAction n as) \<in> simple_acts tp" using as d 
          unfolding simple_acts_def is_act_simple by simp
        moreover
        have "Some (at_end_spec (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff)))
              = map_option at_end_spec (resolve_temporal_action_schema n)" using as by simp
        ultimately
        show ?thesis by auto
      qed
      thus ?case by auto
    next
      case (DurativeActionSchema n ps dcs pre eff)
      hence b: "(DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, d) \<in> set ref_plan" by simp
      show ?case
        using at_end_snap_at_t_if_durative[OF b] by simp
    qed
  qed
next
  fix s
  assume s: "s \<in> set (acts_of_plan_at_simplified t tp)"
  consider n as where "(t, SimplePlanAction n as) \<in> set tp" "s = the (res_inst (SimplePlanAction n as))"
    | n as dur where "(t, DurativePlanAction n as dur) \<in> set tp" "s = at_start_spec (the (resolve_temporal_action_schema n))"
    | t' n as dur where "(t', DurativePlanAction n as dur) \<in> set tp" "t = t' + dur" "s = at_end_spec (the (resolve_temporal_action_schema n))"
    using s by (rule in_acts_of_plan_at_simplifiedE) blast+
  note c = this

  thus "(t, s) \<in> imp_defs.rat_impl.plan_happ_seq" 
  proof (cases rule: c)
    case a: (1 n as)
    have mem: "(t, SimplePlanAction n as) \<in> set tp" using a(1) .
    have ref: "(the (resolve_temporal_action_schema n), \<lfloor>t\<rfloor>, 0) \<in> set ref_plan" 
      apply (rule in_set_ref_planI(1))
      using mem by auto

    obtain ps pre eff where 
      res: "the (resolve_temporal_action_schema n) = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff)" 
      using mem simple_plan_action_schema_type1 wf_plan_actions by fastforce

    have as_Nil: "as = []" 
      using plan_acts_no_args mem 
      unfolding list_all_iff
      apply (cases as) 
      by fastforce+

    have abstr: "(the (resolve_temporal_action_schema n), rat_of_int \<lfloor>t\<rfloor>, rat_of_int 0) \<in> ran abstr_plan" 
      using ran_abstr_planI ref by blast
    have s: "s = at_start_spec (the (resolve_temporal_action_schema n))"
      using a(2) unfolding res_inst.simps res at_start_spec.simps as_Nil by simp
      
    have "is_integer t" using mem plan_acts_durs_integer 
      unfolding list_all_iff by fastforce
    hence t: "rat_of_int (floor t) = t" using is_integer_of_int by blast

    show ?thesis using imp_defs.rat_impl.in_happ_seqI(1)[OF abstr[simplified abstr_plan_def]] 
      unfolding s t by blast
  next
    case a: (2 n as d)
    have mem: "(t, DurativePlanAction n as d) \<in> set tp" using a(1) .
    have ref: "(the (resolve_temporal_action_schema n), \<lfloor>t\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
      apply (rule in_set_ref_planI(2))
      using mem by auto

    obtain ps dcs pre eff where 
      res: "the (resolve_temporal_action_schema n) = DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)" 
      using mem durative_plan_action_schema_type1 wf_plan_actions by fastforce

    have abstr: "(the (resolve_temporal_action_schema n), rat_of_int \<lfloor>t\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
      using ran_abstr_planI ref by blast
    have s: "s = at_start_spec (the (resolve_temporal_action_schema n))"
      using a(2) .
      
    have "is_integer t" "is_integer d" using mem plan_acts_durs_integer 
      unfolding list_all_iff by fastforce+
    hence td: "rat_of_int (floor t) = t" "rat_of_int (floor d) = d" using is_integer_of_int by blast+

    show ?thesis using imp_defs.rat_impl.in_happ_seqI(1)[OF abstr[simplified abstr_plan_def]] 
      unfolding s td by blast
  next
    case a: (3 t' n as d)
    have mem: "(t', DurativePlanAction n as d) \<in> set tp" using a(1) .
    have ref: "(the (resolve_temporal_action_schema n), \<lfloor>t'\<rfloor>, \<lfloor>d\<rfloor>) \<in> set ref_plan" 
      apply (rule in_set_ref_planI(2))
      using mem by blast

    obtain ps dcs pre eff where 
      res: "the (resolve_temporal_action_schema n) = DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)" 
      using mem durative_plan_action_schema_type1 wf_plan_actions by fastforce

    have abstr: "(the (resolve_temporal_action_schema n), rat_of_int \<lfloor>t'\<rfloor>, rat_of_int \<lfloor>d\<rfloor>) \<in> ran abstr_plan" 
      using ran_abstr_planI ref by blast
    have s: "s = at_end_spec (the (resolve_temporal_action_schema n))"
      using a(3) .
      
    have "is_integer t'" "is_integer d" using mem plan_acts_durs_integer 
      unfolding list_all_iff by fastforce+
    hence td: "rat_of_int (floor t') = t'" "rat_of_int (floor d) = d" using is_integer_of_int by blast+

    show ?thesis using imp_defs.rat_impl.in_happ_seqI(2)[OF abstr[simplified abstr_plan_def]] 
      unfolding s td a(2) using a(2) plan_action.sel td by auto
  qed
next
  fix s a
  assume x: "(t, a) \<in> simple_acts tp" 
    and s: "Some s = map_option at_end_spec (resolve_temporal_action_schema (plan_action.name a))"

  obtain n as where
    a: "a = SimplePlanAction n as" using x(1) unfolding simple_acts_def is_act_simple 
    by (cases a) auto

  have wfa: "wf_plan_action (SimplePlanAction n as)"
    using a x simple_acts_in_plan wf_plan_actions by fastforce
  obtain ps pre eff where 
    resS: "resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))" 
    using wfa simple_plan_action_schema_type1 by blast
  hence res: "the (resolve_temporal_action_schema n) = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff)" 
    by simp

  have s: "s = at_end_spec (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
    using s resS a by simp

  have ref: "(the (resolve_temporal_action_schema n), \<lfloor>t\<rfloor>, 0) \<in> set ref_plan"
    apply (rule in_set_ref_planI)
    using x a simple_acts_in_plan by auto

  have abstr: "(SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff), rat_of_int \<lfloor>t\<rfloor>, rat_of_int 0) \<in> ran abstr_plan" 
    using ran_abstr_planI ref res by fastforce

  have t: "rat_of_int (floor t) = t" 
    apply (rule is_integer_of_int)
    using plan_acts_durs_integer x 
      simple_acts_in_plan a unfolding list_all_iff by fastforce
  
  show "(t, s) \<in> imp_defs.rat_impl.plan_happ_seq" 
    using imp_defs.rat_impl.in_happ_seqI(2)[folded abstr_plan_def, OF abstr] unfolding abstr_plan_def
    unfolding s t by simp
qed

lemma plan_happ_seq_alt: "imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq t =
  set (acts_of_plan_at_simplified t tp) \<union> missing_ends t tp"
  using plan_happ_seq_alt' by blast


lemma missing_ends_ground_non_actions:
  "missing_ends t tp \<subseteq> {ground_non_action}"
proof (rule subsetI)
  fix x
  assume "x \<in> missing_ends t tp"
  then obtain a where
    "(t, a) \<in> simple_acts tp" 
    "Some x = map_option at_end_spec (resolve_temporal_action_schema (plan_action.name a))"
    unfolding missing_ends_def by auto
  then obtain n ps pre eff where
    x: "x = at_end_spec (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))" 
    using res_simple_act_name by fastforce
  show "x \<in> {ground_non_action}" unfolding x
    by auto
qed


lemma Union_diff_eq_diff:
  assumes "\<forall>x \<in> S. f x = {x}"
     and "\<forall>x \<in> T. f x = {x}"
   shows "\<Union>(f ` S - f ` T) = S - T"
  using assms by auto

lemma apply_effects_if:
  assumes "S - (\<Union>x\<in>h. set (dels (ground_action.effect x))) \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))) = T"
     and S_props: "S \<subseteq> {x. form_preds_no_args x \<and> is_predAtom x}"
     and h_props: "h \<subseteq> {x. ground_act_no_args x \<and> wf_ground_action x}" 
  shows "(\<Union>x\<in>S. set (map to_predicate (to_literals x))) - (\<Union>x\<in>h. set (dels_spec x)) \<union> (\<Union>x\<in>h. set (adds_spec x)) 
    = (\<Union>x\<in>T. set (map to_predicate (to_literals x)))"
proof -
  
  have S_lits: "(\<Union>x \<in> S. set (to_literals x)) = S" 
    using is_predAtom_literals S_props by force

  have S_lits': "\<forall>x \<in> S. set (to_literals x) = {x}"
    using is_predAtom_literals S_props by force

  have del_props: "(\<Union>x\<in>h. set (dels (ground_action.effect x))) \<subseteq> {x. form_preds_no_args x \<and> is_predAtom x}"
    using h_props wf_ground_action_dels_preds ground_act_no_args_imp_dels_no_args
    by blast
  
  have add_props: "(\<Union>x\<in>h. set (adds (ground_action.effect x))) \<subseteq> {x. form_preds_no_args x \<and> is_predAtom x}"
    using h_props wf_ground_action_adds_preds ground_act_no_args_imp_adds_no_args
    by blast

  have del_lits': "\<forall>f \<in> (\<Union>x\<in>h. set (dels (ground_action.effect x))). to_literals f = [f]"
    using is_predAtom_literals del_props by blast
  hence del_lits: "(\<Union>x\<in>h. set (dels (ground_action.effect x))) 
    = (\<Union>x\<in>\<Union>x\<in>h. set (dels (ground_action.effect x)). set (to_literals x))"
    by simp

  

  have add_lits': "\<forall>f \<in> (\<Union>x\<in>h. set (adds (ground_action.effect x))). to_literals f = [f]"
    using is_predAtom_literals add_props by blast
  hence add_lits: "(\<Union>x\<in>h. set (adds (ground_action.effect x))) 
    = (\<Union>x\<in>\<Union>x\<in>h. set (adds (ground_action.effect x)). set (to_literals x))"
    by simp


  {
    have "(\<Union>x\<in>S. to_predicate ` set (to_literals x))
      - (\<Union>x\<in>h. to_predicate ` set (dels (ground_action.effect x))) 
      \<union> (\<Union>x\<in>h. to_predicate ` set (adds (ground_action.effect x))) 
    = to_predicate ` ((\<Union>x\<in>S. set (to_literals x)) 
      - (\<Union>x\<in>h. set (dels (ground_action.effect x))) 
      \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))))"
      unfolding image_UN[symmetric]
      apply (subst inj_on_image_set_diff[symmetric])
         apply (rule inj_on_to_predicate)
      using S_lits S_props apply blast
      using del_props apply blast
      by blast
    also
    have "... = to_predicate `
      ((\<Union>x\<in>S. set (to_literals x)) 
        - (\<Union>x\<in>\<Union>x\<in>h. set (dels (ground_action.effect x)). set (to_literals x))
        \<union> (\<Union>x\<in>\<Union>x\<in>h. set (adds (ground_action.effect x)). set (to_literals x)))"
      apply (subst del_lits)
      apply (subst add_lits)
      by blast
    also 
    have "...
      = to_predicate ` 
        (S 
        - (\<Union>x\<in>h. set (dels (ground_action.effect x))) 
        \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))))"
      using S_lits' add_lits' del_lits' by auto
    finally
    have 1: "(\<Union>x\<in>S. to_predicate ` set (to_literals x))
      - (\<Union>x\<in>h. to_predicate ` set (dels (ground_action.effect x))) 
      \<union> (\<Union>x\<in>h. to_predicate ` set (adds (ground_action.effect x))) 
      = to_predicate ` 
        (S 
        - (\<Union>x\<in>h. set (dels (ground_action.effect x))) 
        \<union> (\<Union>x\<in>h. set (adds (ground_action.effect x))))" by blast
  } note 1 = this
  {
    have "T = \<Union>((\<lambda>x. set (to_literals x)) ` T)"
      unfolding assms(1)[symmetric]
      using S_lits' del_lits' add_lits' by simp
    hence 2: "(\<Union>x\<in>T. to_predicate ` (set (to_literals x))) = to_predicate ` T" by fastforce
  } note 2 = this
  show ?thesis
    unfolding adds_spec_alt dels_spec_alt 
    unfolding set_map set_remdups
    using 1 2 assms(1) by argo
qed
  

text \<open>Apply-effects bridge.  The FPS actions-at-\<open>t\<close> (@{const acts_of_temporal_plan_at}) and the
  project actions-at-\<open>t\<close> (@{const acts_of_plan_at_simplified}) decompose over the same plan
  entries; their durative snaps differ only in the folded duration constraints and duration
  value, which do not touch @{const ast_effect.adds}/@{const ast_effect.dels} (see the snap-effect
  bridges above).  Hence the @{const ast_effect.adds}/@{const ast_effect.dels} unions coincide, and
  the set-based @{const imp_defs.rat_impl.apply_effects} agrees on the two action lists.\<close>

lemma acts_of_plan_snap_effect_bridge:
  assumes "a \<in> set (acts_of_temporal_plan_at t tp)"
  obtains a' where "a' \<in> set (acts_of_plan_at_simplified t tp)"
    "set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))"
    "set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))"
proof (rule in_acts_of_temporal_plan_atE[OF assms], goal_cases)
  case (1 \<pi>)
  obtain n args where \<pi>: "\<pi> = SimplePlanAction n args"
    using 1 unfolding simple_acts_def is_act_simple_def by (cases \<pi>) auto
  have mem: "(t, SimplePlanAction n args) \<in> set tp" using 1 \<pi> unfolding simple_acts_def by simp
  show ?case
    apply (rule that[of "the (res_inst (SimplePlanAction n args))"])
    using acts_of_plan_at_simplified_res_instI[OF mem] 1 \<pi> by simp_all
next
  case (2 \<pi>)
  obtain n args dur where \<pi>: "\<pi> = DurativePlanAction n args dur"
    using 2 unfolding durative_acts_def is_act_simple_def by (cases \<pi>) auto
  have mem: "(t, DurativePlanAction n args dur) \<in> set tp"
    using 2 \<pi> unfolding durative_acts_def by auto
  have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
  obtain ps dcs pre eff where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
  show ?case
    apply (rule that[of "at_start_spec (the (resolve_temporal_action_schema n))"])
      apply (rule acts_of_plan_at_simplified_startI[OF mem])
    using 2 \<pi> args res_inst_snap_start_adds[OF res] res_inst_snap_start_dels[OF res] by simp_all
next
  case (3 t' \<pi>)
  obtain n args dur where \<pi>: "\<pi> = DurativePlanAction n args dur"
    using 3 unfolding durative_acts_def is_act_simple_def by (cases \<pi>) auto
  have mem: "(t', DurativePlanAction n args dur) \<in> set tp"
    using 3 \<pi> unfolding durative_acts_def by auto
  have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
  have te: "t = t' + dur" using 3 \<pi> by simp
  obtain ps dcs pre eff where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
  show ?case
    apply (rule that[of "at_end_spec (the (resolve_temporal_action_schema n))"])
      apply (rule acts_of_plan_at_simplified_endI[OF mem te])
    using 3 \<pi> args res_inst_snap_end_adds[OF res] res_inst_snap_end_dels[OF res] by simp_all
qed

lemma acts_of_plan_snap_effect_bridge':
  assumes "a' \<in> set (acts_of_plan_at_simplified t tp)"
  obtains a where "a \<in> set (acts_of_temporal_plan_at t tp)"
    "set (adds (ground_action.effect a)) = set (adds (ground_action.effect a'))"
    "set (dels (ground_action.effect a)) = set (dels (ground_action.effect a'))"
proof (rule in_acts_of_plan_at_simplifiedE[OF assms], goal_cases)
  case (1 n args)
  have mem: "(t, SimplePlanAction n args) \<in> set tp" using 1 by simp
  have inFPS: "the (res_inst (SimplePlanAction n args)) \<in> set (acts_of_temporal_plan_at t tp)"
    unfolding acts_of_temporal_plan_at_def set_concat set_map
    by (rule UN_I[OF imageI[OF mem]]) simp
  show ?case
    apply (rule that[of "the (res_inst (SimplePlanAction n args))"])
    using inFPS 1 by simp_all
next
  case (2 n args dur)
  have mem: "(t, DurativePlanAction n args dur) \<in> set tp" using 2 by simp
  have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
  obtain ps dcs pre eff where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
  have inFPS: "the (res_inst_snap_action (DurativePlanAction n args dur) At_Start) \<in> set (acts_of_temporal_plan_at t tp)"
    unfolding acts_of_temporal_plan_at_def set_concat set_map
    by (rule UN_I[OF imageI[OF mem]]) simp
  show ?case
    apply (rule that[of "the (res_inst_snap_action (DurativePlanAction n args dur) At_Start)"])
    using inFPS 2 args res_inst_snap_start_adds[OF res] res_inst_snap_start_dels[OF res] by simp_all
next
  case (3 t' n args dur)
  have mem: "(t', DurativePlanAction n args dur) \<in> set tp" using 3 by simp
  have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
  have te: "t = t' + dur" using 3 by simp
  obtain ps dcs pre eff where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
  have inFPS: "the (res_inst_snap_action (DurativePlanAction n args dur) At_End) \<in> set (acts_of_temporal_plan_at t tp)"
    unfolding acts_of_temporal_plan_at_def set_concat set_map
    apply (rule UN_I[OF imageI[OF mem]])
    using te by simp
  show ?case
    apply (rule that[of "the (res_inst_snap_action (DurativePlanAction n args dur) At_End)"])
    using inFPS 3 args res_inst_snap_end_adds[OF res] res_inst_snap_end_dels[OF res] by simp_all
qed

lemma acts_of_plan_at_adds_union_eq:
  "(\<Union>a\<in>set (acts_of_temporal_plan_at t tp). set (adds (ground_action.effect a)))
     = (\<Union>a\<in>set (acts_of_plan_at_simplified t tp). set (adds (ground_action.effect a)))"
  apply (rule equalityI; rule UN_least)
  subgoal for a
    apply (erule acts_of_plan_snap_effect_bridge)
    subgoal for a' by (rule UN_upper[THEN subset_trans]) auto
    done
  subgoal for a'
    apply (erule acts_of_plan_snap_effect_bridge')
    subgoal for a by (rule UN_upper[THEN subset_trans]) auto
    done
  done

lemma acts_of_plan_at_dels_union_eq:
  "(\<Union>a\<in>set (acts_of_temporal_plan_at t tp). set (dels (ground_action.effect a)))
     = (\<Union>a\<in>set (acts_of_plan_at_simplified t tp). set (dels (ground_action.effect a)))"
  apply (rule equalityI; rule UN_least)
  subgoal for a
    apply (erule acts_of_plan_snap_effect_bridge)
    subgoal for a' by (rule UN_upper[THEN subset_trans]) auto
    done
  subgoal for a'
    apply (erule acts_of_plan_snap_effect_bridge')
    subgoal for a by (rule UN_upper[THEN subset_trans]) auto
    done
  done

lemma set_adds_spec: "set (adds_spec a) = to_predicate ` set (adds (ground_action.effect a))"
  by (cases a) (simp add: image_image)

lemma set_dels_spec: "set (dels_spec a) = to_predicate ` set (dels (ground_action.effect a))"
  by (cases a) (simp add: image_image)

lemma apply_effects_acts_bridge:
  "imp_defs.rat_impl.apply_effects (set (acts_of_temporal_plan_at t tp)) M
     = imp_defs.rat_impl.apply_effects (set (acts_of_plan_at_simplified t tp)) M"
proof -
  have A: "(\<Union>x\<in>set (acts_of_temporal_plan_at t tp). set (adds_spec x))
      = (\<Union>x\<in>set (acts_of_plan_at_simplified t tp). set (adds_spec x))"
    unfolding set_adds_spec
    unfolding image_UN[symmetric]
    using acts_of_plan_at_adds_union_eq[of t] by simp
  have D: "(\<Union>x\<in>set (acts_of_temporal_plan_at t tp). set (dels_spec x))
      = (\<Union>x\<in>set (acts_of_plan_at_simplified t tp). set (dels_spec x))"
    unfolding set_dels_spec
    unfolding image_UN[symmetric]
    using acts_of_plan_at_dels_union_eq[of t] by simp
  show ?thesis
    unfolding imp_defs.rat_impl.apply_effects_def
    unfolding temp_plan_defs.apply_effects_def comp_def
    using A D by simp
qed

lemma apply_effects_subseq:
  assumes "i < length imp_defs.rat_impl.htpl" 
  shows "imp_defs.rat_impl.apply_effects 
      (imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq (imp_defs.rat_impl.time_index i)) 
      (plan_state_list ! i) = plan_state_list ! Suc i"
proof -
  have i': "i < length htps" using assms ref_htpl_eq_htps by argo
  hence Sia: "Suc i < length abstr_state_list" 
    and Sip: "Suc i < length plan_state_list" 
      using length_abstr_state_list length_plan_state_list by simp+
  hence ia: "i < length abstr_state_list" 
    and ip: "i < length plan_state_list" by simp+

  have x: "apply_eff (acts_of_temporal_plan_at (htps ! i) tp) (abstr_state_list ! i) = abstr_state_list ! Suc i"
    by (rule abstr_state_list_nth_Suc[OF i', symmetric])

  have 2: "set (acts_of_plan_at_simplified (htps ! i) tp) \<subseteq> {x. ground_act_no_args x \<and> wf_ground_action x}"
    using acts_of_plan_at_simplified_wf acts_of_temporal_plan_at_no_args by blast

  have 3: "fst (abstr_state_list ! i) \<subseteq> {x. form_preds_no_args x \<and> is_predAtom x}"
  proof -
    have "\<forall>p \<in> fst (abstr_state_list ! i). form_preds_no_args p \<and> is_predAtom p"
    proof (rule valid_temporal_state_seq_prop_pred_initial)
      show "valid_temporal_state_seq I (take i htps) tp (abstr_state_list ! i)"
        using valid_temporal_state_seq_abstr_state_list_i i' by fastforce
      show "\<forall>p\<in>fst I. form_preds_no_args p \<and> is_predAtom p"
      proof -
        presume "\<forall>p \<in> fst I. form_preds_no_args p"
        thus ?thesis unfolding I_def by auto
      next
        show "\<forall>p \<in> fst I. form_preds_no_args p" 
          using init_no_args unfolding I_def list_all_iff by simp
      qed
      have "\<forall>t\<in>set htps. \<forall>a\<in>set (acts_of_temporal_plan_at t tp). 
        \<forall>p\<in>set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). 
          form_preds_no_args p \<and> is_predAtom p"
      proof (intro ballI)
        fix t a p
        assume t: "t \<in> set htps" 
          and a: "a \<in> set (acts_of_temporal_plan_at t tp)" 
          and p: "p \<in> set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a))"
        obtain a' where
          a': "a' \<in> set (acts_of_plan_at_simplified t tp)"
          and adds_eq: "set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))"
          and dels_eq: "set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))"
          using acts_of_plan_snap_effect_bridge[OF a] by blast
        have p': "p \<in> set (adds (ground_action.effect a')) \<union> set (dels (ground_action.effect a'))"
          using p adds_eq dels_eq by simp
        have na': "ground_act_no_args a'" 
          and wfa': "wf_ground_action a'"
          using a' acts_of_plan_at_simplified_wf acts_of_temporal_plan_at_no_args by blast+
        have "form_preds_no_args p" 
          using p' na'
          by (metis Un_iff ground_act_no_args_imp_adds_no_args ground_act_no_args_imp_dels_no_args)
        moreover
        have "is_predAtom p"
          using p' wfa'
          by (metis Un_iff wf_ground_action_adds_preds wf_ground_action_dels_preds)
        ultimately show "form_preds_no_args p \<and> is_predAtom p" ..
      qed
      thus "\<forall>t\<in>set (take i htps). \<forall>a\<in>set (acts_of_temporal_plan_at t tp). 
        \<forall>p\<in>set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a)). 
          form_preds_no_args p \<and> is_predAtom p"
        using set_take_subset by fast 
    qed 
    thus ?thesis by blast
  qed

  have x': "fst (abstr_state_list ! i)
      - (\<Union>a\<in>set (acts_of_plan_at_simplified (htps ! i) tp). set (dels (ground_action.effect a)))
      \<union> (\<Union>a\<in>set (acts_of_plan_at_simplified (htps ! i) tp). set (adds (ground_action.effect a)))
      = fst (abstr_state_list ! Suc i)"
    using arg_cong[OF x[unfolded apply_eff_unfold], of fst]
    unfolding acts_of_plan_at_dels_union_eq[of "htps ! i", symmetric]
    unfolding acts_of_plan_at_adds_union_eq[of "htps ! i", symmetric]
    by (simp add: o_def)

  have "imp_defs.rat_impl.apply_effects (set (acts_of_plan_at_simplified (htps ! i) tp)) (plan_state_list ! i) = plan_state_list ! Suc i"
    unfolding plan_state_list_nth_conv_abstr_state_list_nth[OF ip]
    unfolding plan_state_list_nth_conv_abstr_state_list_nth[OF Sip]
    unfolding x'[symmetric]
    using apply_effects_if[OF x' 3 2]
    unfolding x'[symmetric]
    by (simp add: imp_defs.rat_impl.apply_effects_def set_map)
  thus ?thesis
    unfolding plan_happ_seq_alt
    apply (subst ground_non_action_no_effs)
     apply (rule missing_ends_ground_non_actions)
    unfolding imp_defs.rat_impl.time_index_def ref_htpl_eq_htps 
    by blast
qed

text \<open>Point-based temporal invariants active at a time point.  Re-point of the (orphaned) continuous
  \<open>invs_of_plan_at\<close>: built on the clash-free temporal @{const res_inst_temporal_inv} (the over-all snap
  precondition) instead of the continuous \<open>res_inst_inv\<close>.  Proven equivalent to the interval form
  @{const invs_of_temporal_plan_in_interval} where needed (see \<open>invs_of_plan_at\<close>).\<close>
definition invs_of_plan_at :: "time \<Rightarrow> plan \<Rightarrow> (object atom) formula set" where
  "invs_of_plan_at t \<pi>s \<equiv>
     {inv. \<exists>t' a. (t', a) \<in> durative_acts \<pi>s \<and> t' < t \<and> t \<le> t' + duration a
            \<and> Some inv = res_inst_temporal_inv a}"

lemma to_literals_BigAnd: "to_literals (\<^bold>\<And> Fs) = concat (map to_literals Fs)"
  by (induction Fs) auto

lemma map_formula_BigAnd: "map_formula g (\<^bold>\<And> Fs) = \<^bold>\<And> (map (map_formula g) Fs)"
  by (induction Fs) auto

text \<open>@{const inst_duration_in_atom} is the identity on @{const predAtm} and maps every other atom
  constructor to the same constructor, so it is invisible to @{const to_literals} (which keeps only
  positively-occurring @{const predAtm} literals).\<close>
lemma to_literals_map_formula_inst_duration:
  "to_literals (map_formula (\<lambda>a. inst_duration_in_atom a dur) \<psi>) = to_literals \<psi>"
proof (induction \<psi>)
  case (Atom x) thus ?case by (cases x) auto
qed auto

text \<open>Hence the duration value is invisible to @{const to_literals} after instantiation.\<close>
lemma to_literals_inst_formula_dur:
  "to_literals (inst_formula f dur \<psi>) = to_literals (map_formula (map_atom f) \<psi>)"
proof -
  have "inst_formula f dur \<psi> = map_formula (\<lambda>a. inst_duration_in_atom a dur) (map_formula (map_atom f) \<psi>)"
    unfolding inst_formula.simps by (simp add: formula.map_comp)
  thus ?thesis by (simp add: to_literals_map_formula_inst_duration)
qed

lemma filter_time_spec_append:
  "filter_time_spec ta (xs @ ys) = filter_time_spec ta xs @ filter_time_spec ta ys"
  unfolding filter_time_spec_def by simp

text \<open>A folded duration constraint is a numeric atom, hence dropped by @{const to_literals}.\<close>
lemma to_literals_map_atom_duration_constraint:
  "to_literals (map_formula (map_atom f) (duration_constraint_as_formula y)) = []"
proof (cases y)
  case (DurationConstraint dop ex)
  thus ?thesis by (cases dop) auto
qed

text \<open>Bridge replacing the (continuous, clashing) \<open>inst_cond_alt\<close>: the project's predicate-level
  over-all spec equals the predicates of the temporal over-all invariant @{const res_inst_temporal_inv}.
  The folded duration constraints (numeric atoms) and the duration value both vanish under
  @{const to_literals} (see the lemmas above).\<close>
lemma over_all_spec_eq_res_inst_temporal_inv:
  assumes res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "set (over_all_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)))
       = set (map to_predicate (to_literals (the (res_inst_temporal_inv (DurativePlanAction n [] dur)))))"
proof -
  have D_drop: "concat (map (\<lambda>\<phi>. to_literals (map_formula (map_atom f) \<phi>))
      (filter_time_spec Over_All (map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) D))) = []" for f D
    unfolding filter_time_spec_def
    by (induction D) (auto simp: to_literals_map_atom_duration_constraint split: prod.splits)
  have nf: "to_literals (inst_formula (tsubst (ActionHead n ps) []) DUR
        (\<^bold>\<And> (filter_time_spec Over_All (pre @ map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) D))))
      = concat (map (\<lambda>\<phi>. to_literals (map_formula (map_atom (tsubst (ActionHead n ps) [])) \<phi>))
          (filter_time_spec Over_All pre))" for DUR D
    apply (subst to_literals_inst_formula_dur, subst map_formula_BigAnd, subst to_literals_BigAnd)
    apply (simp add: filter_time_spec_append o_def D_drop)
    done
  have rhs: "the (res_inst_temporal_inv (DurativePlanAction n [] dur))
      = inst_formula (tsubst (ActionHead n ps) []) dur
          (\<^bold>\<And> (filter_time_spec Over_All (pre @ map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) dcs)))"
    using res by (simp add: inst_snap_action_body_elements.simps)
  have lhs: "over_all_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))
      = remdups (map to_predicate (to_literals (inst_formula (tsubst (ActionHead n ps) []) 0
          (\<^bold>\<And> (filter_time_spec Over_All (pre @ map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) []))))))"
    by (simp add: pre_spec.simps inst_snap_action_body_elements.simps)
  show ?thesis
    unfolding lhs rhs by (simp only: set_remdups nf)
qed

text \<open>Precondition bridge.  As for the effect, the precondition of the FPS durative snap and of the
  project snap agree once the numeric duration atoms and the duration value are dropped by
  @{const to_literals}, so they share the same @{const pre_spec} (the reduction's predicate-level
  precondition).\<close>

lemma to_literals_inst_snap_body_elements_indep:
  "to_literals (ground_action.precondition (inst_snap_action_body_elements dc cond eff f dur ta))
     = to_literals (ground_action.precondition (inst_snap_action_body_elements [] cond eff f dur' ta))"
  for f :: "term \<Rightarrow> object"
proof -
  have D_drop: "concat (map (\<lambda>\<phi>. to_literals (map_formula (map_atom f) \<phi>))
      (filter_time_spec ta (map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) D))) = []" for D
    unfolding filter_time_spec_def
    by (induction D) (auto simp: to_literals_map_atom_duration_constraint split: prod.splits)
  have nf: "to_literals (inst_formula f DUR
        (\<^bold>\<And> (filter_time_spec ta (cond @ map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) D))))
      = concat (map (\<lambda>\<phi>. to_literals (map_formula (map_atom f) \<phi>)) (filter_time_spec ta cond))" for DUR D
    apply (subst to_literals_inst_formula_dur, subst map_formula_BigAnd, subst to_literals_BigAnd)
    apply (simp add: filter_time_spec_append o_def D_drop)
    done
  show ?thesis
    unfolding inst_snap_action_body_elements.simps Let_def ground_action.sel
    unfolding nf by simp
qed

lemma pre_spec_res_inst_snap_start:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "pre_spec (the (res_inst_snap_action (DurativePlanAction n [] dur) At_Start))
       = pre_spec (at_start_spec (the (resolve_temporal_action_schema n)))"
proof -
  have "pre_spec (inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) []) dur At_Start)
      = pre_spec (inst_snap_action_body_elements [] pre eff (tsubst (ActionHead n ps) []) 0 At_Start)"
    by (cases "inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) []) dur At_Start";
        cases "inst_snap_action_body_elements [] pre eff (tsubst (ActionHead n ps) []) 0 At_Start")
       (metis (no_types, lifting) ground_action.sel(1) pre_spec.simps
          to_literals_inst_snap_body_elements_indep)
  thus ?thesis using assms by simp
qed

lemma pre_spec_res_inst_snap_end:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "pre_spec (the (res_inst_snap_action (DurativePlanAction n [] dur) At_End))
       = pre_spec (at_end_spec (the (resolve_temporal_action_schema n)))"
proof -
  have "pre_spec (inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) []) dur At_End)
      = pre_spec (inst_snap_action_body_elements [] pre eff (tsubst (ActionHead n ps) []) 0 At_End)"
    by (cases "inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) []) dur At_End";
        cases "inst_snap_action_body_elements [] pre eff (tsubst (ActionHead n ps) []) 0 At_End")
       (metis (no_types, lifting) ground_action.sel(1) pre_spec.simps
          to_literals_inst_snap_body_elements_indep)
  thus ?thesis using assms by simp
qed

lemma pre_spec_acts_union_eq:
  "(\<Union>a\<in>set (acts_of_temporal_plan_at t tp). set (pre_spec a))
     = (\<Union>a\<in>set (acts_of_plan_at_simplified t tp). set (pre_spec a))"
proof (rule equalityI; rule UN_least)
  fix a assume "a \<in> set (acts_of_temporal_plan_at t tp)"
  thus "set (pre_spec a) \<subseteq> (\<Union>a\<in>set (acts_of_plan_at_simplified t tp). set (pre_spec a))"
  proof (rule in_acts_of_temporal_plan_atE, goal_cases)
    case (1 \<pi>)
    obtain n args where \<pi>: "\<pi> = SimplePlanAction n args"
      using 1 unfolding simple_acts_def is_act_simple_def by (cases \<pi>) auto
    have mem: "(t, SimplePlanAction n args) \<in> set tp" using 1 \<pi> unfolding simple_acts_def by simp
    show ?case using 1 \<pi> acts_of_plan_at_simplified_res_instI[OF mem] by (blast intro: UN_upper[THEN subset_trans])
  next
    case (2 \<pi>)
    obtain n args dur where \<pi>: "\<pi> = DurativePlanAction n args dur"
      using 2 unfolding durative_acts_def is_act_simple_def by (cases \<pi>) auto
    have mem: "(t, DurativePlanAction n args dur) \<in> set tp" using 2 \<pi> unfolding durative_acts_def by auto
    have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
    obtain ps dcs pre eff where
      res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
    have "set (pre_spec a) = set (pre_spec (at_start_spec (the (resolve_temporal_action_schema n))))"
      using 2 \<pi> args pre_spec_res_inst_snap_start[OF res] by simp
    thus ?case using acts_of_plan_at_simplified_startI[OF mem] by (blast intro: UN_upper[THEN subset_trans])
  next
    case (3 t' \<pi>)
    obtain n args dur where \<pi>: "\<pi> = DurativePlanAction n args dur"
      using 3 unfolding durative_acts_def is_act_simple_def by (cases \<pi>) auto
    have mem: "(t', DurativePlanAction n args dur) \<in> set tp" using 3 \<pi> unfolding durative_acts_def by auto
    have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
    have te: "t = t' + dur" using 3 \<pi> by simp
    obtain ps dcs pre eff where
      res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
    have "set (pre_spec a) = set (pre_spec (at_end_spec (the (resolve_temporal_action_schema n))))"
      using 3 \<pi> args pre_spec_res_inst_snap_end[OF res] by simp
    thus ?case using acts_of_plan_at_simplified_endI[OF mem te] by (blast intro: UN_upper[THEN subset_trans])
  qed
next
  fix a assume "a \<in> set (acts_of_plan_at_simplified t tp)"
  thus "set (pre_spec a) \<subseteq> (\<Union>a\<in>set (acts_of_temporal_plan_at t tp). set (pre_spec a))"
  proof (rule in_acts_of_plan_at_simplifiedE, goal_cases)
    case (1 n args)
    have mem: "(t, SimplePlanAction n args) \<in> set tp" using 1 by simp
    have inFPS: "the (res_inst (SimplePlanAction n args)) \<in> set (acts_of_temporal_plan_at t tp)"
      unfolding acts_of_temporal_plan_at_def set_concat set_map
      by (rule UN_I[OF imageI[OF mem]]) simp
    show ?case using 1 inFPS by (blast intro: UN_upper[THEN subset_trans])
  next
    case (2 n args dur)
    have mem: "(t, DurativePlanAction n args dur) \<in> set tp" using 2 by simp
    have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
    obtain ps dcs pre eff where
      res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
    have inFPS: "the (res_inst_snap_action (DurativePlanAction n args dur) At_Start) \<in> set (acts_of_temporal_plan_at t tp)"
      unfolding acts_of_temporal_plan_at_def set_concat set_map
      by (rule UN_I[OF imageI[OF mem]]) simp
    have "set (pre_spec a) = set (pre_spec (the (res_inst_snap_action (DurativePlanAction n args dur) At_Start)))"
      using 2 args pre_spec_res_inst_snap_start[OF res] by simp
    thus ?case using inFPS by (blast intro: UN_upper[THEN subset_trans])
  next
    case (3 t' n args dur)
    have mem: "(t', DurativePlanAction n args dur) \<in> set tp" using 3 by simp
    have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff by (cases args) auto
    have te: "t = t' + dur" using 3 by simp
    obtain ps dcs pre eff where
      res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using mem wf_plan_actions durative_plan_action_schema_type1 by fastforce
    have inFPS: "the (res_inst_snap_action (DurativePlanAction n args dur) At_End) \<in> set (acts_of_temporal_plan_at t tp)"
      unfolding acts_of_temporal_plan_at_def set_concat set_map
      apply (rule UN_I[OF imageI[OF mem]]) using te by simp
    have "set (pre_spec a) = set (pre_spec (the (res_inst_snap_action (DurativePlanAction n args dur) At_End)))"
      using 3 args pre_spec_res_inst_snap_end[OF res] by simp
    thus ?case using inFPS by (blast intro: UN_upper[THEN subset_trans])
  qed
qed

lemma plan_inv_seq_alt:
  "imp_defs.rat_impl.invs_at imp_defs.rat_impl.plan_inv_seq t = \<Union> (set ` (map to_predicate) ` to_literals ` invs_of_plan_at t tp)"
proof -
  presume "{p. \<exists>a d t'. p \<in> (set \<circ> over_all_spec) a \<and> (a, t', d) \<in> ran abstr_plan \<and> t' < t \<and> t \<le> t' + d} 
    = \<Union> (set ` (map to_predicate) ` to_literals ` invs_of_plan_at t tp)"
  moreover
  have "imp_defs.rat_impl.invs_at imp_defs.rat_impl.plan_inv_seq t = 
    {p. \<exists>a d t'. p \<in> (set \<circ> over_all_spec) a \<and> (a, t', d) \<in> ran abstr_plan \<and> t' < t \<and> t \<le> t' + d}"
    unfolding imp_defs.rat_impl.invs_at_plan_inv_seq_alt
    unfolding abstr_plan_def[symmetric]
    by auto
  ultimately
  show ?thesis by auto
next
  show "{p. \<exists>a d t'. p \<in> (set \<circ> over_all_spec) a \<and> (a, t', d) \<in> ran abstr_plan \<and> t' < t \<and> t \<le> t' + d} 
    = \<Union> (set ` (map to_predicate) ` to_literals ` invs_of_plan_at t tp)" 
  proof (intro subsetI equalityI CollectI; (elim exE CollectE conjE)?)
    fix x a t' d
    assume 
      x: "x \<in> (set \<circ> over_all_spec) a" 
      and plan_act: "(a, t', d) \<in> ran abstr_plan" 
      and t: "t' < t" "t \<le> t' + d" 
    moreover
    presume "\<And>a t' d. (a, t', d) \<in> ran abstr_plan \<Longrightarrow> 
      x \<in> (set \<circ> over_all_spec) a \<longrightarrow> t' < t \<longrightarrow> t \<le> t' + d 
      \<longrightarrow> x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)" 
    ultimately
    show "x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)" 
      by simp
  next
    fix x a t' d
    assume plan_act: "(a, t', d) \<in> ran abstr_plan"
    presume a: "\<And>a ta d taa n as da. (taa, DurativePlanAction n as da) \<in> set tp 
      \<Longrightarrow> x \<in> (set \<circ> over_all_spec) (the (resolve_temporal_action_schema n)) 
        \<longrightarrow> rat_of_int \<lfloor>taa\<rfloor> < t 
        \<longrightarrow> t \<le> rat_of_int \<lfloor>taa\<rfloor> + rat_of_int \<lfloor>da\<rfloor> 
        \<longrightarrow> x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)"
    show "x \<in> (set \<circ> over_all_spec) a \<longrightarrow> t' < t \<longrightarrow> t \<le> t' + d
        \<longrightarrow> x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)"
      using plan_act
      apply (rule ran_abstr_plan_ref_planE)
      apply (erule in_set_ref_planE)
      using a by simp+
  next 
    fix x ta n as da
    assume act: "(ta, DurativePlanAction n as da) \<in> set tp" 
    show "x \<in> (set \<circ> over_all_spec) (the (resolve_temporal_action_schema n)) 
      \<longrightarrow> rat_of_int \<lfloor>ta\<rfloor> < t 
      \<longrightarrow> t \<le> rat_of_int \<lfloor>ta\<rfloor> + rat_of_int \<lfloor>da\<rfloor> 
      \<longrightarrow> x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)"
    proof (intro strip)
      assume x: "x \<in> (set \<circ> over_all_spec) (the (resolve_temporal_action_schema n))" 
        and t: "rat_of_int \<lfloor>ta\<rfloor> < t" "t \<le> rat_of_int \<lfloor>ta\<rfloor> + rat_of_int \<lfloor>da\<rfloor>" 
      have t: "ta < t" "t \<le> ta + da" 
        using plan_acts_durs_integer unfolding list_all_iff
        using act is_integer_of_int[of ta] is_integer_of_int[of da] t 
        by fastforce+
      have dur_act: "(ta, DurativePlanAction n as da) \<in> durative_acts tp" 
        unfolding durative_acts_def is_act_simple using act by force

      have as: "as = []" using plan_acts_no_args act unfolding list_all_iff by (cases as) auto
    
      obtain ps dcs pre eff where
        res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
        using dur_act[THEN res_durative_act_name] by auto 
      have inv: "res_inst_temporal_inv (DurativePlanAction n [] da) = Some (the (res_inst_temporal_inv (DurativePlanAction n [] da)))"
        by simp
      have "x \<in> set (over_all_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)))"
        using x res by simp
      hence xinv: "x \<in> set (map to_predicate (to_literals (the (res_inst_temporal_inv (DurativePlanAction n [] da)))))"
        using over_all_spec_eq_res_inst_temporal_inv[OF res, of da] by simp
      show "x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)" 
        unfolding invs_of_plan_at_def using xinv dur_act t as inv by fastforce
    qed
  next
    fix x
    assume "x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at t tp)" 
    then obtain t' a inv where
      x: "x \<in> set (map to_predicate (to_literals inv))"
      and act: "(t', a) \<in> durative_acts tp" 
      and tlt: "t' < t" "t \<le> t' + duration a" 
      and invF: "Some inv = res_inst_temporal_inv a" unfolding invs_of_plan_at_def by blast
    obtain n as da where
      a: "a = DurativePlanAction n as da" 
      using act unfolding durative_acts_def is_act_simple by (cases a) auto
    have act: "(t', DurativePlanAction n as da) \<in> durative_acts tp" using act a by simp

    have as: "as = []" using plan_acts_no_args act unfolding list_all_iff durative_acts_def by (cases as) auto
  
    obtain ps dcs pre eff where
      res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using res_durative_act_name[OF act] by auto
    have invE: "res_inst_temporal_inv (DurativePlanAction n [] da) = Some inv" using invF a as by simp
    have x: "x \<in> (set \<circ> over_all_spec) (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))" 
      using over_all_spec_eq_res_inst_temporal_inv[OF res, of da] invE x by simp

    have "(DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), rat_of_int \<lfloor>t'\<rfloor>, rat_of_int \<lfloor>da\<rfloor>) \<in> ran abstr_plan"
      using ran_abstr_planI in_set_ref_planI act res unfolding durative_acts_def by fastforce
    moreover
    have "is_integer t'" "is_integer da" using act plan_acts_durs_integer 
      unfolding durative_acts_def list_all_iff by auto
    ultimately
    have "(DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t', da) \<in> ran abstr_plan" 
      using is_integer_of_int by simp
    thus "\<exists>a d t'. x \<in> (set \<circ> over_all_spec) a \<and> (a, t', d) \<in> ran abstr_plan \<and> t' < t \<and> t \<le> t' + d" 
      using x tlt a by force
  qed
qed


lemma lwm_basic_to_predicate_subset:
  assumes "lwm_basic (fst M)"
      and "S \<subseteq> fst M"
    shows "to_predicate ` S \<subseteq> (\<Union>f \<in> fst M. set (map to_predicate (to_literals f)))"
proof
  fix x assume "x \<in> to_predicate ` S"
  then obtain l where l: "l \<in> S" and x: "x = to_predicate l" by blast
  have "l \<in> fst M" using l assms(2) by blast
  hence "is_predAtom l" using assms(1) unfolding lwm_basic_def by blast
  hence "to_literals l = [l]" using is_predAtom_literals by blast
  hence "x \<in> set (map to_predicate (to_literals l))" using x by simp
  thus "x \<in> (\<Union>f \<in> fst M. set (map to_predicate (to_literals f)))"
    using \<open>l \<in> fst M\<close> by blast
qed

text \<open>An element of the strictly-sorted \<open>htps\<close> that is below \<open>htps ! i\<close> lies at or before index
  \<open>i - 1\<close>; in particular \<open>i\<close> is positive.\<close>
lemma htps_set_lt_nth_le_prev:
  assumes "t' \<in> set htps" and "t' < htps ! i" and "i < length htps"
  shows "0 < i \<and> t' \<le> htps ! (i - 1)"
proof -
  have srt: "sorted_wrt (<) htps" using htps_seq_htps unfolding htps_seq_def by blast
  obtain k where klen: "k < length htps" and kt: "htps ! k = t'"
    using assms(1) by (metis in_set_conv_nth)
  have lt: "htps ! k < htps ! i" using kt assms(2) by simp
  have ki: "k < i"
  proof (rule ccontr)
    assume "\<not> k < i" hence ik: "i \<le> k" by simp
    show False
    proof (cases "i = k")
      case True thus False using lt by simp
    next
      case False hence "i < k" using ik by simp
      hence "htps ! i < htps ! k" using sorted_wrt_nth_less[OF srt _ klen] by blast
      thus False using lt by simp
    qed
  qed
  hence pos: "0 < i" by simp
  have "t' \<le> htps ! (i - 1)"
  proof (cases "k = i - 1")
    case True thus ?thesis using kt by simp
  next
    case False hence ki2: "k < i - 1" using ki pos by simp
    have "i - 1 < length htps" using assms(3) by simp
    hence "htps ! k < htps ! (i - 1)" using sorted_wrt_nth_less[OF srt ki2] by blast
    thus ?thesis using kt by simp
  qed
  thus ?thesis using pos by simp
qed

text \<open>An invariant active at \<open>htps ! i\<close> (necessarily \<open>i > 0\<close>) is satisfied by the abstract state
  \<open>abstr_state_list ! i\<close>: the durative action's interval covers \<open>(htps!(i-1), htps!i)\<close>, whose
  over-all invariants the state-sequence checks at \<open>M'' = apply_eff (\<dots>htps!(i-1)\<dots>) = abstr_state_list ! i\<close>
  (cf. \<open>Temporal_Continuous_Reduction.valid_temporal_plan_equiv\<close> case 3).\<close>
lemma invs_of_plan_at_sat:
  fixes inv :: "object atom formula"
  assumes i': "i < length htps"
      and "inv \<in> invs_of_plan_at (htps ! i) tp"
    shows "valuation (abstr_state_list ! i) \<Turnstile>\<^sub>m inv"
proof -
  from assms(2) obtain t' a where
        act: "(t', a) \<in> durative_acts tp"
    and tlt: "t' < htps ! i"
    and tle: "htps ! i \<le> t' + duration a"
    and invF: "Some inv = res_inst_temporal_inv a"
    unfolding invs_of_plan_at_def by blast
  obtain n as d where a: "a = DurativePlanAction n as d"
    using act unfolding durative_acts_def is_act_simple by (cases a) auto
  have act': "(t', DurativePlanAction n as d) \<in> set tp"
    using act a unfolding durative_acts_def by auto
  have t'_htp: "t' \<in> set htps"
  proof -
    have "(t' \<in> set htps) = ((\<exists>\<pi>. (t', \<pi>) \<in> set tp) \<or> (\<exists>(t\<^sub>\<pi>, \<pi>)\<in>durative_acts tp. t' = t\<^sub>\<pi> + duration \<pi>))"
      using htps_seq_htps unfolding htps_seq_def is_htp_def by blast
    thus ?thesis using act' by blast
  qed
  have prev: "0 < i" "t' \<le> htps ! (i - 1)" using htps_set_lt_nth_le_prev[OF t'_htp tlt i'] by auto
  have im1: "i - 1 < length htps" using i' by simp
  have suc: "Suc (i - 1) = i" using prev(1) by simp
  have inv_in: "inv \<in> set (invs_of_temporal_plan_in_interval (htps ! (i - 1), htps ! i) tp)"
    using act' invF a prev(2) tle
    by (force simp: invs_of_temporal_plan_in_interval_def set_map_filter)
  have v: "valid_temporal_state_seq (abstr_state_list ! (i - 1)) (drop (i - 1) htps) tp final_state"
    using valid_temporal_state_seq_abstr_state_list_f[OF less_imp_le_nat[OF im1]] .
  have di: "drop (i - 1) htps = htps ! (i - 1) # htps ! i # drop (Suc i) htps"
    using Cons_nth_drop_Suc[OF im1, symmetric] Cons_nth_drop_Suc[OF i', symmetric] suc by simp
  have hi: "valuation (apply_eff (acts_of_temporal_plan_at (htps ! (i - 1)) tp) (abstr_state_list ! (i - 1))) \<Turnstile>\<^sub>m inv"
    using valid_temporal_state_seq_head_inv[OF v[unfolded di] inv_in] .
  have "abstr_state_list ! i = apply_eff (acts_of_temporal_plan_at (htps ! (i - 1)) tp) (abstr_state_list ! (i - 1))"
    using abstr_state_list_nth_Suc[OF im1] suc by simp
  thus ?thesis using hi by simp
qed

lemma invs_sat:
  assumes "i < length imp_defs.rat_impl.htpl" 
  shows "imp_defs.rat_impl.invs_at imp_defs.rat_impl.plan_inv_seq (imp_defs.rat_impl.time_index i) \<subseteq> plan_state_list ! i"
proof -
  have i': "i < length htps" using assms ref_htpl_eq_htps by argo
  have ia: "i < length abstr_state_list" using i' length_abstr_state_list by simp
  have lwm: "lwm_basic (fst (abstr_state_list ! i))"
    using abstr_state_list_nth_wf_world_model[OF less_imp_le_nat[OF i']]
    by (cases "abstr_state_list ! i")
       (auto simp: lwm_basic_def wf_fmla_atom_imp_is_predAtom wf_world_model.simps)
  have psl: "plan_state_list ! i = (\<Union>f \<in> fst (abstr_state_list ! i). set (map to_predicate (to_literals f)))"
    unfolding plan_state_list_def using ia by simp
  have "\<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at (htps ! i) tp) \<subseteq> plan_state_list ! i"
  proof
    fix x assume "x \<in> \<Union> (set ` map to_predicate ` to_literals ` invs_of_plan_at (htps ! i) tp)"
    then obtain inv where iv: "inv \<in> invs_of_plan_at (htps ! i) tp"
      and xinv: "x \<in> set (map to_predicate (to_literals inv))" by auto
    have "set (to_literals inv) \<subseteq> fst (abstr_state_list ! i)"
      using to_literals_subset_if_models invs_of_plan_at_sat[OF i' iv] by blast
    hence "to_predicate ` set (to_literals inv) \<subseteq> (\<Union>f \<in> fst (abstr_state_list ! i). set (map to_predicate (to_literals f)))"
      using lwm_basic_to_predicate_subset[OF lwm] by blast
    moreover have "x \<in> to_predicate ` set (to_literals inv)" using xinv by auto
    ultimately show "x \<in> plan_state_list ! i" using psl by blast
  qed
  thus ?thesis
    unfolding plan_inv_seq_alt 
    unfolding imp_defs.rat_impl.time_index_def ref_htpl_eq_htps 
    by blast
qed



lemma pres_sat:
  assumes i: "i < length imp_defs.rat_impl.htpl"
  shows "\<Union> ((set \<circ> pre_spec) ` imp_defs.rat_impl.happ_at imp_defs.rat_impl.plan_happ_seq (imp_defs.rat_impl.time_index i)) \<subseteq> plan_state_list ! i"
proof -
  presume "\<Union> ((set \<circ> pre_spec) ` set (acts_of_temporal_plan_at (htps ! i) tp)) \<subseteq> plan_state_list ! i"
  moreover
  have "\<Union> ((set \<circ> pre_spec) ` missing_ends (htps ! i) tp) = {}"
    using missing_ends_ground_non_actions ground_non_action_pre by fastforce
  ultimately
  show ?thesis
    unfolding plan_happ_seq_alt
    unfolding imp_defs.rat_impl.time_index_def ref_htpl_eq_htps
    using pre_spec_acts_union_eq[of "htps ! i"]
    by (simp add: comp_def)
next
  have i': "i < length htps" using assms ref_htpl_eq_htps by argo
  hence Sia: "Suc i < length abstr_state_list" 
    and Sip: "Suc i < length plan_state_list" 
      using length_abstr_state_list length_plan_state_list by simp+
  hence ia: "i < length abstr_state_list" 
    and ip: "i < length plan_state_list" by simp+

  have v: "valid_temporal_state_seq (abstr_state_list ! i) (drop i htps) tp final_state" 
    using valid_temporal_state_seq_abstr_state_list_f i' by simp
  
  have "length (drop i htps) > 0" using length_drop i' by simp
  then
  obtain t ts where
    "drop i htps = t#ts" by (cases "drop i htps") auto
  hence di: "drop i htps = (htps ! i)#ts" using i' using hd_drop_conv_nth by fastforce

  have entails: "valuation (abstr_state_list ! i) \<Turnstile>\<^sub>m ground_action.precondition a"
    if "a \<in> set (acts_of_temporal_plan_at (htps ! i) tp)" for a
    using valid_temporal_state_seq_head_precond[OF v[unfolded di] that] .

  have basic: "lwm_basic (fst (abstr_state_list ! i))"
  proof -
    have "wf_world_model (abstr_state_list ! i)"
      using abstr_state_list_nth_wf_world_model[of i] i' by simp
    hence "\<forall>f \<in> fst (abstr_state_list ! i). wf_fmla_atom objT f"
      by (cases "abstr_state_list ! i") simp
    thus ?thesis
      unfolding lwm_basic_def using wf_fmla_atom_imp_is_predAtom by blast
  qed

  have sub: "to_predicate ` set (to_literals (ground_action.precondition a))
      \<subseteq> (\<Union>f \<in> fst (abstr_state_list ! i). set (map to_predicate (to_literals f)))"
    if "a \<in> set (acts_of_temporal_plan_at (htps ! i) tp)" for a
  proof (rule lwm_basic_to_predicate_subset[OF basic])
    show "set (to_literals (ground_action.precondition a)) \<subseteq> fst (abstr_state_list ! i)"
      using to_literals_subset_if_models[OF entails[OF that]] .
  qed

  show "\<Union> ((set \<circ> pre_spec) ` set (acts_of_temporal_plan_at (htps ! i) tp)) \<subseteq> plan_state_list ! i "
    unfolding plan_state_list_def
    apply (subst nth_map)
    using Sia apply simp
    unfolding comp_def pre_spec_alt set_remdups set_map image_image
    using sub by auto
qed

text \<open>Non-interference bridge.  @{const acts_non_intrf} depends on its arguments only through their
  @{const ast_effect.adds}/@{const ast_effect.dels} (equal for the FPS and project snaps),
  the numeric-effect @{const lvalues}/@{const additive_lvalues} (the numeric-effect \<^emph>\<open>lhs\<close> is
  untouched by the duration substitution, hence equal), and the precondition/@{const rvalues}
  (the project snap's are \<^emph>\<open>sub\<close>-sets — it drops the folded numeric duration atoms and the
  duration value).  Non-interference is monotone in those two subset positions, so it transfers
  from the FPS snaps to the project snaps.\<close>

lemma numeric_effect_lhs_inst_dur[simp]:
  "numeric_effect.lhs (inst_duration_in_numeric_effect ne d) = numeric_effect.lhs ne"
  by (cases ne) simp

lemma is_additive_effect_inst_dur[simp]:
  "is_additive_effect (inst_duration_in_numeric_effect ne d) = is_additive_effect ne"
  by (cases ne rule: is_additive_effect.cases) simp_all

lemma numeric_effects_inst_duration_in_ast_effect[simp]:
  "numeric_effects (inst_duration_in_ast_effect e d)
     = map (\<lambda>x. inst_duration_in_numeric_effect x d) (numeric_effects e)"
  by (cases e) simp

lemma no_func_sig: "func_sig f = None"
  unfolding func_sig_def by (simp add: no_functions)

lemma no_wf_func_args: "\<not> wf_func_args objT fa"
proof -
  obtain f vs where fa: "fa = (f, vs)" by (cases fa)
  show ?thesis unfolding fa by (simp add: no_func_sig)
qed

lemma no_wf_numeric_effect: "\<not> wf_numeric_effect objT ne"
proof (cases ne)
  case (NumericEffect p l r)
  have "\<not> wf_primitive_numeric_expression objT l"
    using no_wf_func_args by (cases l) auto
  thus ?thesis unfolding NumericEffect by simp
qed

lemma wf_effect_numeric_effects_Nil:
  assumes "wf_effect objT eff"
  shows "numeric_effects eff = []"
proof (cases eff)
  case (Effect a d n)
  have "n = []" using assms no_wf_numeric_effect unfolding Effect by (cases n) auto
  thus ?thesis unfolding Effect by simp
qed

lemma wf_ground_action_numeric_effects_Nil:
  assumes "wf_ground_action g"
  shows "numeric_effects (ground_action.effect g) = []"
  using assms wf_effect_numeric_effects_Nil by (cases g) simp

lemma wf_ground_action_lvalues_Nil:
  assumes "wf_ground_action g"
  shows "lvalues g = []"
  using wf_ground_action_numeric_effects_Nil[OF assms] unfolding lvalues_def by simp

lemma wf_ground_action_additive_lvalues_Nil:
  assumes "wf_ground_action g"
  shows "additive_lvalues g = []"
  using wf_ground_action_numeric_effects_Nil[OF assms] unfolding additive_lvalues_def by simp

lemma inst_snap_action_body_elements_lvalues_indep:
  "lvalues (inst_snap_action_body_elements dc cond eff f dur ta)
     = lvalues (inst_snap_action_body_elements dc' cond' eff f dur' ta)"
  "additive_lvalues (inst_snap_action_body_elements dc cond eff f dur ta)
     = additive_lvalues (inst_snap_action_body_elements dc' cond' eff f dur' ta)"
  for f :: "term \<Rightarrow> object"
  unfolding lvalues_def additive_lvalues_def
  by (simp_all add: inst_snap_action_body_elements.simps comp_def filter_map o_def)

lemma to_literals_subset_Atom_atoms:
  "set (to_literals \<phi>) \<subseteq> Atom ` atoms \<phi>"
  by (induction \<phi> rule: to_literals.induct) auto

lemma acts_non_intrf_mono:
  assumes base: "acts_non_intrf a b"
      and adds_a: "set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))"
      and dels_a: "set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))"
      and lval_a: "set (lvalues a') = set (lvalues a)"
      and alval_a: "set (additive_lvalues a') = set (additive_lvalues a)"
      and pre_a: "Atom ` atoms (precondition a') \<subseteq> Atom ` atoms (precondition a)"
      and rval_a: "set (rvalues a') \<subseteq> set (rvalues a)"
      and adds_b: "set (adds (ground_action.effect b')) = set (adds (ground_action.effect b))"
      and dels_b: "set (dels (ground_action.effect b')) = set (dels (ground_action.effect b))"
      and lval_b: "set (lvalues b') = set (lvalues b)"
      and alval_b: "set (additive_lvalues b') = set (additive_lvalues b)"
      and pre_b: "Atom ` atoms (precondition b') \<subseteq> Atom ` atoms (precondition b)"
      and rval_b: "set (rvalues b') \<subseteq> set (rvalues b)"
    shows "acts_non_intrf a' b'"
proof -
  note eqs = adds_a dels_a lval_a alval_a adds_b dels_b lval_b alval_b
  have base': "Atom ` atoms (precondition a) \<inter> (set (adds (ground_action.effect b)) \<union> set (dels (ground_action.effect b))) = {}"
      "Atom ` atoms (precondition b) \<inter> (set (adds (ground_action.effect a)) \<union> set (dels (ground_action.effect a))) = {}"
      "set (adds (ground_action.effect a)) \<inter> set (dels (ground_action.effect b)) = {}"
      "set (adds (ground_action.effect b)) \<inter> set (dels (ground_action.effect a)) = {}"
      "set (lvalues a) \<inter> set (rvalues b) = {}"
      "set (rvalues a) \<inter> set (lvalues b) = {}"
      "set (lvalues a) \<inter> set (lvalues b) \<subseteq> set (additive_lvalues a) \<inter> set (additive_lvalues b)"
    using base unfolding acts_non_intrf_def Let_def by simp_all
  show ?thesis
    unfolding acts_non_intrf_def Let_def
  proof (intro conjI)
    show "Atom ` atoms (precondition a') \<inter> (set (adds (ground_action.effect b')) \<union> set (dels (ground_action.effect b'))) = {}"
      using base'(1) pre_a adds_b dels_b by blast
    show "Atom ` atoms (precondition b') \<inter> (set (adds (ground_action.effect a')) \<union> set (dels (ground_action.effect a'))) = {}"
      using base'(2) pre_b adds_a dels_a by blast
    show "set (adds (ground_action.effect a')) \<inter> set (dels (ground_action.effect b')) = {}"
      using base'(3) adds_a dels_b by blast
    show "set (adds (ground_action.effect b')) \<inter> set (dels (ground_action.effect a')) = {}"
      using base'(4) adds_b dels_a by blast
    show "set (lvalues a') \<inter> set (rvalues b') = {}"
      using base'(5) lval_a rval_b by blast
    show "set (rvalues a') \<inter> set (lvalues b') = {}"
      using base'(6) rval_a lval_b by blast
    show "set (lvalues a') \<inter> set (lvalues b') \<subseteq> set (additive_lvalues a') \<inter> set (additive_lvalues b')"
      using base'(7) lval_a lval_b alval_a alval_b by blast
  qed
qed

text \<open>A positive, argument-free ground snap has no primitive numeric expressions in its
  precondition (all its precondition atoms are predicate atoms) and no numeric effects (it is
  well-formed and the domain has no functions), hence its @{const rvalues} are empty.\<close>
lemma pos_no_args_rvalues_Nil:
  assumes "ground_act_pres_pos a"
      and "ground_act_no_args a"
      and "wf_ground_action a"
    shows "rvalues a = []"
proof -
  have fna: "form_preds_no_args (ground_action.precondition a)"
    using assms(2) by (cases a) simp
  have pa: "\<forall>x \<in> atoms (ground_action.precondition a). is_predAtom (Atom x)"
    using is_pos_conj_atoms_preds[OF fna] by blast
  have "atom_enumerate_primitive_numeric_expressions x = []"
    if "x \<in> atoms (ground_action.precondition a)" for x
  proof -
    have "is_predAtom (Atom x)" using pa that by blast
    then obtain p vs where "x = predAtm p vs" by (cases "Atom x" rule: is_predAtom.cases) auto
    thus ?thesis by simp
  qed
  hence pre_nil0: "\<forall>x \<in> atoms (ground_action.precondition a). atom_enumerate_primitive_numeric_expressions x = []"
    by blast
  have "set (formula_enumerate_primitive_numeric_expressions (ground_action.precondition a)) = {}"
    unfolding set_formula_enumerate_primitive_numeric_expressions_conv using pre_nil0 by auto
  hence pre_nil': "formula_enumerate_primitive_numeric_expressions (ground_action.precondition a) = []"
    by simp
  have eff_nil: "numeric_effects (ground_action.effect a) = []"
    by (rule wf_ground_action_numeric_effects_Nil[OF assms(3)])
  show ?thesis
    unfolding rvalues_def eff_nil pre_nil' by simp
qed

text \<open>Raw @{const to_literals} precondition bridge for the FPS durative snaps versus the project
  snaps (@{const at_start_spec}/@{const at_end_spec}); the project snaps drop the folded duration
  atoms and the duration value, but @{const to_literals} does too (see
  @{thm to_literals_inst_snap_body_elements_indep}).\<close>
lemma to_literals_res_inst_snap_start:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "to_literals (ground_action.precondition (the (res_inst_snap_action (DurativePlanAction n [] dur) At_Start)))
       = to_literals (ground_action.precondition (at_start_spec (the (resolve_temporal_action_schema n))))"
  using assms to_literals_inst_snap_body_elements_indep by simp

lemma to_literals_res_inst_snap_end:
  assumes "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "to_literals (ground_action.precondition (the (res_inst_snap_action (DurativePlanAction n [] dur) At_End)))
       = to_literals (ground_action.precondition (at_end_spec (the (resolve_temporal_action_schema n))))"
  using assms to_literals_inst_snap_body_elements_indep by simp

lemma list_all2_concat_map:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> list_all2 R (f x) (g x)"
  shows "list_all2 R (concat (map f xs)) (concat (map g xs))"
  using assms by (induction xs) (auto intro: list_all2_appendI)

text \<open>Position-preserving bridge between the project actions-at-\<open>t\<close>
  (@{const acts_of_plan_at_simplified}) and the FPS actions-at-\<open>t\<close>
  (@{const acts_of_temporal_plan_at}).  Both are @{const concat}s over the same plan entries,
  produced by structurally identical clause functions (@{const snap_of_plan_action_at_simplified}
  vs @{const simplified_res_inst_temporal_plan_action_at}) with identical guards, so the two lists
  have equal length and their positions correspond one-to-one.  On each corresponding pair the
  project snap and the FPS snap agree on @{const ast_effect.adds}/@{const ast_effect.dels} and on
  the @{const to_literals} of the precondition (the folded duration atoms and duration value drop
  under @{const to_literals}); for a simple action the two snaps are literally identical.\<close>
lemma acts_of_plan_at_simplified_fps_list_all2:
  "list_all2 (\<lambda>a' a. set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))
                   \<and> set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))
                   \<and> to_literals (ground_action.precondition a') = to_literals (ground_action.precondition a))
     (acts_of_plan_at_simplified t tp) (acts_of_temporal_plan_at t tp)"
  unfolding acts_of_plan_at_simplified_def acts_of_temporal_plan_at_def
proof (rule list_all2_concat_map)
  fix p assume p: "p \<in> set tp"
  obtain t\<^sub>\<pi> \<pi> where p_eq: "p = (t\<^sub>\<pi>, \<pi>)" by (cases p)
  have mem: "(t\<^sub>\<pi>, \<pi>) \<in> set tp" using p p_eq by simp
  show "list_all2 (\<lambda>a' a. set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))
                   \<and> set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))
                   \<and> to_literals (ground_action.precondition a') = to_literals (ground_action.precondition a))
     (snap_of_plan_action_at_simplified t p) (simplified_res_inst_temporal_plan_action_at t p)"
    unfolding p_eq
  proof (cases \<pi>)
    case (SimplePlanAction n args)
    show "list_all2 (\<lambda>a' a. set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))
                   \<and> set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))
                   \<and> to_literals (ground_action.precondition a') = to_literals (ground_action.precondition a))
       (snap_of_plan_action_at_simplified t (t\<^sub>\<pi>, \<pi>)) (simplified_res_inst_temporal_plan_action_at t (t\<^sub>\<pi>, \<pi>))"
      unfolding SimplePlanAction snap_of_plan_action_at_simplified_simps
        simplified_res_inst_temporal_plan_action_at.simps
      by simp
  next
    case (DurativePlanAction n args dur)
    have args: "args = []" using mem plan_acts_no_args unfolding list_all_iff DurativePlanAction by (cases args) auto
    obtain ps dcs pre eff where
      res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using mem wf_plan_actions durative_plan_action_schema_type1 unfolding DurativePlanAction by fastforce
    show "list_all2 (\<lambda>a' a. set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))
                   \<and> set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))
                   \<and> to_literals (ground_action.precondition a') = to_literals (ground_action.precondition a))
       (snap_of_plan_action_at_simplified t (t\<^sub>\<pi>, \<pi>)) (simplified_res_inst_temporal_plan_action_at t (t\<^sub>\<pi>, \<pi>))"
      unfolding DurativePlanAction snap_of_plan_action_at_simplified_simps
        simplified_res_inst_temporal_plan_action_at.simps args
      using res_inst_snap_start_adds[OF res] res_inst_snap_start_dels[OF res] to_literals_res_inst_snap_start[OF res]
      using res_inst_snap_end_adds[OF res] res_inst_snap_end_dels[OF res] to_literals_res_inst_snap_end[OF res]
      by (auto intro: list_all2_appendI)
  qed
qed

text \<open>The ground actions of the simplified plan at a timepoint have positive preconditions.\<close>
lemma acts_of_plan_at_simplified_pres_pos:
  assumes "a \<in> set (acts_of_plan_at_simplified t tp)"
  shows "ground_act_pres_pos a"
proof (rule in_acts_of_plan_at_simplifiedE[OF assms], goal_cases)
  case (1 n as)
  have mem: "(t, SimplePlanAction n as) \<in> set tp" using 1 by simp
  hence wfpa: "wf_plan_action (SimplePlanAction n as)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (SimpleActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain pre eff where bb: "b = SimpleActionBody pre eff"
    by (cases b)
  have sch: "SimpleActionSchema h (SimpleActionBody pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] bb by simp
  have p: "act_pres_pos (SimpleActionSchema h (SimpleActionBody pre eff))"
    using act_pres_pos_spec sch by blast
  have n: "form_preds_no_args pre"
    using sch conds_no_args unfolding actions_spec_def list_all_iff by auto
  have "ground_act_pres_pos (instantiate_temporal_action_schema (SimpleActionSchema h (SimpleActionBody pre eff)) as)"
    using instantiate_action_schema_pres_pos[OF p n] .
  thus ?case using 1 res bb by simp
next
  case (2 n as dur)
  have mem: "(t, DurativePlanAction n as dur) \<in> set tp" using 2 by simp
  hence wfpa: "wf_plan_action (DurativePlanAction n as dur)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff"
    by (cases b)
  have sch: "DurativeActionSchema h (DurativeActionBody dcs pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] b by simp
  have "ground_act_pres_pos (at_start_spec (DurativeActionSchema h (DurativeActionBody dcs pre eff)))"
    using start_snap_pre_pos_conj[OF sch] .
  thus ?case using 2 res b by simp
next
  case (3 t' n as dur)
  have mem: "(t', DurativePlanAction n as dur) \<in> set tp" using 3 by simp
  hence wfpa: "wf_plan_action (DurativePlanAction n as dur)" using wf_plan_actions by blast
  obtain h b where
    res: "resolve_temporal_action_schema n = Some (DurativeActionSchema h b)"
    using wfpa by (cases "resolve_temporal_action_schema n") (auto split: ast_temporal_action_schema.splits)
  obtain dcs pre eff where b: "b = DurativeActionBody dcs pre eff"
    by (cases b)
  have sch: "DurativeActionSchema h (DurativeActionBody dcs pre eff) \<in> set actions_spec"
    using resolve_action_in_actions[OF res] b by simp
  have "ground_act_pres_pos (at_end_spec (DurativeActionSchema h (DurativeActionBody dcs pre eff)))"
    using end_snap_pre_pos_conj[OF sch] .
  thus ?case using 3 res b by simp
qed

text \<open>Position-based non-interference for the project snaps at a happening time.  Transferred from
  the FPS @{const list_pairwise} @{thm htps_acts_list_pairwise} through the position-preserving
  bridge @{thm acts_of_plan_at_simplified_fps_list_all2} and @{thm acts_non_intrf_mono}: the
  project snaps are positive (@{thm acts_of_plan_at_simplified_pres_pos}), argument-free
  (@{thm acts_of_temporal_plan_at_no_args}) and well-formed (@{thm acts_of_plan_at_simplified_wf}),
  so their numeric components (@{const lvalues}/@{const additive_lvalues}/@{const rvalues}) are
  empty and their precondition atoms coincide with their @{const to_literals}.\<close>
lemma all_htps_acts_non_intrf_simplified:
  assumes t_htp: "t \<in> set htps"
  shows "list_pairwise acts_non_intrf (acts_of_plan_at_simplified t tp)"
proof -
  define S where "S = acts_of_plan_at_simplified t tp"
  define F where "F = acts_of_temporal_plan_at t tp"
  have la2: "list_all2 (\<lambda>a' a. set (adds (ground_action.effect a')) = set (adds (ground_action.effect a))
                   \<and> set (dels (ground_action.effect a')) = set (dels (ground_action.effect a))
                   \<and> to_literals (ground_action.precondition a') = to_literals (ground_action.precondition a))
     S F"
    unfolding S_def F_def by (rule acts_of_plan_at_simplified_fps_list_all2)
  have len: "length S = length F" using la2 by (rule list_all2_lengthD)
  have fps_lp: "list_pairwise acts_non_intrf F"
    unfolding F_def using htps_acts_list_pairwise[OF t_htp] .
  have S_props: "ground_act_pres_pos (S ! i)" "ground_act_no_args (S ! i)" "wf_ground_action (S ! i)"
    if "i < length S" for i
  proof -
    have "S ! i \<in> set S" using that by simp
    thus "ground_act_pres_pos (S ! i)" "ground_act_no_args (S ! i)" "wf_ground_action (S ! i)"
      unfolding S_def
      using acts_of_plan_at_simplified_pres_pos acts_of_temporal_plan_at_no_args acts_of_plan_at_simplified_wf
      by blast+
  qed
  have pre_eq: "Atom ` atoms (ground_action.precondition (S ! i)) = set (to_literals (ground_action.precondition (S ! i)))"
    if "i < length S" for i
    using S_props(1)[OF that] by (cases "S ! i") (simp add: pos_conj_form_def)
  have "acts_non_intrf (S ! i) (S ! j)"
    if i: "i < length S" and j: "j < length S" and ij: "i \<noteq> j" for i j
  proof -
    have iF: "i < length F" and jF: "j < length F" using i j len by simp_all
    have base: "acts_non_intrf (F ! i) (F ! j)"
      using list_pairwise_then_at_list_indices[OF fps_lp jF iF ij] .
    note bridge_i = list_all2_nthD[OF la2 i]
    note bridge_j = list_all2_nthD[OF la2 j]
    \<comment> \<open>Both project snaps and both FPS snaps are well-formed, so their numeric components vanish.\<close>
    have wfF_i: "wf_ground_action (F ! i)"
      unfolding F_def using wf_acts_of_temporal_plan_at[OF wf_plan iF[unfolded F_def, THEN nth_mem]] .
    have wfF_j: "wf_ground_action (F ! j)"
      unfolding F_def using wf_acts_of_temporal_plan_at[OF wf_plan jF[unfolded F_def, THEN nth_mem]] .
    show ?thesis
    proof (rule acts_non_intrf_mono[OF base])
      show "set (adds (ground_action.effect (S ! i))) = set (adds (ground_action.effect (F ! i)))"
       and "set (dels (ground_action.effect (S ! i))) = set (dels (ground_action.effect (F ! i)))"
        using bridge_i by simp_all
      show "set (adds (ground_action.effect (S ! j))) = set (adds (ground_action.effect (F ! j)))"
       and "set (dels (ground_action.effect (S ! j))) = set (dels (ground_action.effect (F ! j)))"
        using bridge_j by simp_all
      show "set (lvalues (S ! i)) = set (lvalues (F ! i))"
        using wf_ground_action_lvalues_Nil[OF S_props(3)[OF i]] wf_ground_action_lvalues_Nil[OF wfF_i] by simp
      show "set (lvalues (S ! j)) = set (lvalues (F ! j))"
        using wf_ground_action_lvalues_Nil[OF S_props(3)[OF j]] wf_ground_action_lvalues_Nil[OF wfF_j] by simp
      show "set (additive_lvalues (S ! i)) = set (additive_lvalues (F ! i))"
        using wf_ground_action_additive_lvalues_Nil[OF S_props(3)[OF i]] wf_ground_action_additive_lvalues_Nil[OF wfF_i] by simp
      show "set (additive_lvalues (S ! j)) = set (additive_lvalues (F ! j))"
        using wf_ground_action_additive_lvalues_Nil[OF S_props(3)[OF j]] wf_ground_action_additive_lvalues_Nil[OF wfF_j] by simp
      show "set (rvalues (S ! i)) \<subseteq> set (rvalues (F ! i))"
        using pos_no_args_rvalues_Nil[OF S_props(1)[OF i] S_props(2)[OF i] S_props(3)[OF i]] by simp
      show "set (rvalues (S ! j)) \<subseteq> set (rvalues (F ! j))"
        using pos_no_args_rvalues_Nil[OF S_props(1)[OF j] S_props(2)[OF j] S_props(3)[OF j]] by simp
      show "Atom ` atoms (ground_action.precondition (S ! i)) \<subseteq> Atom ` atoms (ground_action.precondition (F ! i))"
      proof -
        have "Atom ` atoms (ground_action.precondition (S ! i)) = set (to_literals (ground_action.precondition (S ! i)))"
          using pre_eq[OF i] .
        also have "\<dots> = set (to_literals (ground_action.precondition (F ! i)))" using bridge_i by simp
        also have "\<dots> \<subseteq> Atom ` atoms (ground_action.precondition (F ! i))" by (rule to_literals_subset_Atom_atoms)
        finally show ?thesis .
      qed
      show "Atom ` atoms (ground_action.precondition (S ! j)) \<subseteq> Atom ` atoms (ground_action.precondition (F ! j))"
      proof -
        have "Atom ` atoms (ground_action.precondition (S ! j)) = set (to_literals (ground_action.precondition (S ! j)))"
          using pre_eq[OF j] .
        also have "\<dots> = set (to_literals (ground_action.precondition (F ! j)))" using bridge_j by simp
        also have "\<dots> \<subseteq> Atom ` atoms (ground_action.precondition (F ! j))" by (rule to_literals_subset_Atom_atoms)
        finally show ?thesis .
      qed
    qed
  qed
  thus ?thesis
    unfolding S_def[symmetric]
    using list_pairwise_nth_refl[OF acts_non_intrf_symmetric, of S] by blast
qed

text \<open>Two elements drawn from \<^emph>\<open>distinct blocks\<close> of a @{const list_pairwise}-related @{const concat}
  are non-interfering (even when they are equal as values): if they are distinct they occupy distinct
  positions; if they are equal they occur in two distinct blocks, hence at least twice, so the
  reflexive-multiplicity clause of @{thm list_pairwise_as_nonrec} applies.\<close>
lemma list_pairwise_concat_distinct_blocks:
  assumes lp: "list_pairwise R (concat (map f xs))"
      and i: "i < length xs" and j: "j < length xs" and ij: "i \<noteq> j"
      and x: "x \<in> set (f (xs ! i))" and y: "y \<in> set (f (xs ! j))"
    shows "R x y"
proof -
  have xin: "x \<in> set (concat (map f xs))" using x i by auto
  have yin: "y \<in> set (concat (map f xs))" using y j by auto
  have "x = y \<Longrightarrow> 1 < count_list (concat (map f xs)) x"
  proof -
    assume xy: "x = y"
    have ci: "1 \<le> count_list (f (xs ! i)) x" using x count_list_zero_iff[of "f (xs ! i)" x] by linarith
    have "x \<in> set (f (xs ! j))" using y xy by simp
    hence cj: "1 \<le> count_list (f (xs ! j)) x" using count_list_zero_iff[of "f (xs ! j)" x] by linarith
    have "(\<Sum>k\<in>{i, j}. count_list (f (xs ! k)) x) \<le> (\<Sum>k<length xs. count_list (f (xs ! k)) x)"
      using i j by (intro sum_mono2) auto
    hence "2 \<le> (\<Sum>k<length xs. count_list (f (xs ! k)) x)"
      using ci cj ij by simp
    also have "(\<Sum>k<length xs. count_list (f (xs ! k)) x)
             = sum_list (map (\<lambda>ys. count_list ys x) (map f xs))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = count_list (concat (map f xs)) x" by (simp add: count_list_concat)
    finally show "1 < count_list (concat (map f xs)) x" by simp
  qed
  thus ?thesis
    using lp xin yin unfolding list_pairwise_as_nonrec by blast
qed

text \<open>Position-keyed block membership: the @{const at_start_spec} snap of the reference-plan entry at
  position \<open>i\<close> occurs in the \<open>i\<close>-th block of @{term "acts_of_plan_at_simplified (rat_of_int ta) tp"}
  (the block produced by @{term "tp ! i"}).  Mirrors @{thm at_start_snap_at_t} but records the exact
  block, so distinct reference-plan positions yield distinct concat blocks.\<close>
lemma at_start_block_of_ref_plan:
  assumes i: "i < length tp" and eq: "ref_plan ! i = (a, ta, da)"
  shows "at_start_spec a \<in> set (snap_of_plan_action_at_simplified (rat_of_int ta) (tp ! i))"
proof -
  obtain t' \<pi> where tpi: "tp ! i = (t', \<pi>)" by (cases "tp ! i")
  have mem: "(t', \<pi>) \<in> set tp" using i tpi nth_mem by fastforce
  have ref_i: "timed_plan_action_to_ref_plan_action (t', \<pi>) = (a, ta, da)"
    using eq i unfolding ref_plan_def by (simp add: tpi)
  show ?thesis
  proof (cases \<pi>)
    case (SimplePlanAction n as)
    have as_Nil: "as = []" using mem plan_acts_no_args unfolding list_all_iff SimplePlanAction by (cases as) auto
    have int_t: "is_integer t'" using mem plan_acts_durs_integer unfolding list_all_iff SimplePlanAction by auto
    have t_eq: "rat_of_int ta = t'" and a_eq: "a = the (resolve_temporal_action_schema n)"
      using ref_i int_t is_integer_of_int unfolding SimplePlanAction by auto
    have wfpa: "wf_plan_action (SimplePlanAction n as)" using mem wf_plan_actions unfolding SimplePlanAction by blast
    then obtain ps pre eff where
      res: "resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
      using simple_plan_action_schema_type1 by blast
    have "at_start_spec a = the (res_inst (SimplePlanAction n as))"
      unfolding a_eq res as_Nil res_inst.simps option.sel at_start_spec.simps by simp
    thus ?thesis
      unfolding tpi SimplePlanAction snap_of_plan_action_at_simplified_simps t_eq by simp
  next
    case (DurativePlanAction n as dur)
    have int_t: "is_integer t'" using mem plan_acts_durs_integer unfolding list_all_iff DurativePlanAction by auto
    have t_eq: "rat_of_int ta = t'" and a_eq: "a = the (resolve_temporal_action_schema n)"
      using ref_i int_t is_integer_of_int unfolding DurativePlanAction by auto
    show ?thesis
      unfolding tpi DurativePlanAction snap_of_plan_action_at_simplified_simps t_eq a_eq by simp
  qed
qed

text \<open>The @{const at_end_spec} block-membership analogue, for a \<^emph>\<open>durative\<close> reference-plan entry: its
  end snap occurs in the \<open>i\<close>-th block at time @{term "rat_of_int (ta + da)"}.\<close>
lemma at_end_block_of_ref_plan:
  assumes i: "i < length tp"
      and eq: "ref_plan ! i = (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), ta, da)"
  shows "at_end_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))
           \<in> set (snap_of_plan_action_at_simplified (rat_of_int (ta + da)) (tp ! i))"
proof -
  obtain t' \<pi> where tpi: "tp ! i = (t', \<pi>)" by (cases "tp ! i")
  have mem: "(t', \<pi>) \<in> set tp" using i tpi nth_mem by fastforce
  have ref_i: "timed_plan_action_to_ref_plan_action (t', \<pi>)
             = (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), ta, da)"
    using eq i unfolding ref_plan_def by (simp add: tpi)
  show ?thesis
  proof (cases \<pi>)
    case (SimplePlanAction n' as)
    have wfpa: "wf_plan_action (SimplePlanAction n' as)"
      using mem wf_plan_actions unfolding SimplePlanAction by blast
    then obtain ps' pre' eff' where
      res': "resolve_temporal_action_schema n' = Some (SimpleActionSchema (ActionHead n' ps') (SimpleActionBody pre' eff'))"
      using simple_plan_action_schema_type1 by blast
    have "False" using ref_i res' unfolding SimplePlanAction by simp
    thus ?thesis ..
  next
    case (DurativePlanAction n' as dur)
    have int_t: "is_integer t'" and int_d: "is_integer dur"
      using mem plan_acts_durs_integer unfolding list_all_iff DurativePlanAction by auto
    have wfpa: "wf_plan_action (DurativePlanAction n' as dur)"
      using mem wf_plan_actions unfolding DurativePlanAction by blast
    then obtain ps'' dcs'' pre'' eff'' where
      res'': "resolve_temporal_action_schema n' = Some (DurativeActionSchema (ActionHead n' ps'') (DurativeActionBody dcs'' pre'' eff''))"
      using durative_plan_action_schema_type1 by blast
    have the_eq: "the (resolve_temporal_action_schema n') = DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff)"
      and t_eq_fl: "ta = \<lfloor>t'\<rfloor>" and d_eq_fl: "da = \<lfloor>dur\<rfloor>"
      using ref_i unfolding DurativePlanAction by auto
    have res: "resolve_temporal_action_schema n' = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      using res'' the_eq by simp
    have n_eq: "n' = n"
      using resolve_schema_name[OF res] by simp
    have t_eq: "rat_of_int ta = t'" using t_eq_fl int_t is_integer_of_int by auto
    have d_eq: "rat_of_int da = dur" using d_eq_fl int_d is_integer_of_int by auto
    have "at_end_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))
        = at_end_spec (the (resolve_temporal_action_schema n'))"
      unfolding res by simp
    have te_add: "rat_of_int (ta + da) = t' + dur" using t_eq d_eq by (simp add: of_int_add)
    have end_eq: "at_end_spec (the (resolve_temporal_action_schema n'))
                = at_end_spec (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      unfolding res by simp
    show ?thesis
      unfolding tpi DurativePlanAction snap_of_plan_action_at_simplified_simps te_add
      by (simp add: end_eq)
  qed
qed

text \<open>The mutex consumer: two project snaps taken from \<^emph>\<open>distinct reference-plan entries\<close> (distinct
  positions) but landing at the same happening time are non-interfering.  This is the position-based
  replacement for the (now false) snap-injectivity argument: distinct plan entries occupy distinct
  blocks of @{term "acts_of_plan_at_simplified t tp"}, so @{thm list_pairwise_concat_distinct_blocks}
  applies to @{thm all_htps_acts_non_intrf_simplified} even when the two snaps coincide as values.\<close>
lemma acts_non_intrf_simplified_distinct_entries:
  assumes t_htp: "t \<in> set htps"
      and i: "i < length tp" and j: "j < length tp" and ij: "i \<noteq> j"
      and x: "x \<in> set (snap_of_plan_action_at_simplified t (tp ! i))"
      and y: "y \<in> set (snap_of_plan_action_at_simplified t (tp ! j))"
    shows "acts_non_intrf x y"
proof -
  have "list_pairwise acts_non_intrf (concat (map (snap_of_plan_action_at_simplified t) tp))"
    using all_htps_acts_non_intrf_simplified[OF t_htp] unfolding acts_of_plan_at_simplified_def .
  thus ?thesis
    using list_pairwise_concat_distinct_blocks[OF _ i j ij x y] by blast
qed

text \<open>Two elements of the \<^emph>\<open>same block\<close> of a @{const list_pairwise}-related @{const concat} are
  non-interfering provided they are either distinct or occur with multiplicity in that block (both
  hold for the @{const at_start_spec}/@{const at_end_spec} pair of a zero-duration durative entry,
  whose block is @{term "[at_start_spec a, at_end_spec a]"}).\<close>
lemma list_pairwise_concat_same_block:
  assumes lp: "list_pairwise R (concat (map f xs))"
      and i: "i < length xs"
      and x: "x \<in> set (f (xs ! i))" and y: "y \<in> set (f (xs ! i))"
      and dc: "x \<noteq> y \<or> 1 < count_list (f (xs ! i)) x"
    shows "R x y"
proof -
  have xin: "x \<in> set (concat (map f xs))" using x i by auto
  have yin: "y \<in> set (concat (map f xs))" using y i by auto
  have "x = y \<Longrightarrow> 1 < count_list (concat (map f xs)) x"
  proof -
    assume "x = y"
    hence blk: "1 < count_list (f (xs ! i)) x" using dc by simp
    have "count_list (f (xs ! i)) x \<le> (\<Sum>k<length xs. count_list (f (xs ! k)) x)"
      using i by (intro member_le_sum) auto
    also have "\<dots> = sum_list (map (\<lambda>ys. count_list ys x) (map f xs))"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = count_list (concat (map f xs)) x" by (simp add: count_list_concat)
    finally show "1 < count_list (concat (map f xs)) x" using blk by simp
  qed
  thus ?thesis using lp xin yin unfolding list_pairwise_as_nonrec by blast
qed

text \<open>Same-entry mutex consumer: the start and end snaps of a \<^emph>\<open>zero-duration\<close> durative reference-plan
  entry both occur in that entry's block at the common time, so they are non-interfering (no snap
  self-interference argument needed).\<close>
lemma acts_non_intrf_simplified_same_entry:
  assumes t_htp: "t \<in> set htps"
      and i: "i < length tp"
      and x: "x \<in> set (snap_of_plan_action_at_simplified t (tp ! i))"
      and y: "y \<in> set (snap_of_plan_action_at_simplified t (tp ! i))"
      and dc: "x \<noteq> y \<or> 1 < count_list (snap_of_plan_action_at_simplified t (tp ! i)) x"
    shows "acts_non_intrf x y"
proof -
  have lp: "list_pairwise acts_non_intrf (concat (map (snap_of_plan_action_at_simplified t) tp))"
    using all_htps_acts_non_intrf_simplified[OF t_htp] unfolding acts_of_plan_at_simplified_def .
  show ?thesis
    by (rule list_pairwise_concat_same_block[OF lp i x y dc])
qed


lemma valid_temporal_state_seq_some_state_precond:
  assumes "valid_temporal_state_seq M ts \<pi> M'"
      and "t \<in> set ts"
      and "a \<in> set (acts_of_temporal_plan_at t \<pi>)"
    shows "\<exists>N. valuation N \<Turnstile>\<^sub>m ground_action.precondition a"
  using assms
proof (induction M ts \<pi> M' rule: valid_temporal_state_seq.induct)
  case (1 M \<pi>s M')
  then show ?case by simp
next
  case (2 M t\<^sub>i \<pi>s M')
  hence "t = t\<^sub>i" by simp
  hence "valuation M \<Turnstile>\<^sub>m ground_action.precondition a"
    using valid_temporal_state_seq_head_precond[OF 2(1)] 2(3) by simp
  thus ?case by blast
next
  case (3 M t\<^sub>i t\<^sub>j ts \<pi>s M')
  show ?case
  proof (cases "t = t\<^sub>i")
    case True
    hence "valuation M \<Turnstile>\<^sub>m ground_action.precondition a"
      using valid_temporal_state_seq_head_precond[OF 3(2)] 3(4) True by simp
    thus ?thesis by blast
  next
    case False
    have rec: "valid_temporal_state_seq (apply_eff (acts_of_temporal_plan_at t\<^sub>i \<pi>s) M) (t\<^sub>j # ts) \<pi>s M'"
      using 3(2) by (simp add: Let_def)
    have "t \<in> set (t\<^sub>j # ts)" using 3(3) False by simp
    thus ?thesis using 3(1) rec 3(4) by blast
  qed
qed

lemma inst_formula_And:
  "inst_formula f d (And a b) = And (inst_formula f d a) (inst_formula f d b)"
  by simp

lemma inst_formula_BigAnd_conjunct:
  assumes "valuation M \<Turnstile>\<^sub>m inst_formula f d (BigAnd gs)"
      and "g \<in> set gs"
    shows "valuation M \<Turnstile>\<^sub>m inst_formula f d g"
  using assms
proof (induction gs)
  case Nil
  then show ?case by simp
next
  case (Cons g' gs')
  have "valuation M \<Turnstile>\<^sub>m inst_formula f d (And g' (BigAnd gs'))"
    using Cons.prems(1) by simp
  hence "valuation M \<Turnstile>\<^sub>m inst_formula f d g'"
    and rest: "valuation M \<Turnstile>\<^sub>m inst_formula f d (BigAnd gs')"
    unfolding inst_formula_And by simp_all
  thus ?case using Cons by (cases "g = g'") auto
qed

lemma duration_matches_of_inst_atom:
  assumes ent: "valuation M \<Turnstile>\<^sub>m inst_formula f d (duration_constraint_as_formula dc)"
      and nf: "\<not> is_Func_Const dc"
    shows "duration_matches d dc ps as"
proof -
  have nfd: "dc_no_func dc" using nf unfolding is_Func_Const_def by simp
  obtain dop e where de: "dc = DurationConstraint dop e" by (cases dc) auto
  have "dc_no_func (DurationConstraint dop e)" using nfd de by simp
  then obtain x where e: "e = ConstantExpr x" by (cases e) auto
  show ?thesis using ent unfolding de e
    by (cases dop)
       (auto simp: valuation_def map_two_options_eq_Some_iff of_rat_eq_iff of_rat_less_eq)
qed

lemma duration_matches_of_snap_precond:
  assumes ent: "valuation M \<Turnstile>\<^sub>m ground_action.precondition
                  (inst_snap_action_body_elements dcs pre eff f d ta)"
      and mem: "(ta, dc) \<in> set dcs"
      and nf: "\<not> is_Func_Const dc"
    shows "duration_matches d dc ps as"
proof -
  let ?gs = "filter_time_spec ta (pre @ map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) dcs)"
  have "valuation M \<Turnstile>\<^sub>m inst_formula f d (BigAnd ?gs)"
    using ent by (simp add: inst_snap_action_body_elements.simps Let_def)
  moreover
  have "(ta, duration_constraint_as_formula dc)
          \<in> set (map (\<lambda>(x, y). (x, duration_constraint_as_formula y)) dcs)"
    using mem by force
  hence "duration_constraint_as_formula dc \<in> set ?gs"
    unfolding filter_time_spec_def by force
  ultimately have "valuation M \<Turnstile>\<^sub>m inst_formula f d (duration_constraint_as_formula dc)"
    by (rule inst_formula_BigAnd_conjunct)
  thus ?thesis using nf by (rule duration_matches_of_inst_atom)
qed

lemma res_inst_snap_action_eq:
  assumes res: "resolve_temporal_action_schema n
                  = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
  shows "the (res_inst_snap_action (DurativePlanAction n as d) ta)
           = inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) as) d ta"
  using res by simp

lemma at_start_snap_mem:
  assumes "(t, DurativePlanAction n as d) \<in> set tp"
  shows "the (res_inst_snap_action (DurativePlanAction n as d) At_Start)
           \<in> set (acts_of_temporal_plan_at t tp)"
proof -
  have "the (res_inst_snap_action (DurativePlanAction n as d) At_Start)
          \<in> set (simplified_res_inst_temporal_plan_action_at t (t, DurativePlanAction n as d))"
    by simp
  thus ?thesis using assms unfolding acts_of_temporal_plan_at_def by force
qed

lemma at_end_snap_mem:
  assumes "(t, DurativePlanAction n as d) \<in> set tp"
  shows "the (res_inst_snap_action (DurativePlanAction n as d) At_End)
           \<in> set (acts_of_temporal_plan_at (t + d) tp)"
proof -
  have "the (res_inst_snap_action (DurativePlanAction n as d) At_End)
          \<in> set (simplified_res_inst_temporal_plan_action_at (t + d) (t, DurativePlanAction n as d))"
    by simp
  thus ?thesis using assms unfolding acts_of_temporal_plan_at_def by force
qed

lemma htp_start_of_durative:
  assumes "(t, DurativePlanAction n as d) \<in> set tp"
  shows "t \<in> set htps"
proof -
  have "is_htp tp t"
    using assms unfolding is_htp_def by blast
  thus ?thesis using htps_seq_htps unfolding htps_seq_def by blast
qed

lemma htp_end_of_durative:
  assumes "(t, DurativePlanAction n as d) \<in> set tp"
  shows "t + d \<in> set htps"
proof -
  have "(t, DurativePlanAction n as d) \<in> durative_acts tp"
    using assms unfolding durative_acts_def is_act_simple_def by force
  hence "is_htp tp (t + d)"
    unfolding is_htp_def by force
  thus ?thesis using htps_seq_htps unfolding htps_seq_def by blast
qed

lemma durations_match_of_valid:
  assumes a: "(t, DurativePlanAction n as d) \<in> set tp"
      and res: "resolve_temporal_action_schema n
                  = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
      and no_func: "list_all (\<lambda>x. \<not> is_Func_Const x) (map snd dcs)"
    shows "durations_match d (map snd dcs) ps as"
  unfolding durations_match_def list_all_iff
proof (intro ballI)
  fix dc assume "dc \<in> set (map snd dcs)"
  then obtain ta where mem: "(ta, dc) \<in> set dcs" by auto
  have nf: "\<not> is_Func_Const dc"
    using no_func \<open>dc \<in> set (map snd dcs)\<close> unfolding list_all_iff by blast
  \<comment> \<open>The resolved schema is well-formed, so every duration-constraint annotation is
      \<open>At_Start\<close> or \<open>At_End\<close>.\<close>
  have wfsch: "wf_temporal_action_schema (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
    using resolve_temporal_action_wf res by blast
  hence "(ta = At_Start \<or> ta = At_End)"
    using mem by (auto simp: Let_def)
  thus "duration_matches d dc ps as"
  proof
    assume ta: "ta = At_Start"
    have "t \<in> set htps" using htp_start_of_durative[OF a] .
    hence v: "valid_temporal_state_seq (abstr_state_list ! 0) (drop 0 htps) tp final_state"
      using valid_temporal_state_seq_abstr_state_list_f[of 0] by simp
    obtain M where
      M: "valuation M \<Turnstile>\<^sub>m ground_action.precondition
              (the (res_inst_snap_action (DurativePlanAction n as d) At_Start))"
      using valid_temporal_state_seq_some_state_precond[OF
              valid_temporal_state_seq_final_state \<open>t \<in> set htps\<close>
              at_start_snap_mem[OF a]] by blast
    have "valuation M \<Turnstile>\<^sub>m ground_action.precondition
            (inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) as) d At_Start)"
      using M unfolding res_inst_snap_action_eq[OF res] .
    thus ?thesis
      using duration_matches_of_snap_precond[OF _ mem[unfolded ta] nf] ta by simp
  next
    assume ta: "ta = At_End"
    have "t + d \<in> set htps" using htp_end_of_durative[OF a] .
    obtain M where
      M: "valuation M \<Turnstile>\<^sub>m ground_action.precondition
              (the (res_inst_snap_action (DurativePlanAction n as d) At_End))"
      using valid_temporal_state_seq_some_state_precond[OF
              valid_temporal_state_seq_final_state \<open>t + d \<in> set htps\<close>
              at_end_snap_mem[OF a]] by blast
    have "valuation M \<Turnstile>\<^sub>m ground_action.precondition
            (inst_snap_action_body_elements dcs pre eff (tsubst (ActionHead n ps) as) d At_End)"
      using M unfolding res_inst_snap_action_eq[OF res] .
    thus ?thesis
      using duration_matches_of_snap_precond[OF _ mem[unfolded ta] nf] ta by simp
  qed
qed

lemma temp_plan_valid:
  "imp_defs.rat_impl.valid_plan"
proof -
  have vss: "\<exists>M. imp_defs.rat_impl.valid_state_sequence M \<and> M 0 = set init_spec \<and> set goal_spec \<subseteq> M (length imp_defs.rat_impl.htpl)" 
  proof (intro exI conjI)
    show "imp_defs.rat_impl.valid_state_sequence ((!) plan_state_list)"
    proof (rule imp_defs.rat_impl.valid_state_sequenceI, goal_cases)
      case (1 i)
      then show ?case using apply_effects_subseq by simp
    next
      case (2 i)
      then show ?case using invs_sat by simp
    next
      case (3 i)
      then show ?case using pres_sat by simp
    qed
    show "plan_state_list ! 0 = set init_spec" 
      unfolding plan_state_list_def init_spec_def I_def 
      apply (subst nth_map)
      using length_abstr_state_list apply simp
      unfolding abstr_state_list_nth_0_is_init
      unfolding I_def
      unfolding set_remdups set_map set_filter
      using is_predAtom_literals
      by auto
    show "set goal_spec \<subseteq> plan_state_list ! length imp_defs.rat_impl.htpl"
    proof -
      have basic: "lwm_basic (fst final_state)"
      proof -
        have "wf_world_model final_state"
          using abstr_state_list_nth_length_is_final
          using abstr_state_list_nth_wf_world_model[of "length htps"] by simp
        hence "\<forall>f \<in> fst final_state. wf_fmla_atom objT f"
          by (cases final_state) simp
        thus ?thesis
          unfolding lwm_basic_def using wf_fmla_atom_imp_is_predAtom by blast
      qed
      have sub: "set (to_literals (goal P)) \<subseteq> fst final_state"
        using to_literals_subset_if_models[OF final_state_sat_goal] .
      have "to_predicate ` set (to_literals (goal P))
          \<subseteq> (\<Union>f \<in> fst final_state. set (map to_predicate (to_literals f)))"
        using lwm_basic_to_predicate_subset[OF basic sub] .
      thus ?thesis
        unfolding ref_htpl_eq_htps
        unfolding plan_state_list_def
        apply (subst nth_map)
        using length_abstr_state_list apply simp
        unfolding abstr_state_list_nth_length_is_final
        unfolding goal_spec_def
        unfolding set_remdups set_map image_image comp_def
        by simp
    qed
  qed                                              
  moreover
  have durs_ge_0: "imp_defs.rat_impl.durations_ge_0"
  proof -
    have "\<forall>a t d. (a, t, d) \<in> ran abstr_plan \<longrightarrow> 0 \<le> d"
    proof (intro strip, elim ran_abstr_plan_ref_planE in_set_ref_planE)
      fix t n as 
      show "(t, SimplePlanAction n as) \<in> set tp \<Longrightarrow> 0 \<le> rat_of_int 0" by simp
    next
      fix t n as d
      assume "(t, DurativePlanAction n as d) \<in> set tp"
      hence "wf_plan_action (DurativePlanAction n as d)" using wf_plan_actions by fast
      hence "0 \<le> d" by (rule durative_plan_action_durs)
      thus "0 \<le> rat_of_int \<lfloor>d\<rfloor>" by simp
    qed
    thus ?thesis unfolding imp_defs.rat_impl.durations_ge_0_def abstr_plan_def by simp
  qed
  moreover
  have durs_valid: "imp_defs.rat_impl.durations_valid"
  proof -
    have "\<forall>a t d. (a, t, d) \<in> ran abstr_plan \<longrightarrow> imp_defs.rat_impl.satisfies_duration_bounds a d"
    proof (intro strip, elim ran_abstr_plan_ref_planE in_set_ref_planE)
      fix t n as
      assume "(t, SimplePlanAction n as) \<in> set tp"
      hence "wf_plan_action (SimplePlanAction n as)" using wf_plan_actions by fast
      then obtain ps pre eff where
        res: "resolve_temporal_action_schema n = Some (SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff))"
        using simple_plan_action_schema_type1 by blast
      show "imp_defs.rat_impl.satisfies_duration_bounds (the (resolve_temporal_action_schema n)) (rat_of_int 0)"
        unfolding imp_defs.rat_impl.satisfies_duration_bounds_def Let_def res option.sel 
        unfolding comp_def lower_spec.simps upper_spec.simps
        unfolding option.map
        by simp
    next 
      fix t n as d
      assume a: "(t, DurativePlanAction n as d) \<in> set tp"
      hence wfp: "wf_plan_action (DurativePlanAction n as d)" using wf_plan_actions by fast
      then obtain ps pre eff dcs where
        res: "resolve_temporal_action_schema n = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
        using durative_plan_action_schema_type1 by blast
      \<comment> \<open>HANDOVER \<section>B: FPS \<open>wf_plan_action (DurativePlanAction n as d)\<close> yields only \<open>d \<ge> 0\<close>
         (see \<open>Continuous_Planning.Instantiations.wf_plan_action.simps(2)\<close>), NOT \<open>durations_match\<close>.  The
         match is derived from PLAN VALIDITY via @{thm durations_match_of_valid}: the At_Start / At_End
         snaps fold the (temporally filtered) duration atoms \<open>duration_constraint_as_formula\<close> into their
         preconditions, and plan validity makes the valuation model those atoms at value \<open>d\<close>, giving
         \<open>d = r\<close> / \<open>d \<le> r\<close> / \<open>d \<ge> r\<close> for every duration constraint.\<close>
      have no_func_dcs: "list_all (\<lambda>d. \<not> is_Func_Const d) (map snd dcs)" 
        using acts_no_func_dcs resolve_action_in_actions[OF res]
        unfolding actions_spec_def list_all_iff
        apply -
        apply (drule bspec, assumption)
        unfolding list_all_iff[symmetric] by (simp add: is_Func_Const_def)
      have dms: "durations_match d (map snd dcs) ps as"
        using durations_match_of_valid[OF a res no_func_dcs] .
      have sat: "imp_defs.rat_impl.satisfies_lower_bound (dc_list_lower (map snd dcs)) d"
           "imp_defs.rat_impl.satisfies_upper_bound (dc_list_upper (map snd dcs)) d"
        using durations_match_imp_sat_lb[OF dms no_func_dcs]
              durations_match_imp_sat_ub[OF dms no_func_dcs] by blast+

      have d_integer: "is_integer d" using plan_acts_durs_integer a unfolding list_all_iff by auto

      have dcs_integer: "list_all duration_constraint_integer (map snd dcs)"
        using acts_dcs_integers resolve_action_in_actions[OF res]
        unfolding actions_spec_def list_all_iff
        apply -
        apply (drule bspec, assumption)
        by (simp add: list_all_iff)

      have lbs_integer: "pred_option (pred_lower_bound is_integer) (dc_list_lower (map snd dcs))" 
      proof (rule dc_list_lower_propI)
        show "list_all (pred_option (pred_lower_bound is_integer)) (map dc_to_lb (map snd dcs))"
          using dcs_integer no_func_dcs unfolding list_all_iff
          using dc_integer_imp_lb_integer by auto
        show "pred_option (pred_lower_bound is_integer) None" by simp
      qed

      have ubs_integer: "pred_option (pred_upper_bound is_integer) (dc_list_upper (map snd dcs))" 
      proof (rule dc_list_upper_propI)
        show "list_all (pred_option (pred_upper_bound is_integer)) (map dc_to_ub (map snd dcs))"
          using dcs_integer no_func_dcs unfolding list_all_iff
          using dc_integer_imp_ub_integer by auto
        show "pred_option (pred_upper_bound is_integer) None" by simp
      qed

      show "imp_defs.rat_impl.satisfies_duration_bounds (the (resolve_temporal_action_schema n)) (rat_of_int \<lfloor>d\<rfloor>)" 
        unfolding imp_defs.rat_impl.satisfies_duration_bounds_def Let_def res option.sel 
        unfolding comp_def lower_spec.simps upper_spec.simps
        unfolding option.map_comp comp_def lower_bound.map_comp upper_bound.map_comp
        using sat integers_sat_bounds lbs_integer ubs_integer d_integer by simp
    qed
    thus ?thesis unfolding imp_defs.rat_impl.durations_valid_def abstr_plan_def by simp
  qed
  moreover
  have mutex_valid: "imp_defs.rat_impl.mutex_valid_plan"
  proof -
    show ?thesis 
      unfolding imp_defs.rat_impl.mutex_valid_plan_eq
      imp_defs.rat_impl.mutex_valid_plan_alt_def
      unfolding abstr_plan_def[symmetric]
    proof (intro conjI)
      show "\<forall>i j a ta da b tb db. i \<in> dom abstr_plan \<and> j \<in> dom abstr_plan \<and> i \<noteq> j 
          \<and> abstr_plan i = Some (a, ta, da) \<and> abstr_plan j = Some (b, tb, db) 
        \<longrightarrow> imp_defs.rat_impl.mutex_sched a ta da b tb db" 
      proof -
        have 1: "\<forall>i j a ta da b tb db. i < length ref_plan \<longrightarrow> j < length ref_plan \<longrightarrow> i \<noteq> j \<longrightarrow> ref_plan ! i = (a, ta, da) \<longrightarrow> ref_plan ! j = (b, tb, db) \<longrightarrow> imp_defs.rat_impl.mutex_sched a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)"
        proof (intro strip)
          fix i j a ta da b tb db
          assume i:   "i < length ref_plan"
            and j:    "j < length ref_plan" 
            and ij:   "i \<noteq> j" 
            and atd:  "ref_plan ! i = (a, ta, da)"
            and btd:  "ref_plan ! j = (b, tb, db)"


          have len_eq: "length ref_plan = length tp" unfolding ref_plan_def by simp
          have itp: "i < length tp" and jtp: "j < length tp" using i j len_eq by simp_all

          have in_ref_plan: "(a, ta, da) \<in> set ref_plan" 
            "(b, tb, db) \<in> set ref_plan"
            using nth_mem[OF i] nth_mem[OF j] unfolding atd btd by simp+

          
          have durs_ge0: "0 \<le> da"
                         "0 \<le> db" 
            using in_ref_plan ref_plan_durs by blast+

          have nso_cond: "ref_no_self_overlap (a, ta, da) (b, tb, db)" 
            using ref_plan_no_self_overlap unfolding ref_plan_no_self_overlap_def
            unfolding list_pairwise_nth_refl[OF ref_no_self_overlap_refl]
            using i j ij atd[symmetric] btd[symmetric]
            by auto

          \<comment> \<open>Position-keyed block memberships: the snaps of the two distinct reference-plan entries \<open>i\<close>, \<open>j\<close>
             occur in the corresponding (distinct) concat blocks of @{const acts_of_plan_at_simplified}.\<close>
          have a_start_blk: "at_start_spec a \<in> set (snap_of_plan_action_at_simplified (rat_of_int ta) (tp ! i))"
            using at_start_block_of_ref_plan[OF itp atd] .
          have b_start_blk: "at_start_spec b \<in> set (snap_of_plan_action_at_simplified (rat_of_int tb) (tp ! j))"
            using at_start_block_of_ref_plan[OF jtp btd] .

          have a_end_blk: "at_end_spec a \<in> set (snap_of_plan_action_at_simplified (rat_of_int (ta + da)) (tp ! i))"
            if "at_end_spec a \<noteq> ground_non_action"
          proof (cases a)
            case (SimpleActionSchema h b')
            have "at_end_spec a = ground_non_action" unfolding SimpleActionSchema by simp
            thus ?thesis using that by simp
          next
            case (DurativeActionSchema h b')
            obtain nb psb where h: "h = ActionHead nb psb" by (cases h)
            obtain dcsb preb effb where b': "b' = DurativeActionBody dcsb preb effb" by (cases b')
            show ?thesis using at_end_block_of_ref_plan[OF itp] atd
              unfolding DurativeActionSchema h b' by simp
          qed
          have b_end_blk: "at_end_spec b \<in> set (snap_of_plan_action_at_simplified (rat_of_int (tb + db)) (tp ! j))"
            if "at_end_spec b \<noteq> ground_non_action"
          proof (cases b)
            case (SimpleActionSchema h b')
            have "at_end_spec b = ground_non_action" unfolding SimpleActionSchema by simp
            thus ?thesis using that by simp
          next
            case (DurativeActionSchema h b')
            obtain nb psb where h: "h = ActionHead nb psb" by (cases h)
            obtain dcsb preb effb where b': "b' = DurativeActionBody dcsb preb effb" by (cases b')
            show ?thesis using at_end_block_of_ref_plan[OF jtp] btd
              unfolding DurativeActionSchema h b' by simp
          qed

          consider "at_end_spec a \<noteq> ground_non_action" | "at_end_spec a = ground_non_action" by blast
          note a_end = this
          consider "at_end_spec b \<noteq> ground_non_action" | "at_end_spec b = ground_non_action" by blast
          note b_end = this

          have a_in_acts: "a \<in> set actions_spec" 
           and b_in_acts: "b \<in> set actions_spec" 
            using in_ref_plan
            using ref_plan_acts_in_actions by auto
          note ab_in_acts = this

          have acts_pres_pos: 
                "ground_act_pres_pos (at_start_spec a)"
                "ground_act_pres_pos (at_start_spec b)" 
                "ground_act_pres_pos (at_end_spec a)"
                "ground_act_pres_pos (at_end_spec b)"
            using ab_in_acts start_snap_pre_pos_conj end_snap_pre_pos_conj by blast+
          have acts_no_args: 
                "ground_act_no_args (at_start_spec a)"
                "ground_act_no_args (at_start_spec b)"
                "ground_act_no_args (at_end_spec a)"
                "ground_act_no_args (at_end_spec b)"
            using ab_in_acts start_snap_no_args end_snap_no_args by blast+
          have acts_wf:
                "wf_ground_action (at_start_spec a)"
                "wf_ground_action (at_start_spec b)"
                "wf_ground_action (at_end_spec a)"
                "wf_ground_action (at_end_spec b)"
            using ab_in_acts start_snaps_wf end_snaps_wf by blast+

          have start_times_in_htps: 
            "rat_of_int ta \<in> set htps" 
            "rat_of_int tb \<in> set htps" 
            using ref_plan_start_in_htps in_ref_plan by force+

          have "rat_of_int (ta + da) \<in> set htps \<or> at_end_spec a = ground_non_action" 
            apply (cases a rule: ast_temporal_action_schema_cases_unfold)
            using ref_plan_end_in_htps_if_durative in_ref_plan
            by auto
          then
          consider "rat_of_int (ta + da) \<in> set htps" 
            | "at_end_spec a = ground_non_action"
            by blast+
          note a_end_time = this

          show "imp_defs.rat_impl.mutex_sched a (rat_of_int ta) (rat_of_int da) b (rat_of_int tb) (rat_of_int db)" 
          proof (intro imp_defs.rat_impl.mutex_sched_zero_sepI acts_non_intrf_imp_mutex_snap_action acts_pres_pos acts_no_args acts_wf)
            show "rat_of_int 0 = 0" by simp
          next 
            assume t: "rat_of_int ta = rat_of_int tb"
            show "acts_non_intrf (at_start_spec a) (at_start_spec b)" 
              using acts_non_intrf_simplified_distinct_entries[OF start_times_in_htps(1) itp jtp ij
                  a_start_blk b_start_blk[unfolded t[symmetric]]] .
          next
            assume t: "rat_of_int ta = rat_of_int tb + rat_of_int db" 
            show "acts_non_intrf (at_start_spec a) (at_end_spec b)"
            proof (cases rule: b_end)
              case 1
              have tb_eq: "rat_of_int ta = rat_of_int (tb + db)" using t by simp
              show ?thesis
                using acts_non_intrf_simplified_distinct_entries[OF start_times_in_htps(1) itp jtp ij
                    a_start_blk b_end_blk[OF 1, unfolded tb_eq[symmetric]]] .
            next
              case 2
              thus ?thesis using ground_non_action_non_intrf by auto
            qed
          next 
            assume t: "rat_of_int ta + rat_of_int da = rat_of_int tb" 
            show "acts_non_intrf (at_end_spec a) (at_start_spec b)"
            proof (cases rule: a_end)
              case 1
              have ta_eq: "rat_of_int (ta + da) = rat_of_int tb" using t by simp
              show ?thesis
                using acts_non_intrf_simplified_distinct_entries[OF start_times_in_htps(2) itp jtp ij
                    a_end_blk[OF 1, unfolded ta_eq] b_start_blk] .
            next
              case 2
              thus ?thesis using ground_non_action_non_intrf by auto
            qed
          next 
            assume t: "rat_of_int ta + rat_of_int da = rat_of_int tb + rat_of_int db" 
            show "acts_non_intrf (at_end_spec a) (at_end_spec b)"
            proof (cases rule: a_end)
              case a1: 1
              show ?thesis
              proof (cases rule: b_end)
                case b1: 1
                have ab_eq: "rat_of_int (ta + da) = rat_of_int (tb + db)" using t by simp
                show ?thesis
                proof (cases rule: a_end_time)
                  case at1: 1
                  show ?thesis
                    using acts_non_intrf_simplified_distinct_entries[OF at1 itp jtp ij
                        a_end_blk[OF a1] b_end_blk[OF b1, unfolded ab_eq[symmetric]]] .
                next
                  case at2: 2
                  thus ?thesis using a1 by blast
                qed
              next
                case b2: 2
                thus ?thesis using ground_non_action_non_intrf by auto
              qed
            next
              case a2: 2
              thus ?thesis using ground_non_action_non_intrf by auto
            qed
          qed
        qed
        show ?thesis
        apply (intro strip, elim conjE)
        subgoal
          apply (rule abstr_plan_binary_prop')
          using imp_defs.rat_impl.mutex_sched_refl 
          using 1 by blast+
        done
      qed
      show "\<forall>(a, t, d)\<in>ran abstr_plan. d = 0 \<or> d < rat_of_int 0 
      \<longrightarrow> \<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a) (at_end_spec a)"
      proof -
        { fix a' t' d'
          assume "(a', t', d') \<in> ran abstr_plan"
          hence "(d' = 0 \<or> d' < rat_of_int 0) \<longrightarrow> \<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a') (at_end_spec a')"
          proof (elim ran_abstr_plan_ref_planE; intro strip)
            fix a t d
            assume a: "(a, t, d) \<in> set ref_plan"
              and d: "rat_of_int d = 0 \<or> rat_of_int d < rat_of_int 0" 
            have d[simp]: "d = 0" using a d ref_plan_durs by fastforce
  
            have a_in_acts: "a \<in> set actions_spec" using a ref_plan_acts_in_actions by simp
            
            show "\<not> imp_defs.rat_impl.set_impl.mutex_snap_action (at_start_spec a) (at_end_spec a)"
            proof (cases a rule: ast_temporal_action_schema_cases_unfold)
              case (SimpleActionSchema n ps pre eff)
              hence "at_end_spec a = ground_non_action" by simp
              thus ?thesis using ground_non_action_not_mutex(2) by simp
            next
              case x: (DurativeActionSchema n ps dcs pre eff)
              \<comment> \<open>The zero-duration durative entry contributes BOTH its start and end snap to its own block
                 at the common time; @{thm acts_non_intrf_simplified_same_entry} then applies without any
                 snap-inequality (if the two snaps coincide, they occur twice in the block).\<close>
              obtain i where i: "i < length tp" and refi: "ref_plan ! i = (a, t, d)"
                using a unfolding ref_plan_def in_set_conv_nth by auto
              have refi': "ref_plan ! i = (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, 0)"
                using refi d x by simp
              have blk: "snap_of_plan_action_at_simplified (rat_of_int t) (tp ! i)
                       = [at_start_spec a, at_end_spec a]"
              proof -
                obtain t\<^sub>\<pi> \<pi> where tpi: "tp ! i = (t\<^sub>\<pi>, \<pi>)" by (cases "tp ! i")
                have mem: "(t\<^sub>\<pi>, \<pi>) \<in> set tp" using i tpi nth_mem by fastforce
                have ref_i: "timed_plan_action_to_ref_plan_action (t\<^sub>\<pi>, \<pi>)
                           = (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff), t, 0)"
                  using refi' i unfolding ref_plan_def by (simp add: tpi)
                obtain nb asb where \<pi>_eq: "\<pi> = DurativePlanAction nb asb 0"
                proof (cases \<pi>)
                  case (SimplePlanAction nb asb)
                  have wfpa: "wf_plan_action (SimplePlanAction nb asb)" using mem wf_plan_actions unfolding SimplePlanAction by blast
                  then obtain ps'' pre'' eff'' where
                    "resolve_temporal_action_schema nb = Some (SimpleActionSchema (ActionHead nb ps'') (SimpleActionBody pre'' eff''))"
                    using simple_plan_action_schema_type1 by blast
                  hence "False" using ref_i unfolding SimplePlanAction by simp
                  thus ?thesis ..
                next
                  case (DurativePlanAction nb asb durb)
                  have int_d: "is_integer durb" using mem plan_acts_durs_integer unfolding list_all_iff DurativePlanAction by auto
                  have "0 = \<lfloor>durb\<rfloor>" using ref_i unfolding DurativePlanAction by simp
                  hence "durb = 0" using int_d is_integer_of_int by force
                  thus ?thesis using that DurativePlanAction by simp
                qed
                have int_t: "is_integer t\<^sub>\<pi>" using mem plan_acts_durs_integer unfolding list_all_iff \<pi>_eq by auto
                have wfpa: "wf_plan_action (DurativePlanAction nb asb 0)" using mem wf_plan_actions unfolding \<pi>_eq by blast
                then obtain ps'' dcs'' pre'' eff'' where
                  res'': "resolve_temporal_action_schema nb = Some (DurativeActionSchema (ActionHead nb ps'') (DurativeActionBody dcs'' pre'' eff''))"
                  using durative_plan_action_schema_type1 by blast
                have res: "resolve_temporal_action_schema nb = Some (DurativeActionSchema (ActionHead n ps) (DurativeActionBody dcs pre eff))"
                  using ref_i res'' unfolding \<pi>_eq by simp
                have t_eq: "rat_of_int t = t\<^sub>\<pi>" using ref_i int_t is_integer_of_int unfolding \<pi>_eq by auto
                have a_st: "at_start_spec a = at_start_spec (the (resolve_temporal_action_schema nb))" using res x refi' by simp
                have a_en: "at_end_spec a = at_end_spec (the (resolve_temporal_action_schema nb))" using res x refi' by simp
                show ?thesis
                  unfolding tpi \<pi>_eq snap_of_plan_action_at_simplified_simps t_eq[symmetric] a_st a_en by simp
              qed
              have x_in: "at_start_spec a \<in> set (snap_of_plan_action_at_simplified (rat_of_int t) (tp ! i))"
                and y_in: "at_end_spec a \<in> set (snap_of_plan_action_at_simplified (rat_of_int t) (tp ! i))"
                unfolding blk by simp_all
              have dc: "at_start_spec a \<noteq> at_end_spec a
                      \<or> 1 < count_list (snap_of_plan_action_at_simplified (rat_of_int t) (tp ! i)) (at_start_spec a)"
                unfolding blk by (cases "at_start_spec a = at_end_spec a") simp_all
              have non_int: "acts_non_intrf (at_start_spec a) (at_end_spec a)"
                using acts_non_intrf_simplified_same_entry[OF ref_plan_start_in_htps[OF a] i x_in y_in dc] .
              show ?thesis
                by (rule acts_non_intrf_imp_mutex_snap_action[OF non_int
                      start_snap_pre_pos_conj[OF a_in_acts] end_snap_pre_pos_conj[OF a_in_acts]
                      start_snaps_wf[OF a_in_acts] end_snaps_wf[OF a_in_acts]
                      start_snap_no_args[OF a_in_acts] end_snap_no_args[OF a_in_acts]])
            qed
          qed
        }
        thus ?thesis by auto
      qed
    qed
  qed
  moreover
  have finite: "imp_defs.rat_impl.finite_plan" 
    unfolding imp_defs.rat_impl.finite_plan_def
    unfolding dom_map_option comp_def
    using dom_plan_imp by simp
  ultimately
  show "imp_defs.rat_impl.valid_plan" 
    unfolding imp_defs.rat_impl.valid_plan_def
    by simp
qed

end

end
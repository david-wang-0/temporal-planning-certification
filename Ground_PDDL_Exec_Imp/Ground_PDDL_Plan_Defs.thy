theory Ground_PDDL_Plan_Defs
  imports Ground_PDDL_Problem_Defs
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics_Alt"
begin

fun list_pairwise::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"list_pairwise P [] = True" |
"list_pairwise P (x#xs) = (list_all (P x) xs \<and> list_pairwise P xs)"

(* Todo?: list_pairwise and Set.pairwise conditional equivalence.
    Not needed, because the abstract definition of a plan accesses every
    member of the plan separately by index. *)


definition "is_integral q \<equiv> \<exists>a b. q = Fract a b \<and> 0 < b \<and> coprime a b \<and> b = 1"

definition "is_integral_code (q::rat) \<equiv> snd (quotient_of q) = 1"

lemma is_integral_code[code]: "is_integral q = is_integral_code q"
  apply (rule iffI)
  unfolding is_integral_def is_integral_code_def 
  subgoal apply (elim exE conjE)
    subgoal for a b
      apply (erule ssubst)
      apply (subst quotient_of_Fract)
      by simp
    done
  subgoal 
    apply (rule Rat_cases[of q])
    subgoal for a b
      apply simp
      apply (cases "Rat.normalize (a, b)")
      subgoal for a' b'
    apply (subst (asm) quotient_of_Fract)
    apply (rule exI)
        apply (subst Rat.normalize_eq[symmetric])
         apply assumption
        by simp
      done
    done
  done


lemma is_integral_add:
  assumes "is_integral q"
      and "is_integral r"
    shows "is_integral (q + r)"
proof -
  obtain a b where
    "q = Fract a 1"
    "r = Fract b 1" using assms is_integral_def by auto
  hence "q + r = Fract (a + b) 1" by auto
  thus ?thesis using is_integral_def by auto
qed

lemma is_integral_of_int:
  assumes "is_integral q"
  shows "rat_of_int (floor q) = q"
proof -
  obtain a b where
    q: "q = Fract a b"
    "b = 1" using assms is_integral_def by auto
  have "rat_of_int a = q" using q Fract_of_int_eq by auto
  moreover
  have "floor q = a" using q by simp
  moreover
  have "floor (rat_of_int a) = a" by simp
  ultimately
  show ?thesis by simp
qed


lemma is_integral_floor_less: 
  assumes "x < y"
      and "is_integral x"
      and "is_integral y"
    shows "floor x < floor y"
  using assms
  apply -
  apply (subst (asm) is_integral_of_int[symmetric, of x], simp)
  apply (subst (asm) is_integral_of_int[symmetric, of y], simp)
  apply (subst (asm) of_int_less_iff)
  by (assumption)

(* lemma is_integral_floor_le: 
  assumes "x \<le> y"
      and "is_integral x"
      and "is_integral y"
    shows "floor x \<le> floor y"
  using assms is_integral_floor_less by linarith *)

thm Archimedean_Field.floor_mono

lemma is_integral_floor_ne:
  assumes "x \<noteq> y"
      and "is_integral x"
      and "is_integral y"
    shows "floor x \<noteq> floor y"
  using assms is_integral_floor_less 
  by (cases "x \<le> y") force+

locale ground_plan_defs = 
  ground_ast_problem_defs P
  for P::ast_problem 
begin



fun plan_act_no_args where
"plan_act_no_args (Simple_Plan_Action n []) = True" |
"plan_act_no_args (Durative_Plan_Action n [] d) = True" |
"plan_act_no_args _ = False"

definition nth_opt where
"nth_opt xs n \<equiv> if n < length xs then Some (xs ! n) else None"

fun timed_plan_action_durs_integral::"rat \<times> plan_action \<Rightarrow> bool" where
"timed_plan_action_durs_integral (t, Simple_Plan_Action n as) = (is_integral t)" |
"timed_plan_action_durs_integral (t, Durative_Plan_Action n as d) = (is_integral t \<and> is_integral d)"

fun timed_plan_action_to_ref_plan_action::"rat \<times> plan_action \<Rightarrow> ast_action_schema \<times> int \<times> int" where
"timed_plan_action_to_ref_plan_action (t, Simple_Plan_Action n as) = (the (resolve_action_schema n), floor t, 0)" |
"timed_plan_action_to_ref_plan_action (t, Durative_Plan_Action n as d) = (the (resolve_action_schema n), floor t, floor d)"

fun PDDL_no_self_overlap::"(rat \<times> plan_action) \<Rightarrow> (rat \<times> plan_action) \<Rightarrow> bool" where
"PDDL_no_self_overlap (t, Simple_Plan_Action x _) (u, Simple_Plan_Action y _) = (x = y \<longrightarrow> t \<noteq> u)" |
"PDDL_no_self_overlap (_, Simple_Plan_Action _ _) (_, Durative_Plan_Action _ _ _) = True" |
"PDDL_no_self_overlap (_, Durative_Plan_Action _ _ _) (_, Simple_Plan_Action _ _) = True" |
"PDDL_no_self_overlap (t, Durative_Plan_Action x _ d) (u, Durative_Plan_Action y _ e) =
  (x = y \<longrightarrow> \<not>((t \<le> u \<and> u \<le> t + d) \<or> (u \<le> t \<and> t \<le> u + e)))"

definition "PDDL_plan_no_self_overlap tp \<equiv> list_pairwise PDDL_no_self_overlap tp"

fun ref_no_self_overlap::"(ast_action_schema \<times> int \<times> int) \<Rightarrow> (ast_action_schema \<times> int \<times> int) \<Rightarrow> bool" where
"ref_no_self_overlap (a, t, d) (b, u, e) = ((a = b) \<longrightarrow> \<not>((t \<le> u \<and> u \<le> t + d) \<or> (u \<le> t \<and> t \<le> u + e)))"

definition ref_plan where
"ref_plan tp \<equiv> (map timed_plan_action_to_ref_plan_action tp)"

definition "ref_plan_no_self_overlap tp \<equiv> list_pairwise ref_no_self_overlap (ref_plan tp)"

end

locale valid_ground_plan =
  ground_ast_problem P +
  ground_plan_defs P tp 
  for P::ast_problem 
  and tp::"(rat \<times> plan_action) list" +
assumes valid_plan: "valid_plan tp"
  and "PDDL_plan_no_self_overlap"
  and plan_acts_no_args: "list_all (snd #> plan_act_no_args) tp"
  and plan_acts_durs_integral: "list_all (timed_plan_action_durs_integral) tp"
begin
(* Needs an assumption that durations are integral *)

lemma resolve_action_schema_inj_on_dom:
  assumes "resolve_action_schema x = resolve_action_schema y"
      and "resolve_action_schema x = Some a"
      and "resolve_action_schema y = Some b"
  shows "x = y"
proof (cases a; cases b)
  fix l as pre eff n bs ore fff
  assume a: "a = Simple_Action_Schema l as pre eff" 
     and b: "b = Simple_Action_Schema n bs ore fff"
  have dist: "distinct (map ast_action_schema.name (actions D))" using wf_domain wf_domain_def by blast
  have "x = l" using index_by_eq_Some_eq[OF dist] a assms(2) unfolding resolve_action_schema_def by simp
  moreover
  have "y = n" using index_by_eq_Some_eq[OF dist] b assms(3) unfolding resolve_action_schema_def by simp
  ultimately 
  show "x = y" using assms a b by simp
next 
  fix l as pre eff n bs ore fff d
  assume a: "a = Simple_Action_Schema l as pre eff" 
     and b: "b = Durative_Action_Schema n bs d ore fff"
  show "x = y" using assms a b by simp
next 
  fix l as pre eff n bs ore fff d
  assume a: "a = Durative_Action_Schema l as d pre eff" 
     and b: "b = Simple_Action_Schema n bs ore fff"
  show "x = y" using assms a b by simp
next 
  fix l as pre eff n bs ore fff d e
  assume a: "a = Durative_Action_Schema l as d pre eff" 
     and b: "b = Durative_Action_Schema n bs e ore fff"
  have dist: "distinct (map ast_action_schema.name (actions D))" using wf_domain wf_domain_def by blast
  have "x = l" using index_by_eq_Some_eq[OF dist] a assms(2) unfolding resolve_action_schema_def by simp
  moreover
  have "y = n" using index_by_eq_Some_eq[OF dist] b assms(3) unfolding resolve_action_schema_def by simp
  ultimately 
  show "x = y" using assms a b by simp
qed

lemma PDDL_no_self_overlap_imp_ref_no_self_overlap:
  assumes "PDDL_no_self_overlap a b"
      and "wf_plan_action (snd a)"
      and "wf_plan_action (snd b)"
      and "plan_act_no_args (snd a)"
      and "plan_act_no_args (snd b)"
      and "timed_plan_action_durs_integral a"
      and "timed_plan_action_durs_integral b"
  shows "ref_no_self_overlap (timed_plan_action_to_ref_plan_action a) (timed_plan_action_to_ref_plan_action b)"
  using assms
proof (induction rule: PDDL_no_self_overlap.induct)
  case (1 t x as u y bs)

  have t_integral: "is_integral t" 
   and u_integral: "is_integral u" using 1 by auto

  have a: "x = y \<longrightarrow> t \<noteq> u" using 1 unfolding PDDL_no_self_overlap.simps by auto

  have wf_acts: 
    "wf_plan_action (Simple_Plan_Action x as)"
    "wf_plan_action (Simple_Plan_Action y bs)" using 1 by auto

  hence res_some: 
    "\<exists>a. resolve_action_schema x = Some a"
    "\<exists>b. resolve_action_schema y = Some b" using simple_plan_action_schema_type1 by blast+

  have res_iff: "the (resolve_action_schema x) = the (resolve_action_schema y) \<longleftrightarrow> x = y"
    using res_some resolve_action_schema_inj_on_dom by auto 

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    apply (subst res_iff)
    using a is_integral_floor_ne t_integral u_integral 
    by auto
next
  case (2 t x as u y d bs)

  have t_integral: "is_integral t" 
   and u_integral: "is_integral u" using 2 by auto


  have wf_acts: 
    "wf_plan_action (Simple_Plan_Action x as)"
    "wf_plan_action (Durative_Plan_Action y d bs)" using 2 by auto

  hence res_some: 
    "\<exists>a. resolve_action_schema x = Some a"
    "\<exists>b. resolve_action_schema y = Some b" 
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 by blast+

  have res_neq: "the (resolve_action_schema x) \<noteq> the (resolve_action_schema y)"
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 wf_acts by fastforce

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    using res_neq by auto
next
  case (3 t x d as u y bs)

  have t_integral: "is_integral t" 
   and u_integral: "is_integral u" using 3 by auto

  have wf_acts: 
    "wf_plan_action (Durative_Plan_Action x d as)"
    "wf_plan_action (Simple_Plan_Action y bs)" using 3 by auto

  hence res_some: 
    "\<exists>a. resolve_action_schema x = Some a"
    "\<exists>b. resolve_action_schema y = Some b" 
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 by blast+

  have res_neq: "the (resolve_action_schema x) \<noteq> the (resolve_action_schema y)"
    using simple_plan_action_schema_type1 durative_plan_action_schema_type1 wf_acts by fastforce

  show ?case 
    apply (subst timed_plan_action_to_ref_plan_action.simps)+
    apply (subst ref_no_self_overlap.simps)+
    using res_neq by auto
next
  case (4 t x as d u y bs e)

  have t_integral: "is_integral t" 
   and u_integral: "is_integral u" 
   and d_integral: "is_integral d"
   and e_integral: "is_integral e" using 4 by auto

  note vs_integral = t_integral u_integral d_integral e_integral
  
  have wf_acts: 
    "wf_plan_action (Durative_Plan_Action x as d)"
    "wf_plan_action (Durative_Plan_Action y bs e)" using 4 by auto

  have res_iff: "the (resolve_action_schema x) = the (resolve_action_schema y) \<longleftrightarrow> x = y"
    using durative_plan_action_schema_type1[OF wf_acts(1)] durative_plan_action_schema_type1[OF wf_acts(2)]
    by auto

  {
    assume "x = y"
    hence " \<not> (t \<le> u \<and> u \<le> t + d \<or> u \<le> t \<and> t \<le> u + e)" using 4 by simp
    hence "(u < t \<or> t + d < u) \<and> (t < u \<or> u + e < t)" by linarith
    moreover
    { assume "u < t"
      hence "floor u < floor t" using vs_integral is_integral_floor_less by auto
    }
    moreover
    { assume "t + d < u"
      hence "floor (t + d) < floor u" 
        by (intro vs_integral is_integral_floor_less is_integral_add)
      hence "floor t + floor d < floor u" by linarith
    }
    moreover
    { assume "t < u"
      hence "floor t < floor u" using vs_integral is_integral_floor_less by auto
    }
    moreover
    { assume "u + e < t"
      hence "floor (u + e) < floor t" 
        by (intro vs_integral is_integral_floor_less is_integral_add)
      hence "floor u + floor e < floor y" by linarith
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


lemma no_PDDL_plan_self_overlap_imp_no_ref_plan_self_overlap:
  assumes PDDL_plan_no_self_overlap
  shows ref_plan_no_self_overlap
proof -
  have "wf_plan tp" using valid_plan unfolding valid_plan_def valid_plan_from_def by blast
  hence "list_all (snd #> wf_plan_action) tp" unfolding wf_plan_def list_all_iff by auto
  thus ?thesis
    using assms plan_acts_no_args plan_acts_durs_integral
    unfolding PDDL_plan_no_self_overlap_def ref_plan_no_self_overlap_def ref_plan_def
    proof (induction tp)
      case Nil
      then show ?case by simp
    next
      case (Cons pa pas)
      have 1: "list_pairwise ref_no_self_overlap (map timed_plan_action_to_ref_plan_action pas)" using Cons by simp

      have nso: "list_all (PDDL_no_self_overlap pa) pas" using Cons by simp
      have wf: "list_all (\<lambda>x. wf_plan_action (snd x)) (pa # pas)" using Cons by blast
      have no_args: "list_all (\<lambda>x. plan_act_no_args (snd x)) (pa # pas)" using Cons by blast
      have are_integral: "list_all timed_plan_action_durs_integral (pa # pas)" using Cons by blast

      have 2: "list_all (ref_no_self_overlap (timed_plan_action_to_ref_plan_action pa)) (map timed_plan_action_to_ref_plan_action pas)"
        using nso wf no_args are_integral PDDL_no_self_overlap_imp_ref_no_self_overlap unfolding list_all_iff by simp

      show ?case using 1 2 by simp
    qed
qed

definition plan_imp where
"plan_imp \<equiv> 
  map timed_plan_action_to_ref_plan_action tp
  |> nth_opt"


sublocale red_corr: tp_nta_reduction_correctness' init_spec goal_spec 
  at_start_spec at_end_spec over_all_spec
  lower_spec upper_spec pre_spec adds_spec dels_spec
  0 
  props_spec actions_spec plan_imp  
  act_to_name_spec prop_to_name_spec
  apply unfold_locales
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry


end

end
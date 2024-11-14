theory PDDL_temporal_plan_instantiation
  imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
    Temporal_Plans
    Containers.Containers
begin

text \<open>This is the type of propositions, we will use to instantiate the locale\<close>
type_synonym pr = "object atom formula"

type_synonym suff_cond = "pr list"

text \<open>Note, that this is not the type we will use as @{typ \<open>'snap_action\<close>}}, because we would
have to implement \<open>at_start\<close> as @{term \<open>fst\<close>}, which would make it violate injectivity.\<close>
type_synonym snap = "suff_cond \<times> object ast_effect"

type_synonym dc = "duration_op \<times> rat"

text \<open>This is the actual type of action\<close>
type_synonym action = "(string \<times> snap \<times> snap \<times> snap \<times> dc option)"

text \<open>This is the actual @{typ \<open>'snap_action\<close>}} we will use to instantiate the locale.\<close>
type_synonym snap_action = "temporal_annotation \<times> action"


derive (linorder) compare rat 

derive (eq) ceq predicate func atom object formula 
derive ccompare predicate func atom object formula
derive (no) cenum atom object formula
derive (rbt) set_impl func atom object formula

derive (rbt) mapping_impl object

derive linorder predicate func object atom "object atom formula" prod list ast_effect duration_op

instantiation rat :: time
begin
instance apply standard
  apply (rule dense_order_class.dense, assumption)
  using zero_neq_one[symmetric] by (rule exI)
end

context wf_ast_problem
begin
subsection \<open>Propositions\<close>
definition "objs \<equiv> set (map fst (consts D @ objects P))"

definition "tos = {(ty, obj). obj \<in> objs \<and> is_obj_of_type obj ty}"

definition "ltos \<equiv> {(tys, objs). list_all2 (\<lambda>ty ob. (ty, ob) \<in> tos) tys objs}"

definition "preds \<equiv> {(predAtm n os)| n os ts. PredDecl n ts \<in> set (predicates D) \<and> (ts, os) \<in> ltos}"

definition "eqs \<equiv> {(eqAtm a a)| a. a \<in> objs}"

definition "neqs \<equiv> {(eqAtm a b)| a b. a \<in> objs \<and> b \<in> objs \<and> a \<noteq> b}"

definition propositions::"pr set" where
"propositions \<equiv> (\<lambda>x. Not (Atom x)) ` preds \<union> Atom ` preds \<union> (\<lambda>x. Not (Atom x)) ` neqs \<union> Atom ` eqs"

subsection \<open>Actions\<close>

text \<open>If the duration constraint is not instantiable it will invalidate the plan according
to temporal PDDL semantics. Therefore, we can filter out instantiated actions that have
such duration constraints.\<close>
fun dur_const_instantiable::"term duration_constraint \<Rightarrow> (term \<Rightarrow> object) \<Rightarrow> bool" where
"dur_const_instantiable No_Const _ = True" |
"dur_const_instantiable (Time_Const op d) _ = True" |
"dur_const_instantiable (Func_Const op f ps) fun = (
  case (func_eval (FuncEnt f (map fun ps))) of
    None \<Rightarrow> False
  | Some v \<Rightarrow> True
)"

fun instantiate_duration_constraint::"term duration_constraint \<Rightarrow> (term \<Rightarrow> object) \<Rightarrow> duration_op \<times> (rat option)" where
"instantiate_duration_constraint No_Const _ = (GEQ, None)" |
"instantiate_duration_constraint (Time_Const op d) _ = (op, Some d)" |
"instantiate_duration_constraint (Func_Const op f ps) fun =
  (op, func_eval (FuncEnt f (map fun ps)))" 

definition "inst_dur_const c f \<equiv> case (instantiate_duration_constraint c f) of
  (op, Some v) \<Rightarrow> Some (op, v)
| (op, None  ) \<Rightarrow> None"

text \<open>This will not contain any invalid duration constraints.
It is interesting that duration constraints for propositional actions corresponding to 
PDDL actions depend on arguments.\<close>
definition "pddl_durative_actions \<equiv> {
  (n, inst_snap_action a args At_Start, 
  inst_snap_action a args Over_All, 
  inst_snap_action a args At_End, inst_dur_const const substt) |
  a args n params cond eff const tys substt. 
    a \<in> set (actions D) 
  \<and> a = Durative_Action_Schema n params const cond eff 
  \<and> tys = map snd params 
  \<and> (tys, args) \<in> ltos 
  \<and> substt = subst_term (the o (map_of (zip (map fst params) args)))
  \<and> dur_const_instantiable const substt}"

definition "none_snap = Ground_Action (Not Bot) (Effect Nil Nil)"

definition "pddl_instant_actions \<equiv>{
  (n, instantiate_action_schema a args, 
    none_snap, none_snap, Some (EQ, 0)) |
  a args n params pre eff tys. 
    a \<in> set (actions D) 
  \<and> a = Simple_Action_Schema n params pre eff 
  \<and> tys = map snd params 
  \<and> (tys, args) \<in> ltos}"

definition "pddl_actions = pddl_durative_actions \<union> pddl_instant_actions"

fun negate_literal::"'a formula \<Rightarrow> 'a formula" where
"negate_literal (Not x)   = x" |
"negate_literal x         = Not x"


text \<open>If suff_prop_conds returns a set S = {{1,2,3},{a,b}}, where all propositions in {1,2,3} or in 
{a,b} are sufficient to, then suff_prop_conds returns a formula in disjunctive_normal form. Negating the
formula is equivalent to violating one proposition in each subset. Therefore, negate all literals
and take one negated literal from each subset to create a set of literals that is sufficient to 
violate the formula.\<close>
definition prod'::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
"prod' xs Ys = (\<lambda>(x, Y). insert x Y) ` (xs \<times> Ys)"

definition negate_sc::"'a formula set set \<Rightarrow> 'a formula set set" where
"negate_sc S \<equiv> Finite_Set.fold (prod') {(negate_literal ` s) |s. s \<in> S} {}"

fun suff_prop_conds::"'a formula \<Rightarrow> 'a formula set set" where
"suff_prop_conds (Atom a) = {{Atom a}}" |
"suff_prop_conds Bot      = {}" |
"suff_prop_conds (Not Bot) = {{}}" |
"suff_prop_conds (Not a)  = negate_sc (suff_prop_conds a)" |
"suff_prop_conds (And a b) = {ca \<union> cb| ca cb. ca \<in> suff_prop_conds a \<and> cb \<in> suff_prop_conds b}" |
"suff_prop_conds (Or a b) = suff_prop_conds a \<union> suff_prop_conds b" |
"suff_prop_conds (Imp a b) =  negate_sc (suff_prop_conds a) \<union> suff_prop_conds b"

definition "suff_prop_list f \<equiv> sorted_list_of_set ` (suff_prop_conds f)"

fun snap_actions::"ground_action \<Rightarrow> (object atom formula list \<times> object ast_effect) set" where
"snap_actions (Ground_Action pre eff) = {(pre', eff)|pre'. pre' \<in> (suff_prop_list pre)}"

definition prop_actions::"action set" where
"prop_actions = {(n, a', inv', e', c)|n a inv e c a' inv' e'. 
  (n, a, inv, e, c) \<in> pddl_actions
  \<and> a' \<in> snap_actions a \<and> inv' \<in> snap_actions inv \<and> e' \<in> snap_actions e}"

subsection \<open>The initial state and the goal\<close>

text \<open>The initial state must contain all equalities and the propositions that are in \<open>I\<close> as positive 
literals, and inequalities and the propositions that are not in \<open>I\<close> as negative literals\<close>

definition "initial_state' \<equiv> (\<lambda>x. Not (Atom x)) ` neqs \<union> Atom ` eqs \<union> I \<union> Not ` (Atom ` preds - I)"

text \<open>The plan is to define a set of snap-actions Locks. Each of these has one of the sufficient conditions
for the goal to be satisfied as precondition. They will make goal true. All other 
snap-actions can only be taken when the goal has not been satisfied.\<close>
definition "goal_lock \<equiv> Or Bot (Not Bot)"

text \<open>Now, we have all propositions\<close>
definition "props \<equiv> propositions \<union> {Not goal_lock, goal_lock}"

text \<open>The single proposition that leads to the goal state is not by default satisfied in the initial
state.\<close>

definition "initial_state \<equiv> initial_state' \<union> {Not goal_lock}"

text \<open>We now define some actions that will lead to the goal state and will prevent any other snap-actions
from being executed. This needs some consideration about the manner in which we distinguish these snap-actions.\<close>

definition "goal_conditions \<equiv> suff_prop_list (goal P)"

abbreviation "goal_eff \<equiv> Effect [goal_lock] [Not goal_lock]"

definition goal_snaps::"snap set" where
"goal_snaps \<equiv> {(s, goal_eff)|s. s \<in> goal_conditions}"

definition "goal_actions \<equiv> {(''Goal'',gs,gs,gs, Some (EQ, 0))| gs. gs \<in> goal_snaps}"

definition "acts \<equiv> prop_actions \<union> goal_actions"

definition "goal_imp \<equiv> {goal_lock}"

text \<open>Lemma: propositional actions and goal actions are disjoint. Proof with auxiliary lemmas: the goal_lock
 is not in the set of PDDL \<open>propositions\<close>. PDDL effects only contain PDDL \<open>propositions\<close>.\<close>

subsection \<open>Snap actions\<close>


definition "at_start_imp \<equiv> Pair At_Start"

definition "at_end_imp \<equiv> Pair At_End"

subsubsection \<open>Preconditions, additions, and deletions\<close>

text \<open>Before we can implement \<open>over_all\<close> for @{typ snap_action}, we must define functions
from @{typ snap} to @{typ pr} for \<open>pre\<close>, \<open>adds\<close>, and \<open>dels\<close> respectively.\<close>

definition snap_pre::"snap \<Rightarrow> pr set" where
"snap_pre \<equiv> set o fst"

fun snap_adds::"snap \<Rightarrow> pr set" where
"snap_adds (pre, eff) = (set (adds eff)) \<union> (negate_literal ` (set (dels eff)))"

fun snap_dels::"snap \<Rightarrow> pr set" where
"snap_dels (pre, eff) = (set (dels eff)) \<union> (negate_literal ` (set (adds eff)))"

text \<open>When implementing the \<open>adds\<close> and \<open>dels\<close> functions, we have to add all literal negations of deletions
and remove all literal negations of additions, on top of adding the additions and removing the deletions.\<close>

text \<open>We need a few lemmas: 
\begin{itemize}
  \item For every proposition, either its addition or negation is in the initial state.
  \item For every proposition, only its addition or only its negation is in the initial state.
  \item For every propositional action. When applied to a state that is consistent, then the state
    maintains consistency
\end{itemize}
\<close>

text \<open>The @{typ snap}, which contains the \<open>over_all\<close> condition\<close>
definition "o_snap \<equiv> fst o snd o snd"

text \<open>The start snap\<close>
definition "s_snap \<equiv> fst o snd"

text \<open>The end snap\<close>
definition "e_snap \<equiv> fst o snd o snd o snd"

definition over_all_imp::"action \<Rightarrow> pr set" where
"over_all_imp = snap_pre o o_snap"

fun snap_action_to_snap::"snap_action \<Rightarrow> snap" where
"snap_action_to_snap (At_Start, act) = s_snap act" |
"snap_action_to_snap (At_End, act) = e_snap act"

text \<open>This is the actual function we will use to instantiate \<open>pre\<close> in the @{term temp_planning_problem} locale.\<close>
definition snap_action_pre::"snap_action \<Rightarrow> pr set" where
"snap_action_pre \<equiv> snap_pre o snap_action_to_snap" 

definition snap_action_adds::"snap_action \<Rightarrow> pr set" where
"snap_action_adds \<equiv> snap_adds o snap_action_to_snap"

definition snap_action_dels::"snap_action \<Rightarrow> pr set" where
"snap_action_dels \<equiv> snap_dels o snap_action_to_snap"

subsubsection \<open>Duration bounds\<close>
text \<open>First, define a function from our notion of a ground action to its duration constraint.\<close>

definition action_consts::"action \<Rightarrow> dc option" where
"action_consts \<equiv> snd o snd o snd o snd"

text \<open>The duration constraints can be negative. They just can never be satisfied by a valid plan. It
is also a good idea to set the lower bound to 0.\<close>
fun dc_to_ul::"dc option \<Rightarrow> rat lower_bound \<times> (rat upper_bound option)" where
"dc_to_ul (Some (EQ, n)) = (GE n, Some (LE n))" |
"dc_to_ul (Some (GEQ, n)) = (GE n, None)" |
"dc_to_ul (Some (LEQ, n)) = (GE 0, Some (LE n))" |
"dc_to_ul None = (GE 0, None)"

definition "lower_impl \<equiv> fst o dc_to_ul o action_consts"
definition "upper_impl \<equiv> snd o dc_to_ul o action_consts"

end

context wf_ast_problem
begin

lemma objs_typed: "obj \<in> objs \<longleftrightarrow> (\<exists>ty. (ty, obj) \<in> tos)" 
proof (rule iffI)
  assume a: "obj \<in> objs"
  hence "obj \<in> set (map fst (consts D @ objects P))" unfolding objs_def by blast
  with wf_problem[simplified wf_problem_def]
  obtain t where "map_of (consts D @ objects P) obj = Some t" by fastforce
  hence "is_obj_of_type obj t" unfolding is_of_type_def objT_alt is_obj_of_type_alt using of_type_refl by simp
  with a
  show "\<exists>ty. (ty, obj) \<in> tos" unfolding tos_def by auto
next
  assume "\<exists>ty. (ty, obj) \<in> tos"
  thus "obj \<in> objs" unfolding tos_def by simp
qed

lemma typed_args_correct: "(tys, args) \<in> ltos \<longleftrightarrow> list_all2 is_obj_of_type args tys"
proof (rule iffI) 
  assume "(tys, args) \<in> ltos"
  thus "list_all2 is_obj_of_type args tys"
  unfolding ltos_def tos_def
    apply (subst list_all2_twist)
    apply (rule list_all2_mono)
  by simp+
next
  have "obj \<in> objs" if "is_obj_of_type obj ty" for obj ty
  proof -
    from that
    have "is_of_type objT obj ty" using is_obj_of_type_alt by simp
    then obtain T where
      "objT obj = Some T"
      "of_type T ty" unfolding is_of_type_def 
      by (auto split: option.splits)
    hence "obj \<in> set (map fst (consts D @ objects P))"
      unfolding objT_alt using map_of_SomeD by fastforce
    thus ?thesis unfolding objs_def by blast
  qed
  moreover
  assume "list_all2 is_obj_of_type args tys"
  ultimately
  have "list_all2 (\<lambda>obj ty. is_obj_of_type obj ty \<and> obj \<in> objs) args tys" using list_all2_mono by force
  thus "(tys, args) \<in> ltos" unfolding ltos_def tos_def
    using list_all2_twist list_all2_mono by fastforce
qed


lemma sig_iff: "sig n = Some ts \<longleftrightarrow> PredDecl n ts \<in> set (predicates D)"
proof (rule iffI)
  assume "sig n = Some ts"
  thus "PredDecl n ts \<in> set (predicates D)"
    unfolding sig_def 
    apply -
    apply (drule map_of_SomeD)
    by (auto split: predicate_decl.splits) 
next
  assume "PredDecl n ts \<in> set (predicates D)"
  hence "(n, ts) \<in> set (map (\<lambda>(PredDecl n ts) \<Rightarrow> (n, ts)) (predicates D))" by force
  moreover
  have "distinct (map fst (map (\<lambda>(PredDecl n ts) \<Rightarrow> (n, ts)) (predicates D)))" 
  proof (subst distinct_map; rule conjI)

    have distinct_names: "distinct (map pred (predicates D))" using wf_domain unfolding wf_domain_def by blast
    hence distinct_preds: "distinct (predicates D)" using distinct_mapI by blast
    
    show "distinct (map (case_predicate_decl Pair) (predicates D))" 
    proof (subst distinct_map; rule conjI)
      show "distinct (predicates D)" using distinct_preds .
      have inj_pd: "inj (\<lambda>x. case x of PredDecl n ts \<Rightarrow> (n, ts))" 
      unfolding inj_def 
      apply (intro allI) 
      subgoal for x y
        by (cases x; cases y) auto
      done
    thus "inj_on (case_predicate_decl Pair) (set (predicates D))" unfolding inj_on_def inj_def by simp
    qed
    show "inj_on fst (set (map (case_predicate_decl Pair) (predicates D)))" 
    proof (rule inj_onI)
      fix x y
      assume x: "x \<in> set (map (case_predicate_decl Pair) (predicates D))"
        and  y: "y \<in> set (map (case_predicate_decl Pair) (predicates D))" 
        and xy: "fst x = fst y"
      from x
      obtain px nx vx  where
        px: "case_predicate_decl Pair px = x"
        "px \<in> set (predicates D)"
        "px = PredDecl nx vx"
        "x = (nx, vx)" by (auto split: predicate_decl.splits)
      
      from y
      obtain py ny vy  where
        py: "case_predicate_decl Pair py = y"
        "py \<in> set (predicates D)"
        "py = PredDecl ny vy"
        "y = (ny, vy)" by (auto split: predicate_decl.splits)
      
      from xy px py
      have n_eq: "ny = nx" by simp
      moreover
      have "vx = vy" 
      proof (rule ccontr)
        assume "vx \<noteq> vy"
        with px(2-3) py(2-3) n_eq
        have "\<exists>n vs vs'. PredDecl n vs \<in> set (predicates D) \<and> PredDecl n vs' \<in> set (predicates D) \<and> vs \<noteq> vs'" by blast
        hence "\<exists>p p'. p \<in> set (predicates D) \<and> p' \<in> set (predicates D) \<and> pred p = pred p' \<and> p \<noteq> p'" by fastforce
        moreover
        have "\<forall>p p'. p \<in> set (predicates D) \<and> p' \<in> set (predicates D) \<and> pred p = pred p' \<longrightarrow> p = p'" 
          using distinct_map_eq[OF distinct_names] by blast
        ultimately
        show False by blast
      qed
      ultimately
      show "x = y" using px py by blast
    qed
  qed
  ultimately
  show "sig n = Some ts" unfolding sig_def by (auto intro: map_of_is_SomeI)
qed


lemma wf_inst_with_objs_of_type:
  fixes n params d cond eff
  defines "a \<equiv> Durative_Action_Schema n params d cond eff"  
  assumes "a \<in> set (actions D)"
      and "(map snd params, args) \<in> ltos"
shows "wf_ground_action (inst_snap_action a args ta)"
proof -
  have "action_params_match a args" using typed_args_correct assms(3)
    unfolding action_params_match_def parameters_def using assms(1) by simp
  moreover
  have "wf_action_schema a" using wf_domain unfolding wf_domain_def using assms(2) by blast
  ultimately
  show ?thesis using wf_inst_durative_action_schema assms(1) by blast
qed

lemma wf_pred_atom_iff: "wf_pred_atom objT (n, vs) \<longleftrightarrow> predAtm n vs \<in> preds"
  apply (rule iffI)
  subgoal by (auto split: option.splits simp: preds_def sig_iff typed_args_correct[simplified is_obj_of_type_alt])
  subgoal 
    apply (simp add: preds_def)
    apply (erule exE)
    subgoal for ts
      apply (erule conjE)
      apply (subst (asm) sig_iff[symmetric])
      apply (subst (asm) typed_args_correct)
      apply (subst (asm) is_obj_of_type_alt)
      by auto
    done
  done

lemma wf_fmla_atom_in_propositions: "wf_fmla_atom objT f \<Longrightarrow> f \<in> propositions"
  apply (cases f)
  subgoal for x
    apply (cases x)
    using wf_pred_atom_iff unfolding propositions_def by auto
  by auto

fun effect_props::"object ast_effect \<Rightarrow> object atom formula set" where
"effect_props (Effect xs ys) = set xs \<union> set ys"

definition "effect_preds f \<equiv> \<Union> (atoms ` (effect_props f))"

abbreviation "form_preds \<equiv> atoms"

fun ga_preds::"ground_action \<Rightarrow> object atom set" where
"ga_preds (Ground_Action pre eff) = form_preds pre \<union> effect_preds eff"


lemma 
  assumes "wf_effect objT eff"
  shows "effect_preds eff \<subseteq> preds"
  using assms unfolding preds_def

lemma 
  assumes "wf_ground_action a"
  shows "ga_preds a \<subseteq> preds" 
  sorry
lemma 
  assumes "(n, s, i, e, c) \<in> pddl_durative_actions" 
  shows"ga_preds s \<subseteq> preds \<and> ga_preds i \<subseteq> preds \<and> ga_preds e \<subseteq> preds"
  sorry

end

context wf_ast_problem
begin

sublocale temp_planning_problem props acts initial_state goal_imp at_start_imp at_end_imp over_all_imp lower_impl upper_impl snap_action_pre snap_action_adds snap_action_dels 0
proof 
  show "initial_state \<subseteq> props"
  proof -
    from wf_problem
    have "\<forall>f \<in> set (init P). wf_fmla_atom objT f \<or> wf_func_assign f" unfolding wf_problem_def by simp
    moreover
    have "\<forall>p. is_predAtom p \<longrightarrow> \<not>(wf_func_assign p)"
      apply (rule allI) 
      subgoal for p apply (cases p) 
        subgoal for x apply (cases x) by auto 
        by auto
      done
    ultimately
    have "\<forall>p \<in> I. wf_fmla_atom objT p" unfolding I_def by auto
    with wf_fmla_atom_in_propositions
    show ?thesis unfolding initial_state_def props_def initial_state'_def propositions_def by blast
  qed
  show "goal_imp \<subseteq> props" unfolding goal_imp_def props_def by simp
  show "let snap_props = \<lambda>s. snap_action_pre s \<union> snap_action_adds s \<union> snap_action_dels s
    in \<forall>a\<in>acts. snap_props (at_start_imp a) \<subseteq> props \<and> snap_props (at_end_imp a) \<subseteq> props \<and> over_all_imp a \<subseteq> props"
  proof -
    define snap_props where [simp]: "snap_props = (\<lambda>s. snap_action_pre s \<union> snap_action_adds s \<union> snap_action_dels s)"
    have "snap_props (at_start_imp a) \<subseteq> props \<and> snap_props (at_end_imp a) \<subseteq> props \<and> over_all_imp a \<subseteq> props" 
      if a_in_acts: "a \<in> acts" for a
    proof -
      consider "a \<in> prop_actions" | "a \<in> goal_actions" using a_in_acts unfolding acts_def by blast
      thus ?thesis
      proof cases
        case 1
        then obtain n s s' inv inv' e e' c where
          "a = (n, s, inv, e, c)" 
          "s \<in> snap_actions s'"
          "inv \<in> snap_actions inv'"
          "e \<in> snap_actions e'"
          "(n, s', inv', e', c) \<in> pddl_actions" 
          unfolding prop_actions_def by blast
        show ?thesis 
          sorry
      next
        case 2
        show ?thesis 
          sorry
      qed
    qed
    thus ?thesis by auto
  qed
  show "inj_on at_start_imp acts"
 "inj_on at_end_imp acts"
 "at_start_imp ` acts \<inter> at_end_imp ` acts = {}"
 "0 < card props"
 "0 < card acts"
 "finite props"
 "finite acts"
 "0 \<le> 0" sorry
qed 
end

end
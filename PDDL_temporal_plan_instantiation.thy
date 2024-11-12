theory PDDL_temporal_plan_instantiation
  imports Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Semantics
    Temporal_Plans
    Containers.Containers
begin

derive (linorder) compare rat

derive (eq) ceq predicate func atom object formula 
derive ccompare predicate func atom object formula
derive (no) cenum atom object formula
derive (rbt) set_impl func atom object formula

derive (rbt) mapping_impl object

derive linorder predicate func object atom "object atom formula"

context wf_ast_problem
begin
definition "objs \<equiv>  set (map fst (consts D @ objects P))"

definition "tos = {(ty, obj). obj \<in> objs \<and> is_obj_of_type obj ty}"

definition "ltos \<equiv> {(tys, objs). list_all2 (\<lambda>ty ob. (ty, ob) \<in> tos) tys objs}"

definition "preds \<equiv> {(predAtm n os)| n os ts. PredDecl n ts \<in> set (predicates D) \<and> (ts, os) \<in> ltos}"

definition "eqs \<equiv> {(eqAtm a a)| a. a \<in> objs}"

definition "neqs \<equiv> {(eqAtm a b)| a b. a \<in> objs \<and> b \<in> objs \<and> a \<noteq> b}"

definition "propositions \<equiv> (\<lambda>x. Not (Atom x)) ` preds \<union> Atom ` preds \<union> (\<lambda>x. Not (Atom x)) ` neqs \<union> Atom ` eqs"

text \<open>The plan is to define a set of snap-actions Locks. Each of these has one of the sufficient conditions
for the goal to be satisfied as precondition. They will make goal true. All other 
snap-actions can only be taken when the goal has not been satisfied.\<close>
definition "goal_lock \<equiv> Or Bot (Not Bot)"

fun instantiate_duration_constraint::"term duration_constraint \<Rightarrow> object list \<Rightarrow> duration_op \<times> (rat option)" where
"instantiate_duration_constraint No_Const _ = (EQ, Some 0)" |
"instantiate_duration_constraint (Time_Const op d) as = (op, Some d)" |
"instantiate_duration_constraint (Func_Const op f ps) as = (op, func_eval (FuncEnt f as))"

definition "inst_dur_const c as \<equiv> case (instantiate_duration_constraint c as) of
  (op, Some v) \<Rightarrow> Some (op, v)
| (op, None  ) \<Rightarrow> None"


definition "pddl_durative_actions \<equiv> {(n, inst_snap_action a args At_Start, inst_snap_action a args Over_All, inst_snap_action a args At_End, v)
          |a args n params cond eff const tys v. a \<in> set (actions D) \<and> a = Durative_Action_Schema n params const cond eff 
            \<and> tys = map snd params \<and> (tys, args) \<in> ltos \<and> Some v = inst_dur_const const args}"

definition "none_snap = Ground_Action (Not Bot) (Effect Nil Nil)"

definition "pddl_instant_actions \<equiv>{(n, instantiate_action_schema a args, none_snap, none_snap, (EQ, 0))
          |a args n params pre eff tys. a \<in> set (actions D) \<and> a = Simple_Action_Schema n params pre eff 
            \<and> tys = map snd params \<and> (tys, args) \<in> ltos}"

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

definition negate::"'a formula set set \<Rightarrow> 'a formula set set" where
"negate S \<equiv> Finite_Set.fold (prod') {(negate_literal ` s) |s. s \<in> S} {}"


fun suff_prop_conds::"'a formula \<Rightarrow> 'a formula set set" where
"suff_prop_conds (Atom a) = {{Atom a}}" |
"suff_prop_conds Bot      = {}" |
"suff_prop_conds (Not Bot) = {{}}" |
"suff_prop_conds (Not a)  = negate (suff_prop_conds a)" |
"suff_prop_conds (And a b) = {ca \<union> cb| ca cb. ca \<in> suff_prop_conds a \<and> cb \<in> suff_prop_conds b}" |
"suff_prop_conds (Or a b) = suff_prop_conds a \<union> suff_prop_conds b" |
"suff_prop_conds (Imp a b) =  negate (suff_prop_conds a) \<union> suff_prop_conds b"

fun snap_actions::"ground_action \<Rightarrow> (object atom formula set \<times> object ast_effect) set" where
"snap_actions (Ground_Action pre eff) = {(pre', eff)|pre'. pre' \<in> (suff_prop_conds pre)}"

definition "prop_actions = {(n, a', inv', e', c)|n a inv e c a' inv' e'. 
  (n, a, inv, e, c) \<in> pddl_actions
  \<and> a' \<in> snap_actions a \<and> inv' \<in> snap_actions inv \<and> e' \<in> snap_actions e}"

definition "initial_state \<equiv> (\<lambda>x. Not (Atom x)) ` neqs \<union> Atom ` eqs \<union> I"

definition "goal_conditions \<equiv> suff_prop_conds (goal P)"

sublocale temp_planning_problem sorry
end

end
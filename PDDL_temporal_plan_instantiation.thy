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
subsection \<open>Propositions\<close>
definition "objs \<equiv>  set (map fst (consts D @ objects P))"

definition "tos = {(ty, obj). obj \<in> objs \<and> is_obj_of_type obj ty}"

definition "ltos \<equiv> {(tys, objs). list_all2 (\<lambda>ty ob. (ty, ob) \<in> tos) tys objs}"

definition "preds \<equiv> {(predAtm n os)| n os ts. PredDecl n ts \<in> set (predicates D) \<and> (ts, os) \<in> ltos}"

definition "eqs \<equiv> {(eqAtm a a)| a. a \<in> objs}"

definition "neqs \<equiv> {(eqAtm a b)| a b. a \<in> objs \<and> b \<in> objs \<and> a \<noteq> b}"

type_synonym pr = "object atom formula"

definition propositions::"pr set" where
"propositions \<equiv> (\<lambda>x. Not (Atom x)) ` preds \<union> Atom ` preds \<union> (\<lambda>x. Not (Atom x)) ` neqs \<union> Atom ` eqs"

subsection \<open>Actions\<close>
fun instantiate_duration_constraint::"term duration_constraint \<Rightarrow> (term \<Rightarrow> object) \<Rightarrow> duration_op \<times> (rat option)" where
"instantiate_duration_constraint No_Const _ = (EQ, Some 0)" |
"instantiate_duration_constraint (Time_Const op d) _ = (op, Some d)" |
"instantiate_duration_constraint (Func_Const op f ps) fun = (
  (op, func_eval (FuncEnt f (map fun ps)))
)" 

definition "inst_dur_const c f \<equiv> case (instantiate_duration_constraint c f) of
  (op, Some v) \<Rightarrow> Some (op, v)
| (op, None  ) \<Rightarrow> None"

text \<open>This will not contain any invalid duration constraints. On a theoretical level,
it is interesting that duration constraints for the propositional actions corresponding to 
PDDL actions depend on the parameters.\<close>
definition "pddl_durative_actions \<equiv> {
  (n, inst_snap_action a args At_Start, 
  inst_snap_action a args Over_All, 
  inst_snap_action a args At_End, v) |
  a args n params cond eff const tys v substt. 
    a \<in> set (actions D) 
  \<and> a = Durative_Action_Schema n params const cond eff 
  \<and> tys = map snd params 
  \<and> (tys, args) \<in> ltos 
  \<and> substt = subst_term (the o (map_of (zip (map fst params) args)))
  \<and> Some v = inst_dur_const const substt }"

definition "none_snap = Ground_Action (Not Bot) (Effect Nil Nil)"

definition "pddl_instant_actions \<equiv>{
  (n, instantiate_action_schema a args, 
    none_snap, none_snap, (EQ, 0)) |
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

fun snap_actions::"ground_action \<Rightarrow> (object atom formula set \<times> object ast_effect) set" where
"snap_actions (Ground_Action pre eff) = {(pre', eff)|pre'. pre' \<in> (suff_prop_conds pre)}"

type_synonym suff_cond = "pr set"

text \<open>Note, that this is not the type we will use as @{typ \<open>'snap_action\<close>}}, because we would
have to implement \<open>at_start\<close> as @{term \<open>fst\<close>}, which would cause it violate injectivity.\<close>
type_synonym snap = "suff_cond \<times> object ast_effect"

type_synonym dc = "duration_op \<times> rat"

text \<open>This is the actual type of action\<close>
type_synonym action = "(string \<times> snap \<times> snap \<times> snap \<times> dc)"

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

definition "goal_conditions \<equiv> suff_prop_conds (goal P)"

abbreviation "goal_eff \<equiv> Effect [goal_lock] [Not goal_lock]"

definition goal_snaps::"snap set" where
"goal_snaps \<equiv> {(s, goal_eff)|s. s \<in> goal_conditions}"

definition "goal_actions \<equiv> {(''Goal'',gs,gs,gs,(EQ, 0))| gs. gs \<in> goal_snaps}"

definition "acts \<equiv> prop_actions \<union> goal_actions"

text \<open>Lemma: propositional actions and goal actions are disjoint. Proof with auxiliary lemmas: the goal_lock
 is not in the set of PDDL \<open>propositions\<close>. PDDL effects only contain PDDL \<open>propositions\<close>.\<close>

subsection \<open>Snap actions\<close>

type_synonym snap_action = "temporal_annotation \<times> action"

definition "at_start_imp \<equiv> Pair At_Start"

definition "at_end_imp \<equiv> Pair At_End"

subsubsection \<open>Preconditions, additions, and deletions\<close>

text \<open>Before we can implement \<open>over_all\<close> for @{typ snap_action}, we must define functions
from @{typ snap} to @{typ pr} for \<open>pre\<close>, \<open>adds\<close>, and \<open>dels\<close> respectively.\<close>

definition snap_pre::"snap \<Rightarrow> pr set" where
"snap_pre \<equiv> fst"

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

definition over_all::"action \<Rightarrow> pr set" where
"over_all = snap_pre o o_snap"

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
text \<open>First, define a function from our notion of a ground action to the \<close>


sublocale temp_planning_problem sorry
end

end
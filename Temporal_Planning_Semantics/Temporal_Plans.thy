theory Temporal_Plans
  imports Temporal_Planning_Common.Utils "Difference_Bound_Matrices.DBM"
begin

datatype ('t) lower_bound =
  GT 't |
  GE 't

datatype ('t) upper_bound =
  LT 't |
  LE 't

section \<open>Abstract numeric syntax\<close>
text \<open>Numeric expressions and comparisons over opaque ground fluents @{typ 'n} and a rational-like
value sort @{typ 'r} (intended instance @{typ rat}). These stay PDDL-agnostic: PDDL's
@{text numeric_expression} is mapped into this type only at the @{text Ground_PDDL} boundary, exactly
as PDDL atoms become an opaque @{text 'proposition}. Explicit operator constructors (not Munta's
@{text \<open>binop "'r \<Rightarrow> 'r \<Rightarrow> 'r"\<close>}) so the type code-exports, has decidable equality, and maps 1:1 to
@{text \<open>binop (+)/(-)/(*)/(div)\<close>}. See @{file \<open>../NUMERIC_PLAN.md\<close>} \<section>A.1.\<close>

datatype ('n, 'r) nexp =
    NConst 'r                                       \<comment> \<open>a value constant\<close>
  | NVar   'n                                       \<comment> \<open>read a ground fluent's valuation\<close>
  | NAdd "('n, 'r) nexp" "('n, 'r) nexp"
  | NSub "('n, 'r) nexp" "('n, 'r) nexp"
  | NMul "('n, 'r) nexp" "('n, 'r) nexp"
  | NDiv "('n, 'r) nexp" "('n, 'r) nexp"            \<comment> \<open>integer-division gap at the Munta boundary\<close>

datatype cmp_op = Ceq | Cle | Cge | Clt | Cgt

datatype ('n, 'r) comp = Comp cmp_op "('n, 'r) nexp" "('n, 'r) nexp"

section \<open>Numeric semantics\<close>
text \<open>Evaluation of numeric expressions and comparisons against a partial fluent valuation
@{typ \<open>'n \<rightharpoonup> 'r\<close>}, and application of numeric effects. Partiality is definedness: a read of an
undefined fluent makes the expression undefined, so any comparison over it fails (fail-closed). Values
live in a @{class linordered_field} (intended instance @{typ rat}); division is exact field division
here -- the integer-division/truncation gap lives only at the Munta boundary. See
@{file \<open>../NUMERIC_PLAN.md\<close>} \<section>A.2.\<close>

text \<open>Fluents read by a numeric expression (its @{term NVar} leaves).\<close>
fun nexp_fluents :: "('n, 'r) nexp \<Rightarrow> 'n set" where
  "nexp_fluents (NConst _) = {}"
| "nexp_fluents (NVar f)   = {f}"
| "nexp_fluents (NAdd a b) = nexp_fluents a \<union> nexp_fluents b"
| "nexp_fluents (NSub a b) = nexp_fluents a \<union> nexp_fluents b"
| "nexp_fluents (NMul a b) = nexp_fluents a \<union> nexp_fluents b"
| "nexp_fluents (NDiv a b) = nexp_fluents a \<union> nexp_fluents b"

text \<open>Evaluate an expression against a partial valuation; @{term None} on an undefined-fluent read or
division by zero (fail-closed).\<close>
fun eval_nexp :: "('n \<rightharpoonup> 'r::linordered_field) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> 'r option" where
  "eval_nexp v (NConst c) = Some c"
| "eval_nexp v (NVar f)   = v f"
| "eval_nexp v (NAdd a b) =
     lift2_option (+) (eval_nexp v a) (eval_nexp v b)"
| "eval_nexp v (NSub a b) =
     lift2_option (-) (eval_nexp v a) (eval_nexp v b)"
| "eval_nexp v (NMul a b) =
     lift2_option (\<lambda>x y. x * y) (eval_nexp v a) (eval_nexp v b)"
| "eval_nexp v (NDiv a b) =
     bind2_option (\<lambda>x y. if y = 0 then None else Some (x / y)) (eval_nexp v a) (eval_nexp v b)"

text \<open>@{const eval_nexp} depends only on the fluents the expression reads.\<close>
lemma eval_nexp_cong:
  assumes "\<And>g. g \<in> nexp_fluents e \<Longrightarrow> v g = v' g"
  shows "eval_nexp v e = eval_nexp v' e"
  using assms by (induction e) auto

text \<open>Comparison operators as relations.\<close>
fun cmp_op_rel :: "cmp_op \<Rightarrow> 'r::linorder \<Rightarrow> 'r \<Rightarrow> bool" where
  "cmp_op_rel Ceq = (=)"
| "cmp_op_rel Cle = (\<le>)"
| "cmp_op_rel Cge = (\<ge>)"
| "cmp_op_rel Clt = (<)"
| "cmp_op_rel Cgt = (>)"

text \<open>A single comparison holds against a valuation; fails if either side is undefined (fail-closed).\<close>
definition sat_comp :: "('n \<rightharpoonup> 'r::linordered_field) \<Rightarrow> ('n, 'r) comp \<Rightarrow> bool" where
  "sat_comp v c \<longleftrightarrow> (case c of Comp p a b \<Rightarrow>
     (case (eval_nexp v a, eval_nexp v b) of (Some x, Some y) \<Rightarrow> cmp_op_rel p x y | _ \<Rightarrow> False))"

text \<open>A set of comparisons is read conjunctively (all hold simultaneously).\<close>
definition sat_comps :: "('n \<rightharpoonup> 'r::linordered_field) \<Rightarrow> ('n, 'r) comp set \<Rightarrow> bool" where
  "sat_comps v C \<longleftrightarrow> (\<forall>c \<in> C. sat_comp v c)"

lemma sat_compsI: "(\<And>c. c \<in> C \<Longrightarrow> sat_comp v c) \<Longrightarrow> sat_comps v C"
  unfolding sat_comps_def by blast

lemma sat_compsD: "sat_comps v C \<Longrightarrow> c \<in> C \<Longrightarrow> sat_comp v c"
  unfolding sat_comps_def by blast

lemma sat_compsE:
  assumes "sat_comps v C"
  obtains "\<And>c. c \<in> C \<Longrightarrow> sat_comp v c"
  using assms unfolding sat_comps_def by blast

text \<open>Fluents read by a comparison (both sides).\<close>
fun comp_fluents :: "('n, 'r) comp \<Rightarrow> 'n set" where
  "comp_fluents (Comp _ a b) = nexp_fluents a \<union> nexp_fluents b"

subsection \<open>Numeric effects\<close>
text \<open>A numeric effect set @{term U} maps each affected fluent to the expression assigned to it. Two
well-formedness conditions (fail-closed, checked per snap, see \<section>A.2): the left-hand side is
@{emph \<open>functional\<close>} (no fluent assigned twice), and no effect reads a fluent that the same snap also
writes (@{emph \<open>no intra-snap read-after-write\<close>}) -- PDDL snap effects are simultaneous, but Munta
edge updates are sequential, so we reject the case where the two differ.\<close>

definition upds_functional :: "('n \<times> ('n, 'r) nexp) set \<Rightarrow> bool" where
  "upds_functional U \<longleftrightarrow> (\<forall>(f, e) \<in> U. \<forall>(f', e') \<in> U. f = f' \<longrightarrow> e = e')"

lemma upds_functionalI:
  assumes "\<And>f e e'. (f, e) \<in> U \<Longrightarrow> (f, e') \<in> U \<Longrightarrow> e = e'"
  shows "upds_functional U"
  unfolding upds_functional_def using assms by fastforce

lemma upds_functionalD:
  assumes "upds_functional U" and "(f, e) \<in> U" and "(f, e') \<in> U"
  shows "e = e'"
  using assms unfolding upds_functional_def by fastforce

definition upds_no_self_read :: "('n \<times> ('n, 'r) nexp) set \<Rightarrow> bool" where
  "upds_no_self_read U \<longleftrightarrow> (\<forall>(f, e) \<in> U. nexp_fluents e \<inter> fst ` U = {})"

definition upds_wf :: "('n \<times> ('n, 'r) nexp) set \<Rightarrow> bool" where
  "upds_wf U \<longleftrightarrow> upds_functional U \<and> upds_no_self_read U"

lemma upds_wfI:
  assumes "\<And>f e e'. (f, e) \<in> U \<Longrightarrow> (f, e') \<in> U \<Longrightarrow> e = e'"
      and "\<And>f e g. (f, e) \<in> U \<Longrightarrow> g \<in> nexp_fluents e \<Longrightarrow> g \<notin> fst ` U"
    shows "upds_wf U"
  unfolding upds_wf_def upds_functional_def upds_no_self_read_def
  using assms by fast

lemma upds_wf_functionalD:
  assumes "upds_wf U" and "(f, e) \<in> U" and "(f, e') \<in> U"
  shows "e = e'"
  using assms unfolding upds_wf_def upds_functional_def by fastforce

lemma upds_wf_no_self_readD:
  assumes "upds_wf U" and "(f, e) \<in> U" and "g \<in> nexp_fluents e"
  shows "g \<notin> fst ` U"
  using assms unfolding upds_wf_def upds_no_self_read_def by fastforce

text \<open>Apply a numeric effect set to the @{emph \<open>pre\<close>}-state @{term v} (all reads are against the
pre-state -- simultaneous semantics). An assigned fluent whose right-hand side reads an undefined
fluent becomes undefined (fail-closed). Well-defined on a functional @{term U} via @{const The}.\<close>
definition apply_upds :: "('n \<times> ('n, 'r) nexp) set \<Rightarrow> ('n \<rightharpoonup> 'r::linordered_field) \<Rightarrow> ('n \<rightharpoonup> 'r)" where
  "apply_upds U v = (\<lambda>f. if f \<in> fst ` U then eval_nexp v (THE e. (f, e) \<in> U) else v f)"

lemma apply_upds_notin:
  assumes "f \<notin> fst ` U"
  shows "apply_upds U v f = v f"
  using assms unfolding apply_upds_def by simp

lemma apply_upds_in:
  assumes "upds_functional U" and "(f, e) \<in> U"
  shows "apply_upds U v f = eval_nexp v e"
proof -
  have uniq: "(THE e'. (f, e') \<in> U) = e"
  proof (rule the_equality)
    show "(f, e) \<in> U" using assms(2) .
    show "e' = e" if "(f, e') \<in> U" for e'
      using assms(1) assms(2) that unfolding upds_functional_def by fastforce
  qed
  have "f \<in> fst ` U" using assms(2) by force
  thus ?thesis unfolding apply_upds_def using uniq by simp
qed

section \<open>Plan validity\<close>
text \<open>This and similar notions need to be used in multiple places. I formulate this to a 
sufficient level of abstraction.\<close>

type_synonym 'p state = "'p set"

text \<open>A numeric state pairs the propositional set with a partial fluent valuation (partiality =
definedness). The propositional component @{typ \<open>'p set\<close>} is exactly the old @{typ \<open>'p state\<close>}, so it
remains a projection (@{term fst}) and the existing purely-propositional lemmas carry over unchanged
(\<section>3 Layer A: keep a propositional projection so existing lemmas degrade gracefully).\<close>
type_synonym ('p, 'n, 'r) num_state = "'p set \<times> ('n \<rightharpoonup> 'r)"

type_synonym 'p state_sequence = "nat \<Rightarrow> ('p state)"

text \<open>Invariants\<close>
type_synonym ('p, 't) invariant_sequence = "('t \<times> 'p set) set"

datatype (action: 'a) snap_action = 
  AtStart 'a |
  AtEnd 'a


text \<open>Temporal plans could be multi-sets, lists or just the range of a partial function. 
It is only necessary that the entries do not have to be unique, because unique entries are a 
consequence of prohibiting self-overlap. I chose a partial function.\<close>
type_synonym ('i, 'a, 't) temp_plan = "'i \<rightharpoonup> ('a \<times> 't \<times> 't)"



section \<open>Characterisation of some ideas surrounding temporal planning\<close>

text \<open>We assert things over the set of actions in a plan. If we assert the same thing set over the 
set of all actions in the problem. Then it holds for all plans which are possible for the problem.
We could assert over all actions, but that is not necessary.\<close>

subsection \<open>Actions\<close>
text \<open>Minimal definition\<close>
locale action_defs =
  fixes at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> 'time lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
begin

subsubsection \<open>Mutual exclusivity\<close>

text \<open>We want to define a plan in an abstract manner. This needs to be more abstract.\<close>
definition mutex_snap_action::"'snap_action \<Rightarrow> 'snap_action \<Rightarrow> bool" where
"mutex_snap_action a b = (
  (pre a) \<inter> ((adds b) \<union> (dels b)) \<noteq> {} \<or>
  ((adds a) \<inter> (dels b)) \<noteq> {} \<or>
  (pre b) \<inter> ((adds a) \<union> (dels a)) \<noteq> {} \<or>
  (adds b) \<inter> (dels a) \<noteq> {}
)"

fun app_snap::"('snap_action \<Rightarrow> 'x) \<Rightarrow> 'action snap_action \<Rightarrow> 'x" where
"app_snap f (AtStart a) = f (at_start a)" |
"app_snap f (AtEnd a) = f (at_end a)"

definition pre_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"pre_imp x = app_snap pre x"

definition add_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"add_imp x = app_snap adds x"

definition del_imp::"'action snap_action \<Rightarrow> 'proposition set" where
"del_imp x = app_snap dels x"

definition mutex_annotated_action where
"mutex_annotated_action a b = (
  (pre_imp a) \<inter> ((add_imp b) \<union> (del_imp b)) \<noteq> {} \<or>
  ((add_imp a) \<inter> (del_imp b)) \<noteq> {} \<or>
  (pre_imp b) \<inter> ((add_imp a) \<union> (del_imp a)) \<noteq> {} \<or>
  (add_imp b) \<inter> (del_imp a) \<noteq> {}
)"

definition snaps_disj_on where
"snaps_disj_on S \<equiv> inj_on at_start S
  \<and> inj_on at_end S
  \<and> at_start ` S \<inter> at_end ` S = {}"


lemma snaps_disj_on_subset: 
  assumes "snaps_disj_on A"
  and "B \<subseteq> A"
shows "snaps_disj_on B"
  using assms unfolding snaps_disj_on_def 
  using inj_on_subset by blast

lemma snaps_disj_onE:
  assumes "snaps_disj_on S"
      and "\<forall>x\<in>S. \<forall>y\<in>S. at_start x = at_start y \<longrightarrow> x = y \<Longrightarrow> \<forall>x\<in>S. \<forall>y\<in>S. at_end x = at_end y \<longrightarrow> x = y \<Longrightarrow> at_start ` S \<inter> at_end ` S = {} \<Longrightarrow> thesis"
    shows "thesis"
  using assms unfolding snaps_disj_on_def inj_on_def by auto

lemma mutex_snap_action_refl:
  "mutex_snap_action a b = mutex_snap_action b a"
  unfolding mutex_snap_action_def by blast

end

text \<open>Numeric extension of @{locale action_defs}. Additive: it imports every @{locale action_defs}
parameter and adds the numeric data, so @{locale action_defs} and its existing sublocales are
untouched. Numeric preconditions/effects attach to snap actions; the @{term over_all} numeric
invariant @{term n_inv} is per action (cf. @{term over_all}). A comparison/effect @{emph \<open>set\<close>} is
read conjunctively. See @{file \<open>../NUMERIC_PLAN.md\<close>} \<section>A.2.\<close>
locale numeric_action_defs =
  action_defs at_start at_end over_all lower upper pre adds dels
    for at_start :: "'action  \<Rightarrow> 'snap_action"
    and at_end   :: "'action  \<Rightarrow> 'snap_action"
    and over_all :: "'action  \<Rightarrow> 'proposition set"
    and lower    :: "'action  \<rightharpoonup> 'time lower_bound"
    and upper    :: "'action  \<rightharpoonup> 'time upper_bound"
    and pre      :: "'snap_action \<Rightarrow> 'proposition set"
    and adds     :: "'snap_action \<Rightarrow> 'proposition set"
    and dels     :: "'snap_action \<Rightarrow> 'proposition set" +
  fixes n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp set"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp set"
    and upds  :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) set"
begin

text \<open>Numeric data lifted from snap actions to annotated actions (cf. @{const pre_imp}).\<close>
definition n_pre_imp :: "'action snap_action \<Rightarrow> ('n, 'r) comp set" where
  "n_pre_imp x = app_snap n_pre x"

definition upds_imp :: "'action snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) set" where
  "upds_imp x = app_snap upds x"

lemma n_pre_imp_simps[simp]:
  "n_pre_imp (AtStart a) = n_pre (at_start a)"
  "n_pre_imp (AtEnd a)   = n_pre (at_end a)"
  unfolding n_pre_imp_def by simp_all

lemma upds_imp_simps[simp]:
  "upds_imp (AtStart a) = upds (at_start a)"
  "upds_imp (AtEnd a)   = upds (at_end a)"
  unfolding upds_imp_def by simp_all

text \<open>Well-formedness of a snap's numeric effects (\<section>A.2): functional lhs + no intra-snap
read-after-write.\<close>
definition snap_upds_wf :: "'snap_action \<Rightarrow> bool" where
  "snap_upds_wf a \<longleftrightarrow> upds_wf (upds a)"

subsection \<open>Numeric conditions and effects at a numeric state\<close>
text \<open>A snap's numeric precondition holds at a numeric state when all its comparisons hold against the
state's valuation; an action's @{term over_all} numeric invariant likewise. Numeric-effect
application updates only the valuation, reading the pre-state (simultaneous semantics).\<close>

definition num_pre_holds :: "'action snap_action \<Rightarrow> ('proposition, 'n, 'r) num_state \<Rightarrow> bool" where
  "num_pre_holds x s \<longleftrightarrow> sat_comps (snd s) (n_pre_imp x)"

definition num_inv_holds :: "'action \<Rightarrow> ('proposition, 'n, 'r) num_state \<Rightarrow> bool" where
  "num_inv_holds a s \<longleftrightarrow> sat_comps (snd s) (n_inv a)"

lemma num_pre_holdsI: "(\<And>c. c \<in> n_pre_imp x \<Longrightarrow> sat_comp (snd s) c) \<Longrightarrow> num_pre_holds x s"
  unfolding num_pre_holds_def by (rule sat_compsI)

lemma num_pre_holdsD: "num_pre_holds x s \<Longrightarrow> c \<in> n_pre_imp x \<Longrightarrow> sat_comp (snd s) c"
  unfolding num_pre_holds_def by (rule sat_compsD)

definition apply_num_eff ::
  "'action snap_action \<Rightarrow> ('proposition, 'n, 'r) num_state \<Rightarrow> ('proposition, 'n, 'r) num_state" where
  "apply_num_eff x s = (fst s, apply_upds (upds_imp x) (snd s))"

lemma apply_num_eff_props[simp]: "fst (apply_num_eff x s) = fst s"
  unfolding apply_num_eff_def by simp

lemma apply_num_eff_val[simp]: "snd (apply_num_eff x s) = apply_upds (upds_imp x) (snd s)"
  unfolding apply_num_eff_def by simp

subsection \<open>Numeric interference and simultaneous application\<close>
text \<open>The fluents a snap writes (lhs of its effects) and reads (its numeric precondition + every
effect rhs).\<close>
definition snap_writes :: "'snap_action \<Rightarrow> 'n set" where
  "snap_writes a = fst ` upds a"

definition snap_reads :: "'snap_action \<Rightarrow> 'n set" where
  "snap_reads a = (\<Union>c \<in> n_pre a. comp_fluents c) \<union> (\<Union>(f, e) \<in> upds a. nexp_fluents e)"

text \<open>Two snaps numerically interfere when one writes a fluent the other reads or writes (cf.
@{const mutex_snap_action}). Because all reads are pre-state, a @{emph \<open>simultaneous\<close>} set of snaps is
well defined only when its snaps pairwise do not interfere -- in particular no two may write a common
fluent. @{emph \<open>Soundness caveat\<close>}: treating every shared write as interference is stricter than PDDL
for additive @{text increase}/@{text decrease} effects, which PDDL accumulates; the supported fragment
(Gigante) never additively co-writes a fluent (e.g. the painter @{text counter} is serialised by its
@{text \<open>(= item_id counter)\<close>} guard), and the Layer-C checker rejects (fail-closed) any task that could.
This includes the @{emph \<open>self\<close>}-pair @{term \<open>at_start a\<close>}/@{term \<open>at_end a\<close>} of one action when its
duration collapses (@{term \<open>d = 0\<close>}/@{term \<open>d < \<epsilon>\<close>}): an action's own start/end effects must not write a
common fluent (mirrors the propositional self-pair clause in @{term mutex_valid_plan}). See
@{file \<open>../NUMERIC_PLAN.md\<close>} \<section>A.2.\<close>
definition num_mutex_snap_action :: "'snap_action \<Rightarrow> 'snap_action \<Rightarrow> bool" where
  "num_mutex_snap_action a b \<longleftrightarrow>
      snap_writes a \<inter> snap_writes b \<noteq> {}
    \<or> snap_writes a \<inter> snap_reads b \<noteq> {}
    \<or> snap_writes b \<inter> snap_reads a \<noteq> {}"

lemma num_mutex_snap_action_refl: "num_mutex_snap_action a b = num_mutex_snap_action b a"
  unfolding num_mutex_snap_action_def by blast

lemma num_mutex_snap_action_empty:
  assumes "upds = (\<lambda>_. {})"
  shows "\<not> num_mutex_snap_action a b"
  using assms unfolding num_mutex_snap_action_def snap_writes_def by simp

text \<open>The numeric effect of a single snap on the valuation: apply its (pre-combined, functional)
effect set @{term \<open>upds a\<close>}, reading every rhs from the snap's pre-state @{term v}. The \<section>A.3 boundary
combines same-fluent effects into one assignment per fluent (PDDL @{text combine_additive_numeric_effects}
/ @{text action_numeric_update_function_simplified}), so @{term \<open>upds a\<close>} is functional by construction.\<close>
definition snap_num_update :: "'snap_action \<Rightarrow> ('n \<rightharpoonup> 'r) \<Rightarrow> ('n \<rightharpoonup> 'r)" where
  "snap_num_update a v = apply_upds (upds a) v"

text \<open>Degenerate (no-effect) facts -- used by the migration lemma. Stated here so the locale
definitions unfold in their home locale.\<close>
lemma snap_writes_empty: "upds a = {} \<Longrightarrow> snap_writes a = {}"
  by (simp add: snap_writes_def)

lemma snap_num_update_empty: "upds a = {} \<Longrightarrow> snap_num_update a v = v"
  by (simp add: snap_num_update_def apply_upds_def)

text \<open>The numeric effect of a @{emph \<open>happening\<close>} (a set of co-occurring snaps, presented as a list) is
the sequential @{const fold} of the per-snap updates -- each snap reads the @{emph \<open>running\<close>} valuation.
This mirrors PDDL's happening update @{text action_list_numeric_update_function} (Formal-PDDL-Semantics,
@{text \<open>Continuous_Planning/Numeric_Update_Functions\<close>}: @{text \<open>fold (o) (map ...) id\<close>}) and the Munta run
(interleaved zero-delay edges, each update reading the running store). It is @{emph \<open>not\<close>} a set-union of
effects: co-occurring additive writes of one fluent must @{emph \<open>accumulate\<close>} (@{text \<open>f+ea\<close>} then
@{text \<open>+eb\<close>}), which a union would wrongly dedup.

Key obligation (next milestone): independence of the list order under non-interference -- the abstract
analog of PDDL's @{text same_actions_then_happening_numeric_update_function_equal}, via commutativity of
@{const snap_num_update} for non-@{const num_mutex_snap_action} snaps. Interference itself is discharged by
the existing clock/\<epsilon>-separation machinery: mutex snaps are forced \<ge>\<epsilon> apart, so they never co-occur in a
happening -- only commuting (non-interfering) snaps do.\<close>
definition happening_num_update :: "'snap_action list \<Rightarrow> ('n \<rightharpoonup> 'r) \<Rightarrow> ('n \<rightharpoonup> 'r)" where
  "happening_num_update = fold snap_num_update"

lemma happening_num_update_Nil: "happening_num_update [] = id"
  unfolding happening_num_update_def by simp

lemma happening_num_update_Cons:
  "happening_num_update (a # as) v = happening_num_update as (snap_num_update a v)"
  unfolding happening_num_update_def by simp

text \<open>Pointwise behaviour of a single snap's numeric update.\<close>
lemma snap_num_update_writes:
  assumes "upds_functional (upds a)" and "(f, e) \<in> upds a"
  shows "snap_num_update a v f = eval_nexp v e"
  unfolding snap_num_update_def using assms by (rule apply_upds_in)

lemma snap_num_update_unwritten:
  assumes "f \<notin> snap_writes a"
  shows "snap_num_update a v f = v f"
  using assms unfolding snap_num_update_def snap_writes_def by (rule apply_upds_notin)

lemma snap_write_witness:
  assumes "f \<in> snap_writes a"
  obtains e where "(f, e) \<in> upds a" and "nexp_fluents e \<subseteq> snap_reads a"
proof -
  obtain e where e: "(f, e) \<in> upds a" using assms unfolding snap_writes_def by auto
  have "nexp_fluents e \<subseteq> snap_reads a" using e unfolding snap_reads_def by fastforce
  thus thesis using e that by blast
qed

text \<open>Two non-interfering snaps' numeric updates commute -- the load-bearing fact behind
order-independence of @{const happening_num_update}. The functional hypotheses hold by construction
(\<section>A.3 combination); non-interference (@{term \<open>\<not> num_mutex_snap_action a b\<close>}) gives disjoint writes and
no cross read/write, so each snap's rhs reads the same value whichever snap runs first.\<close>
lemma snap_num_update_commute:
  assumes fa: "upds_functional (upds a)" and fb: "upds_functional (upds b)"
      and nm: "\<not> num_mutex_snap_action a b"
  shows "snap_num_update a (snap_num_update b v) = snap_num_update b (snap_num_update a v)"
proof (rule ext)
  fix f
  have ww: "snap_writes a \<inter> snap_writes b = {}"
   and ar: "snap_writes a \<inter> snap_reads b = {}"
   and br: "snap_writes b \<inter> snap_reads a = {}"
    using nm unfolding num_mutex_snap_action_def by auto
  consider (A) "f \<in> snap_writes a" | (B) "f \<in> snap_writes b"
    | (N) "f \<notin> snap_writes a \<and> f \<notin> snap_writes b" by auto
  then show "snap_num_update a (snap_num_update b v) f = snap_num_update b (snap_num_update a v) f"
  proof cases
    case A
    hence fnb: "f \<notin> snap_writes b" using ww by blast
    obtain e where e: "(f, e) \<in> upds a" "nexp_fluents e \<subseteq> snap_reads a"
      using A by (rule snap_write_witness)
    have agree: "snap_num_update b v g = v g" if "g \<in> nexp_fluents e" for g
    proof -
      have "g \<in> snap_reads a" using e(2) that by blast
      hence "g \<notin> snap_writes b" using br by blast
      thus ?thesis by (rule snap_num_update_unwritten)
    qed
    have "snap_num_update a (snap_num_update b v) f = eval_nexp (snap_num_update b v) e"
      using snap_num_update_writes[OF fa e(1)] .
    also have "\<dots> = eval_nexp v e" using eval_nexp_cong agree by blast
    also have "\<dots> = snap_num_update a v f" using snap_num_update_writes[OF fa e(1)] by simp
    also have "\<dots> = snap_num_update b (snap_num_update a v) f"
      using snap_num_update_unwritten[OF fnb] by simp
    finally show ?thesis .
  next
    case B
    hence fna: "f \<notin> snap_writes a" using ww by blast
    obtain e where e: "(f, e) \<in> upds b" "nexp_fluents e \<subseteq> snap_reads b"
      using B by (rule snap_write_witness)
    have agree: "snap_num_update a v g = v g" if "g \<in> nexp_fluents e" for g
    proof -
      have "g \<in> snap_reads b" using e(2) that by blast
      hence "g \<notin> snap_writes a" using ar by blast
      thus ?thesis by (rule snap_num_update_unwritten)
    qed
    have "snap_num_update b (snap_num_update a v) f = eval_nexp (snap_num_update a v) e"
      using snap_num_update_writes[OF fb e(1)] .
    also have "\<dots> = eval_nexp v e" using eval_nexp_cong agree by blast
    also have "\<dots> = snap_num_update b v f" using snap_num_update_writes[OF fb e(1)] by simp
    also have "\<dots> = snap_num_update a (snap_num_update b v) f"
      using snap_num_update_unwritten[OF fna] by simp
    finally show ?thesis by simp
  next
    case N
    hence a': "f \<notin> snap_writes a" and b': "f \<notin> snap_writes b" by auto
    have "snap_num_update a (snap_num_update b v) f = v f"
      using a' b' by (simp add: snap_num_update_unwritten)
    moreover have "snap_num_update b (snap_num_update a v) f = v f"
      using a' b' by (simp add: snap_num_update_unwritten)
    ultimately show ?thesis by simp
  qed
qed

text \<open>Adjacent swap of two non-interfering snaps in a happening leaves the numeric update unchanged --
the inductive engine for full order-independence of @{const happening_num_update} (lift to arbitrary
permutations of a pairwise-non-interfering happening is the remaining step).\<close>
lemma happening_num_update_swap:
  assumes "upds_functional (upds a)" and "upds_functional (upds b)"
      and "\<not> num_mutex_snap_action a b"
  shows "happening_num_update (a # b # as) v = happening_num_update (b # a # as) v"
  using snap_num_update_commute[OF assms(1,2,3)]
  by (simp add: happening_num_update_Cons)

text \<open>On a functional, pairwise-non-interfering set of snaps the per-snap updates commute, so
@{const Finite_Set.fold} of @{const snap_num_update} is **order-independent** -- this is the set-level
numeric happening update, the abstract analog of PDDL's
@{text same_actions_then_happening_numeric_update_function_equal}. The two hypotheses hold for a real
happening: @{term \<open>upds a\<close>} is functional by construction (\<section>A.3 combination), and pairwise
non-interference is exactly what the clock/\<epsilon>-separation enforces among co-occurring snaps.\<close>
lemma comp_fun_commute_on_snap_num_update:
  assumes "\<And>a. a \<in> S \<Longrightarrow> upds_functional (upds a)"
      and "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> num_mutex_snap_action a b"
    shows "comp_fun_commute_on S snap_num_update"
proof (unfold_locales)
  fix x y assume xy: "x \<in> S" "y \<in> S"
  show "snap_num_update y \<circ> snap_num_update x = snap_num_update x \<circ> snap_num_update y"
  proof (cases "x = y")
    case True thus ?thesis by simp
  next
    case False
    have "\<not> num_mutex_snap_action x y" using assms(2)[OF xy False] .
    thus ?thesis
      using snap_num_update_commute[OF assms(1)[OF xy(1)] assms(1)[OF xy(2)]]
      by (simp add: comp_def fun_eq_iff)
  qed
qed

definition happening_num_update_set :: "'snap_action set \<Rightarrow> ('n \<rightharpoonup> 'r) \<Rightarrow> ('n \<rightharpoonup> 'r)" where
  "happening_num_update_set S v = Finite_Set.fold snap_num_update v S"

text \<open>Insertion recursion for the set-level update (under the non-interference precondition), and the
empty case -- the computational laws @{text valid_state_sequence}'s numeric analog will use.\<close>
lemma happening_num_update_set_empty[simp]: "happening_num_update_set {} v = v"
  unfolding happening_num_update_set_def by simp

lemma happening_num_update_set_insert:
  assumes "finite S" and "a \<notin> S"
      and "\<And>x. x \<in> insert a S \<Longrightarrow> upds_functional (upds x)"
      and "\<And>x y. x \<in> insert a S \<Longrightarrow> y \<in> insert a S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> num_mutex_snap_action x y"
    shows "happening_num_update_set (insert a S) v = happening_num_update_set S (snap_num_update a v)"
proof -
  interpret comp_fun_commute_on "insert a S" snap_num_update
    using comp_fun_commute_on_snap_num_update[OF assms(3,4)] .
  show ?thesis
    unfolding happening_num_update_set_def
    using assms(1,2) by (simp add: fold_insert2 del: fold_insert)
qed

end

text \<open>Unique snap actions\<close>
locale action_defs_unique_snaps = action_defs +
  assumes snaps_disj_on_UNIV: "snaps_disj_on UNIV"

text \<open>A set of actions\<close>
locale action_set = 
  action_defs at_start at_end over_all lower upper pre adds dels
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set" +
  fixes actions::"'action set"

text \<open>Changing the behaviour of actions. Used to replace all plan actions with equivalent ones.\<close>
locale double_action_defs = 
  action_defs at_start at_end over_all lower upper pre adds dels 
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set" +
  fixes at_start'::"'action \<Rightarrow> 'snap_action_1"
    and at_end'::  "'action  \<Rightarrow> 'snap_action_1"
    and over_all':: "'action \<Rightarrow> 'proposition set"
    and pre'::     "'snap_action_1 \<Rightarrow> 'proposition set"
    and adds'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and dels'::    "'snap_action_1 \<Rightarrow> 'proposition set"
begin
(* Setting up a step in which actions' behaviour can be replaced with equivalent behaviour *)
sublocale acts2: 
  action_defs at_start' at_end' over_all' lower upper pre' adds' dels'
  .
end

subsubsection \<open>Restriction to a set of action\<close>

locale action_set_finite = action_set +
  assumes finite_actions: "finite actions"

locale action_set_some = action_set +
  assumes some_actions: "0 < card actions"
begin
sublocale action_set_finite using some_actions card_ge_0_finite by unfold_locales blast 
end

locale action_set_unique_snaps = action_set +
  assumes snaps_disj_on_acts: "snaps_disj_on actions"
begin
lemma at_start_inj_on_acts:
  "inj_on at_start actions" 
  using snaps_disj_on_acts unfolding snaps_disj_on_def by auto
lemma at_end_inj_on_acts:
  "inj_on at_end actions" 
  using snaps_disj_on_acts unfolding snaps_disj_on_def by auto
lemma end_start_disj_on_acts:
  "at_start ` actions \<inter> at_end ` actions = {}" 
  using snaps_disj_on_acts snaps_disj_on_def by auto
  
end


subsubsection \<open>Restriction to a set of propositions\<close>
locale action_and_prop_set = action_defs at_start at_end over_all lower upper pre adds dels
  for at_start::"'action  \<Rightarrow> 'snap_action"
  and at_end::  "'action  \<Rightarrow> 'snap_action"
  and over_all::"'action  \<Rightarrow> 'proposition set"
  and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
  and upper::   "'action  \<rightharpoonup> 'time upper_bound"
  and pre::     "'snap_action \<Rightarrow> 'proposition set"
  and adds::    "'snap_action \<Rightarrow> 'proposition set"
  and dels::    "'snap_action \<Rightarrow> 'proposition set" +
fixes props::"'proposition set"
begin
text \<open>Restricting actions to props\<close>
definition "over_all_restr = (\<lambda>a. over_all a \<inter> props)"
definition "pre_restr = (\<lambda>s. pre s \<inter> props)"

definition "pre_imp_restr = (\<lambda>s. pre_imp s \<inter> props)"

text \<open>Actions only modify a certain set of propositions. The problem can have constants.\<close>
definition snap_mod_props where
"snap_mod_props s \<equiv> adds s \<union> dels s \<subseteq> props"

definition act_mod_props where
"act_mod_props a \<equiv>
    snap_mod_props (at_start a)
  \<and> snap_mod_props (at_end a)"

lemma snap_mod_propsI:
  assumes "adds s \<subseteq> props"
      and "dels s \<subseteq> props"
  shows "snap_mod_props s"
  unfolding snap_mod_props_def
  using assms by simp

lemma act_mod_propsI:
  assumes "snap_mod_props (at_start a)"
    "snap_mod_props (at_end a)"
  shows "act_mod_props a"
  unfolding act_mod_props_def using assms by simp

text \<open>Actions only refer to a certain set of propositions.\<close>
definition snap_ref_props where
"snap_ref_props s \<equiv> pre s \<union> adds s \<union> dels s \<subseteq> props"

lemma snap_ref_props_imp_snap_mod_props:
  "snap_ref_props a \<Longrightarrow> snap_mod_props a" unfolding snap_ref_props_def snap_mod_props_def by auto

definition act_ref_props where
"act_ref_props a \<equiv>
    snap_ref_props (at_start a) 
  \<and> snap_ref_props (at_end a)
  \<and> over_all a \<subseteq> props"


lemma act_ref_props_imp_act_mod_props:
  "act_ref_props a \<Longrightarrow> act_mod_props a" using snap_ref_props_imp_snap_mod_props
  unfolding act_ref_props_def act_mod_props_def by auto

text \<open>Constants \<close>
definition snap_consts where
"snap_consts s \<equiv> pre s \<union> adds s \<union> dels s - props"

definition act_consts where
"act_consts a \<equiv> snap_consts (at_start a) \<union> snap_consts (at_end a) \<union> (over_all a - props)"

end

locale actions_and_finite_props = action_and_prop_set +
  assumes finite_props: "finite props"

locale actions_and_some_props = action_and_prop_set +
  assumes some_props: "0 < card props"
begin
sublocale actions_and_finite_props
  using some_props card_ge_0_finite by unfold_locales blast
end

locale double_actions_and_props = double_action_defs + action_and_prop_set

locale action_set_and_props =
  action_and_prop_set at_start at_end over_all lower upper pre adds dels props +
  action_set at_start at_end over_all lower upper pre adds dels actions
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and props::"'proposition set"
    and actions::"'action set"
begin
definition "action_consts \<equiv> \<Union>(act_consts ` actions)"
end

locale double_action_set_and_props = 
  double_actions_and_props at_start at_end over_all lower upper pre adds dels at_start' at_end' over_all' pre' adds' dels' props +
  action_set at_start at_end over_all lower upper pre adds dels actions
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and at_start'::"'action \<Rightarrow> 'snap_action_1"
    and at_end'::  "'action  \<Rightarrow> 'snap_action_1"
    and over_all'::"'action  \<Rightarrow> 'proposition set"
    and pre'::     "'snap_action_1 \<Rightarrow> 'proposition set"
    and adds'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and dels'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and props::"'proposition set"
    and actions::"'action set"
begin
sublocale acts2: action_set at_start' at_end' over_all' lower upper pre' adds' dels' actions .
end

locale temp_planning_problem = action_defs at_start at_end over_all lower upper pre adds dels
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set" +
  fixes init::    "'proposition set"
    and goal::    "'proposition set"
    and \<epsilon>::       "'time::time" 
  assumes eps_ran: "0 \<le> \<epsilon>"

locale temp_planning_problem_and_props = 
  temp_planning_problem + 
  action_and_prop_set

locale temp_planning_problem_and_finite_props = 
  temp_planning_problem_and_props +
  actions_and_finite_props
begin
sublocale action_and_prop_set .
end

locale temp_planning_problem_and_some_props = 
  temp_planning_problem_and_props +
  actions_and_some_props
begin
sublocale temp_planning_problem_and_finite_props by unfold_locales
end

locale temp_planning_problem_and_actions =
  temp_planning_problem + 
  action_set

locale temp_planning_problem_and_finite_actions = 
  temp_planning_problem_and_actions + 
  action_set_finite

locale temp_planning_problem_and_some_actions = 
  temp_planning_problem_and_actions +
  action_set_some
begin
sublocale temp_planning_problem_and_finite_actions by unfold_locales
end

locale temp_planning_problem_and_actions_with_unique_snaps = 
  temp_planning_problem_and_actions +
  action_set_unique_snaps

locale temp_planning_problem_with_unique_snaps = 
  temp_planning_problem +
  action_defs_unique_snaps
begin
sublocale temp_planning_problem_and_actions_with_unique_snaps apply unfold_locales
  using snaps_disj_on_UNIV snaps_disj_on_subset by auto
end

locale temp_planning_problem_with_bounded_init_and_goal = 
  temp_planning_problem_and_props +
  assumes init_in_props: "init \<subseteq> props"
      and goal_in_props: "goal \<subseteq> props"

locale temp_planning_problem_goal_consts_in_init_consts =
  temp_planning_problem_and_props +
  assumes goal_consts_in_init_consts: "goal - props \<subseteq> init - props"
  
locale temp_planning_problem_and_actions_mod_props = 
  temp_planning_problem_and_actions +
  action_and_prop_set +
  assumes domain_acts_mod_props: "\<forall>a \<in> actions. act_mod_props a"

locale temp_planning_problem_and_actions_ref_props = 
  temp_planning_problem_and_actions + 
  action_and_prop_set +
  assumes domain_acts_ref_props: "\<forall>a \<in> actions. act_ref_props a"
begin
sublocale temp_planning_problem_and_actions_mod_props
  apply unfold_locales using domain_acts_ref_props act_ref_props_imp_act_mod_props by blast
end

locale temp_planning_problem_and_action_consts_in_init_consts =
  temp_planning_problem_and_actions + 
  action_set_and_props +
  assumes domain_action_consts_in_init_consts: "action_consts \<subseteq> init - props"
  

locale temp_planning_problem_restr_to_props =
  temp_planning_problem_goal_consts_in_init_consts +
  temp_planning_problem_and_actions_mod_props
begin
  
end
text \<open>It is possible to reason about plans without relating them to the sets of actions and propositions.
Assumptions regarding propositions and plans can be added later.\<close>

text \<open>First, we define things w.r.t. a plan\<close>
locale temp_plan_defs = temp_planning_problem  
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon>
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::    "'proposition set"
    and goal::    "'proposition set"
    and \<epsilon>::       "'time" +
  fixes \<pi>::       "('i, 'action, 'time) temp_plan"
begin

definition "plan_actions \<equiv> {a| a t d. (a, t, d) \<in> ran \<pi>}"

lemma in_plan_actionsI: "(a, t, d) \<in> ran \<pi> \<Longrightarrow> a \<in> plan_actions"
  and in_plan_actions_iff: "\<exists>t d. (a, t, d) \<in> ran \<pi> \<longleftrightarrow> a \<in> plan_actions"
  and in_plan_actionsE: "a \<in> plan_actions \<Longrightarrow> (\<And>t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  and plan_rangeE: "(a, t, d) \<in> ran \<pi> \<Longrightarrow> (a \<in> plan_actions \<Longrightarrow>  thesis) \<Longrightarrow> thesis"
  unfolding plan_actions_def by blast+

definition apply_effects::"'snap_action set \<Rightarrow> 'proposition set \<Rightarrow> 'proposition set" where
"apply_effects S M \<equiv> (M - \<Union>(dels ` S)) \<union> \<Union>(adds ` S)"

definition htps::"'time set" where
"htps \<equiv> {t |a t d. (a, t, d) \<in> ran \<pi>} \<union> {t + d |a t d. (a, t, d) \<in> ran \<pi>}"

definition htpl::"'time list" where
"htpl = sorted_list_of_set htps"

definition time_index::"nat \<Rightarrow> 'time" where
"time_index \<equiv> ((!) htpl)"

text \<open>Happening Sequences\<close>

definition plan_happ_seq::"('time \<times> 'snap_action) set" where
"plan_happ_seq \<equiv> 
    {(t, at_start a) | a t d. (a, t, d) \<in> ran \<pi>}
  \<union> {(t + d, at_end a) | a t d. (a, t, d) \<in> ran \<pi>}"

abbreviation happ_at::"('time \<times> 'snap_action) set \<Rightarrow> 'time \<Rightarrow> 'snap_action set" where
"happ_at B t \<equiv> {s. (t, s) \<in> B}"
    
text \<open>Invariants\<close>
definition plan_inv_seq::"('proposition, 'time) invariant_sequence" where
"plan_inv_seq \<equiv>
  {(t', over_all a) | a t d t'. (a, t, d) \<in> ran \<pi> \<and> (t < t' \<and> t' \<le> t + d)}"

definition invs_at::"('proposition, 'time) invariant_sequence \<Rightarrow> 'time \<Rightarrow> 'proposition set" where
"invs_at Inv t \<equiv> \<Union>{p | p. (t, p) \<in> Inv}"

subsubsection \<open>Mutual exclusivity\<close>

text \<open>This is our most general formulation of actions not interfering. This considers the tuples in the range 
of the plan to be actions. The contents may be the same (duplicate action/self-overlap), unless this is explicitly
prohibited. Therefore, the mutual exclusivity of actions refers to the index for equivalence of 
actions. We also need to check the case that the same action has a duration of 0.

\<close>
definition mutex_valid_plan::bool where
"mutex_valid_plan \<equiv> (\<forall>i j a ta da b tb db sa sb t u. 
  i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j 
  \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db)
  \<and> (sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da)
  \<and> (sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db)
  \<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
  \<longrightarrow> \<not>mutex_snap_action sa sb)
  \<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))
"

definition mutex_sched where
"mutex_sched a ta da b tb db \<equiv> \<forall>sa t sb u. 
  (sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da)
\<and> (sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db)
\<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
\<longrightarrow> \<not>mutex_snap_action sa sb"

definition mutex_valid_plan_alt::bool where
"mutex_valid_plan_alt \<equiv> (\<forall>i j a ta da b tb db. 
  i \<in> dom \<pi> 
\<and> j \<in> dom \<pi> 
\<and> i \<noteq> j 
\<and> \<pi> i = Some (a, ta, da) 
\<and> \<pi> j = Some (b, tb, db) 
\<longrightarrow> mutex_sched a ta da b tb db)
\<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))"

lemma mutex_valid_plan_eq: "mutex_valid_plan \<longleftrightarrow> mutex_valid_plan_alt"
  unfolding mutex_valid_plan_def mutex_valid_plan_alt_def mutex_sched_def 
  apply (rule iffI; intro conjI)
  by blast+

lemma mutex_sched_refl:
  "mutex_sched a ta da b tb db = mutex_sched b tb db a ta da"
  unfolding mutex_sched_def
  apply (intro iffI)
   apply (subst mutex_snap_action_refl)
  apply blast
   apply (subst mutex_snap_action_refl)
  by blast

lemma mutex_schedI:
  assumes 
    "ta - tb < \<epsilon> \<Longrightarrow> tb - ta < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_start b)"
    "ta = tb \<Longrightarrow> \<not>mutex_snap_action (at_start a) (at_start b)"
    "ta - (tb + db) < \<epsilon> \<Longrightarrow> tb + db - ta < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end b)"
    "ta = tb + db \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end b)"
    "ta + da - tb < \<epsilon> \<Longrightarrow> tb - (ta + da) < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_end a) (at_start b)"
    "ta + da = tb \<Longrightarrow> \<not> mutex_snap_action (at_end a) (at_start b)"
    "ta + da - (tb + db) < \<epsilon> \<Longrightarrow> tb + db - (ta + da) < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_end a) (at_end b)"
    "ta + da = tb + db \<Longrightarrow> \<not> mutex_snap_action (at_end a) (at_end b)"
  shows "mutex_sched a ta da b tb db"
  unfolding mutex_sched_def
  apply (intro strip, elim conjE disjE)
  using assms by simp+

lemma mutex_sched_zero_sepI:
  assumes "\<epsilon> = 0"
    "ta = tb \<Longrightarrow> \<not>mutex_snap_action (at_start a) (at_start b)"
    "ta = tb + db \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end b)"
    "ta + da = tb \<Longrightarrow> \<not> mutex_snap_action (at_end a) (at_start b)"
    "ta + da = tb + db \<Longrightarrow> \<not> mutex_snap_action (at_end a) (at_end b)"
  shows "mutex_sched a ta da b tb db"
  using mutex_schedI assms by simp
  

subsubsection \<open>Valid state sequence\<close>

definition valid_state_sequence::"'proposition state_sequence \<Rightarrow> bool" where
"valid_state_sequence M \<equiv> (
  let 
    t = time_index;
    Inv = plan_inv_seq;
    B = plan_happ_seq
  in
    (\<forall>i. i < length htpl \<longrightarrow> (
      let 
        S = happ_at B (t i);
        pres = \<Union>(pre ` S);
        invs = invs_at Inv (t i)
      in
        apply_effects S (M i) = (M (Suc i))
        \<and> invs \<subseteq> (M i)
        \<and> pres \<subseteq> (M i)))
)"

fun satisfies_lower_bound::"'time lower_bound option \<Rightarrow> 'time \<Rightarrow> bool" where
"satisfies_lower_bound (Some (GT t')) t = (t' < t)" | 
"satisfies_lower_bound (Some (GE t')) t = (t' \<le> t)" |
"satisfies_lower_bound None t = True"

fun satisfies_upper_bound::"'time upper_bound option \<Rightarrow> 'time \<Rightarrow> bool" where
"satisfies_upper_bound (Some (LT t')) t = (t < t')" | 
"satisfies_upper_bound (Some (LE t')) t = (t \<le> t')" |
"satisfies_upper_bound None t = True"

definition satisfies_duration_bounds::"'action \<Rightarrow> 'time \<Rightarrow> bool" where
"satisfies_duration_bounds a t \<equiv> 
  let 
  lb = satisfies_lower_bound (lower a) t;
  ub = satisfies_upper_bound (upper a) t
  in lb \<and> ub
"
(* An action with a duration of 0 is an instant snap-action. We restrict this to 0 < d for some 
proofs, because of how some automata are constructed. *)
definition durations_ge_0::bool where
"durations_ge_0 \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> 0 \<le> d"


definition durations_valid::bool where
"durations_valid \<equiv> \<forall>a t d. (a, t, d) \<in> ran \<pi> \<longrightarrow> satisfies_duration_bounds a d"

(* The validity of infinite plans is ill-defined. *)

definition finite_plan::bool where
"finite_plan \<equiv> finite (dom \<pi>)"

definition valid_plan::"bool" where
"valid_plan \<equiv> \<exists>M. 
    valid_state_sequence M
    \<and> M 0 = init
    \<and> goal \<subseteq> M (length htpl)
    \<and> durations_ge_0
    \<and> durations_valid
    \<and> mutex_valid_plan
    \<and> finite_plan"


definition no_self_overlap::"bool" where
"no_self_overlap \<equiv> \<not>(\<exists>i j a t d u e. i \<noteq> j
  \<and> i \<in> dom \<pi>
  \<and> j \<in> dom \<pi>
  \<and> Some (a, t, d) = \<pi> i
  \<and> Some (a, u, e) = \<pi> j
  \<and> t \<le> u \<and> u \<le> t + d)"

(* move this *)
definition mutex_valid_plan_inj::bool where
"mutex_valid_plan_inj \<equiv> 
  (\<forall>a ta da b tb db. 
      (a, ta, da) \<in> ran \<pi> 
    \<and> (b, tb, db) \<in> ran \<pi>
    \<and> (a, ta, da) \<noteq> (b, tb, db)
  \<longrightarrow> mutex_sched a ta da b tb db)
\<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not>mutex_snap_action (at_start a) (at_end a))"

definition annotated_action_seq::"('time \<times> 'action snap_action) set" where
"annotated_action_seq \<equiv>                                       
    {(t, AtStart a) | a t d. (a, t, d) \<in> ran \<pi>}
  \<union> {(t + d, AtEnd a) | a t d. (a, t, d) \<in> ran \<pi>}"

abbreviation snap_at::"('time \<times> 'action snap_action) set \<Rightarrow> 'time \<Rightarrow> 'action snap_action set" where
"snap_at B t \<equiv> {s. (t, s) \<in> B}"


definition nm_anno_act_seq where
"nm_anno_act_seq \<equiv> let B = annotated_action_seq in 
  (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> (t, a) \<in> B \<and> (u, b) \<in> B
    \<and> (a \<noteq> b \<or> t \<noteq> u) 
  \<longrightarrow> \<not>mutex_annotated_action a b)
  \<and> (\<forall>t a b. (t, a) \<in> B \<and> (t, b) \<in> B \<and> a \<noteq> b \<longrightarrow> \<not>mutex_annotated_action a b)"

subsubsection \<open>Non-Interference w.r.t the Happening Sequence\<close>

text \<open>This definition comes from the statement in \<^cite>\<open>giganteDecidabilityComplexityActionBased2020\<close>, that every at-start 
snap-action interferes with itself for self-overlap. Therefore, we can assume the same for at-end
snap-actions. Moreover, in their definition of a planning problem, the assumption is made that 
no two actions share snap-actions. at-start(a) \<noteq> at-start(b) and at-start(a) \<noteq> at-end(b) and at-start(a) \<noteq> at-end(a).\<close>

definition nm_happ_seq::"('time \<times> 'snap_action) set \<Rightarrow> bool" where
"nm_happ_seq B \<equiv> 
  (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u
    \<and> (a \<noteq> b \<or> t \<noteq> u) \<longrightarrow> \<not>mutex_snap_action a b)
  \<and> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"

text \<open>Rules\<close>


lemma eps_cases: 
  assumes "\<epsilon> = 0 \<Longrightarrow> thesis"
      and "0 \<le> \<epsilon> \<Longrightarrow> thesis"
    shows "thesis"
  using assms eps_ran by blast

lemma in_happ_atD:
  assumes "x \<in> happ_at B t"
  shows "(t, x) \<in> B"
  using assms by (rule CollectD)

lemma in_happ_atI:
  assumes "(t, x) \<in> B"
  shows "x \<in> happ_at B t"
  using assms by (rule CollectI)

lemma a_in_B_iff_t_in_htps: "(\<exists>a. a \<in> happ_at plan_happ_seq t) \<longleftrightarrow> (t \<in> htps)"
proof
  assume "\<exists>a. a \<in> happ_at plan_happ_seq t"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" unfolding plan_happ_seq_def by blast
  thus "t \<in> htps" unfolding plan_happ_seq_def htps_def by blast
next
  assume "t \<in> htps"
  then obtain a where
    "(t, a) \<in> plan_happ_seq" unfolding plan_happ_seq_def htps_def by blast
  thus "\<exists>a. a \<in> happ_at plan_happ_seq t" by blast
qed

text \<open>If something is in the happening sequence, then there must be an action in the plan.\<close>
lemma in_happ_seq_exD:
  assumes in_happ_seq: "(time, snap) \<in> plan_happ_seq"
  shows "\<exists>a t d. (a, t, d) \<in> ran \<pi> 
    \<and> (at_start a = snap \<and> time = t \<or> at_end a = snap \<and> time = t + d)"
  using assms unfolding plan_happ_seq_def by blast

lemma in_happ_seqE:
  assumes "(time, snap) \<in> plan_happ_seq"
    and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> at_start a = snap \<Longrightarrow> time = t \<Longrightarrow> thesis"
    and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> at_end a = snap \<Longrightarrow> time = t + d \<Longrightarrow> thesis"
  shows thesis
  using in_happ_seq_exD assms by blast

lemma in_happ_seq_propE:
  assumes "(time, snap) \<in> plan_happ_seq"
    and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> Q t (at_start a)"
    and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> Q (t + d) (at_end a)"
  shows "Q time snap"
  apply (rule in_happ_seqE[OF assms(1)])
  using assms by auto

lemma in_happ_seq_exD_act:
  assumes in_happ_seq: "(time, snap) \<in> plan_happ_seq"
  shows "\<exists>a t d. (a, t, d) \<in> ran \<pi> \<and> (at_start a = snap \<or> at_end a = snap)"
  using assms unfolding plan_happ_seq_def by blast

lemma in_happ_seqI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "(t, at_start a) \<in> plan_happ_seq" "(t + d, at_end a) \<in> plan_happ_seq"
  using assms unfolding plan_happ_seq_def by blast+

lemma htpsE:
  assumes "time \<in> htps"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> time = t \<Longrightarrow> thesis"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> time = t + d \<Longrightarrow> thesis"
  shows thesis 
  using assms unfolding htps_def by blast 

lemma htpsI:
  assumes "(a, t, d) \<in> ran \<pi>"
  shows "t \<in> htps" "t + d \<in> htps"
  unfolding htps_def using assms by blast+

lemma htps_conv_happ_seq_ex:
  assumes "t \<in> htps"
  shows "\<exists>h. (t, h) \<in> plan_happ_seq"
  using assms
  apply -
  apply (erule htpsE)
  using in_happ_seqI by blast+

lemma happ_seq_conv_htps:
  assumes "(t, h) \<in> plan_happ_seq"
  shows "t \<in> htps"
  using assms 
  apply -
  apply (erule in_happ_seqE)
  using htpsI by blast+


lemma valid_state_sequenceE: 
  assumes "valid_state_sequence MS"
    and "i < length htpl"
    and "apply_effects (happ_at plan_happ_seq (time_index i)) (MS i) = MS (Suc i) \<Longrightarrow> invs_at plan_inv_seq (time_index i) \<subseteq> MS i \<Longrightarrow> \<Union> (pre ` happ_at plan_happ_seq (time_index i)) \<subseteq> MS i \<Longrightarrow> thesis"
  shows thesis
  apply (insert assms(1)) unfolding valid_state_sequence_def valid_state_sequence_def Let_def
  apply (drule spec)
  apply (drule mp[OF _ assms(2)])
  apply (erule conjE)+
  using assms(3) by blast

lemma valid_state_sequenceI:
  assumes "\<And>i. i < length htpl \<Longrightarrow> apply_effects (happ_at plan_happ_seq (time_index i)) (MS i) = MS (Suc i)" 
      and "\<And>i. i < length htpl \<Longrightarrow> invs_at plan_inv_seq (time_index i) \<subseteq> MS i" 
      and "\<And>i. i < length htpl \<Longrightarrow> \<Union> (pre ` happ_at plan_happ_seq (time_index i)) \<subseteq> MS i"
  shows "valid_state_sequence MS"
  using assms unfolding valid_state_sequence_def by simp
text \<open>Time\<close>
    
lemma time_index_bij_betw_list: "bij_betw time_index {n. n < length htpl} (set htpl)"
  using bij_betw_nth distinct_sorted_list_of_set htpl_def[symmetric] lessThan_def time_index_def
  by metis

lemma time_index_inj_on_list: "inj_on time_index {n. n < length htpl}" 
  using bij_betw_def time_index_bij_betw_list by blast

lemma time_index_img_list: "time_index ` {n. n < length htpl} = set htpl"
  using time_index_bij_betw_list unfolding bij_betw_def by blast

lemma card_htps_len_htpl: "card htps = length htpl" unfolding htpl_def by simp

lemmas time_index_strict_sorted_list = strict_sorted_list_of_set[of htps, 
    simplified htpl_def[symmetric], THEN sorted_wrt_nth_less, simplified time_index_def[symmetric]]

lemma sorted_htpl: "sorted_wrt (<) htpl" unfolding htpl_def by simp

lemma time_index_strict_mono_on_list: 
  "strict_mono_on {n. n < length htpl} time_index" 
  using time_index_strict_sorted_list unfolding monotone_on_def time_index_def
  by blast

lemmas time_index_sorted_list = sorted_list_of_set(2)[of htps, simplified htpl_def[symmetric], 
    THEN sorted_nth_mono, simplified time_index_def[symmetric]]

lemma time_index_strict_sorted_list':
  assumes i: "i < length htpl"
      and ti: "time_index i < time_index j"
    shows "i < j"
proof (rule ccontr)
  assume "\<not> i < j"
  hence "j \<le> i" by simp
  hence "time_index j \<le> time_index i" using i time_index_sorted_list by simp
  thus False using ti by simp
qed

lemma time_index_sorted_list':
  assumes i: "i < length htpl"
      and ti: "time_index i \<le> time_index j"
    shows "i \<le> j"
proof (rule ccontr)
  assume "\<not> i \<le> j"
  hence "j < i" by simp
  hence "time_index j < time_index i" using i time_index_strict_sorted_list  by simp
  thus False using ti by simp
qed

lemma time_index_mono_on_list:
  "mono_on {n. n < length htpl} time_index" 
  using time_index_sorted_list unfolding monotone_on_def by auto

lemma no_non_indexed_time_points: 
  assumes a: "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'. (time_index l) < t' \<and> t' < (time_index (Suc l)) \<and> t' \<in> set htpl)"
proof (rule notI)
  assume "\<exists>t'>time_index l. t' < time_index (Suc l) \<and> t' \<in> set htpl"
  with time_index_bij_betw_list
  obtain l' where
    l': "l' < length htpl"
    "time_index l < time_index l'"
    "time_index l' < time_index (Suc l)"
    unfolding time_index_def
    by (metis in_set_conv_nth)
  
  have "l' < (Suc l)" using l'(1, 3) time_index_strict_sorted_list' by simp
  moreover
  have "l < l'" using l'(2) time_index_strict_sorted_list' a by simp
  ultimately
  show "False" by simp
qed

text \<open>Relating ideas of plan validity\<close>

lemma anno_trans: 
  "pre (at_start a) = pre_imp (AtStart a)"
  "pre (at_end a) = pre_imp (AtEnd a)"
  "adds (at_start a) = add_imp (AtStart a)"
  "adds (at_end a) = add_imp (AtEnd a)"
  "dels (at_start a) = del_imp (AtStart a)"
  "dels (at_end a) = del_imp (AtEnd a)"
  unfolding pre_imp_def add_imp_def del_imp_def by simp+

lemma mutex_trans:
  "mutex_snap_action (at_start a) (at_start b) \<longleftrightarrow> mutex_annotated_action (AtStart a) (AtStart b)"
  "mutex_snap_action (at_start a) (at_end b) \<longleftrightarrow> mutex_annotated_action (AtStart a) (AtEnd b)"
  "mutex_snap_action (at_end a) (at_start b) \<longleftrightarrow> mutex_annotated_action (AtEnd a) (AtStart b)"
  "mutex_snap_action (at_end a) (at_end b) \<longleftrightarrow> mutex_annotated_action (AtEnd a) (AtEnd b)" 
  unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans[symmetric] by blast+

text \<open>When the domain map is injective there are no duplicate plan actions (weaker than no
self-overlap). Two transfer lemmas relate the @{const ran}-quantified pairwise condition to the
@{const dom}-quantified one; @{text inj_mutex_def} is then immediate.\<close>
lemma ran_pair_imp_dom_pair:
  assumes inj: "inj_on \<pi> (dom \<pi>)"
      and ran: "\<And>a ta da b tb db.
        (a, ta, da) \<in> ran \<pi> \<Longrightarrow> (b, tb, db) \<in> ran \<pi> \<Longrightarrow> (a, ta, da) \<noteq> (b, tb, db)
          \<Longrightarrow> P a ta da b tb db"
      and ij: "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j"
      and \<pi>ij: "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)"
    shows "P a ta da b tb db"
proof -
  have "\<pi> i \<noteq> \<pi> j" by (rule inj_on_contraD[OF inj ij(3,1,2)])
  hence ne: "(a, ta, da) \<noteq> (b, tb, db)" using \<pi>ij by simp
  have "(a, ta, da) \<in> ran \<pi>" "(b, tb, db) \<in> ran \<pi>" using \<pi>ij by (auto simp: ran_def)
  thus ?thesis using ran ne by blast
qed

lemma dom_pair_imp_ran_pair:
  assumes dom: "\<And>i j.
        i \<in> dom \<pi> \<Longrightarrow> j \<in> dom \<pi> \<Longrightarrow> i \<noteq> j
          \<Longrightarrow> \<pi> i = Some (a, ta, da) \<Longrightarrow> \<pi> j = Some (b, tb, db) \<Longrightarrow> P a ta da b tb db"
      and ran: "(a, ta, da) \<in> ran \<pi>" "(b, tb, db) \<in> ran \<pi>" "(a, ta, da) \<noteq> (b, tb, db)"
    shows "P a ta da b tb db"
proof -
  obtain i where i: "\<pi> i = Some (a, ta, da)" using ran(1) unfolding ran_def by blast
  obtain j where j: "\<pi> j = Some (b, tb, db)" using ran(2) unfolding ran_def by blast
  have "i \<noteq> j" using i j ran(3) by auto
  moreover have "i \<in> dom \<pi>" "j \<in> dom \<pi>" using i j by (auto simp: dom_def)
  ultimately show ?thesis using dom i j by blast
qed

text \<open>Intro/elim/dest rules for the two mutex-validity bundles -- each a pairwise condition plus a
duration-0 self-pair condition -- so callers reason through named facts instead of @{command unfolding}
the definitions and re-deriving the nested quantifiers.\<close>
lemma mutex_valid_plan_altI:
  assumes "\<And>i j a ta da b tb db.
            i \<in> dom \<pi> \<Longrightarrow> j \<in> dom \<pi> \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<pi> i = Some (a, ta, da) \<Longrightarrow> \<pi> j = Some (b, tb, db)
              \<Longrightarrow> mutex_sched a ta da b tb db"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> d = 0 \<or> d < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a)"
    shows "mutex_valid_plan_alt"
  unfolding mutex_valid_plan_alt_def using assms by fastforce

lemma mutex_valid_plan_altD1:
  assumes "mutex_valid_plan_alt"
      and "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)"
    shows "mutex_sched a ta da b tb db"
  using assms unfolding mutex_valid_plan_alt_def by blast

lemma mutex_valid_plan_altD2:
  assumes "mutex_valid_plan_alt" and "(a, t, d) \<in> ran \<pi>" "d = 0 \<or> d < \<epsilon>"
    shows "\<not> mutex_snap_action (at_start a) (at_end a)"
  using assms unfolding mutex_valid_plan_alt_def by fastforce

lemma mutex_valid_plan_altE:
  assumes "mutex_valid_plan_alt"
  obtains "\<And>i j a ta da b tb db.
            i \<in> dom \<pi> \<Longrightarrow> j \<in> dom \<pi> \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<pi> i = Some (a, ta, da) \<Longrightarrow> \<pi> j = Some (b, tb, db)
              \<Longrightarrow> mutex_sched a ta da b tb db"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> d = 0 \<or> d < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a)"
  using assms by (blast dest: mutex_valid_plan_altD1 mutex_valid_plan_altD2)

lemma mutex_valid_plan_injI:
  assumes "\<And>a ta da b tb db.
            (a, ta, da) \<in> ran \<pi> \<Longrightarrow> (b, tb, db) \<in> ran \<pi> \<Longrightarrow> (a, ta, da) \<noteq> (b, tb, db)
              \<Longrightarrow> mutex_sched a ta da b tb db"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> d = 0 \<or> d < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a)"
    shows "mutex_valid_plan_inj"
  unfolding mutex_valid_plan_inj_def using assms by fastforce

lemma mutex_valid_plan_injD1:
  assumes "mutex_valid_plan_inj"
      and "(a, ta, da) \<in> ran \<pi>" "(b, tb, db) \<in> ran \<pi>" "(a, ta, da) \<noteq> (b, tb, db)"
    shows "mutex_sched a ta da b tb db"
  using assms unfolding mutex_valid_plan_inj_def by blast

lemma mutex_valid_plan_injD2:
  assumes "mutex_valid_plan_inj" and "(a, t, d) \<in> ran \<pi>" "d = 0 \<or> d < \<epsilon>"
    shows "\<not> mutex_snap_action (at_start a) (at_end a)"
  using assms unfolding mutex_valid_plan_inj_def by fastforce

lemma mutex_valid_plan_injE:
  assumes "mutex_valid_plan_inj"
  obtains "\<And>a ta da b tb db.
            (a, ta, da) \<in> ran \<pi> \<Longrightarrow> (b, tb, db) \<in> ran \<pi> \<Longrightarrow> (a, ta, da) \<noteq> (b, tb, db)
              \<Longrightarrow> mutex_sched a ta da b tb db"
      and "\<And>a t d. (a, t, d) \<in> ran \<pi> \<Longrightarrow> d = 0 \<or> d < \<epsilon> \<Longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a)"
  using assms by (blast dest: mutex_valid_plan_injD1 mutex_valid_plan_injD2)

lemma inj_mutex_def:
  assumes inj: "inj_on \<pi> (dom \<pi>)"
  shows "mutex_valid_plan = mutex_valid_plan_inj"
  unfolding mutex_valid_plan_eq
proof (rule iffI)
  assume A: "mutex_valid_plan_alt"
  show "mutex_valid_plan_inj"
  proof (rule mutex_valid_plan_injI)
    show "mutex_sched a ta da b tb db"
      if r: "(a, ta, da) \<in> ran \<pi>" "(b, tb, db) \<in> ran \<pi>" "(a, ta, da) \<noteq> (b, tb, db)"
      for a ta da b tb db
    proof (rule dom_pair_imp_ran_pair[OF _ r])
      fix i j assume "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j"
        "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)"
      thus "mutex_sched a ta da b tb db" by (rule mutex_valid_plan_altD1[OF A])
    qed
  next
    show "\<not> mutex_snap_action (at_start a) (at_end a)"
      if "(a, t, d) \<in> ran \<pi>" "d = 0 \<or> d < \<epsilon>" for a t d
      using that by (rule mutex_valid_plan_altD2[OF A])
  qed
next
  assume B: "mutex_valid_plan_inj"
  show "mutex_valid_plan_alt"
  proof (rule mutex_valid_plan_altI)
    show "mutex_sched a ta da b tb db"
      if ij: "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)"
      for i j a ta da b tb db
    proof (rule ran_pair_imp_dom_pair[OF inj _ ij])
      fix a ta da b tb db
      assume "(a, ta, da) \<in> ran \<pi>" "(b, tb, db) \<in> ran \<pi>" "(a, ta, da) \<noteq> (b, tb, db)"
      thus "mutex_sched a ta da b tb db" by (rule mutex_valid_plan_injD1[OF B])
    qed
  next
    show "\<not> mutex_snap_action (at_start a) (at_end a)"
      if "(a, t, d) \<in> ran \<pi>" "d = 0 \<or> d < \<epsilon>" for a t d
      using that by (rule mutex_valid_plan_injD2[OF B])
  qed
qed

lemma invs_at_plan_inv_seq_alt:
  "invs_at plan_inv_seq t = {p. \<exists>a d t'. p \<in> over_all a \<and> (a, t', d) \<in> ran \<pi> \<and> t' < t \<and> t \<le> t' + d}"
  unfolding invs_at_def plan_inv_seq_def by auto
  
end


text \<open>Numeric plan-level locale: the propositional @{locale temp_plan_defs} merged with the numeric
data of @{locale numeric_action_defs}, sharing the @{locale action_defs} parameters. This is the
@{emph \<open>parallel\<close>} (additive) numeric hierarchy -- the propositional development is untouched. See
@{file \<open>../NUMERIC_PLAN.md\<close>} \<section>3 / \<section>7 (P2).\<close>
locale numeric_temp_plan_defs =
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
  + numeric_action_defs at_start at_end over_all lower upper pre adds dels n_pre n_inv upds
  for at_start :: "'action \<Rightarrow> 'snap_action"
  and at_end   :: "'action \<Rightarrow> 'snap_action"
  and over_all :: "'action \<Rightarrow> 'proposition set"
  and lower    :: "'action \<rightharpoonup> ('time::time) lower_bound"
  and upper    :: "'action \<rightharpoonup> 'time upper_bound"
  and pre      :: "'snap_action \<Rightarrow> 'proposition set"
  and adds     :: "'snap_action \<Rightarrow> 'proposition set"
  and dels     :: "'snap_action \<Rightarrow> 'proposition set"
  and init     :: "'proposition set"
  and goal     :: "'proposition set"
  and \<epsilon>        :: "'time"
  and \<pi>        :: "('i, 'action, 'time) temp_plan"
  and n_pre    :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp set"
  and n_inv    :: "'action \<Rightarrow> ('n, 'r) comp set"
  and upds     :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) set" +
  fixes num_init :: "'n \<rightharpoonup> 'r"
    and num_goal :: "('n, 'r) comp set"
begin

text \<open>Actions whose @{term over_all} interval is active at @{term t} (cf. @{const plan_inv_seq}).\<close>
definition active_actions :: "'time \<Rightarrow> 'action set" where
  "active_actions t = {a |a tt d. (a, tt, d) \<in> ran \<pi> \<and> tt < t \<and> t \<le> tt + d}"

text \<open>Numeric state-sequence validity. The propositional conjuncts are exactly
@{const valid_state_sequence}'s on the @{term fst} projection; the numeric conjuncts thread the
valuation through @{const happening_num_update_set}, check each happening snap's numeric precondition
against the pre-state valuation, and check every active @{term over_all} numeric invariant. With
@{term \<open>n_pre = (\<lambda>_. {})\<close>} / @{term \<open>n_inv = (\<lambda>_. {})\<close>} / @{term \<open>upds = (\<lambda>_. {})\<close>} the numeric conjuncts
degenerate (identity update, vacuous checks), recovering the propositional semantics -- the migration
lemma (next).\<close>
definition num_valid_state_sequence ::
  "(nat \<Rightarrow> ('proposition, 'n, 'r) num_state) \<Rightarrow> bool" where
"num_valid_state_sequence M \<equiv> (
  let t = time_index; Inv = plan_inv_seq; B = plan_happ_seq in
    (\<forall>i. i < length htpl \<longrightarrow> (
      let S = happ_at B (t i); pres = \<Union>(pre ` S); invs = invs_at Inv (t i) in
        apply_effects S (fst (M i)) = fst (M (Suc i))
        \<and> invs \<subseteq> fst (M i)
        \<and> pres \<subseteq> fst (M i)
        \<and> happening_num_update_set S (snd (M i)) = snd (M (Suc i))
        \<and> (\<forall>s \<in> S. sat_comps (snd (M i)) (n_pre s))
        \<and> (\<forall>a \<in> active_actions (t i). sat_comps (snd (M i)) (n_inv a)))))
"

text \<open>With no numeric effects, a happening's numeric update is the identity -- the degenerate case
behind the migration lemma.\<close>
lemma happening_num_update_set_id:
  assumes upd: "upds = (\<lambda>_. {})" and fin: "finite S"
  shows "happening_num_update_set S v = v"
proof -
  have sw: "snap_writes a = {}" for a
    by (rule snap_writes_empty) (simp add: upd)
  have snid: "snap_num_update a w = w" for a w
    by (rule snap_num_update_empty) (simp add: upd)
  have ccomm: "comp_fun_commute_on T snap_num_update" for T :: "'snap_action set"
  proof (rule comp_fun_commute_on_snap_num_update)
    show "upds_functional (upds a)" if "a \<in> T" for a
      by (simp add: upd upds_functional_def)
    show "\<not> num_mutex_snap_action a b" if "a \<in> T" "b \<in> T" "a \<noteq> b" for a b
      by (simp add: num_mutex_snap_action_def sw)
  qed
  show ?thesis
    using fin unfolding happening_num_update_set_def
  proof (induction S rule: finite_induct)
    case empty
    show ?case by simp
  next
    case (insert a S)
    interpret comp_fun_commute_on "insert a S" snap_num_update by (rule ccomm)
    have "Finite_Set.fold snap_num_update v (insert a S)
            = snap_num_update a (Finite_Set.fold snap_num_update v S)"
      using insert.hyps by simp
    also have "\<dots> = Finite_Set.fold snap_num_update v S" by (simp add: snid)
    also have "\<dots> = v" using insert.IH .
    finally show ?case .
  qed
qed

text \<open>**Migration lemma** (the collapse go/no-go). With empty numeric data the numeric state-sequence
validity is @{emph \<open>definitionally\<close>} the propositional one on the @{term fst} projection, plus a
constant valuation. So the numeric semantics conservatively generalises the propositional one: every
propositional plan lifts (pick any constant valuation), and certifying the empty-numeric task is the
old certification. This is the clean signal that the parallel hierarchy can be collapsed by promotion
+ retirement (NUMERIC_PLAN \<section> "How would you collapse"). Needs finite happenings (true for a finite
plan).\<close>
lemma num_valid_state_sequence_empty:
  assumes upd: "upds = (\<lambda>_. {})" and npre: "n_pre = (\<lambda>_. {})" and ninv: "n_inv = (\<lambda>_. {})"
      and fin: "\<And>i. i < length htpl \<Longrightarrow> finite (happ_at plan_happ_seq (time_index i))"
  shows "num_valid_state_sequence M
           \<longleftrightarrow> valid_state_sequence (\<lambda>i. fst (M i))
               \<and> (\<forall>i < length htpl. snd (M i) = snd (M (Suc i)))"
proof -
  have num: "happening_num_update_set (happ_at plan_happ_seq (time_index i)) (snd (M i)) = snd (M i)"
    if "i < length htpl" for i
    by (rule happening_num_update_set_id[OF upd fin[OF that]])
  show ?thesis
    unfolding num_valid_state_sequence_def valid_state_sequence_def Let_def
    by (auto simp: num npre ninv sat_comps_def)
qed

text \<open>Numeric mutual-exclusivity of a plan: the propositional @{const mutex_valid_plan} @{emph \<open>and\<close>}
the same \<epsilon>-separation discipline for @{const num_mutex_snap_action} -- numerically interfering snaps
(write/write or read/write) must also be \<ge>\<epsilon> apart (incl. the @{term \<open>at_start a\<close>}/@{term \<open>at_end a\<close>}
self-pair when @{term \<open>d = 0\<close>}/@{term \<open>d < \<epsilon>\<close>}). It is exactly this that lets a happening contain only
commuting snaps (so @{const happening_num_update_set} is order-independent there).\<close>
definition num_mutex_valid_plan :: bool where
"num_mutex_valid_plan \<equiv> mutex_valid_plan \<and>
  (\<forall>i j a ta da b tb db sa sb t u.
    i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j
    \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db)
    \<and> (sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da)
    \<and> (sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db)
    \<and> (t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u)
    \<longrightarrow> \<not> num_mutex_snap_action sa sb)
  \<and> (\<forall>(a, t, d) \<in> ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> num_mutex_snap_action (at_start a) (at_end a))
"

text \<open>Migration: with no numeric effects every @{const num_mutex_snap_action} is false, so numeric
mutex-validity collapses to the propositional one.\<close>
lemma num_mutex_valid_plan_empty:
  assumes "upds = (\<lambda>_. {})"
  shows "num_mutex_valid_plan \<longleftrightarrow> mutex_valid_plan"
  using num_mutex_snap_action_empty[OF assms]
  unfolding num_mutex_valid_plan_def by simp

text \<open>Numeric plan validity (cf. @{const valid_plan}): a numeric state sequence valid throughout,
starting from @{term init} / @{term num_init} and reaching @{term goal} with the numeric goal
comparisons @{term num_goal} holding at the end, under numeric mutex-validity.\<close>
definition num_valid_plan :: bool where
"num_valid_plan \<equiv> \<exists>M.
    num_valid_state_sequence M
    \<and> fst (M 0) = init
    \<and> snd (M 0) = num_init
    \<and> goal \<subseteq> fst (M (length htpl))
    \<and> sat_comps (snd (M (length htpl))) num_goal
    \<and> durations_ge_0
    \<and> durations_valid
    \<and> num_mutex_valid_plan
    \<and> finite_plan"

text \<open>**Migration lemma for plan validity** (the capstone of the migration story). With empty numeric
data and no numeric goal, numeric plan validity is the propositional one: forward via the two component
migrations; backward by the constant-valuation witness @{term \<open>M i = (M' i, num_init)\<close>}. (Finite
happenings -- the @{term finhap} hypothesis -- follow from @{const finite_plan} via
@{text temp_plan_finite.finite_happ_seq}.)\<close>
lemma num_valid_plan_empty:
  assumes upd: "upds = (\<lambda>_. {})" and npre: "n_pre = (\<lambda>_. {})" and ninv: "n_inv = (\<lambda>_. {})"
      and ngoal: "num_goal = {}"
      and finhap: "\<And>i. i < length htpl \<Longrightarrow> finite (happ_at plan_happ_seq (time_index i))"
  shows "num_valid_plan \<longleftrightarrow> valid_plan"
proof
  assume "num_valid_plan"
  then obtain M where
      M1: "num_valid_state_sequence M" and M2: "fst (M 0) = init"
  and M4: "goal \<subseteq> fst (M (length htpl))"
  and M6: "durations_ge_0" and M7: "durations_valid"
  and M8: "num_mutex_valid_plan" and M9: "finite_plan"
    unfolding num_valid_plan_def by blast
  have vss: "valid_state_sequence (\<lambda>i. fst (M i))"
    using num_valid_state_sequence_empty[OF upd npre ninv finhap] M1 by blast
  have mut: "mutex_valid_plan"
    using num_mutex_valid_plan_empty[OF upd] M8 by blast
  show "valid_plan"
    unfolding valid_plan_def
    using vss mut M2 M4 M6 M7 M9 by (intro exI[of _ "\<lambda>i. fst (M i)"]) auto
next
  assume "valid_plan"
  then obtain M' where
      P1: "valid_state_sequence M'" and P2: "M' 0 = init"
  and P4: "goal \<subseteq> M' (length htpl)"
  and P6: "durations_ge_0" and P7: "durations_valid"
  and P8: "mutex_valid_plan" and P9: "finite_plan"
    unfolding valid_plan_def by blast
  define M where "M = (\<lambda>i. (M' i, num_init))"
  have fstM: "fst (M i) = M' i" for i by (simp add: M_def)
  have sndM: "snd (M i) = num_init" for i by (simp add: M_def)
  have nvss: "num_valid_state_sequence M"
    using num_valid_state_sequence_empty[OF upd npre ninv finhap] P1 by (simp add: fstM sndM)
  have nmut: "num_mutex_valid_plan" using num_mutex_valid_plan_empty[OF upd] P8 by blast
  show "num_valid_plan"
    unfolding num_valid_plan_def
  proof (intro exI[of _ M] conjI)
    show "num_valid_state_sequence M" by (rule nvss)
    show "fst (M 0) = init" using P2 by (simp add: fstM)
    show "snd (M 0) = num_init" by (simp add: sndM)
    show "goal \<subseteq> fst (M (length htpl))" using P4 by (simp add: fstM)
    show "sat_comps (snd (M (length htpl))) num_goal" by (simp add: ngoal sat_comps_def)
    show "durations_ge_0" by (rule P6)
    show "durations_valid" by (rule P7)
    show "num_mutex_valid_plan" by (rule nmut)
    show "finite_plan" by (rule P9)
  qed
qed

end


locale temp_plan_for_action_defs =
  temp_plan_defs +
  temp_planning_problem_and_actions
begin
  definition "plan_actions_in_problem \<equiv> plan_actions \<subseteq> actions"
end

locale temp_plan_for_actions = 
  temp_plan_for_action_defs +
  assumes pap: plan_actions_in_problem
begin
lemma acts_in_prob: "(a, t, d) \<in> ran \<pi> \<Longrightarrow> a \<in> actions" using pap 
  unfolding plan_actions_in_problem_def plan_actions_def by auto
end

locale temp_plan_finite = temp_plan_defs +
  assumes fp: finite_plan
begin

lemma finite_plan: 
  "finite (dom \<pi>)"
  "finite (ran \<pi>)"
  using fp finite_plan_def finite_ran by auto 
text \<open>Finite happening sequences\<close>

lemma finite_acts_imp_finite_happ_seq: "finite (plan_happ_seq)"
proof -
 have 1: "finite ((\<lambda>(a, t, d). (t, at_start a)) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). (t + d, at_end a)) ` (ran \<pi>))"
   using finite_plan by simp+
  moreover
  have "(\<lambda>(a, t, d). (t, at_start a)) ` (ran \<pi>) = {(t, at_start a) |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). (t + d, at_end a)) ` (ran \<pi>)  = {(t + d, at_end a) |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite plan_happ_seq" unfolding plan_happ_seq_def by auto
qed

lemma finite_happ_seq: "finite plan_happ_seq"
  using finite_acts_imp_finite_happ_seq finite_plan finite_plan_def by blast

text \<open>Indexing of timepoints and such with respect to a finite plan\<close>

lemma finite_htps: "finite htps"
proof -
 have 1: "finite ((\<lambda>(a, t, d). t) ` (ran \<pi>))" 
    "finite ((\<lambda>(a, t, d). t + d) ` (ran \<pi>))"
   using finite_plan by simp+
  moreover
  have "(\<lambda>(a, t, d). t) ` (ran \<pi>) = {t |a t d. (a, t, d) \<in> ran \<pi>}" by force
  moreover
  have " (\<lambda>(a, t, d). t + d) ` (ran \<pi>)  = {t + d |a t d. (a, t, d) \<in> ran \<pi>}" by force
  ultimately
  show "finite htps" unfolding htps_def by auto
qed


lemma htps_set_htpl: "htps = set htpl"
  using finite_htps htpl_def set_sorted_list_of_set[symmetric] by simp

lemma time_index_bij_betw_set: "bij_betw time_index {n. n < card htps} htps"
proof -
  have 3: "distinct htpl" unfolding htpl_def by simp
  show "bij_betw time_index {n. n < card htps} htps"
    using htps_set_htpl
    using time_index_bij_betw_list 
    using card_htps_len_htpl by auto
qed

lemma time_index_inj_on_set: "inj_on time_index {n. n < card htps}" 
  using time_index_bij_betw_set finite_plan bij_betw_def by blast

lemma time_index_img_set:
  "time_index ` {n. n < card htps} = htps" 
  using time_index_bij_betw_set finite_plan unfolding bij_betw_def by blast

lemmas time_index_strict_sorted_set = time_index_strict_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set = time_index_sorted_list[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_strict_sorted_set' = time_index_strict_sorted_list'[simplified card_htps_len_htpl[symmetric]]
lemmas time_index_sorted_set' = time_index_sorted_list'[simplified card_htps_len_htpl[symmetric]]

lemmas time_index_sorted = time_index_sorted_list time_index_sorted_set time_index_strict_sorted_list time_index_strict_sorted_set
  time_index_sorted_list' time_index_sorted_set' time_index_strict_sorted_list' time_index_strict_sorted_set'

lemma time_indexI_htps:
  assumes "t \<in> htps"
    shows "\<exists>i < card htps. time_index i = t"
  using time_index_img_set assms by force

lemma time_indexI_htpl:    
  assumes "t \<in> set (htpl)"
    shows "\<exists>i < length htpl. time_index i = t"
  using time_index_img_list assms by force

lemma time_index_htplD:
  assumes "i < length htpl"
    shows "time_index i \<in> set htpl" 
  using nth_mem assms unfolding time_index_def by blast

lemma time_index_htpsD:
  assumes "i < length htpl"
    shows "time_index i \<in> htps" 
  using time_index_img_set assms card_htps_len_htpl by auto
  

lemma exists_snaps_at_time_index:
  assumes "i < length htpl"
  shows "\<exists>a. (time_index i, at_start a) \<in> plan_happ_seq \<or> (time_index i, at_end a) \<in> plan_happ_seq"
  apply (insert time_index_htpsD[OF assms])
  apply (erule htpsE)
  subgoal for a t d
    apply (rule exI[of _ a])
    apply (rule disjI1)
    unfolding plan_happ_seq_def by blast
  subgoal for a t d
    apply (rule exI[of _ a])
    apply (rule disjI2)
    unfolding plan_happ_seq_def by blast
  done
lemma snaps_at_time_index_cases:
  assumes "i < length htpl"
    and "\<And>a. (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_snaps_at_time_index by blast

lemma snaps_at_time_index_exhaustive_cases:
  assumes "i < length htpl"
    and "\<And>a. (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<notin> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. (time_index i, at_start a) \<notin> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_snaps_at_time_index by blast
lemma no_actions_between_indexed_timepoints: 
  assumes "(Suc l) < length htpl"
  shows "\<not> (\<exists>t'>time_index l. t' < time_index (Suc l) \<and> a \<in> happ_at plan_happ_seq t')"
  using no_non_indexed_time_points a_in_B_iff_t_in_htps finite_htps assms
  unfolding htpl_def by auto


lemma empty_acts_if_empty_htpl: 
  assumes len: "length htpl = 0"
  shows "card (ran \<pi>) = 0"
proof -
  { assume a: "card (ran \<pi>) \<noteq> 0"
    hence "card (ran \<pi>) > 0" by blast
    hence fr: "finite (ran \<pi>)" using card_ge_0_finite  by blast
    hence "ran \<pi> \<noteq> {}" using card_0_eq a by simp
    hence "\<exists>s. s \<in> ran \<pi>" by auto
    hence "\<exists>x. x \<in> htps" unfolding htps_def by auto
    hence "\<exists>x. x \<in> set htpl" using htps_set_htpl by blast 
    with len
    have False by simp
  }
  thus "card (ran \<pi>) = 0" by blast
qed

lemma empty_acts_if_empty_htpl_finite:
  assumes len: "length htpl = 0"
      and fp: "finite_plan"
    shows "ran \<pi> = {}"
  using assms empty_acts_if_empty_htpl finite_ran finite_plan_def by fastforce

lemma no_actions_after_final_timepoint:
  assumes "0 < length htpl"
    "time_index (length htpl - 1) < t"
  shows "happ_at plan_happ_seq t = {}"
proof -
  { assume "happ_at plan_happ_seq t \<noteq> {}"
    then obtain h where
      "(t, h) \<in> plan_happ_seq"
      "t \<in> htps" using a_in_B_iff_t_in_htps by blast
    hence "t \<in> set htpl" using htps_set_htpl assms by blast
    then obtain l where
      "l < length htpl"
      "time_index l = t" using time_index_img_list by force
    with time_index_sorted_list
    have "t \<le> time_index (length htpl - 1)" using assms time_index_def by auto
    with assms
    have False by simp
  }
  thus ?thesis by blast
qed
end

locale temp_plan_dg0 = temp_plan_defs + 
  assumes dg0: durations_ge_0

locale temp_plan_mutex = temp_plan_defs +
  assumes mutex_valid_plan: "mutex_valid_plan"

subsubsection \<open>Plan validity\<close>
text \<open>Plan validity is just a proposition\<close>
locale valid_temp_plan = temp_plan_defs +
  assumes vp: valid_plan
begin
subsubsection \<open>Finite Plans\<close>

lemma valid_plan_state_seq: "\<exists>M. valid_state_sequence M \<and> M 0 = init \<and> goal \<subseteq> M (length htpl)"
  and valid_plan_durs: "durations_ge_0" "durations_valid"
  and valid_plan_mutex: "mutex_valid_plan"
  and valid_plan_finite: "finite_plan" using vp unfolding valid_plan_def by blast+

sublocale temp_plan_finite using valid_plan_finite vp 
  by unfold_locales

sublocale temp_plan_dg0 using valid_plan_durs by unfold_locales blast

sublocale temp_plan_mutex using valid_plan_mutex by unfold_locales blast

subsubsection \<open>Time index and happenings\<close>

lemma time_index_happ_at:
  assumes "i < length htpl"
  shows "\<exists>h. (time_index i, h) \<in> plan_happ_seq"
  apply (insert assms)
  apply (frule time_index_htpsD)
  apply (erule htpsE)
   apply (rule exI)
  by (auto intro: in_happ_seqI)

end

text \<open>Plan validity is equivalent if actions behave equivalently\<close>

locale plan_validity_equivalence = temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
    double_action_defs at_start at_end over_all lower upper pre adds dels at_start' at_end' over_all' pre' adds' dels'
    for at_start::"'action  \<Rightarrow> 'snap_action"
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::"'proposition set"
    and goal::"'proposition set"
    and \<epsilon>::"'time"
    and \<pi>::"('i, 'action, 'time::time) temp_plan" 
    and at_start'::"'action \<Rightarrow> 'snap_action_1"
    and at_end'::  "'action  \<Rightarrow> 'snap_action_1"
    and over_all'::"'action  \<Rightarrow> 'proposition set"
    and pre'::     "'snap_action_1 \<Rightarrow> 'proposition set"
    and adds'::    "'snap_action_1 \<Rightarrow> 'proposition set"
    and dels'::    "'snap_action_1 \<Rightarrow> 'proposition set" +
  fixes init':: "'proposition set"
    and goal':: "'proposition set"
  assumes start_snap_replacement: 
    "\<forall>a \<in> plan_actions. pre (at_start a) = pre' (at_start' a)"
    "\<forall>a \<in> plan_actions. adds (at_start a) = adds' (at_start' a)"
    "\<forall>a \<in> plan_actions. dels (at_start a) = dels' (at_start' a)"
    and end_snap_replacement:
    "\<forall>a \<in> plan_actions. pre (at_end a) = pre' (at_end' a)"
    "\<forall>a \<in> plan_actions. adds (at_end a) = adds' (at_end' a)"
    "\<forall>a \<in> plan_actions. dels (at_end a) = dels' (at_end' a)"
    and inv_replacement:
    "\<forall>a \<in> plan_actions. over_all a = over_all' a"
    and init_and_goal_eq: "init = init'" "goal = goal'"
begin


sublocale plan2: temp_plan_defs at_start' at_end' over_all' lower upper pre' adds' dels' init' goal' \<epsilon> \<pi>
  by standard

lemma f_functionally_equiv_1: 
  assumes "\<forall>a \<in> plan_actions. f (at_start a) = f' (at_start' a)"
      and "\<forall>a \<in> plan_actions. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f ` happ_at plan_happ_seq t) \<subseteq> \<Union>(f' ` plan2.happ_at plan2.plan_happ_seq t)"
proof (rule subsetI)
  fix x
  assume "x \<in> \<Union> (f ` happ_at plan_happ_seq t)"
  then obtain h where
    x: "x \<in> f h"
    and x_happ: "(t, h) \<in> plan_happ_seq" by blast
  have "\<exists>h. x \<in> f' h \<and> h \<in> plan2.happ_at plan2.plan_happ_seq t" 
    apply (cases rule: in_happ_seqE[OF x_happ])
    using assms x unfolding plan2.plan_happ_seq_def by (blast elim: plan_rangeE)+
  thus "x \<in> \<Union> (f' ` plan2.happ_at plan2.plan_happ_seq t)" by blast
qed

lemma f_functionally_equiv_2:
  assumes "\<forall>a \<in> plan_actions. f (at_start a) = f' (at_start' a)"
      and "\<forall>a \<in> plan_actions. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f' ` plan2.happ_at plan2.plan_happ_seq t) \<subseteq> \<Union>(f ` happ_at plan_happ_seq t)"
proof (rule subsetI)
  fix x
  assume "x \<in> \<Union> (f' ` plan2.happ_at plan2.plan_happ_seq t)"
  then obtain h where
    x: "x \<in> f' h"
    and x_happ: "(t, h) \<in> plan2.plan_happ_seq" by blast
  have "\<exists>h. x \<in> f h \<and> h \<in> happ_at plan_happ_seq t" 
    apply (cases rule: plan2.in_happ_seqE[OF x_happ])
    using assms x unfolding plan_happ_seq_def by (blast elim: plan_rangeE)+
  thus "x \<in> \<Union> (f ` happ_at plan_happ_seq t)" by blast
qed

lemma f_functionally_equiv:
  assumes "\<forall>a \<in> plan_actions. f (at_start a) = f' (at_start' a)"
      and "\<forall>a \<in> plan_actions. f (at_end a) = f' (at_end' a)"
    shows "\<Union>(f ` happ_at plan_happ_seq t) = \<Union>(f' ` plan2.happ_at plan2.plan_happ_seq t)"
  apply (rule equalityI) using f_functionally_equiv_1[OF assms] f_functionally_equiv_2[OF assms] by auto

lemmas pre_functionally_equiv = f_functionally_equiv[OF start_snap_replacement(1) end_snap_replacement(1)]
lemmas adds_functionally_equiv = f_functionally_equiv[OF start_snap_replacement(2) end_snap_replacement(2)]
lemmas dels_functionally_equiv = f_functionally_equiv[OF start_snap_replacement(3) end_snap_replacement(3)]

lemma plan_inv_seq_equiv:
  "plan_inv_seq = plan2.plan_inv_seq"
  using inv_replacement
  unfolding plan_inv_seq_def plan2.plan_inv_seq_def
  unfolding plan_actions_def by blast
    

lemma vss_equiv_if_snaps_functionally_equiv:
  "valid_state_sequence MS \<longleftrightarrow> plan2.valid_state_sequence MS"
  unfolding valid_state_sequence_def plan2.valid_state_sequence_def 
  using adds_functionally_equiv dels_functionally_equiv pre_functionally_equiv 
  unfolding Let_def 
  unfolding apply_effects_def plan2.apply_effects_def 
  unfolding local.invs_at_def plan2.invs_at_def
  using plan_inv_seq_equiv
  by auto
  

lemma in_happ_seq_trans_1:  
  assumes "h \<in> happ_at plan_happ_seq time" 
    shows "\<exists>h' \<in> plan2.happ_at plan2.plan_happ_seq time. pre h = pre' h' \<and> adds h = adds' h' \<and> dels h = dels' h'"
  apply (cases rule: in_happ_seqE[OF assms[simplified]])
  unfolding plan2.plan_happ_seq_def
  using end_snap_replacement start_snap_replacement 
  by (blast elim: plan_rangeE)+

lemma in_happ_seqE1:
  assumes "h \<in> happ_at plan_happ_seq time" 
      and "\<And>h'. h' \<in> plan2.happ_at plan2.plan_happ_seq time \<Longrightarrow> pre h = pre' h' \<Longrightarrow> adds h = adds' h' \<Longrightarrow> dels h = dels' h' \<Longrightarrow> thesis"
    shows thesis
  using in_happ_seq_trans_1 assms by blast

lemma in_happ_seq_trans_2:  
  assumes "h \<in> plan2.happ_at plan2.plan_happ_seq time" 
    shows "\<exists>h' \<in> happ_at plan_happ_seq time. pre h' = pre' h \<and> adds h' = adds' h \<and> dels h' = dels' h"
  apply (rule plan2.in_happ_seqE[OF assms[simplified]])
  unfolding plan_happ_seq_def using start_snap_replacement
  using end_snap_replacement start_snap_replacement by (blast elim: plan_rangeE)+

lemma in_happ_seqE2:  
  assumes "h \<in> plan2.happ_at plan2.plan_happ_seq time" 
      and "\<And>h'. h' \<in> happ_at plan_happ_seq time \<Longrightarrow> pre h' = pre' h \<Longrightarrow> adds h' = adds' h \<Longrightarrow> dels h' = dels' h \<Longrightarrow> thesis"
    shows thesis
  using assms in_happ_seq_trans_2 by blast

lemma mutex_snap_action_equiv:
  assumes a: "a \<in> plan_actions"
      and b: "b \<in> plan_actions"
      and h: "h = at_start a \<and> h' = at_start' a \<or> h = at_end a \<and> h' = at_end' a"
      and i: "i = at_start b \<and> i' = at_start' b \<or> i = at_end b \<and> i' = at_end' b"
    shows "mutex_snap_action h i
    \<longleftrightarrow> acts2.mutex_snap_action h' i'"
proof -
  have "pre h = pre' h'" using h a start_snap_replacement end_snap_replacement by auto
  moreover
  have "adds h = adds' h'" using h a start_snap_replacement end_snap_replacement by auto
  moreover 
  have "dels h = dels' h'" using h a start_snap_replacement end_snap_replacement by auto
  moreover
  have "pre i = pre' i'" using i b start_snap_replacement end_snap_replacement by auto
  moreover
  have "adds i = adds' i'" using i b start_snap_replacement end_snap_replacement by auto
  moreover 
  have "dels i = dels' i'" using i b start_snap_replacement end_snap_replacement by auto
  ultimately
  show ?thesis unfolding mutex_snap_action_def acts2.mutex_snap_action_def by simp
qed

lemma mutex_valid_plan_equiv_if_snaps_functionally_equiv:
  "mutex_valid_plan
\<longleftrightarrow> plan2.mutex_valid_plan"
proof -
  have "(\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a))
    \<longleftrightarrow> (\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> acts2.mutex_snap_action (at_start' a) (at_end' a))"
    using mutex_snap_action_equiv 
    unfolding plan_actions_def
    by fast
  moreover
  have "mutex_sched a ta da b tb db \<longleftrightarrow> plan2.mutex_sched a ta da b tb db" if 
    "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" 
    "\<pi> i = Some (a, ta, da)" 
    "\<pi> j = Some (b, tb, db)" for i j a ta da b tb db
   proof -
     have ab_ran: "\<exists>t d. (a, t, d) \<in> ran \<pi>" "\<exists>t d. (b, t, d) \<in> ran \<pi>" 
       using that ranI by fast+
    show ?thesis 
         proof 
      assume as: "mutex_sched a ta da b tb db"
      have "\<not> acts2.mutex_snap_action sa sb" 
        if "sa = at_start' a \<and> t = ta \<or> sa = at_end' a \<and> t = ta + da" 
           "sb = at_start' b \<and> u = tb \<or> sb = at_end' b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start' a \<and> t = ta" "sb = at_start' b \<and> u = tb" |
          "sa = at_start' a \<and> t = ta" "sb = at_end' b \<and> u = tb + db" | 
          "sa = at_end' a \<and> t = ta + da" "sb = at_start' b \<and> u = tb" |
          "sa = at_end' a \<and> t = ta + da" "sb = at_end' b \<and> u = tb + db" by argo
        thus ?thesis
        proof (cases)
          case 1
          with t as
          have "\<not>mutex_snap_action (at_start a) (at_start b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 1 unfolding plan_actions_def by fast
        next
          case 2
          with t as
          have "\<not>mutex_snap_action (at_start a) (at_end b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 2 unfolding plan_actions_def by fast
        next
          case 3
          with t as
          have "\<not>mutex_snap_action (at_end a) (at_start b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 3 unfolding plan_actions_def by fast
        next
          case 4
          with t as
          have "\<not>mutex_snap_action (at_end a) (at_end b)" 
            unfolding mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 4 unfolding plan_actions_def by fast
        qed
      qed
      thus "plan2.mutex_sched a ta da b tb db" 
        unfolding plan2.mutex_sched_def by blast
    next
      assume as: "plan2.mutex_sched a ta da b tb db"
      have "\<not> mutex_snap_action sa sb" 
        if "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da" 
           "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start a \<and> t = ta" "sb = at_start b \<and> u = tb" |
          "sa = at_start a \<and> t = ta" "sb = at_end b \<and> u = tb + db" | 
          "sa = at_end a \<and> t = ta + da" "sb = at_start b \<and> u = tb" |
          "sa = at_end a \<and> t = ta + da" "sb = at_end b \<and> u = tb + db" by argo
        thus ?thesis
        proof (cases)
          case 1
          with t as
          have "\<not>acts2.mutex_snap_action (at_start' a) (at_start' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 1 unfolding plan_actions_def by fast
        next
          case 2
          with t as
          have "\<not>acts2.mutex_snap_action (at_start' a) (at_end' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 2 unfolding plan_actions_def by fast
        next
          case 3
          with t as
          have "\<not>acts2.mutex_snap_action (at_end' a) (at_start' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 3 unfolding plan_actions_def by fast
        next
          case 4
          with t as
          have "\<not>acts2.mutex_snap_action (at_end' a) (at_end' b)" 
            unfolding plan2.mutex_sched_def by blast
          then show ?thesis using mutex_snap_action_equiv ab_ran 4 unfolding plan_actions_def by fast
        qed
      qed
      thus "mutex_sched a ta da b tb db" 
        unfolding mutex_sched_def by blast
    qed
  qed
  hence "(\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched a ta da b tb db) 
  \<longleftrightarrow> (\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> plan2.mutex_sched a ta da b tb db)" by blast
  ultimately
  show ?thesis unfolding mutex_valid_plan_eq mutex_valid_plan_alt_def plan2.mutex_valid_plan_eq plan2.mutex_valid_plan_alt_def by argo
qed

lemma valid_plan_equiv_if_snaps_functionally_equiv:
  "valid_plan \<longleftrightarrow> plan2.valid_plan"
  unfolding valid_plan_def plan2.valid_plan_def
  using vss_equiv_if_snaps_functionally_equiv mutex_valid_plan_equiv_if_snaps_functionally_equiv
  using init_and_goal_eq
  by simp
end

text \<open>If there is no self overlap, then the mutex condition can be asserted on the annotated action sequence\<close>
locale temp_plan_nso = temp_plan_defs +
  assumes nso: "no_self_overlap"
begin 
  
lemma no_self_overlap_spec:
  assumes "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows
    "\<not>(t \<le> u \<and> u \<le> t + d)"
  using assms nso
  unfolding no_self_overlap_def ran_def by force

lemma no_self_overlap_ran:
  assumes "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows
    "(t > u \<or> u > t + d)"
  using no_self_overlap_spec[OF assms] by fastforce
end

text \<open>The definition of no self overlap also assumes that durations are at least 0\<close>
locale temp_plan_nso_dg0 = temp_plan_nso + 
  temp_plan_dg0
begin

lemma nso_double_act_spec:
  assumes a: "(a, t, d) \<in> ran \<pi>"
    "(a, u, e) \<in> ran \<pi>"
    "t \<noteq> u \<or> d \<noteq> e"
  shows "u + e < t \<or> t + d < u"
proof -
  from no_self_overlap_ran[OF a(1)] no_self_overlap_ran[OF a(2)] a
  have "u < t \<or> t + d < u" "t < u \<or> u + e < t" by blast+
  thus ?thesis by auto
qed

lemma nso_no_double_sched:
  assumes a: "(a, t, d) \<in> ran \<pi>"
    "(a, t, e) \<in> ran \<pi>"
  shows "d = e"
proof -
  from nso_double_act_spec assms
  have "d \<noteq> e \<Longrightarrow> t + e < t \<or> t + d < t" by blast
  with dg0[simplified durations_ge_0_def] a
  show ?thesis by force
qed

lemma nso_no_double_start:
  assumes a: "(a, t, d) \<in> ran \<pi>"
           "(b, t, e) \<in> ran \<pi>"
    and "(a, t, d) \<noteq> (b, t, e)"
  shows "a \<noteq> b"
  using assms nso_no_double_sched by blast

lemma nso_start_end:
  assumes a: "(a, t, d) \<in> ran \<pi>"
           "(b, s, e) \<in> ran \<pi>"
           "(a, t, d) \<noteq> (b, s, e)"
           "t = s + e"
  shows "a \<noteq> b"
proof 
  assume e: "a = b"
  hence "t \<noteq> s \<or> d \<noteq> e" using a by blast
  hence "t + d < s" using nso_double_act_spec[OF a(1) a(2)[simplified e[symmetric]]] a(4) by blast
  moreover
  have "0 \<le> e" "0 \<le> d" using dg0[simplified durations_ge_0_def] a(1,2) by auto
  ultimately
  show False using \<open>t = s + e\<close>
    apply (cases "e \<le> 0") 
    subgoal by auto 
    using linorder_not_less by fastforce
qed

lemma nso_ends:
  assumes  a: "(a, t, d) \<in> ran \<pi>"
           "(b, s, e) \<in> ran \<pi>"
           "(a, t, d) \<noteq> (b, s, e)"
           "t + d = s + e"
  shows "a \<noteq> b"
proof 
  assume e: "a = b"
  have ed: "0 \<le> e" "0 \<le> d" using dg0[simplified durations_ge_0_def] a(1,2) by auto
  moreover
  have "t \<noteq> s \<or> d \<noteq> e" using a e by blast
  then consider "s + e < t" | "t + d < s" 
    using nso_double_act_spec[OF a(1) a(2)[simplified e[symmetric]]] a(4) by blast
  hence "s + e < t + d \<or> t + d < s + e" apply (cases) using ed 
    by (simp add: add.commute add_strict_increasing2)+
  thus False using \<open>t + d = s + e\<close> by simp
qed

lemma nso_imp_inj:
  shows "inj_on \<pi> (dom \<pi>)"
proof -
{ fix i j
    assume i: "i \<in> dom \<pi>" and j: "j \<in> dom \<pi>"
    assume ij: "i \<noteq> j"
    obtain a ta da b tb db where
      pi: "\<pi> i = Some (a, ta, da)"
      "\<pi> j = Some (b, tb, db)"
      using i j by auto
    hence ij_ran: "(a, ta, da) \<in> ran \<pi>"
          "(b, tb, db) \<in> ran \<pi>" 
      by (auto intro: ranI)
    { assume "a = b"
      hence ab: "\<not>(ta \<le> tb \<and> tb \<le> ta + da)"
        and ba: "\<not>(tb \<le> ta \<and> ta \<le> tb + db)" using pi i j ij nso[simplified no_self_overlap_def] 
        by metis+
      consider "tb < ta" | "ta + da < tb" using ab by fastforce
      note lt_case1 = this
      consider "ta < tb" | "tb + db < ta" using ba by fastforce
      note lt_case2 = this
      have "ta \<noteq> tb"
        apply (cases rule: lt_case1; cases rule: lt_case2)
        using dg0[simplified durations_ge_0_def] ij_ran by force+
      }
    with pi
    have "\<pi> i \<noteq> \<pi> j" by auto
  } 
  thus ?thesis unfolding inj_on_def by blast
qed



lemma nso_mutex_eq_nm_anno_act_seq: "mutex_valid_plan \<longleftrightarrow> nm_anno_act_seq"
proof -
  have "mutex_valid_plan_inj \<longleftrightarrow> nm_anno_act_seq"
  proof
    assume mvp: mutex_valid_plan_inj
    have "\<not>mutex_annotated_action a b"
      if ne: "a \<noteq> b \<or> t \<noteq> u" and tu: "t - u < \<epsilon> \<and> u - t < \<epsilon>" 
      and a: "(t, a) \<in> annotated_action_seq" 
      and b: "(u, b) \<in> annotated_action_seq" for a b t u
    proof -
      consider aa ab where "a = AtStart aa" "b = AtStart ab"
        | aa ab where "a = AtStart aa" "b = AtEnd ab"
        | aa ab where "a = AtEnd aa" "b = AtStart ab"
        | aa ab where "a = AtEnd aa" "b = AtEnd ab" 
        by (cases a; cases b; blast)
      thus "\<not>mutex_annotated_action a b" 
      proof cases
        case 1
        with a b
        obtain da db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, u, db) \<in> ran \<pi>" unfolding annotated_action_seq_def by blast 
        have "(aa, t, da) \<noteq> (ab, u, db)" using ne 1 by blast
        hence "mutex_sched aa t da ab u db" using ta tb mvp unfolding mutex_valid_plan_inj_def by blast
        from this[simplified mutex_sched_def] tu
        have "\<not>mutex_snap_action (at_start aa) (at_start ab)" by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 1 .
      next
        case 2
        with a b
        obtain da tb db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, tb, db) \<in> ran \<pi>" "tb + db = u"
          unfolding annotated_action_seq_def by blast
        
        hence da: "0 \<le> da" and db: "0 \<le> db" using dg0 unfolding durations_ge_0_def by blast+
        show ?thesis
        proof (cases "(aa, t, da) = (ab, tb, db)")
          case True
          hence "da < \<epsilon>" using tb(2) tu by auto
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          thus ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa t da ab tb db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" unfolding mutex_sched_def using tu tb(2) by blast
          then show ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 3
        with a b
        obtain ta da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "ta + da = t"
          and tb: "(ab, u, db) \<in> ran \<pi>" 
          unfolding annotated_action_seq_def by fast
        
        show ?thesis
        proof (cases "(aa, ta, da) = (ab, u, db)")
          case True
          hence "da < \<epsilon>" using ta(2) tu by auto
          hence "\<not>mutex_snap_action (at_start aa) (at_end aa)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)"
            using True unfolding mutex_snap_action_def by auto
          thus ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa ta da ab u db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)" unfolding mutex_sched_def using tu ta(2) by blast
          then show ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 4
        with a b
        obtain ta tb da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "t = ta + da"
          and tb: "(ab, tb, db) \<in> ran \<pi>" "u = tb + db" unfolding annotated_action_seq_def by blast 
        hence "(aa, ta, da) \<noteq> (ab, tb, db)" using ne 4 by blast
        hence "mutex_sched aa ta da ab tb db" using ta tb mvp unfolding mutex_valid_plan_inj_def by blast
        hence "\<not>mutex_snap_action (at_end aa) (at_end ab)" unfolding mutex_sched_def using tu ta(2) tb(2) by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 4 by blast
      qed
    qed
    moreover
    have "\<not>mutex_annotated_action a b" 
      if a: "(t, a) \<in> annotated_action_seq" 
      and b: "(t, b) \<in> annotated_action_seq" 
      and ne: "a \<noteq> b" for t a b
    proof -
      consider aa ab where "a = AtStart aa" "b = AtStart ab"
        | aa ab where "a = AtStart aa" "b = AtEnd ab"
        | aa ab where "a = AtEnd aa" "b = AtStart ab"
        | aa ab where "a = AtEnd aa" "b = AtEnd ab" 
        by (cases a; cases b; blast)
      thus "\<not>mutex_annotated_action a b" 
      proof cases
        case 1
        with a b
        obtain da db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, t, db) \<in> ran \<pi>" unfolding annotated_action_seq_def by blast 
        hence "mutex_sched aa t da ab t db" using 1 mvp ne unfolding mutex_valid_plan_inj_def by blast
        from this[simplified mutex_sched_def] 
        have "\<not>mutex_snap_action (at_start aa) (at_start ab)" by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 1 by simp
      next
        case 2
        with a b
        obtain da tb db where
          ta: "(aa, t, da) \<in> ran \<pi>" 
          and tb: "(ab, tb, db) \<in> ran \<pi>" "tb + db = t"
          unfolding annotated_action_seq_def by blast
        
        hence da: "0 \<le> da" and db: "0 \<le> db" using dg0 unfolding durations_ge_0_def by blast+
        show ?thesis
        proof (cases "(aa, t, da) = (ab, tb, db)")
          case True
          hence "da = 0" using tb(2) by simp
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          thus ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa t da ab tb db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_start aa) (at_end ab)" unfolding mutex_sched_def using tb(2) by blast
          then show ?thesis using 2 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 3
        with a b
        obtain ta da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "ta + da = t"
          and tb: "(ab, t, db) \<in> ran \<pi>" 
          unfolding annotated_action_seq_def by fast
        
        show ?thesis
        proof (cases "(aa, ta, da) = (ab, t, db)")
          case True
          hence "da = 0" using ta(2) by auto
          hence "\<not>mutex_snap_action (at_start aa) (at_end aa)" 
            using True ta mvp unfolding mutex_valid_plan_inj_def by auto
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)"
            using True unfolding mutex_snap_action_def by auto
          thus ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        next
          case False
          hence "local.mutex_sched aa ta da ab t db" using mvp[simplified mutex_valid_plan_inj_def] ta tb by simp
          hence "\<not>mutex_snap_action (at_end aa) (at_start ab)" unfolding mutex_sched_def using ta(2) by blast
          then show ?thesis using 3 mutex_snap_action_def mutex_annotated_action_def anno_trans by simp
        qed
      next
        case 4
        with a b
        obtain ta tb da db where
          ta: "(aa, ta, da) \<in> ran \<pi>" "t = ta + da"
          and tb: "(ab, tb, db) \<in> ran \<pi>" "t = tb + db" unfolding annotated_action_seq_def by blast 
        have "aa \<noteq> ab" using ne 4 by blast
        hence "mutex_sched aa ta da ab tb db" using ta tb mvp unfolding mutex_valid_plan_inj_def by blast
        hence "\<not>mutex_snap_action (at_end aa) (at_end ab)" unfolding mutex_sched_def using ta(2) tb(2) by blast
        thus ?thesis unfolding mutex_snap_action_def mutex_annotated_action_def anno_trans 4 by blast
      qed
    qed
    ultimately
    show "nm_anno_act_seq" unfolding nm_anno_act_seq_def by (auto simp: Let_def)
  next
    assume naas: "nm_anno_act_seq"
    have "mutex_sched a ta da b tb db"
      if a: "(a, ta, da) \<in> ran \<pi>"
      and b: "(b, tb, db) \<in> ran \<pi>"
      and ne: "(a, ta, da) \<noteq> (b, tb, db)"
    for a ta da b tb db
    proof -
      
      from a b
      have aas: "(ta, AtStart a) \<in> annotated_action_seq" 
           "(tb, AtStart b) \<in> annotated_action_seq"
           "(ta + da, AtEnd a) \<in> annotated_action_seq" 
           "(tb + db, AtEnd b) \<in> annotated_action_seq" 
        unfolding annotated_action_seq_def by blast+


      have dadb: "0 \<le> da \<and> 0 \<le> db" using dg0 a b unfolding durations_ge_0_def by blast
    
      have "\<not>mutex_snap_action sa sb" 
        if sa:  "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da"
        and sb: "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db"
        and tu: "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for t u sa sb
      proof -
        { assume "ta - tb < \<epsilon> \<and> tb - ta < \<epsilon> \<or> ta = tb"
          then consider "ta - tb < \<epsilon> \<and> tb - ta < \<epsilon>" | "ta = tb" by blast
          hence "\<not>mutex_annotated_action (AtStart a) (AtStart b)" 
          proof cases
            case 1
            have "a \<noteq> b \<or> ta \<noteq> tb"
            proof (cases "a = b")
              case True
              hence "ta + da < tb \<or> tb + db < ta" using ne nso_double_act_spec nso dg0 a b by blast
              thus "a \<noteq> b \<or> ta \<noteq> tb" using dadb by auto
            qed simp
            thus ?thesis using 1 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with nso_no_double_start nso dg0 a b ne
            have "a \<noteq> b" by blast
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_start a) (at_start b)" using mutex_trans by simp
        } moreover
        { assume "ta - (tb + db) < \<epsilon> \<and> (tb + db) - ta < \<epsilon> \<or> ta = (tb + db)"
          then consider "ta - (tb + db) < \<epsilon> \<and> (tb + db) - ta < \<epsilon>" | "ta = tb + db " by blast
          hence "\<not>mutex_annotated_action (AtStart a) (AtEnd b)" 
          proof cases
            case 1
            thus ?thesis using aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with  nso dg0 a b ne
            have "a \<noteq> b" using nso_start_end by blast
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_start a) (at_end b)" using mutex_trans by blast
        } moreover
        { assume "(ta + da) - tb < \<epsilon> \<and> tb - (ta + da) < \<epsilon> \<or> (ta + da) = tb"
          then consider "(ta + da) - tb < \<epsilon> \<and> tb - (ta + da) < \<epsilon>" | "tb = (ta + da)" by blast
          hence "\<not>mutex_annotated_action (AtEnd a) (AtStart b)" 
          proof cases
            case 1
            thus ?thesis using 1 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with  nso dg0 a b ne
            have "a \<noteq> b" using nso_start_end by metis
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_end a) (at_start b)" using mutex_trans by blast
        } moreover
        { assume "(ta + da) - (tb + db) < \<epsilon> \<and> (tb + db) - (ta + da) < \<epsilon> \<or> (ta + da) = (tb + db)"
          then consider "(ta + da) - (tb + db) < \<epsilon> \<and> (tb + db) - (ta + da) < \<epsilon>" | "(tb + db) = (ta + da)" by argo
          hence "\<not>mutex_annotated_action (AtEnd a) (AtEnd b)" 
          proof cases
            case 1
            have "a \<noteq> b \<or> (ta + da) \<noteq> (tb + db)"
            proof (cases "a = b")
              case True
              hence "ta + da < tb \<or> tb + db < ta" using ne nso_double_act_spec nso dg0 a b by blast
              then consider "ta + da < tb" | "tb + db < ta" by auto
              hence "ta + da < tb + db \<or> tb + db < ta + da" 
                apply (cases) using dadb 
                by (metis add_less_same_cancel1 leD linorder_cases)+
              thus "a \<noteq> b \<or> (ta + da) \<noteq> (tb + db)" using dadb by auto
            qed simp
            thus ?thesis using 1 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          next
            case 2
            with  nso dg0 a b ne
            have "a \<noteq> b" using nso_ends by metis
            thus ?thesis using 2 aas naas[simplified nm_anno_act_seq_def] by (auto simp: Let_def)
          qed
          hence "\<not>mutex_snap_action (at_end a) (at_end b)" using mutex_trans by blast
        } ultimately
        show ?thesis using sa sb tu by fast
      qed
      thus ?thesis unfolding mutex_sched_def by blast
    qed
    moreover
    have "\<not>mutex_snap_action (at_start a) (at_end a)" 
      if "(a, t, d)\<in>ran \<pi>" "d = 0 \<or> d < \<epsilon>" for a t d
    proof -
      from that
      have as: "(t, AtStart a) \<in> annotated_action_seq"
           "(t + d, AtEnd a) \<in> annotated_action_seq" 
        unfolding annotated_action_seq_def by auto
      from that
      consider "d = 0" | "d < \<epsilon>" by blast
      hence "\<not>mutex_annotated_action (AtStart a) (AtEnd a)"
      proof cases
        case 1
        with as 
        have "AtStart a \<noteq> AtEnd a" "(t, AtStart a) \<in> annotated_action_seq" "(t, AtEnd a) \<in> annotated_action_seq" by auto
        thus ?thesis using naas unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      next
        case 2  
        moreover
        have "0 \<le> d" using that dg0 unfolding durations_ge_0_def by blast
        hence 1: "t - (t + d) < \<epsilon> \<and> (t + d) - t < \<epsilon>" using 2 
          by (metis add_cancel_right_right add_diff_cancel_left' add_strict_increasing2 diff_less_eq eps_ran less_add_same_cancel1 nless_le)
        from naas[simplified nm_anno_act_seq_def]
        have "\<And>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<Longrightarrow> (t, a) \<in> local.annotated_action_seq \<and> (u, b) \<in> local.annotated_action_seq \<and> (a = b \<longrightarrow> t \<noteq> u) \<longrightarrow> \<not> local.mutex_annotated_action a b" by (auto simp: Let_def)
        from this[OF 1]
        show ?thesis using as by blast
      qed
      thus ?thesis using mutex_trans by blast
    qed
    ultimately
    show mutex_valid_plan_inj unfolding mutex_valid_plan_inj_def by blast
  qed
  thus ?thesis using nso_imp_inj inj_mutex_def by blast
qed
end

locale temp_plan_unique_snaps = temp_plan_defs +
  assumes snaps_disj_on_plan_actions: "snaps_disj_on plan_actions"
begin 

text \<open>Non-zero- vs. epsilon-separation for mutually exclusive snap actions\<close>
lemma eps_zero_imp_zero_sep: 
  assumes "\<epsilon> = 0"
  shows "nm_happ_seq B = (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)" 
  using assms unfolding nm_happ_seq_def by fastforce

lemma eps_gt_zero_imp_eps_sep:
  assumes "0 < \<epsilon>"
  shows "nm_happ_seq B = (\<forall>t u a b. t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u
    \<and> (a \<noteq> b \<or> t \<noteq> u) \<longrightarrow> \<not>mutex_snap_action a b)"
proof -
  from assms
  have "(\<forall>t u a b. (t - u < \<epsilon> \<and> u - t < \<epsilon> \<and> a \<in> happ_at B t \<and> b \<in> happ_at B u) 
    \<longrightarrow> (a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)) \<Longrightarrow> (\<forall>t a b. a \<in> happ_at B t \<and> b \<in> happ_at B t \<and> a \<noteq> b \<longrightarrow> \<not>mutex_snap_action a b)"
    by force
  thus ?thesis unfolding nm_happ_seq_def using assms by blast
qed

end

locale temp_plan_unique_snaps_dg0 = 
  temp_plan_unique_snaps +
  temp_plan_dg0
begin

text \<open>If snap actions are uniquely identifiable, then the mutex condition on the happening sequence
is the same as that asserted on the annotated action sequence\<close>
lemma nm_anno_act_seq_eq_nm_happ_seq: "nm_anno_act_seq \<longleftrightarrow> nm_happ_seq plan_happ_seq"
proof 
  assume a: "nm_anno_act_seq"
  have "\<not>local.mutex_snap_action h i" 
      if ta: "(t, h) \<in> plan_happ_seq" 
      and tb: "(t, i) \<in> plan_happ_seq" 
      and ne: "h \<noteq> i" for h i t
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, t, e) \<in> ran \<pi>" "at_start b = i"
      | a d b u e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, u, e) \<in> ran \<pi>" "at_end b = i" "t = u + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, t, e) \<in> ran \<pi>" "at_start b = i"
      | a t' d b u e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "at_end b = i" "t = u + e" 
      apply (cases rule: in_happ_seqE[OF ta]; cases rule: in_happ_seqE[OF tb])
      by (blast, blast, blast, force)
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b" using ne 1 by auto
      hence "AtStart a \<noteq> AtStart b" by simp
      moreover
      have "(t, AtStart a) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtStart b) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtStart b)"using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "(t, AtStart a) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtEnd b) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtEnd b)"using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "(t, AtEnd a) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtStart b) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtStart b)"using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b" using ne 4 by auto
      hence "AtEnd a \<noteq> AtEnd b" by simp
      moreover
      have "(t, AtEnd a) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by auto
      moreover
      have "(t, AtEnd b) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by blast
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtEnd b)" using a unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  moreover
  have "\<not>local.mutex_snap_action h i"
    if tu: "t - u < \<epsilon> \<and> u - t < \<epsilon>" 
    and ta: "(t, h) \<in> plan_happ_seq" 
    and tb:"(u, i) \<in> plan_happ_seq" 
    and ne: "h \<noteq> i \<or> t \<noteq> u" for h i t u
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, u, e) \<in> ran \<pi>" "at_start b = i"
      | a d b u' e where 
        "(a, t, d) \<in> ran \<pi>" "at_start a = h" 
        "(b, u', e) \<in> ran \<pi>" "at_end b = i" "u = u' + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "at_start b = i"
      | a t' d b u' e where 
        "(a, t', d) \<in> ran \<pi>" "at_end a = h" "t = t' + d" 
        "(b, u', e) \<in> ran \<pi>" "at_end b = i" "u = u' + e" 
      apply (cases rule: in_happ_seqE[OF ta]; cases rule: in_happ_seqE[OF tb])
      by (blast, blast, blast, force)
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b \<or> t \<noteq> u" using ne 1 by auto
      hence "AtStart a \<noteq> AtStart b \<or> t \<noteq> u" by simp
      moreover
      have "(t, AtStart a) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtStart b) \<in> annotated_action_seq" using 1 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtStart b)" using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "(t, AtStart a) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtEnd b) \<in> annotated_action_seq" using 2 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtStart a) (AtEnd b)"using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "(t, AtEnd a) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtStart b) \<in> annotated_action_seq" using 3 unfolding annotated_action_seq_def by auto
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtStart b)" using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b \<or> t \<noteq> u" using ne 4 by auto
      hence "AtEnd a \<noteq> AtEnd b \<or> t \<noteq> u" by simp
      moreover
      have "(t, AtEnd a) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by auto
      moreover
      have "(u, AtEnd b) \<in> annotated_action_seq" using 4 unfolding annotated_action_seq_def by blast
      ultimately
      have "\<not>mutex_annotated_action (AtEnd a) (AtEnd b)" using a tu unfolding nm_anno_act_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  ultimately
  show "nm_happ_seq plan_happ_seq" unfolding nm_happ_seq_def by blast
next
  assume a: "nm_happ_seq plan_happ_seq"
  have "\<not>mutex_annotated_action h i" if 
    tu: "t - u < \<epsilon> \<and> u - t < \<epsilon>" 
    and th: "(t, h) \<in> annotated_action_seq" 
    and ti: "(u, i) \<in> annotated_action_seq" 
    and ne: "h \<noteq> i \<or> t \<noteq> u" for h i t u
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, u, e) \<in> ran \<pi>" "AtStart b = i"
      | a d b u' e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, u', e) \<in> ran \<pi>" "AtEnd b = i" "u = u' + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "AtStart b = i"
      | a t' d b u' e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, u', e) \<in> ran \<pi>" "AtEnd b = i" "u = u' + e" 
      using th ti unfolding annotated_action_seq_def by blast
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b \<or> t \<noteq> u" using ne 1 by auto
      hence "at_start a \<noteq> at_start b \<or> t \<noteq> u" using 1 snaps_disj_on_plan_actions 
        unfolding plan_actions_def snaps_disj_on_def plan_actions_def inj_on_def by fast
      moreover
      have "(t, at_start a) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      moreover
      have "(u, at_start b) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_start b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "(t, at_start a) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by blast 
      moreover
      have "(u, at_end b) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by blast
      moreover
      have "at_start a \<noteq> at_end b" using 2 snaps_disj_on_plan_actions plan_actions_def snaps_disj_on_def plan_actions_def by force
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_end b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "(t, at_end a) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by blast 
      moreover
      have "(u, at_start b) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by blast
      moreover
      have "at_end a \<noteq> at_start b" using 3 snaps_disj_on_plan_actions plan_actions_def snaps_disj_on_def plan_actions_def by force
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_start b)" using a tu unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b \<or> t \<noteq> u" using ne 4 by auto
      hence "at_end a \<noteq> at_end b \<or> t \<noteq> u" using 4 snaps_disj_on_plan_actions 
        unfolding plan_actions_def snaps_disj_on_def plan_actions_def inj_on_def by fast
      moreover
      have "(t, at_end a) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by auto
      moreover
      have "(u, at_end b) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by blast
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_end b)" using a tu 
        unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  moreover
  have "\<not>mutex_annotated_action h i"
    if th: "(t, h) \<in> annotated_action_seq"
    and ti: "(t, i) \<in> annotated_action_seq"
    and ne: "h \<noteq> i" for h i t 
  proof -
    consider 
        a d b e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, t, e) \<in> ran \<pi>" "AtStart b = i"
      | a d b u e where 
        "(a, t, d) \<in> ran \<pi>" "AtStart a = h" 
        "(b, u, e) \<in> ran \<pi>" "AtEnd b = i" "t = u + e"
      | a t' d b e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, t, e) \<in> ran \<pi>" "AtStart b = i"
      | a t' d b u e where 
        "(a, t', d) \<in> ran \<pi>" "AtEnd a = h" "t = t' + d" 
        "(b, u, e) \<in> ran \<pi>" "AtEnd b = i" "t = u + e" 
      using th ti unfolding annotated_action_seq_def by auto
    thus ?thesis
    proof cases
      case 1
      have "a \<noteq> b" using ne 1 by auto
      hence "at_start a \<noteq> at_start b" using 1 snaps_disj_on_plan_actions 
        unfolding snaps_disj_on_def plan_actions_def inj_on_def by fast
      moreover
      have "(t, at_start a) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_start b) \<in> plan_happ_seq" using 1 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_start b)"using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 1 mutex_trans by auto
    next
      case 2
      have "at_start a \<noteq> at_end b" using 2 snaps_disj_on_plan_actions 
        unfolding snaps_disj_on_def plan_actions_def inj_on_def by fast
      moreover
      have "(t, at_start a) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_end b) \<in> plan_happ_seq" using 2 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_start a) (at_end b)"using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 2 mutex_trans by auto
    next
      case 3
      have "at_end a \<noteq> at_start b" using 3 snaps_disj_on_plan_actions 
        unfolding snaps_disj_on_def plan_actions_def inj_on_def by fast
      moreover
      have "(t, at_end a) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_start b) \<in> plan_happ_seq" using 3 unfolding plan_happ_seq_def by auto
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_start b)" using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 3 mutex_trans by auto
    next
      case 4
      have "a \<noteq> b" using ne 4 by auto
      hence "at_end a \<noteq> at_end b" using 4 snaps_disj_on_plan_actions 
        unfolding snaps_disj_on_def plan_actions_def inj_on_def by fast
      moreover
      have "(t, at_end a) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by auto
      moreover
      have "(t, at_end b) \<in> plan_happ_seq" using 4 unfolding plan_happ_seq_def by blast
      ultimately
      have "\<not>mutex_snap_action (at_end a) (at_end b)" using a unfolding nm_happ_seq_def by (auto simp: Let_def)
      thus ?thesis using 4 mutex_trans by auto
    qed
  qed
  ultimately
  show nm_anno_act_seq unfolding nm_anno_act_seq_def Let_def by blast
qed
end

                                                     
locale temp_plan_unique_snaps_nso_dg0 = 
  temp_plan_unique_snaps +
  temp_plan_nso +
  temp_plan_dg0
begin
sublocale temp_plan_nso_dg0 by unfold_locales 
sublocale temp_plan_unique_snaps_dg0 by unfold_locales

lemma at_start_in_happ_seq_exD: 
    assumes in_happ_seq: "(s, at_start a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> plan_actions"
    shows "\<exists>!(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t"
  proof (rule ex_ex1I)
    from in_happ_seq in_happ_seq_exD
    have "\<exists>(a', t, d) \<in> ran \<pi>. (at_start a' = at_start a \<and> s = t \<or> at_end a' = at_start a \<and> s = t + d)"
      by blast
    with snaps_disj_on_plan_actions a_in_actions plan_actions_def snaps_disj_on_def inj_on_def
    have "\<exists>(a', t, d) \<in> ran \<pi>. at_start a' = at_start a \<and> s = t" by blast
    moreover
    have "\<forall>(a', t, d) \<in> ran \<pi>. at_start a = at_start a' \<longrightarrow> a = a'" 
      using snaps_disj_on_plan_actions a_in_actions 
      unfolding plan_actions_def snaps_disj_on_def inj_on_def by auto
    ultimately
    show "\<exists>x. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t" by auto
  next
    have "t = t' \<and> d = d'" 
         if "(a, t, d) \<in> ran \<pi> \<and> s = t" 
        and "(a, t', d') \<in> ran \<pi> \<and> s = t'" for t d t' d'
      using that nso dg0 nso_no_double_start by blast
    thus "\<And>x y. case x of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> case y of (t, d) \<Rightarrow> (a, t, d) \<in> ran \<pi> \<and> s = t \<Longrightarrow> x = y" by blast
  qed

  lemma at_end_in_happ_seq_exD:
    assumes in_happ_seq: "(s, at_end a) \<in> plan_happ_seq"
        and a_in_actions: "a \<in> plan_actions"
      shows "\<exists>!(t,d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"
  proof -
    define pair where "pair = (SOME (t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d)"
    from in_happ_seq[simplified plan_happ_seq_def]
    consider "(s, at_end a) \<in> {(t, at_start a)|a t d. (a, t, d) \<in> ran \<pi>}" 
        | "(s, at_end a) \<in>  {(t + d, at_end a) |a t d. (a, t, d) \<in> ran \<pi>}"
        by blast
      then
    have some_in_ran: "(a, pair) \<in> ran \<pi> 
      \<and> s = fst pair + snd pair"
    proof cases
      case 1
      hence "\<exists>a' d. (s, at_end a) = (s, at_start a') \<and> (a', s, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" 
        using a_in_actions unfolding plan_actions_def by auto
      thus ?thesis  using 1 snaps_disj_on_plan_actions a_in_actions
        unfolding plan_actions_def snaps_disj_on_def plan_actions_def inj_on_def by fast
    next
      case 2
      hence  "\<exists>a' t d. (s, at_end a) = (t + d, at_end a') \<and> (a', t, d) \<in> ran \<pi> \<and> a' \<in> plan_actions" 
        using a_in_actions unfolding plan_actions_def by blast
      hence "\<exists>t d. (a, t, d) \<in> ran \<pi> \<and> s = t + d" using snaps_disj_on_plan_actions a_in_actions
        unfolding plan_actions_def snaps_disj_on_def plan_actions_def inj_on_def by blast
      thus ?thesis using some_eq_ex[where P = "\<lambda>(t, d). (a, t, d) \<in> ran \<pi> \<and> s = t + d"] pair_def by auto
    qed
    moreover
    have "p = pair" if td_def: "p = (t, d)" and td_in_ran: "(a, t, d) \<in> ran \<pi>" and td_eq_s: "t + d = s" for t d p
    proof -
      obtain t' d' where
        t'd'_def: "pair = (t', d')" by fastforce
      with some_in_ran
      have t'd'_in_ran: "(a, t', d') \<in> ran \<pi>"
        and t'd'_eq_s: "s = t' + d'" by simp+
  
      from td_eq_s t'd'_eq_s
      have td_t'd': "t + d = t' + d'" by simp
      with nso_ends td_in_ran t'd'_in_ran
      have "t = t'" "d = d'" by blast+
      thus "p = pair" using t'd'_def td_def by simp
    qed
    ultimately
    show ?thesis apply - by (rule ex1I, auto)
  qed
end

subsection \<open>Fluents and Constants in a plan\<close>

locale temp_plan_and_props_defs = 
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi> +
  temp_planning_problem_and_props at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props
    for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::"'proposition set"
    and goal::"'proposition set"
    and \<epsilon>::"'time"
    and \<pi>::"('i, 'action, 'time::time) temp_plan" 
    and props::   "'proposition set"
begin

text \<open>Actions only modify a certain set of propositions. The problem can have constants.\<close>

definition plan_acts_mod_props where
"plan_acts_mod_props \<equiv> (\<forall>a \<in> plan_actions. act_mod_props a)"

definition const_resp_happ_seq where
"const_resp_happ_seq \<equiv> \<forall>t. (\<forall>h \<in> happ_at plan_happ_seq t. snap_mod_props h)"

lemma cr_plan_imp_cr_hs: "plan_acts_mod_props \<Longrightarrow> const_resp_happ_seq"
  unfolding plan_acts_mod_props_def act_mod_props_def
    plan_happ_seq_def const_resp_happ_seq_def plan_actions_def
  by blast

text \<open>Actions only refer to fluent propositions. The entire problem is fluent.\<close>

definition plan_acts_ref_props where
"plan_acts_ref_props \<equiv> (\<forall>(a, t, d) \<in> ran \<pi>. act_ref_props a)"

definition fluent_happ_seq where
"fluent_happ_seq \<equiv> \<forall>t. (\<forall>h \<in> happ_at plan_happ_seq t. snap_ref_props h)"

lemma plan_acts_ref_props_imp_fluent_happ_seq: "plan_acts_ref_props \<Longrightarrow> fluent_happ_seq"
  unfolding plan_acts_ref_props_def fluent_happ_seq_def act_ref_props_def plan_happ_seq_def 
  by blast

definition plan_consts where
"plan_consts \<equiv> \<Union>(act_consts ` plan_actions)"

definition happ_seq_consts where
"happ_seq_consts \<equiv> \<Union>(snap_consts ` {s|t s. (t, s) \<in> plan_happ_seq})"

lemma happ_seq_consts_const: "happ_seq_consts \<inter> props = {}" 
  unfolding happ_seq_consts_def act_consts_def snap_consts_def  by auto

definition domain_consts where
"domain_consts \<equiv> plan_consts \<union> (goal - props) \<union> (init - props)"

text \<open>The restriction of a state to its props\<close>
definition fluent_state::"'proposition set \<Rightarrow> 'proposition set" where
"fluent_state S \<equiv> S \<inter> props"

definition fluent_state_seq::"'proposition state_sequence \<Rightarrow> bool" where
"fluent_state_seq M \<equiv> \<forall>i \<le> length htpl. (M i \<subseteq> props)"

lemma app_valid_snap_to_fluent_state:
  assumes "M \<subseteq> props"
      and "\<forall>s \<in> H. snap_mod_props s"
    shows "apply_effects H M \<subseteq> props"
proof -
  have "M - \<Union> (dels ` H) \<subseteq> props" using assms by blast
  moreover
  have "\<And>M. M \<subseteq> props \<Longrightarrow> M \<union> \<Union> (adds ` H) \<subseteq> props" using assms snap_mod_props_def by blast
  ultimately
  show ?thesis unfolding apply_effects_def by simp
qed

lemma app_fluent_valid_snaps:
  assumes "\<forall>s \<in> H. adds s \<union> dels s \<subseteq> props"
      and "apply_effects H M = M'"
    shows "apply_effects H (M \<inter> props) = (M' \<inter> props)" 
  using assms unfolding apply_effects_def by blast

lemma plan_acts_ref_props_is_const_respecting: "plan_acts_ref_props \<Longrightarrow> plan_acts_mod_props" 
  unfolding plan_acts_ref_props_def act_ref_props_def  
    plan_acts_mod_props_def act_mod_props_def snap_mod_props_def plan_actions_def snap_ref_props_def
  by blast

lemma plan_acts_ref_props_consts:
  assumes "plan_acts_ref_props"
  shows "plan_consts = {}"
  using assms unfolding plan_consts_def plan_actions_def 
    plan_acts_ref_props_def act_ref_props_def snap_ref_props_def
    act_consts_def snap_consts_def 
  by (auto simp: Let_def)

lemma cr_plan_consts:
  assumes "plan_acts_mod_props"
  shows "plan_consts = \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - props"
  using assms unfolding plan_acts_mod_props_def plan_consts_def act_mod_props_def snap_mod_props_def plan_actions_def 
  act_consts_def snap_consts_def by fast

lemma cr_domain_consts:
  assumes "plan_acts_mod_props"
  shows "domain_consts = \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - props \<union> (goal - props) \<union> (init - props)"
  using cr_plan_consts assms domain_consts_def by simp

lemma plan_and_happ_seq_consts:
  "plan_consts = (happ_seq_consts \<union> \<Union>(over_all ` {a| a t d. (a, t, d) \<in> ran \<pi>})) - props"
  unfolding plan_consts_def happ_seq_consts_def 
  apply (rule equalityI; rule subsetI)
  subgoal for x
    unfolding plan_happ_seq_def plan_actions_def act_consts_def snap_consts_def  by fast
  subgoal for x
    using in_happ_seq_exD_act unfolding plan_actions_def act_consts_def snap_consts_def by fast
  done

lemma cr_plan_cr_happ_seq:
  "plan_acts_mod_props = const_resp_happ_seq" unfolding plan_acts_mod_props_def const_resp_happ_seq_def 
  plan_happ_seq_def act_mod_props_def plan_actions_def by fast

lemma cr_happ_seq_consts:
  assumes "const_resp_happ_seq"
  shows "happ_seq_consts = \<Union>(pre ` {s|t s. (t, s) \<in> plan_happ_seq}) - props"
  using assms unfolding const_resp_happ_seq_def  happ_seq_consts_def snap_mod_props_def
  unfolding act_consts_def snap_consts_def 
  by blast

lemma plan_consts_not_fluent:
  "props \<inter> plan_consts = {}" unfolding plan_consts_def act_consts_def snap_consts_def  by blast

lemma domain_consts_not_fluent:
  "props \<inter> domain_consts = {}" 
  using plan_consts_not_fluent domain_consts_def by blast
end


locale temp_plan_and_finite_props_defs = 
  temp_plan_and_props_defs +
  actions_and_finite_props

locale temp_plan_and_some_props_defs = 
  temp_plan_and_props_defs + 
  actions_and_some_props
begin
sublocale temp_plan_and_finite_props_defs by unfold_locales 
end

locale temp_plan_resp_props = 
  temp_plan_and_props_defs +
  assumes plan_acts_mod_props: plan_acts_mod_props

locale temp_plan_fluent = temp_plan_and_props_defs +
  assumes plan_acts_ref_props: plan_acts_ref_props
begin
sublocale temp_plan_resp_props
  apply unfold_locales using plan_acts_ref_props 
  unfolding plan_acts_mod_props_def plan_acts_ref_props_def plan_actions_def
  using act_ref_props_imp_act_mod_props by auto
end

text \<open>
- Assume we have identified a set of props that a plan modifies.
- Assume that the constants that the goal refers to are a subset of those the initial state refers to.
- Assume that the constants that the plan refers to are a subset of those the initial state refers to.

The plan validity is equivalent if plan actions never modify constants and the constants present
in the goal or plan are subsets of the constants present in the initial state.
\<close>
locale temp_plan_restr_to_props = 
  temp_plan_resp_props + 
  temp_planning_problem_goal_consts_in_init_consts +
  assumes plan_consts_in_init_consts: "plan_consts \<subseteq> init - props"
begin
text \<open>
The idea behind this abstraction is to maintain the shape of the plan, the time points, and the 
happening sequence, while changing which propositions exist in the states and are modified by the
happenings.

A plan that is "const_respecting" (does not modify some constants, if they exist) can be used when
equality is a proposition. The same plan must be valid, if we restrict the preconditions to the set of props. 

It's part of a simple preprocessing step to reduce the number of propositions present.
\<close>

sublocale rtf: temp_plan_and_props_defs at_start at_end over_all_restr lower upper pre_restr adds dels "init \<inter> props" "goal \<inter> props" \<epsilon> \<pi> props
  using local.temp_plan_and_props_defs_axioms .

sublocale temp_plan_fluent at_start at_end over_all_restr lower upper pre_restr adds dels "init \<inter> props" "goal \<inter> props" \<epsilon> \<pi> props
  apply unfold_locales 
    using plan_acts_mod_props 
    unfolding rtf.plan_acts_ref_props_def
    unfolding rtf.plan_acts_mod_props_def
    unfolding plan_actions_def 
    unfolding rtf.act_mod_props_def rtf.act_ref_props_def
    unfolding rtf.snap_mod_props_def rtf.snap_ref_props_def
    unfolding pre_restr_def over_all_restr_def
    by blast

lemma plan_acts_mod_props_state_seq:
  assumes MS'_p: "\<forall>i \<le> length htpl. MS' i = MS i \<inter> props"
      and vss: "(valid_state_sequence MS)"
    shows "(rtf.valid_state_sequence MS' \<and> rtf.plan_acts_ref_props
    \<and> rtf.fluent_state_seq MS')"
proof -

  let ?B = "plan_happ_seq"
  let ?t = "time_index"

  let ?Inv = "plan_inv_seq"
  let ?Inv' = "rtf.plan_inv_seq"
  
  from plan_acts_mod_props cr_plan_imp_cr_hs
  have cr_hs: "\<forall>t. (\<forall>h \<in> happ_at ?B t. snap_mod_props h)" unfolding const_resp_happ_seq_def by blast

  have app_eff: "apply_effects (happ_at ?B (?t i)) (MS i) = MS (Suc i)"
       and invs: "invs_at ?Inv (?t i) \<subseteq> MS i"
       and pres: "\<Union> (pre ` happ_at ?B (?t i)) \<subseteq> MS i"
       if "i < length htpl" for i using that vss unfolding valid_state_sequence_def by (auto simp: Let_def)

  have "rtf.valid_state_sequence MS'"
       "fluent_state_seq MS'" 
  proof -
    show "fluent_state_seq  MS'" using MS'_p unfolding fluent_state_seq_def by simp
    have "apply_effects (happ_at ?B (?t i)) (MS' i) = MS' (Suc i)" (is "apply_effects ?S (MS' i) = MS' (Suc i)")
       and "invs_at ?Inv' (?t i) \<subseteq> MS' i"
       and "\<Union> (pre_restr ` happ_at ?B (?t i)) \<subseteq> MS' i"
       if i_ran: "i < length htpl" for i
    proof -
      show "apply_effects ?S (MS' i) = MS' (Suc i)" 
      proof -
        have "\<Union>(adds ` ?S) \<subseteq> props" 
             "\<Union>(dels ` ?S) \<subseteq> props" using i_ran cr_hs 
          unfolding fluent_state_seq_def snap_mod_props_def by auto
        hence "\<forall>s\<in>happ_at plan_happ_seq (time_index i). snap_mod_props s" 
          unfolding snap_mod_props_def by blast
        thus "apply_effects ?S (MS' i) = MS' (Suc i)" 
          using app_fluent_valid_snaps[OF _ app_eff[OF that]] 
          using MS'_p that unfolding snap_mod_props_def by simp
      qed
      show "invs_at ?Inv' (?t i) \<subseteq> MS' i" 
      proof -
        have "invs_at rtf.plan_inv_seq (time_index i) = invs_at plan_inv_seq (time_index i) \<inter> props" 
          unfolding invs_at_def
          unfolding local.plan_inv_seq_def rtf.plan_inv_seq_def 
          unfolding over_all_restr_def by auto
        thus "invs_at ?Inv' (?t i) \<subseteq> MS' i" using invs MS'_p i_ran by auto
      qed
      show "\<Union> (pre_restr ` ?S) \<subseteq> MS' i" 
      proof -
        have "\<Union> (pre ` ?S) \<inter> props =  \<Union> (pre_restr ` ?S)" 
          unfolding plan_happ_seq_def pre_restr_def by auto
        thus "\<Union> (pre_restr ` ?S) \<subseteq> MS' i" using pres MS'_p i_ran by auto
      qed
    qed
    thus "rtf.valid_state_sequence MS'" unfolding rtf.valid_state_sequence_def by (auto simp: Let_def)
  qed
  thus "rtf.valid_state_sequence MS' \<and> rtf.plan_acts_ref_props \<and> rtf.fluent_state_seq MS'" 
    using plan_acts_ref_props by (auto intro: exI[where x = "\<lambda>i. (MS i \<inter> props)"])
qed

lemma plan_acts_mod_props_state_seq':
  assumes MS'_p: "\<forall>i \<le> length htpl. MS' i \<inter> props = MS i \<inter> props" 
                 "\<forall>i \<le> length htpl. (MS i - props) = (MS' i - props) \<union> domain_consts" 
    and vss: "rtf.valid_state_sequence MS'"
  shows "valid_state_sequence MS"
proof -

  let ?B = "plan_happ_seq"
  let ?t = "time_index"

  let ?Inv = "plan_inv_seq"
  let ?Inv' = "rtf.plan_inv_seq"

  let ?dc = "domain_consts"

  from MS'_p
  have MS'_p': "\<forall>i \<le> length htpl. MS' i \<union> ?dc = MS i" by auto

  from plan_acts_mod_props cr_plan_imp_cr_hs
  have cr_hs: "\<forall>t. (\<forall>h \<in> happ_at ?B t. snap_mod_props h)" unfolding const_resp_happ_seq_def by blast

  have app_eff: "apply_effects (happ_at ?B (?t i)) (MS' i) = MS' (Suc i)"
       and invs: "invs_at ?Inv' (?t i) \<subseteq> MS' i"
       and pres: "\<Union> (pre_restr ` happ_at ?B (?t i)) \<subseteq> MS' i"
       if "i < length htpl" for i using that vss unfolding rtf.valid_state_sequence_def Let_def by auto

  have dc: "?dc = 
    \<Union> ((\<lambda>a. pre (at_start a) \<union> pre (at_end a) \<union> over_all a) ` {a|a t d. (a, t, d) \<in> ran \<pi>}) - props \<union> (goal - props) \<union> (init - props)" (is "?dc = ?dc'")
    using cr_domain_consts plan_acts_mod_props by fastforce
  have "apply_effects (happ_at ?B (?t i)) (MS i) = MS (Suc i)" (is "apply_effects ?S (MS i) = MS (Suc i)")
     and "invs_at ?Inv (?t i) \<subseteq> MS i"
     and "\<Union> (pre ` happ_at ?B (?t i)) \<subseteq> MS i"
     if i_ran: "i < length htpl" for i
  proof -
    show "apply_effects ?S (MS i) = MS (Suc i)" 
    proof -
      have "\<Union>(adds ` ?S) \<subseteq> props" (is "?as \<subseteq> props")
           "\<Union>(dels ` ?S) \<subseteq> props" (is "?ds \<subseteq> props") using i_ran cr_hs unfolding fluent_state_seq_def snap_mod_props_def by auto
      hence "?as \<inter> ?dc = {}"
            "?ds \<inter> ?dc = {}" using dc by auto
      moreover
      from app_eff i_ran
      have "(MS' i - ?ds) \<union> ?as = MS' (Suc i)" unfolding apply_effects_def by simp
      ultimately
      have "(MS' i \<union> ?dc) - ?ds \<union> ?as = MS' (Suc i) \<union> ?dc" by auto
      thus "apply_effects ?S (MS i) = MS (Suc i)" unfolding apply_effects_def using MS'_p' i_ran by simp
    qed
    show "invs_at ?Inv (?t i) \<subseteq> MS i" 
    proof -
      have "invs_at ?Inv (?t i) \<subseteq> invs_at ?Inv' (?t i) \<union> ?dc" 
        unfolding invs_at_def
        unfolding local.plan_inv_seq_def rtf.plan_inv_seq_def
        unfolding dc over_all_restr_def by auto
      hence "invs_at ?Inv (?t i) \<subseteq> MS' i \<union> ?dc" using invs i_ran by auto
      thus "invs_at ?Inv (?t i) \<subseteq> MS i" 
        apply -
        apply (erule subset_trans)
        using MS'_p' i_ran by auto
    qed
    show "\<Union> (pre ` ?S) \<subseteq> MS i" 
    proof -
      from pres i_ran
      have "\<Union> (pre_restr ` ?S) \<subseteq> MS' i" by simp
      hence "\<Union> (pre ` ?S) \<inter> props \<subseteq> MS' i" unfolding pre_restr_def by simp
      moreover
      from plan_acts_mod_props[simplified cr_plan_cr_happ_seq, THEN cr_happ_seq_consts]
      have "\<Union> (pre ` ?S) - props \<subseteq> happ_seq_consts - props" by auto
      hence "\<Union> (pre ` ?S) - props \<subseteq> ?dc" using plan_and_happ_seq_consts unfolding domain_consts_def by fast
      ultimately
      have "\<Union> (pre ` ?S) \<subseteq> MS' i \<union> ?dc" by blast
      thus "\<Union> (pre ` ?S) \<subseteq> MS i" using MS'_p' i_ran by simp
    qed
  qed
  thus "valid_state_sequence MS" unfolding valid_state_sequence_def by (auto simp: Let_def)
qed


(* Todo: Maybe move or delete
text \<open>Move to other locale\<close>
lemma plan_acts_mod_props_nm_happ_seq_equiv: "nm_happ_seq (plan_happ_seq) 
  \<longleftrightarrow> rtf.nm_happ_seq (plan_happ_seq)"
proof -
  from plan_acts_mod_props
  have "const_resp_happ_seq" using cr_plan_cr_happ_seq by blast
  from this[simplified const_resp_happ_seq_def]
  have "\<forall>s t a b. a \<in> happ_at (plan_happ_seq) s \<and> b \<in> happ_at (plan_happ_seq) t
    \<longrightarrow> (mutex_snap_action a b \<longleftrightarrow> rtf.mutex_snap_action a b)" unfolding mutex_snap_action_def 
    apply -
    apply (intro allI; rule impI; rule iffI; erule conjE)
     apply (elim disjE)
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def snap_mod_props_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def snap_mod_props_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def by auto
    subgoal for s t a b
      apply (frule spec, drule bspec[where x = a], assumption)
      apply (drule spec, drule bspec[where x = b], assumption)
      unfolding pre_restr_def by auto
    done
  thus ?thesis unfolding nm_happ_seq_def by blast
qed
 *)

text \<open>An attempt was made to remove these assumptions by proving that constants in a plan are
      indeed constant. However, this only works for the direction of the proof that does not 
      need it.\<close>

lemma plan_acts_mod_props_mutex_plan_equiv:
  "mutex_valid_plan \<longleftrightarrow> rtf.mutex_valid_plan"
proof -
  have mutex_equiv: "mutex_snap_action a b \<longleftrightarrow> rtf.mutex_snap_action a b"
    if "adds a \<subseteq> props" "dels a \<subseteq> props" "adds b \<subseteq> props" "dels b \<subseteq> props" for a b
  proof -
    have i: "\<And>x y s. x \<subseteq> s \<Longrightarrow> y \<subseteq> s \<Longrightarrow> x \<union> y \<subseteq> s" by blast
    have j: "y \<inter> s \<inter> x \<noteq> {}" if "y \<inter> x \<noteq> {}" "x \<subseteq> s" for x y s::"'a set"
    proof -
      from that
      obtain e where
        e: "e \<in> y \<inter> x" by blast
      moreover
      have "e \<in> s" using e that by blast
      ultimately
      have "e \<in> y \<inter> x \<inter> s" by blast
      thus ?thesis by blast
    qed

    have k: "\<And>x y s. y \<inter> s \<inter> x \<noteq> {} \<Longrightarrow> x \<subseteq> s \<Longrightarrow> y \<inter> x \<noteq> {}" by blast

    show ?thesis
      unfolding local.mutex_snap_action_def rtf.mutex_snap_action_def
      unfolding pre_restr_def
      apply (rule iffI; elim disjE)
      using that by blast+
  qed

  have mutex_equiv': "mutex_snap_action (f a) (g b)
    \<longleftrightarrow> rtf.mutex_snap_action (f a) (g b)" 
    if "\<exists>t d. (a, t, d)\<in>ran \<pi>" "\<exists>t d. (b, t, d)\<in>ran \<pi>" "f = at_start \<or> f = at_end" "g = at_start \<or> g = at_end" for a b f g
    using that
    apply -
    apply (elim disjE; rule mutex_equiv)
    using plan_acts_mod_props unfolding plan_acts_mod_props_def act_mod_props_def snap_mod_props_def
    unfolding plan_actions_def
    by blast+

  have mutex_self: "mutex_snap_action (at_start a) (at_end a) \<longleftrightarrow> rtf.mutex_snap_action (at_start a) (at_end a)" 
    if "\<exists>t d. (a, t, d)\<in>ran \<pi>" for a
    using that mutex_equiv'[of a a at_start at_end] by simp
  hence "(\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> mutex_snap_action (at_start a) (at_end a))
    \<longleftrightarrow> (\<forall>(a, t, d)\<in>ran \<pi>. d = 0 \<or> d < \<epsilon> \<longrightarrow> \<not> rtf.mutex_snap_action (at_start a) (at_end a))"
    by fast
  moreover
  
  have mutex_sched: "mutex_sched a ta da b tb db \<longleftrightarrow> rtf.mutex_sched a ta da b tb db" if 
    "i \<in> dom \<pi>" "j \<in> dom \<pi>" "i \<noteq> j" "\<pi> i = Some (a, ta, da)" "\<pi> j = Some (b, tb, db)" for i j a ta da b tb db
  proof -
    have ab_ran: "\<exists>t d. (a, t, d) \<in> ran \<pi>" "\<exists>t d. (b, t, d) \<in> ran \<pi>" using that ranI by fast+
    show ?thesis
    proof 
      assume as: "mutex_sched a ta da b tb db"
      have "\<not> rtf.mutex_snap_action sa sb" 
        if "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da" 
           "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start a \<and> t = ta" "sb = at_start b \<and> u = tb" |
          "sa = at_start a \<and> t = ta" "sb = at_end b \<and> u = tb + db" | 
          "sa = at_end a \<and> t = ta + da" "sb = at_start b \<and> u = tb" |
          "sa = at_end a \<and> t = ta + da" "sb = at_end b \<and> u = tb + db" by argo
        thus ?thesis
          apply cases
          using t as[simplified mutex_sched_def] 
          by (auto simp: mutex_equiv'[OF ab_ran, symmetric])
      qed
      thus "rtf.mutex_sched a ta da b tb db" 
        unfolding rtf.mutex_sched_def by blast
  
    next
      assume as: "rtf.mutex_sched a ta da b tb db"
      have "\<not> mutex_snap_action sa sb" 
        if "sa = at_start a \<and> t = ta \<or> sa = at_end a \<and> t = ta + da" 
           "sb = at_start b \<and> u = tb \<or> sb = at_end b \<and> u = tb + db" 
        and t:  "t - u < \<epsilon> \<and> u - t < \<epsilon> \<or> t = u" for sa sb t u
      proof -
        from that
        consider 
          "sa = at_start a \<and> t = ta" "sb = at_start b \<and> u = tb" |
          "sa = at_start a \<and> t = ta" "sb = at_end b \<and> u = tb + db" | 
          "sa = at_end a \<and> t = ta + da" "sb = at_start b \<and> u = tb" |
          "sa = at_end a \<and> t = ta + da" "sb = at_end b \<and> u = tb + db" by argo
        thus ?thesis
          apply cases
          using t as[simplified rtf.mutex_sched_def] 
          by (auto simp: mutex_equiv'[OF ab_ran])
      qed
      thus "mutex_sched a ta da b tb db" 
        unfolding mutex_sched_def by blast
    qed
  qed
  hence "(\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> mutex_sched a ta da b tb db) \<longleftrightarrow>
     (\<forall>i j a ta da b tb db. i \<in> dom \<pi> \<and> j \<in> dom \<pi> \<and> i \<noteq> j \<and> \<pi> i = Some (a, ta, da) \<and> \<pi> j = Some (b, tb, db) \<longrightarrow> rtf.mutex_sched a ta da b tb db)"
    by blast
  ultimately
  show ?thesis 
    using mutex_valid_plan_eq rtf.mutex_valid_plan_eq
    using mutex_valid_plan_alt_def rtf.mutex_valid_plan_alt_def
    using mutex_snap_action_def rtf.mutex_snap_action_def by argo
qed


lemma const_plan_equiv: 
    shows "valid_plan \<longleftrightarrow> rtf.valid_plan" 
  unfolding valid_plan_def rtf.valid_plan_def
proof
  assume "\<exists>M. valid_state_sequence M \<and>
        M 0 = init \<and>
        goal \<subseteq> M (length htpl) \<and>
        durations_ge_0 \<and> durations_valid \<and> 
        mutex_valid_plan \<and> 
        finite_plan"
  then obtain MS where
    vss: "valid_state_sequence MS"
    and init: "MS 0 = init"
    and goal: "goal \<subseteq> MS (length htpl)"
    and dur: "durations_ge_0 \<and> durations_valid"
    and mutex: "mutex_valid_plan"
    and finite: "finite_plan" by blast

  define MS' where "MS' = (\<lambda>i. if (i \<le> length htpl) then MS i \<inter> props else undefined)"  
  hence "\<forall>i \<le> length htpl. MS' i = MS i \<inter> props" by auto
  with vss 
  have vss': "rtf.valid_state_sequence MS'" 
    and fss': "fluent_state_seq MS'" 
    and fp: "rtf.plan_acts_ref_props"
    using plan_acts_mod_props_state_seq by auto

  from MS'_def goal
  have goal': "goal \<inter> props \<subseteq> MS' (length htpl)" by auto

  from MS'_def init
  have init': "init \<inter> props = MS' 0" by simp

  show "\<exists>M. rtf.valid_state_sequence M \<and>
      M 0 = init \<inter> props \<and>
      goal \<inter> props \<subseteq> M (length htpl) \<and>
      durations_ge_0 \<and> durations_valid \<and>
      rtf.mutex_valid_plan \<and>
      finite_plan"
    using vss' plan_acts_mod_props_mutex_plan_equiv dur init' goal' mutex finite 
    unfolding fluent_state_def by blast
next
  assume "\<exists>M. rtf.valid_state_sequence M \<and>
        M 0 = init \<inter> props \<and>
        goal \<inter> props \<subseteq> M (length htpl) \<and>
        durations_ge_0 \<and> durations_valid \<and>
        rtf.mutex_valid_plan \<and>
        finite_plan"
  then obtain MS' where
    vss': "rtf.valid_state_sequence MS'"
    and init': "MS' 0 = init \<inter> props"
    and goal': "goal \<inter> props \<subseteq> MS' (length htpl)"
    and dur: "durations_ge_0 \<and> durations_valid"
    and mutex: "rtf.mutex_valid_plan"
    and finite: "finite_plan" unfolding fluent_state_def by auto

  let ?dc = "domain_consts"

  define MS where "MS \<equiv> \<lambda>i. if (i \<le> length htpl) then MS' i \<union> ?dc else undefined"
  have "\<forall>i\<le>length htpl. MS i - props = (MS' i - props) \<union> ?dc"
  proof (rule allI; rule impI)
    fix i
    assume "i \<le> length htpl"
    hence "MS i = MS' i \<union> ?dc" using MS_def by simp
    hence "MS i - props = MS' i \<union> ?dc - props" by simp
    hence "MS i - props = (MS' i - props) \<union> (?dc - props)" by auto
    thus "MS i - props = (MS' i - props) \<union> ?dc" using domain_consts_not_fluent by fast
  qed
  hence vss: "valid_state_sequence MS" 
    using vss' MS_def plan_acts_mod_props_state_seq'[where MS = MS and MS' = MS'] by fastforce
  
  show "\<exists>M. valid_state_sequence M \<and>
        M 0 = init \<and> goal \<subseteq> M (length htpl) \<and> durations_ge_0 \<and> 
        durations_valid \<and>
        mutex_valid_plan \<and>
        finite_plan"
  proof (cases "length htpl")
    case 0
    define MS where "MS \<equiv> (\<lambda>x. init)" 
    
    have "goal \<inter> props \<subseteq> init \<inter> props" using init' goal' 0  by simp
    hence init_goal: "goal \<subseteq> init" using goal_consts_in_init_consts by blast
    have any: "\<forall>M. valid_state_sequence M"
      unfolding valid_state_sequence_def using 0 by (auto simp: Let_def)
    show ?thesis using init_goal MS_def any dur mutex plan_acts_mod_props_mutex_plan_equiv finite by auto
  next
    case (Suc nat)
    have init: "init = MS 0" unfolding MS_def domain_consts_def 
      using goal_consts_in_init_consts plan_consts_in_init_consts Suc using init' by auto
    moreover
    have goal: "goal \<subseteq> MS (length htpl)" unfolding MS_def using goal' 
      unfolding domain_consts_def by auto
    ultimately
    show ?thesis using dur mutex plan_acts_mod_props_mutex_plan_equiv finite vss by auto
  qed
qed
end

locale valid_temp_plan_restr_to_props = 
  temp_plan_restr_to_props +
  valid_temp_plan
begin
sublocale valid_rtf: valid_temp_plan at_start at_end over_all_restr lower upper pre_restr adds dels "init \<inter> props" "goal \<inter> props" \<epsilon> \<pi>
  using const_plan_equiv vp by unfold_locales blast

sublocale fluent_rtf: temp_plan_fluent at_start at_end over_all_restr lower upper pre_restr adds dels "init \<inter> props" "goal \<inter> props" \<epsilon> \<pi>
  by unfold_locales
end

locale temp_plan_mutex_happ_seq = temp_plan_defs +
  assumes nm_happ_seq: "nm_happ_seq plan_happ_seq"
begin
subsubsection \<open>Mutual exclusivity on the happening sequence\<close>

lemma mutex_not_in_same_instant:
  assumes "(t, a) \<in> plan_happ_seq"
      and "(t, b) \<in> plan_happ_seq"
      and "a \<noteq> b"
    shows "\<not>mutex_snap_action a b"
  using nm_happ_seq assms unfolding nm_happ_seq_def  
  by blast

lemma mutex_same_instant_is_same:
  assumes "(t, a) \<in> plan_happ_seq"
      and "(t, b) \<in> plan_happ_seq"
      and "mutex_snap_action a b"
    shows "a = b" 
  using mutex_not_in_same_instant assms by blast
end


locale valid_temp_plan_unique_snaps =
  valid_temp_plan + 
  temp_plan_unique_snaps
begin
sublocale temp_plan_unique_snaps_dg0 by unfold_locales
end


locale valid_temp_plan_nso = 
    valid_temp_plan +
    temp_plan_nso 
begin
sublocale temp_plan_nso_dg0 by unfold_locales
end

locale valid_temp_plan_unique_snaps_nso =
  valid_temp_plan_unique_snaps +
  valid_temp_plan_nso
begin
sublocale temp_plan_unique_snaps_nso_dg0 by unfold_locales
end


locale temp_plan_for_actions_with_unique_snaps_nso_dg0 =
  temp_plan_for_actions +
  action_set_unique_snaps +
  temp_plan_nso +
  temp_plan_dg0
begin
sublocale temp_plan_nso_dg0
  by unfold_locales
end


(* To do: Replacement of definitions on domain actions. The locale to do that. *)
(* To do: Conditions on props (fluents?) on domain actions *)

(* 
locale temp_plan_for_actions = 
  temp_plan_defs at_start at_end over_all lower upper pre adds dels init goal \<epsilon> \<pi>
    for at_start::"'action  \<Rightarrow> 'snap_action" 
    and at_end::  "'action  \<Rightarrow> 'snap_action"
    and over_all::"'action  \<Rightarrow> 'proposition set"
    and lower::   "'action  \<rightharpoonup> ('time::time) lower_bound"
    and upper::   "'action  \<rightharpoonup> 'time upper_bound"
    and pre::     "'snap_action \<Rightarrow> 'proposition set"
    and adds::    "'snap_action \<Rightarrow> 'proposition set"
    and dels::    "'snap_action \<Rightarrow> 'proposition set"
    and init::"'proposition set"
    and goal::"'proposition set"
    and \<epsilon>::"'time"
    and \<pi>::"('i, 'action, 'time::time) temp_plan" +
  fixes actions:: "'action set"
  assumes pap: "\<forall>(a, t, d) \<in> ran \<pi>. a \<in> actions"
begin

lemma exists_actions_happening_at_time_index:
  assumes "i < length htpl"
  shows "\<exists>a \<in> actions. (time_index i, at_start a) \<in> plan_happ_seq \<or> (time_index i, at_end a) \<in> plan_happ_seq"
  apply (insert time_index_htpsD[OF assms])
  apply (erule htpsE)
  subgoal for a t d
    apply (rule bexI[of _ a])
    apply (rule disjI1)
    unfolding plan_happ_seq_def apply blast
    using pap by blast
  subgoal for a t d
    apply (rule bexI[of _ a])
    apply (rule disjI2)
    unfolding plan_happ_seq_def apply blast
    using pap by blast
  done
lemma actions_at_time_index_cases:
  assumes  "i < length htpl"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_actions_happening_at_time_index by blast

lemma actions_at_time_index_exhaustive_cases:
  assumes "i < length htpl"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<in> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<notin> plan_happ_seq \<Longrightarrow> thesis"
    and "\<And>a. a \<in> actions \<Longrightarrow> (time_index i, at_start a) \<notin> plan_happ_seq \<Longrightarrow> (time_index i, at_end a) \<in> plan_happ_seq \<Longrightarrow> thesis"
  shows thesis using assms exists_actions_happening_at_time_index by blast
end
 *)
end
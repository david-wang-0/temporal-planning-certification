theory TP_NTA_Reduction_Numeric_Defs
  imports TP_NTA_Reduction_Defs
begin

section \<open>Numeric augmentation of the reduction (NUMERIC_PLAN Layer B)\<close>

text \<open>The numeric reduction is an ADDITIVE layer over the propositional one (NUMERIC_PLAN A.6): a
locale extending \<open>tp_nta_reduction_defs\<close> with the numeric data (\<open>n_pre\<close>/\<open>n_inv\<close>/\<open>upds\<close>/\<open>num_init\<close>/
\<open>num_goal\<close>), a fluent-naming map \<open>fluent_to_var\<close>, per-fluent integer bounds, and the value-to-int map
\<open>const_to_int\<close>. The numeric net reuses the propositional definitions and APPENDS fluent
var-declarations / numeric guards / numeric updates, so its propositional projection is the
propositional net unchanged. Numeric fields are sets/functions, so they sidestep the list-vs-set split
that \<open>pre\<close>/\<open>adds\<close>/\<open>dels\<close> carry.\<close>

locale numeric_tp_nta_reduction_defs = tp_nta_reduction_defs
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal" +
  fixes n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_name :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int"
begin

text \<open>The fluent variable name is a DEFINED constant (mirroring the propositional \<open>prop_to_var\<close>),
prefixing the fluent's abstract name with \<open>''fluent_''\<close>. The \<open>''fluent_''\<close> prefix is disjoint from
the propositional prefixes (\<open>''var_''\<close>/\<open>''lock_''\<close>) and from \<open>acts_active\<close>/\<open>planning_lock\<close>, which is
what makes the fluent variables fresh (NUMERIC_PLAN A.6).\<close>
definition "fluent_to_var f \<equiv> STR ''fluent_'' + fluent_to_name f"

text \<open>One bounded \<open>int\<close> variable per declared numeric fluent, appended to the propositional
\<open>all_vars\<close> (NUMERIC_PLAN A.5).\<close>
definition num_fluent_vars :: "(String.literal \<times> int \<times> int) list" where
"num_fluent_vars = map (\<lambda>f. (fluent_to_var f, fluent_lo f, fluent_hi f)) nfluents"

definition num_all_vars :: "(String.literal \<times> int \<times> int) list" where
"num_all_vars = all_vars @ num_fluent_vars"

text \<open>Numeric guards and updates, derived from the abstract numeric data through the encoders
(NUMERIC_PLAN A.5): \<open>n_pre\<close>/\<open>n_inv\<close>/\<open>num_goal\<close> become \<open>bexp\<close> guards, \<open>upds\<close> and \<open>num_init\<close> become
\<open>(var, exp)\<close> updates.\<close>
definition num_pre_guard :: "'snap_action \<Rightarrow> (String.literal, int) bexp" where
"num_pre_guard s = bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) (n_pre s))"

definition num_inv_guard :: "'action \<Rightarrow> (String.literal, int) bexp" where
"num_inv_guard a = bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) (n_inv a))"

definition num_goal_guard :: "(String.literal, int) bexp" where
"num_goal_guard = bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) num_goal)"

definition num_upd :: "'snap_action \<Rightarrow> (String.literal \<times> (String.literal, int) exp) list" where
"num_upd s = map (\<lambda>(f, e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) (upds s)"

definition num_init_upd :: "(String.literal \<times> (String.literal, int) exp) list" where
"num_init_upd = map (\<lambda>f. (fluent_to_var f, exp.const (const_to_int (num_init f)))) nfluents"

text \<open>Faithfulness of the integer encoding on the discrete fragment (NUMERIC_PLAN A.3): a numeric
expression is @{emph \<open>ok\<close>} at a valuation when every leaf reads a declared, integer-valued fluent or an
integer constant and every division divides exactly -- the side-condition under which the truncating
Munta integer arithmetic agrees with the abstract field arithmetic. Hoisted here (into the defs locale,
above the well-formedness assumptions) so the grounder-match contract can reference it.\<close>
fun nexp_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n, 'r) nexp \<Rightarrow> bool" where
  "nexp_ok w (NConst c) \<longleftrightarrow> c \<in> \<int>"
| "nexp_ok w (NVar f)   \<longleftrightarrow> f \<in> set nfluents \<and> (\<exists>r. w f = Some r \<and> r \<in> \<int>)"
| "nexp_ok w (NAdd a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NSub a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NMul a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"
| "nexp_ok w (NDiv a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b
     \<and> the (eval_nexp w b) \<noteq> 0
     \<and> const_to_int (the (eval_nexp w b)) dvd const_to_int (the (eval_nexp w a))"

text \<open>@{term \<open>comp_ok w c\<close>}: both sides of the comparison are faithful numeric expressions.\<close>
fun comp_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> ('n, 'r) comp \<Rightarrow> bool" where
  "comp_ok w (Comp p a b) \<longleftrightarrow> nexp_ok w a \<and> nexp_ok w b"

text \<open>A valuation is @{emph \<open>integer-ok\<close>} when every declared fluent is defined and integer-valued
(the encoding @{term const_to_int} round-trips on it), and @{emph \<open>in bounds\<close>} when each fluent's
integer encoding lies within its declared variable range.\<close>
definition num_val_ok :: "('n \<rightharpoonup> 'r) \<Rightarrow> bool" where
"num_val_ok w \<longleftrightarrow> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> r \<in> \<int>)"

definition fluent_in_bounds :: "('n \<rightharpoonup> 'r) \<Rightarrow> bool" where
"fluent_in_bounds w \<longleftrightarrow> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> r \<in> \<int>
    \<and> fluent_lo f \<le> const_to_int r \<and> const_to_int r \<le> fluent_hi f)"

text \<open>In-bounds subsumes integer-OK: the bounded valuation is in particular integer-valued.\<close>
lemma fluent_in_bounds_imp_num_val_ok: "fluent_in_bounds w \<Longrightarrow> num_val_ok w"
  unfolding fluent_in_bounds_def num_val_ok_def by blast

text \<open>Append a numeric \<open>bexp\<close> guard (conjoined) and numeric \<open>(var, exp)\<close> updates (after the
propositional ones) to a propositional edge, leaving source/target locations, clock constraints, the
action label and clock resets untouched -- so the numeric net's propositional projection is the
propositional net.\<close>
definition augment_edge where
"augment_edge g u e =
  (let (src, b, ac, act, upd, rst, tgt) = e in (src, bexp.and b g, ac, act, upd @ u, rst, tgt))"

definition "num_start_edge a =
  augment_edge (num_pre_guard (at_start a)) (num_upd (at_start a)) (start_edge a)"
definition "num_end_edge a =
  augment_edge (num_pre_guard (at_end a)) (num_upd (at_end a)) (end_edge a)"
definition "num_edge_2 a = augment_edge (num_inv_guard a) [] (edge_2 a)"
definition "num_edge_3 a = augment_edge (num_inv_guard a) [] (edge_3 a)"

text \<open>One automaton per action: the start/end snaps carry numeric guards+updates and the running-entry
edge \<open>edge_2\<close> carries the numeric \<open>over_all\<close> invariant. The duration edge \<open>edge_3\<close> and the
instant edge \<open>instant_trans_edge\<close> are reused unchanged.\<close>
definition "num_action_to_automaton a =
(let
  committed_locs = (Nil::nat list);
  urgent_locs = [starting_loc, ending_loc];
  edges = [num_start_edge a, num_edge_2 a, num_edge_3 a, num_end_edge a, instant_trans_edge a];
  invs = []::(nat \<times> (String.literal, int) acconstraint list) list
in (committed_locs, urgent_locs, edges, invs))"

text \<open>The main automaton additionally sets each fluent to its initial value on the init edge and checks
the numeric goal \<open>num_goal\<close> on the goal edge.\<close>
definition "num_main_auto_init_edge = augment_edge bexp.true num_init_upd main_auto_init_edge"
definition "num_main_auto_goal_edge = augment_edge num_goal_guard [] main_auto_goal_edge"

definition "num_main_auto =
(let
  committed_locs = [];
  urgent_locs = [init_loc, goal_loc];
  edges = [num_main_auto_init_edge, num_main_auto_goal_edge, main_auto_loop];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

definition "num_timed_automaton_net = num_main_auto # (map num_action_to_automaton actions)"

text \<open>The numeric network's variable bounds and initial valuation: the propositional declarations plus
one bounded \<open>int\<close> variable per fluent (initialised to its lower bound, then set to \<open>num_init\<close> on the
init edge). Locations and the reachability \<open>reach_formula\<close> are unchanged -- the numeric goal is enforced
on the goal edge.\<close>
abbreviation "num_net_bounds::(String.literal \<times> int \<times> int) list \<equiv> num_all_vars"
definition "num_init_vars::(String.literal \<times> int) list \<equiv> map (map_prod id fst) num_all_vars"

end

section \<open>Well-formedness of the numeric data (the grounder-match contract)\<close>

text \<open>These predicates state the conditions the numeric input must satisfy for the reduction to be
sound. They are written to match, one-for-one, the guarantees the grounder produces
(NUMERIC_PLAN A.2/A.3/B).\<close>

definition upds_functional_list :: "('n \<times> ('n, 'r) nexp) list \<Rightarrow> bool" where
"upds_functional_list us \<longleftrightarrow> distinct (map fst us)"

definition upds_no_cross_read_list :: "('n \<times> ('n, 'r) nexp) list \<Rightarrow> bool" where
"upds_no_cross_read_list us \<longleftrightarrow> (\<forall>(f, e) \<in> set us. nexp_fluents e \<inter> (fst ` set us - {f}) = {})"

text \<open>The element-level fact: a fluent read by an effect's RHS that is also written by the snap can
only be that effect's own left-hand side (so a self-update reads the pre-state of its own fluent, never
another co-written fluent).\<close>
lemma upds_no_cross_read_listD:
  assumes "upds_no_cross_read_list us"
      and "(f, e) \<in> set us"
      and "g \<in> nexp_fluents e"
      and "g \<in> fst ` set us"
    shows "g = f"
  using assms unfolding upds_no_cross_read_list_def by fast

text \<open>The numeric reduction propeItr: the spec locale plus well-formedness. \<open>upds\<close> is functional (one
assignment per fluent, from the grounder's combination-normalisation) and cross-read-free; per-fluent
bounds are valid; the fluent variable names are injective and FRESH (disjoint from the propositional
variable names, so numeric variables never gate a propositional edge -- the keystone of the
additive-tracking architecture, NUMERIC_PLAN A.6/5.5).\<close>
locale numeric_tp_nta_reduction = numeric_tp_nta_reduction_defs
  init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
  n_pre n_inv upds num_init num_goal nfluents fluent_to_name fluent_lo fluent_hi const_to_int +
  fluent_names: unique_names fluent_to_name "set nfluents"
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
    and n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_name :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int" +
  assumes upds_functional_start:   "\<forall>a \<in> set actions. upds_functional_list (upds (at_start a))"
      and upds_functional_end:     "\<forall>a \<in> set actions. upds_functional_list (upds (at_end a))"
      and upds_no_cross_read_start: "\<forall>a \<in> set actions. upds_no_cross_read_list (upds (at_start a))"
      and upds_no_cross_read_end:   "\<forall>a \<in> set actions. upds_no_cross_read_list (upds (at_end a))"
      and fluent_bounds_valid:      "\<forall>f \<in> set nfluents. fluent_lo f \<le> fluent_hi f"
      \<comment> \<open>Integer-encoding faithfulness, the grounder-match contract for the discrete fragment
         (NUMERIC_PLAN A.3): on any integer-valued (@{const num_val_ok}) valuation every snap's update
         RHS and pre/over_all comparison is @{const nexp_ok}/@{const comp_ok} (declared integer reads,
         exact divisions), and the initial valuation is integer-valued. These are static and
         grounder-checkable. Range-boundedness is a @{emph \<open>reachability\<close>} property (a global closure
         over all in-range valuations is false for monotone effects), so it is assumed M-scoped -- the
         certified plan's valuations stay within the declared variable bounds -- as @{text num_seq_in_bounds}
         in the \<open>numeric_tp_nta_reduction_correctness\<close> locale (where the state sequence is in scope); the
         intermediate partial-fold stores are then derived in range from the happening endpoints.\<close>
      and snap_upds_nexp_ok_start:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_start a)). nexp_ok w e)"
      and snap_upds_nexp_ok_end:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>(f, e) \<in> set (upds (at_end a)). nexp_ok w e)"
      and snap_pre_comp_ok_start:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_start a)). comp_ok w c)"
      and snap_pre_comp_ok_end:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_pre (at_end a)). comp_ok w c)"
      and snap_inv_comp_ok:
            "\<forall>a \<in> set actions. \<forall>w. num_val_ok w \<longrightarrow> (\<forall>c \<in> set (n_inv a). comp_ok w c)"
      and num_init_val_ok: "\<forall>f \<in> set nfluents. num_init f \<in> \<int>"
      \<comment> \<open>Faithfulness of the constant-to-int encoding on integer constants: @{term const_to_int}
         is a left inverse of @{term Int.of_int} (a property of the fixed @{term const_to_int}
         parameter, alongside the integrality assumptions above). @{term m} free \<Longrightarrow> implicitly \<And>m.\<close>
      and const_to_int_of_int: "const_to_int (Int.of_int m) = m"
      \<comment> \<open>Snap effects write only DECLARED fluents (grounder-match): every update LHS is in
         @{term nfluents}. Needed for the integer-encoding to land on declared fluent variables.\<close>
      and snap_writes_nfluents_start:
            "\<forall>a \<in> set actions. fst ` set (upds (at_start a)) \<subseteq> set nfluents"
      and snap_writes_nfluents_end:
            "\<forall>a \<in> set actions. fst ` set (upds (at_end a)) \<subseteq> set nfluents"
      \<comment> \<open>Numeric over_all invariants: the OLD static contract -- @{text n_inv_eq} (equalities only) +
         @{text n_inv_readonly} (over_all fluents never written by any snap) + @{text n_inv_init_sat}
         (over_all hold at the initial valuation), discharged via a "read-only \<Rightarrow> constant = initial value"
         shortcut -- has been DROPPED (backlog #8, the lock-based over_all redesign; see
         \<open>NUMERIC_OVERALL_REDESIGN.md\<close>). The general over_all fragment is now GENERAL (arbitrary
         while-active comparisons), and the @{text num_edge_2} (start) and @{text num_edge_3} (end)
         over_all guards are discharged from plan validity's active clause via
         @{text starting_index_active_Suc} / @{text ending_index_inv_sat} -- a sound over-approximation
         (no lock, no write-guard).\<close>

begin

text \<open>The fluent variable names are injective on the declared fluents (now a LEMMA off the defined
\<open>fluent_to_var\<close>: the \<open>''fluent_''\<close> prefix is injective, and \<open>fluent_to_name\<close> is injective on
\<open>nfluents\<close> by the \<open>fluent_names\<close> sublocale). Mirrors \<open>variables_inj\<close>.\<close>
lemma fluent_to_var_inj: "inj_on fluent_to_var (set nfluents)"
  unfolding fluent_to_var_def inj_on_def
  by (intro ballI impI, (subst (asm) String.add_literal_code String.Literal_eq_iff)+,
      use fluent_names.names_unique in blast)

text \<open>The fluent variable names are FRESH: disjoint from every propositional variable name in
\<open>all_vars\<close>. Pure prefix disjointness -- \<open>''fluent_''\<close> differs at char 0 from \<open>''lock_''\<close>/\<open>''var_''\<close>
(the \<open>prop_to_lock\<close>/\<open>prop_to_var\<close> images) and from \<open>''acts_active''\<close>/\<open>''planning_lock''\<close>. Mirrors the
prefix-disjointness of \<open>variables_unique\<close>.\<close>
lemma fluent_vars_fresh: "\<forall>f \<in> set nfluents. fluent_to_var f \<notin> fst ` set all_vars"
  unfolding all_vars_def fluent_to_var_def prop_to_var_def prop_to_lock_def
            acts_active_def planning_lock_def
  by (auto simp: Let_def String.add_literal_code)

end

text \<open>Primed numeric reduction-defs layer -- the numeric twin of @{locale tp_nta_reduction_defs'}.
  Built on @{locale temp_planning_problem_list_impl_int'} (whose @{text prob_list_impl_int} sublocale
  already discharges \<open>snaps_disj_on\<close> at @{const AtStart}/@{const AtEnd} via
  injectivity), it re-instantiates the unprimed numeric reduction on the @{type snap_action} datatype:
  the propositional data are the restricted @{text rat_impl.pre_imp_restr_list}/@{text add_imp_list}/
  @{text del_imp_list}, and the numeric data are lifted through \<open>app_snap\<close> (no props-restriction
  on fluents).  So @{text reduction_ref_impl} is the numeric net over injective snaps, where
  snap-distinctness is free.\<close>
locale numeric_tp_nta_reduction_defs' = temp_planning_problem_list_impl_int'
  at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions
  for init :: "'proposition list"
    and goal :: "'proposition list"
    and at_start :: "'action \<Rightarrow> 'snap_action"
    and at_end :: "'action \<Rightarrow> 'snap_action"
    and over_all :: "'action \<Rightarrow> 'proposition list"
    and lower :: "'action \<Rightarrow> int lower_bound option"
    and upper :: "'action \<Rightarrow> int upper_bound option"
    and pre :: "'snap_action \<Rightarrow> 'proposition list"
    and adds :: "'snap_action \<Rightarrow> 'proposition list"
    and dels :: "'snap_action \<Rightarrow> 'proposition list"
    and \<epsilon> :: "int"
    and props :: "'proposition list"
    and actions :: "'action list"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal" +
  fixes n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_name :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int"
begin
sublocale reduction_ref_impl: numeric_tp_nta_reduction_defs
  "rat_impl.list_inter props init"
  "rat_impl.list_inter props goal"
  AtStart AtEnd rat_impl.over_all_restr_list lower upper
  rat_impl.pre_imp_restr_list rat_impl.add_imp_list rat_impl.del_imp_list
  \<epsilon> props actions act_to_name prop_to_name
  "rat_impl.set_impl.app_snap n_pre" n_inv "rat_impl.set_impl.app_snap upds"
  num_init num_goal nfluents fluent_to_name fluent_lo fluent_hi const_to_int
  by unfold_locales

text \<open>Drop-in re-exposure: the ground numeric leaf refers to every reduction accessor as
\<open>ndefs.X\<close>; since the primed layer keeps the net under \<open>reduction_ref_impl\<close>, alias each accessor
(and its \<open>_def\<close>) up one level so the ground layer resolves unchanged.\<close>
  abbreviation "action_vars \<equiv> reduction_ref_impl.action_vars"
  abbreviation "acts_active \<equiv> reduction_ref_impl.acts_active"
  abbreviation "act_to_end_clock \<equiv> reduction_ref_impl.act_to_end_clock"
  abbreviation "act_to_start_clock \<equiv> reduction_ref_impl.act_to_start_clock"
  abbreviation "all_vars \<equiv> reduction_ref_impl.all_vars"
  abbreviation "augment_edge \<equiv> reduction_ref_impl.augment_edge"
  abbreviation "comp_ok \<equiv> reduction_ref_impl.comp_ok"
  abbreviation "edge_2 \<equiv> reduction_ref_impl.edge_2"
  abbreviation "edge_3 \<equiv> reduction_ref_impl.edge_3"
  abbreviation "end_edge \<equiv> reduction_ref_impl.end_edge"
  abbreviation "ending_loc \<equiv> reduction_ref_impl.ending_loc"
  abbreviation "fluent_in_bounds \<equiv> reduction_ref_impl.fluent_in_bounds"
  abbreviation "fluent_to_var \<equiv> reduction_ref_impl.fluent_to_var"
  abbreviation "goal_loc \<equiv> reduction_ref_impl.goal_loc"
  abbreviation "inc_prop_ab \<equiv> reduction_ref_impl.inc_prop_ab"
  abbreviation "inc_prop_lock_ab \<equiv> reduction_ref_impl.inc_prop_lock_ab"
  abbreviation "init_loc \<equiv> reduction_ref_impl.init_loc"
  abbreviation "init_locs \<equiv> reduction_ref_impl.init_locs"
  abbreviation "instant_trans_edge \<equiv> reduction_ref_impl.instant_trans_edge"
  abbreviation "inv_vars \<equiv> reduction_ref_impl.inv_vars"
  abbreviation "is_prop_ab \<equiv> reduction_ref_impl.is_prop_ab"
  abbreviation "is_prop_lock_ab \<equiv> reduction_ref_impl.is_prop_lock_ab"
  abbreviation "l_dur \<equiv> reduction_ref_impl.l_dur"
  abbreviation "main_auto_goal_edge \<equiv> reduction_ref_impl.main_auto_goal_edge"
  abbreviation "main_auto_init_edge \<equiv> reduction_ref_impl.main_auto_init_edge"
  abbreviation "main_auto_loop \<equiv> reduction_ref_impl.main_auto_loop"
  abbreviation "mutex_effects \<equiv> reduction_ref_impl.mutex_effects"
  abbreviation "net_bounds \<equiv> reduction_ref_impl.net_bounds"
  abbreviation "net_broadcast \<equiv> reduction_ref_impl.net_broadcast"
  abbreviation "net_int_clocks \<equiv> reduction_ref_impl.net_int_clocks"
  abbreviation "nexp_ok \<equiv> reduction_ref_impl.nexp_ok"
  abbreviation "num_action_to_automaton \<equiv> reduction_ref_impl.num_action_to_automaton"
  abbreviation "num_all_vars \<equiv> reduction_ref_impl.num_all_vars"
  abbreviation "num_edge_2 \<equiv> reduction_ref_impl.num_edge_2"
  abbreviation "num_edge_3 \<equiv> reduction_ref_impl.num_edge_3"
  abbreviation "num_end_edge \<equiv> reduction_ref_impl.num_end_edge"
  abbreviation "num_fluent_vars \<equiv> reduction_ref_impl.num_fluent_vars"
  abbreviation "num_goal_guard \<equiv> reduction_ref_impl.num_goal_guard"
  abbreviation "num_init_upd \<equiv> reduction_ref_impl.num_init_upd"
  abbreviation "num_init_vars \<equiv> reduction_ref_impl.num_init_vars"
  abbreviation "num_inv_guard \<equiv> reduction_ref_impl.num_inv_guard"
  abbreviation "num_main_auto \<equiv> reduction_ref_impl.num_main_auto"
  abbreviation "num_main_auto_goal_edge \<equiv> reduction_ref_impl.num_main_auto_goal_edge"
  abbreviation "num_main_auto_init_edge \<equiv> reduction_ref_impl.num_main_auto_init_edge"
  abbreviation "num_net_bounds \<equiv> reduction_ref_impl.num_net_bounds"
  abbreviation "num_pre_guard \<equiv> reduction_ref_impl.num_pre_guard"
  abbreviation "num_start_edge \<equiv> reduction_ref_impl.num_start_edge"
  abbreviation "num_timed_automaton_net \<equiv> reduction_ref_impl.num_timed_automaton_net"
  abbreviation "num_upd \<equiv> reduction_ref_impl.num_upd"
  abbreviation "num_val_ok \<equiv> reduction_ref_impl.num_val_ok"
  abbreviation "off_loc \<equiv> reduction_ref_impl.off_loc"
  abbreviation "planning_loc \<equiv> reduction_ref_impl.planning_loc"
  abbreviation "planning_lock \<equiv> reduction_ref_impl.planning_lock"
  abbreviation "pl_is_1 \<equiv> reduction_ref_impl.pl_is_1"
  abbreviation "prop_to_lock \<equiv> reduction_ref_impl.prop_to_lock"
  abbreviation "prop_to_var \<equiv> reduction_ref_impl.prop_to_var"
  abbreviation "reach_formula \<equiv> reduction_ref_impl.reach_formula"
  abbreviation "running_loc \<equiv> reduction_ref_impl.running_loc"
  abbreviation "set_prop_ab \<equiv> reduction_ref_impl.set_prop_ab"
  abbreviation "set_prop_lock_ab \<equiv> reduction_ref_impl.set_prop_lock_ab"
  abbreviation "snap_vars \<equiv> reduction_ref_impl.snap_vars"
  abbreviation "start_edge \<equiv> reduction_ref_impl.start_edge"
  abbreviation "starting_loc \<equiv> reduction_ref_impl.starting_loc"
  abbreviation "u_dur \<equiv> reduction_ref_impl.u_dur"
  lemmas action_vars_def = reduction_ref_impl.action_vars_def
  lemmas acts_active_def = reduction_ref_impl.acts_active_def
  lemmas act_to_end_clock_def = reduction_ref_impl.act_to_end_clock_def
  lemmas act_to_start_clock_def = reduction_ref_impl.act_to_start_clock_def
  lemmas all_vars_def = reduction_ref_impl.all_vars_def
  lemmas augment_edge_def = reduction_ref_impl.augment_edge_def
  lemmas edge_2_def = reduction_ref_impl.edge_2_def
  lemmas edge_3_def = reduction_ref_impl.edge_3_def
  lemmas end_edge_def = reduction_ref_impl.end_edge_def
  lemmas ending_loc_def = reduction_ref_impl.ending_loc_def
  lemmas fluent_to_var_def = reduction_ref_impl.fluent_to_var_def
  lemmas goal_loc_def = reduction_ref_impl.goal_loc_def
  lemmas inc_prop_ab_def = reduction_ref_impl.inc_prop_ab_def
  lemmas inc_prop_lock_ab_def = reduction_ref_impl.inc_prop_lock_ab_def
  lemmas init_loc_def = reduction_ref_impl.init_loc_def
  lemmas init_locs_def = reduction_ref_impl.init_locs_def
  lemmas instant_trans_edge_def = reduction_ref_impl.instant_trans_edge_def
  lemmas inv_vars_def = reduction_ref_impl.inv_vars_def
  lemmas is_prop_ab_def = reduction_ref_impl.is_prop_ab_def
  lemmas is_prop_lock_ab_def = reduction_ref_impl.is_prop_lock_ab_def
  lemmas l_dur_def = reduction_ref_impl.l_dur_def
  lemmas main_auto_goal_edge_def = reduction_ref_impl.main_auto_goal_edge_def
  lemmas main_auto_init_edge_def = reduction_ref_impl.main_auto_init_edge_def
  lemmas main_auto_loop_def = reduction_ref_impl.main_auto_loop_def
  lemmas net_broadcast_def = reduction_ref_impl.net_broadcast_def
  lemmas net_int_clocks_def = reduction_ref_impl.net_int_clocks_def
  lemmas num_action_to_automaton_def = reduction_ref_impl.num_action_to_automaton_def
  lemmas num_all_vars_def = reduction_ref_impl.num_all_vars_def
  lemmas num_edge_2_def = reduction_ref_impl.num_edge_2_def
  lemmas num_edge_3_def = reduction_ref_impl.num_edge_3_def
  lemmas num_end_edge_def = reduction_ref_impl.num_end_edge_def
  lemmas num_fluent_vars_def = reduction_ref_impl.num_fluent_vars_def
  lemmas num_goal_guard_def = reduction_ref_impl.num_goal_guard_def
  lemmas num_init_upd_def = reduction_ref_impl.num_init_upd_def
  lemmas num_init_vars_def = reduction_ref_impl.num_init_vars_def
  lemmas num_inv_guard_def = reduction_ref_impl.num_inv_guard_def
  lemmas num_main_auto_def = reduction_ref_impl.num_main_auto_def
  lemmas num_main_auto_goal_edge_def = reduction_ref_impl.num_main_auto_goal_edge_def
  lemmas num_main_auto_init_edge_def = reduction_ref_impl.num_main_auto_init_edge_def
  lemmas num_pre_guard_def = reduction_ref_impl.num_pre_guard_def
  lemmas num_start_edge_def = reduction_ref_impl.num_start_edge_def
  lemmas num_timed_automaton_net_def = reduction_ref_impl.num_timed_automaton_net_def
  lemmas num_upd_def = reduction_ref_impl.num_upd_def
  lemmas off_loc_def = reduction_ref_impl.off_loc_def
  lemmas planning_loc_def = reduction_ref_impl.planning_loc_def
  lemmas planning_lock_def = reduction_ref_impl.planning_lock_def
  lemmas pl_is_1_def = reduction_ref_impl.pl_is_1_def
  lemmas prop_to_lock_def = reduction_ref_impl.prop_to_lock_def
  lemmas prop_to_var_def = reduction_ref_impl.prop_to_var_def
  lemmas reach_formula_def = reduction_ref_impl.reach_formula_def
  lemmas running_loc_def = reduction_ref_impl.running_loc_def
  lemmas set_prop_ab_def = reduction_ref_impl.set_prop_ab_def
  lemmas set_prop_lock_ab_def = reduction_ref_impl.set_prop_lock_ab_def
  lemmas snap_vars_def = reduction_ref_impl.snap_vars_def
  lemmas start_edge_def = reduction_ref_impl.start_edge_def
  lemmas starting_loc_def = reduction_ref_impl.starting_loc_def
  lemmas u_dur_def = reduction_ref_impl.u_dur_def
end

end

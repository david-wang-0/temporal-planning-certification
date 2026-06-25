theory TP_NTA_Reduction_Correctness_Numeric_Tracking
  imports TP_NTA_Reduction_Correctness
begin

section \<open>Numeric reduction correctness (Layer B)\<close>

text \<open>The numeric correctness locale merges three layers at the @{emph \<open>same\<close>} propositional
parameters: the propositional reduction correctness @{locale tp_nta_reduction_correctness} (which
gives the @{emph \<open>forward\<close>} direction -- a valid plan induces a goal-reaching run via @{text plan_steps}
and the step lemmas, i.e. the soundness-of-certification direction, @{emph \<open>not\<close>} a full bisimulation),
the numeric net @{locale numeric_tp_nta_reduction} (list-valued numeric data, the numeric automata
@{text num_timed_automaton_net}, and the grounder-match well-formedness), and the abstract numeric
plan layer @{locale numeric_temp_plan_for_problem_list_impl_int} instantiated at the @{text \<open>set o _\<close>}
projection of the list numeric data (so its @{text num_rat_impl} interprets @{locale
numeric_temp_plan_defs} at the rat-refined parameters, where @{text num_valid_plan} lives). The one
genuinely new assumption -- everything else is @{emph \<open>fixes\<close>}-only over shared ancestors -- is that
the numeric plan is valid (@{text num_rat_impl.num_valid_plan}), strengthening the propositional
@{text valid_plan} the reduction already assumes.\<close>
locale numeric_tp_nta_reduction_correctness =
  tp_nta_reduction_correctness
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions \<pi> act_to_name prop_to_name +
  numeric_tp_nta_reduction
    init goal at_start at_end over_all lower upper pre adds dels \<epsilon> props actions act_to_name prop_to_name
    n_pre n_inv upds num_init num_goal nfluents fluent_to_var fluent_lo fluent_hi const_to_int +
  num_plan: numeric_temp_plan_for_problem_list_impl_int
    at_start at_end over_all lower upper pre adds dels init goal \<epsilon> props actions \<pi>
    "set o n_pre" "set o n_inv" "set o upds"
    "\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None" "set num_goal"
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
    and \<pi> :: "('i, 'action, int) temp_plan"
    and act_to_name :: "'action \<Rightarrow> String.literal"
    and prop_to_name :: "'proposition \<Rightarrow> String.literal"
    and n_pre :: "'snap_action \<Rightarrow> ('n, 'r::linordered_field) comp list"
    and n_inv :: "'action \<Rightarrow> ('n, 'r) comp list"
    and upds :: "'snap_action \<Rightarrow> ('n \<times> ('n, 'r) nexp) list"
    and num_init :: "'n \<Rightarrow> 'r"
    and num_goal :: "('n, 'r) comp list"
    and nfluents :: "'n list"
    and fluent_to_var :: "'n \<Rightarrow> String.literal"
    and fluent_lo :: "'n \<Rightarrow> int"
    and fluent_hi :: "'n \<Rightarrow> int"
    and const_to_int :: "'r \<Rightarrow> int" +
  assumes num_valid: "num_plan.num_rat_impl.num_valid_plan"
      and const_to_int_of_int: "const_to_int (Int.of_int m) = m"
      \<comment> \<open>The range-boundedness reachability invariant (grounder-match contract, complementing the
         static integrality assumptions in @{locale numeric_tp_nta_reduction}): along any valid numeric
         state sequence the per-happening valuations stay within the declared fluent variable bounds.
         A certifier checks this against the candidate plan's finite trace; PDDL supplies no bounds, and a
         global closure over all in-range valuations would be false for monotone effects. The intermediate
         partial-fold stores within a happening are derived in range from the @{term i}/@{term \<open>Suc i\<close>}
         endpoints (each fluent is written at most once, so a partial value is one of the two endpoints).
         Indexed by @{term \<open>rat_impl.htpl\<close>}, which the later \<open>rat_impl_htpl_eq\<close> equates with
         @{term \<open>planning_sem.htpl\<close>}.\<close>
      and num_seq_in_bounds:
            "\<And>M i. num_plan.num_rat_impl.num_valid_state_sequence M
               \<Longrightarrow> snd (M 0) = (\<lambda>f. if f \<in> set nfluents then Some (num_init f) else None)
               \<Longrightarrow> i \<le> length rat_impl.htpl
               \<Longrightarrow> fluent_in_bounds (snd (M i))"
begin

text \<open>The numeric network's Munta semantics, mirroring the propositional @{text net_impl}/@{text
graph_impl}: same broadcast channels (none), the augmented automata @{const num_timed_automaton_net},
and the augmented variable bounds @{const num_net_bounds}. @{locale Simple_Network_Impl} is
assumption-free, so this is a bare interpretation.\<close>
sublocale num_net_impl: Simple_Network_Impl num_timed_automaton_net net_broadcast num_net_bounds .
sublocale num_graph_impl: Graph_Defs
  "\<lambda>(L, s, u) (L', s', u'). step_u' num_net_impl.sem L s u L' s' u'" .

text \<open>Sanity: both nets and the numeric plan-validity are in scope at the shared parameters.\<close>
lemma num_net_in_scope: "num_timed_automaton_net = num_main_auto # map num_action_to_automaton actions"
  by (simp add: num_timed_automaton_net_def)

subsection \<open>Tracking the abstract numeric valuation in the integer variable store\<close>

text \<open>The integer variable store @{term v} TRACKS the abstract numeric valuation @{term w} when every
declared fluent is defined in @{term w} and its variable holds the integer encoding of that value.
Numeric fluents are FRESH (disjoint from the propositional variables, @{thm fluent_vars_fresh}), so
tracking constrains only the numeric sub-store and is preserved by every propositional update.\<close>
definition num_tracks :: "(String.literal \<rightharpoonup> int) \<Rightarrow> ('n \<rightharpoonup> 'r) \<Rightarrow> bool" where
"num_tracks v w \<longleftrightarrow> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> v (fluent_to_var f) = Some (const_to_int r))"

lemma num_tracksI:
  assumes "\<And>f. f \<in> set nfluents \<Longrightarrow> \<exists>r. w f = Some r \<and> v (fluent_to_var f) = Some (const_to_int r)"
  shows "num_tracks v w"
  using assms unfolding num_tracks_def by blast

lemma num_tracks_definedD:
  assumes "num_tracks v w" and "f \<in> set nfluents"
  shows "\<exists>r. w f = Some r"
  using assms unfolding num_tracks_def by blast

lemma num_tracks_varD:
  assumes "num_tracks v w" and "f \<in> set nfluents" and "w f = Some r"
  shows "v (fluent_to_var f) = Some (const_to_int r)"
  using assms unfolding num_tracks_def by force

subsection \<open>Faithfulness of the integer encoding on the discrete fragment\<close>

text \<open>On integer-valued operands @{term const_to_int} commutes with the arithmetic that
@{const nexp_to_exp} emits (@{const Int.of_int} round-trips through @{thm const_to_int_of_int}). For
division this needs the operand to divide exactly -- the documented @{text \<open>NDiv \<mapsto> div\<close>} gap, where
the truncating @{const divide_int_inst.divide_int} agrees with the field quotient only on exact
divisions.\<close>
lemma const_to_int_add:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "const_to_int (a + b) = const_to_int a + const_to_int b"
  using assms by (auto simp flip: of_int_add simp: const_to_int_of_int elim!: Ints_cases)

lemma const_to_int_diff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "const_to_int (a - b) = const_to_int a - const_to_int b"
  using assms by (auto simp flip: of_int_diff simp: const_to_int_of_int elim!: Ints_cases)

lemma const_to_int_mult:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "const_to_int (a * b) = const_to_int a * const_to_int b"
  using assms by (auto simp flip: of_int_mult simp: const_to_int_of_int elim!: Ints_cases)

lemma const_to_int_div:
  assumes "a \<in> \<int>" and "b \<in> \<int>" and "b \<noteq> 0"
      and "const_to_int b dvd const_to_int a"
    shows "const_to_int (a / b) = const_to_int a div const_to_int b"
proof -
  obtain ma where a: "a = Int.of_int ma" using assms(1) by (auto elim: Ints_cases)
  obtain mb where b: "b = Int.of_int mb" using assms(2) by (auto elim: Ints_cases)
  have mb0: "mb \<noteq> 0" using assms(3) b by auto
  have "mb dvd ma" using assms(4) a b const_to_int_of_int by simp
  then obtain q where q: "ma = mb * q" by blast
  have ab: "a / b = Int.of_int q"
    using a b mb0 q by (simp add: of_int_mult)
  have "const_to_int a div const_to_int b = q"
  proof -
    have ca: "const_to_int a = ma" using a const_to_int_of_int by simp
    have cb: "const_to_int b = mb" using b const_to_int_of_int by simp
    show ?thesis unfolding ca cb using q mb0 by (simp add: nonzero_mult_div_cancel_left)
  qed
  thus ?thesis using ab const_to_int_of_int by simp
qed

lemma Ints_div_exact:
  assumes "a \<in> \<int>" and "b \<in> \<int>" and "b \<noteq> 0"
      and "const_to_int b dvd const_to_int a"
    shows "a / b \<in> \<int>"
proof -
  obtain ma where a: "a = Int.of_int ma" using assms(1) by (auto elim: Ints_cases)
  obtain mb where b: "b = Int.of_int mb" using assms(2) by (auto elim: Ints_cases)
  have mb0: "mb \<noteq> 0" using assms(3) b by auto
  have "mb dvd ma" using assms(4) a b const_to_int_of_int by simp
  then obtain q where "ma = mb * q" by blast
  hence "a / b = Int.of_int q" using a b mb0 by (simp add: of_int_mult)
  thus ?thesis by (simp add: Ints_of_int)
qed

text \<open>The encoder-faithfulness side-conditions @{const nexp_ok} / @{const comp_ok} (every leaf reads a
declared, integer-valued fluent or an integer constant, and every @{term NDiv} divides exactly -- the
precise discrete-fragment condition under which the truncating Munta integer arithmetic agrees with the
abstract field arithmetic) are now defined in the @{locale numeric_tp_nta_reduction_defs} ancestor, so
the grounder-match well-formedness assumptions can reference them.\<close>

text \<open>The load-bearing correspondence: under a tracking store, a faithful numeric expression evaluates
abstractly to an integer-valued field element whose integer encoding is exactly what Munta computes for
the translated @{const nexp_to_exp}. A single induction gives evaluability, integer-valuedness and the
@{const is_val} agreement at once.\<close>
lemma nexp_ok_is_val:
  assumes "num_tracks v w" and "nexp_ok w e"
  shows "\<exists>r. eval_nexp w e = Some r \<and> r \<in> \<int>
           \<and> is_val v (nexp_to_exp fluent_to_var const_to_int e) (const_to_int r)"
  using assms(2)
proof (induction e)
  case (NConst c)
  thus ?case by (auto simp: is_val_simps)
next
  case (NVar f)
  then obtain r where f: "f \<in> set nfluents" and wf: "w f = Some r" and ri: "r \<in> \<int>" by auto
  have "v (fluent_to_var f) = Some (const_to_int r)" by (rule num_tracks_varD[OF assms(1) f wf])
  thus ?case using wf ri by (auto simp: is_val_simps)
next
  case (NAdd a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NAdd a b)) (const_to_int ra + const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NAdd a b)) (const_to_int (ra + rb))"
    using const_to_int_add[OF a(2) b(2)] by simp
  thus ?case using a(1,2) b(1,2) by (auto simp: Ints_add)
next
  case (NSub a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NSub a b)) (const_to_int ra - const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NSub a b)) (const_to_int (ra - rb))"
    using const_to_int_diff[OF a(2) b(2)] by simp
  thus ?case using a(1,2) b(1,2) by (auto simp: Ints_diff)
next
  case (NMul a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NMul a b)) (const_to_int ra * const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NMul a b)) (const_to_int (ra * rb))"
    using const_to_int_mult[OF a(2) b(2)] by simp
  thus ?case using a(1,2) b(1,2) by (auto simp: Ints_mult)
next
  case (NDiv a b)
  then obtain ra rb where
      a: "eval_nexp w a = Some ra" "ra \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int ra)"
    and b: "eval_nexp w b = Some rb" "rb \<in> \<int>" "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int rb)"
    by auto
  have nz: "rb \<noteq> 0" and dvd: "const_to_int rb dvd const_to_int ra"
    using NDiv.prems a(1) b(1) by auto
  have ev: "eval_nexp w (NDiv a b) = Some (ra / rb)" using a(1) b(1) nz by simp
  have iv: "ra / rb \<in> \<int>" by (rule Ints_div_exact[OF a(2) b(2) nz dvd])
  have "is_val v (nexp_to_exp fluent_to_var const_to_int (NDiv a b)) (const_to_int ra div const_to_int rb)"
    using a(3) b(3) by (force simp: is_val_simps)
  hence "is_val v (nexp_to_exp fluent_to_var const_to_int (NDiv a b)) (const_to_int (ra / rb))"
    using const_to_int_div[OF a(2) b(2) nz dvd] by simp
  thus ?case using ev iv by blast
qed

text \<open>On integer-valued operands the encoding @{term const_to_int} preserves equality and order (it
inverts the monotone @{const Int.of_int}), so each abstract comparison transfers to its Munta
@{const check_bexp} counterpart.\<close>
lemma const_to_int_eq_iff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "(const_to_int a = const_to_int b) = (a = b)"
  using assms by (auto elim!: Ints_cases simp: const_to_int_of_int)

lemma const_to_int_le_iff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "(const_to_int a \<le> const_to_int b) = (a \<le> b)"
  using assms by (auto elim!: Ints_cases simp: const_to_int_of_int)

lemma const_to_int_lt_iff:
  assumes "a \<in> \<int>" and "b \<in> \<int>"
  shows "(const_to_int a < const_to_int b) = (a < b)"
  using assms by (auto elim!: Ints_cases simp: const_to_int_of_int)


text \<open>A satisfied, faithful abstract comparison transfers to the translated Munta guard holding True.\<close>
lemma check_bexp_comp_to_bexp:
  assumes "num_tracks v w" and "comp_ok w c" and "sat_comp w c"
  shows "check_bexp v (comp_to_bexp fluent_to_var const_to_int c) True"
proof -
  obtain p a b where c: "c = Comp p a b" by (cases c) auto
  have oka: "nexp_ok w a" and okb: "nexp_ok w b" using assms(2) c by auto
  obtain x where x: "eval_nexp w a = Some x" "x \<in> \<int>"
    "is_val v (nexp_to_exp fluent_to_var const_to_int a) (const_to_int x)"
    using nexp_ok_is_val[OF assms(1) oka] by blast
  obtain y where y: "eval_nexp w b = Some y" "y \<in> \<int>"
    "is_val v (nexp_to_exp fluent_to_var const_to_int b) (const_to_int y)"
    using nexp_ok_is_val[OF assms(1) okb] by blast
  have rel: "cmp_op_rel p x y" using assms(3) c x(1) y(1) by (simp add: sat_comp_def)
  let ?ea = "nexp_to_exp fluent_to_var const_to_int a"
  let ?eb = "nexp_to_exp fluent_to_var const_to_int b"
  show ?thesis
  proof (cases p)
    case Ceq
    have "(const_to_int y = const_to_int x) = True"
      using rel Ceq const_to_int_eq_iff[OF x(2) y(2)] by auto
    moreover have "check_bexp v (bexp.eq ?ea ?eb) (const_to_int y = const_to_int x)"
      by (rule check_bexp_is_val.intros(6)[OF x(3) y(3)])
    ultimately show ?thesis using c Ceq by simp
  next
    case Cle
    have "(const_to_int x \<le> const_to_int y) = True"
      using rel Cle const_to_int_le_iff[OF x(2) y(2)] by simp
    moreover have "check_bexp v (bexp.le ?ea ?eb) (const_to_int x \<le> const_to_int y)"
      by (rule check_bexp_is_val.intros(7)[OF x(3) y(3)])
    ultimately show ?thesis using c Cle by simp
  next
    case Cge
    have "(const_to_int y \<le> const_to_int x) = True"
      using rel Cge const_to_int_le_iff[OF y(2) x(2)] by simp
    moreover have "check_bexp v (bexp.ge ?ea ?eb) (const_to_int x \<ge> const_to_int y)"
      by (rule check_bexp_is_val.intros(9)[OF x(3) y(3)])
    ultimately show ?thesis using c Cge by simp
  next
    case Clt
    have "(const_to_int x < const_to_int y) = True"
      using rel Clt const_to_int_lt_iff[OF x(2) y(2)] by simp
    moreover have "check_bexp v (bexp.lt ?ea ?eb) (const_to_int x < const_to_int y)"
      by (rule check_bexp_is_val.intros(8)[OF x(3) y(3)])
    ultimately show ?thesis using c Clt by simp
  next
    case Cgt
    have "(const_to_int y < const_to_int x) = True"
      using rel Cgt const_to_int_lt_iff[OF y(2) x(2)] by simp
    moreover have "check_bexp v (bexp.gt ?ea ?eb) (const_to_int x > const_to_int y)"
      by (rule check_bexp_is_val.intros(10)[OF x(3) y(3)])
    ultimately show ?thesis using c Cgt by simp
  qed
qed

text \<open>Lifted to a guard list: a conjunction of satisfied faithful comparisons makes the
@{const bexp_and_all} of their translations hold True. This is the shape of every numeric guard
(@{const num_pre_guard} / @{const num_inv_guard} / @{const num_goal_guard}).\<close>
lemma check_bexp_comps_guard:
  assumes "num_tracks v w" and "\<forall>c \<in> set cs. comp_ok w c" and "sat_comps w (set cs)"
  shows "check_bexp v (bexp_and_all (map (comp_to_bexp fluent_to_var const_to_int) cs)) True"
proof (rule check_bexp_all, intro ballI)
  fix b assume "b \<in> set (map (comp_to_bexp fluent_to_var const_to_int) cs)"
  then obtain c where c: "c \<in> set cs" "b = comp_to_bexp fluent_to_var const_to_int c" by auto
  have "comp_ok w c" using assms(2) c(1) by blast
  moreover have "sat_comp w c" using assms(3) c(1) by (simp add: sat_comps_def)
  ultimately show "check_bexp v b True"
    using check_bexp_comp_to_bexp[OF assms(1)] c(2) by blast
qed

subsection \<open>Tracking is preserved by the numeric updates\<close>

text \<open>A translated numeric expression's Munta value depends only on the store at the fluent variables
it reads, so a store change away from those variables leaves the value unchanged. This is the Munta
counterpart of @{thm [source] eval_nexp_cong}, and it is what makes the sequential Munta update fold
agree with the simultaneous abstract @{const apply_upds} under @{const upds_no_cross_read_list}.\<close>
lemma is_val_nexp_to_exp_cong:
  assumes "is_val v (nexp_to_exp fluent_to_var const_to_int e) k"
      and "\<And>f. f \<in> nexp_fluents e \<Longrightarrow> v' (fluent_to_var f) = v (fluent_to_var f)"
    shows "is_val v' (nexp_to_exp fluent_to_var const_to_int e) k"
  using assms by (induction e arbitrary: k) (auto simp: is_val_simps)

lemma nexp_ok_fluents:
  assumes "nexp_ok w e"
  shows "nexp_fluents e \<subseteq> set nfluents"
  using assms by (induction e) auto

lemma upds_functional_set:
  assumes "distinct (map fst us)"
  shows "upds_functional (set us)"
proof -
  have "e = e'" if "(f, e) \<in> set us" and "(f, e') \<in> set us" for f e e'
    using that assms by (metis map_of_is_SomeI option.inject)
  thus ?thesis unfolding upds_functional_def by auto
qed

text \<open>The sequential Munta update fold reaches the simultaneous override target: each fluent variable
ends holding the value its update's RHS evaluates to @{emph \<open>against the pre-state\<close>} @{term v}, and all
other variables are untouched. The @{const upds_no_cross_read_list} side-condition is exactly what lets
a later update's RHS ignore the earlier writes (via @{thm [source] is_val_nexp_to_exp_cong}).\<close>
lemma is_upds_num_upd_aux:
  assumes "distinct (map fst us)"
      and "\<And>f e. (f, e) \<in> set us \<Longrightarrow> nexp_fluents e \<inter> (fst ` set us - {f}) = {}"
      and "\<And>f e. (f, e) \<in> set us \<Longrightarrow> is_val v (nexp_to_exp fluent_to_var const_to_int e) (kv f)"
      and "inj_on fluent_to_var (fst ` set us \<union> (\<Union>(f, e)\<in>set us. nexp_fluents e))"
    shows "\<exists>v'. is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us) v'
             \<and> (\<forall>x. x \<notin> fluent_to_var ` fst ` set us \<longrightarrow> v' x = v x)
             \<and> (\<forall>(f,e) \<in> set us. v' (fluent_to_var f) = Some (kv f))"
  using assms
proof (induction us arbitrary: v)
  case Nil
  show ?case by (auto intro: is_upds.intros(1))
next
  case (Cons fe us')
  obtain f0 e0 where fe: "fe = (f0, e0)" by (cases fe)
  have f0_notin: "f0 \<notin> fst ` set us'" using Cons.prems(1) fe by auto
  have val0: "is_val v (nexp_to_exp fluent_to_var const_to_int e0) (kv f0)"
    using Cons.prems(3) fe by simp
  let ?v1 = "v(fluent_to_var f0 \<mapsto> kv f0)"
  have upd0: "is_upd v (fluent_to_var f0, nexp_to_exp fluent_to_var const_to_int e0) ?v1"
    unfolding is_upd_def using val0 by blast
  have dist': "distinct (map fst us')" using Cons.prems(1) fe by simp
  have nocross': "nexp_fluents e \<inter> (fst ` set us' - {f}) = {}" if "(f, e) \<in> set us'" for f e
    using Cons.prems(2)[of f e] fe that by auto
  have inj': "inj_on fluent_to_var (fst ` set us' \<union> (\<Union>(f, e)\<in>set us'. nexp_fluents e))"
    using Cons.prems(4) fe by (auto elim!: inj_on_subset)
  have val': "is_val ?v1 (nexp_to_exp fluent_to_var const_to_int e) (kv f)" if fe': "(f, e) \<in> set us'" for f e
  proof -
    have base: "is_val v (nexp_to_exp fluent_to_var const_to_int e) (kv f)"
      using Cons.prems(3) fe fe' by simp
    have "f \<noteq> f0" using f0_notin fe' by (metis image_eqI fst_conv)
    hence f0e: "f0 \<in> fst ` set (fe # us') - {f}" using fe by simp
    hence f0nr: "f0 \<notin> nexp_fluents e" using Cons.prems(2)[of f e] fe fe' by auto
    have agree: "?v1 (fluent_to_var g) = v (fluent_to_var g)" if "g \<in> nexp_fluents e" for g
    proof -
      have "g \<noteq> f0" using f0nr that by auto
      moreover have "g \<in> fst ` set (fe # us') \<union> (\<Union>(f, e)\<in>set (fe # us'). nexp_fluents e)"
        using that fe' by force
      moreover have "f0 \<in> fst ` set (fe # us') \<union> (\<Union>(f, e)\<in>set (fe # us'). nexp_fluents e)"
        using fe by simp
      ultimately have "fluent_to_var g \<noteq> fluent_to_var f0"
        by (rule inj_on_contraD[OF Cons.prems(4)])
      thus ?thesis by simp
    qed
    show ?thesis by (rule is_val_nexp_to_exp_cong[OF base agree])
  qed
  obtain v' where v':
      "is_upds ?v1 (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us') v'"
      "\<forall>x. x \<notin> fluent_to_var ` fst ` set us' \<longrightarrow> v' x = ?v1 x"
      "\<forall>(f,e) \<in> set us'. v' (fluent_to_var f) = Some (kv f)"
    using Cons.IH[OF dist' nocross' val' inj'] by blast
  have notin': "fluent_to_var f0 \<notin> fluent_to_var ` fst ` set us'"
    using f0_notin Cons.prems(4) fe by (auto simp: inj_on_def)
  show ?case
  proof (intro exI[of _ v'] conjI)
    show "is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) (fe # us')) v'"
      using is_upds.intros(2)[OF upd0 v'(1)] fe by simp
  next
    show "\<forall>x. x \<notin> fluent_to_var ` fst ` set (fe # us') \<longrightarrow> v' x = v x"
    proof (intro allI impI)
      fix x assume "x \<notin> fluent_to_var ` fst ` set (fe # us')"
      hence "x \<notin> fluent_to_var ` fst ` set us'" and "x \<noteq> fluent_to_var f0" using fe by auto
      thus "v' x = v x" using v'(2) by auto
    qed
  next
    show "\<forall>(f,e) \<in> set (fe # us'). v' (fluent_to_var f) = Some (kv f)"
    proof safe
      fix f e assume mem: "(f, e) \<in> set (fe # us')"
      show "v' (fluent_to_var f) = Some (kv f)"
      proof (cases "(f, e) \<in> set us'")
        case True thus ?thesis using v'(3) by auto
      next
        case False
        hence "f = f0" using mem fe by auto
        thus ?thesis using v'(2) notin' by simp
      qed
    qed
  qed
qed

text \<open>Per-snap interface: applying a well-formed snap's numeric updates via Munta @{const is_upds}
preserves tracking, landing on the abstract simultaneous update @{const apply_upds} of that snap's
@{term upds} (this is @{text snap_num_update} in the abstract set view). The propositional variables
are untouched, so a propositional transition lifts to the numeric net exactly when this fires.\<close>
lemma is_upds_num_upd:
  assumes tr: "num_tracks v w"
      and fn: "upds_functional_list us"
      and nc: "upds_no_cross_read_list us"
      and ok: "\<And>f e. (f, e) \<in> set us \<Longrightarrow> f \<in> set nfluents \<and> nexp_ok w e"
  obtains v' where
      "is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us) v'"
      and "num_tracks v' (apply_upds (set us) w)"
      and "\<And>x. x \<notin> fluent_to_var ` fst ` set us \<Longrightarrow> v' x = v x"
proof -
  have dist: "distinct (map fst us)" using fn by (simp add: upds_functional_list_def)
  have ufun: "upds_functional (set us)" by (rule upds_functional_set[OF dist])
  have fst_sub: "fst ` set us \<subseteq> set nfluents" using ok by auto
  have rd_sub: "(\<Union>(f, e)\<in>set us. nexp_fluents e) \<subseteq> set nfluents"
    using ok nexp_ok_fluents by fastforce
  let ?kv = "\<lambda>f. const_to_int (the (apply_upds (set us) w f))"
  have val: "is_val v (nexp_to_exp fluent_to_var const_to_int e) (?kv f)" if mem: "(f, e) \<in> set us" for f e
  proof -
    have "nexp_ok w e" using ok mem by blast
    then obtain r where r: "eval_nexp w e = Some r"
        and isv: "is_val v (nexp_to_exp fluent_to_var const_to_int e) (const_to_int r)"
      using nexp_ok_is_val[OF tr] by blast
    have "apply_upds (set us) w f = eval_nexp w e" by (rule apply_upds_in[OF ufun mem])
    hence "?kv f = const_to_int r" using r by simp
    thus ?thesis using isv by simp
  qed
  have ncr: "nexp_fluents e \<inter> (fst ` set us - {f}) = {}" if "(f, e) \<in> set us" for f e
  proof -
    have "\<forall>(f, e)\<in>set us. nexp_fluents e \<inter> (fst ` set us - {f}) = {}"
      using nc by (simp add: upds_no_cross_read_list_def)
    thus ?thesis using that by blast
  qed
  have inj: "inj_on fluent_to_var (fst ` set us \<union> (\<Union>(f, e)\<in>set us. nexp_fluents e))"
    by (rule inj_on_subset[OF fluent_to_var_inj]) (use fst_sub rd_sub in blast)
  obtain v' where v':
      "is_upds v (map (\<lambda>(f,e). (fluent_to_var f, nexp_to_exp fluent_to_var const_to_int e)) us) v'"
      "\<forall>x. x \<notin> fluent_to_var ` fst ` set us \<longrightarrow> v' x = v x"
      "\<forall>(f,e) \<in> set us. v' (fluent_to_var f) = Some (?kv f)"
    using is_upds_num_upd_aux[where kv = "\<lambda>f. const_to_int (the (apply_upds (set us) w f))",
                              OF dist ncr val inj] by blast
  have track: "num_tracks v' (apply_upds (set us) w)"
  proof (rule num_tracksI)
    fix g assume g: "g \<in> set nfluents"
    show "\<exists>r. apply_upds (set us) w g = Some r \<and> v' (fluent_to_var g) = Some (const_to_int r)"
    proof (cases "g \<in> fst ` set us")
      case True
      then obtain e where e: "(g, e) \<in> set us" by auto
      have "nexp_ok w e" using ok e by blast
      then obtain r where r: "eval_nexp w e = Some r" using nexp_ok_is_val[OF tr] by blast
      have au: "apply_upds (set us) w g = Some r" using apply_upds_in[OF ufun e] r by simp
      have "v' (fluent_to_var g) = Some (?kv g)" using v'(3) e by auto
      hence "v' (fluent_to_var g) = Some (const_to_int r)" using au by simp
      thus ?thesis using au by blast
    next
      case False
      have au: "apply_upds (set us) w g = w g" by (rule apply_upds_notin[OF False])
      obtain r where r: "w g = Some r" using num_tracks_definedD[OF tr g] by blast
      have "fluent_to_var g \<notin> fluent_to_var ` fst ` set us"
      proof
        assume "fluent_to_var g \<in> fluent_to_var ` fst ` set us"
        then obtain h where h: "h \<in> fst ` set us" "fluent_to_var g = fluent_to_var h" by auto
        have "g = h" using fluent_to_var_inj g fst_sub h by (auto dest: inj_onD)
        thus False using False h(1) by auto
      qed
      hence "v' (fluent_to_var g) = v (fluent_to_var g)" using v'(2) by auto
      hence "v' (fluent_to_var g) = Some (const_to_int r)" using num_tracks_varD[OF tr g r] by simp
      thus ?thesis using au r by simp
    qed
  qed
  have outside: "v' x = v x" if "x \<notin> fluent_to_var ` fst ` set us" for x
    using v'(2) that by blast
  show ?thesis by (rule that[OF v'(1) track outside])
qed

subsection \<open>Stronger numeric invariants (the propositional ones plus correct numeric tracking)\<close>

text \<open>The per-step invariants of the propositional bisimulation, strengthened with the requirement that
the integer variable store @{emph \<open>also\<close>} tracks the abstract numeric valuation at the matching index
(NUMERIC_PLAN A.6 / 5.5). @{term M} is the abstract numeric state sequence supplied by
@{text num_valid_plan}: @{term \<open>snd (M i)\<close>} is the valuation @{emph \<open>before\<close>} happening @{term i} and
@{term \<open>snd (M (Suc i))\<close>} the valuation after it. Each twin implies its propositional original, so the
projection direction reuses the existing proof verbatim; the extra @{const num_tracks} conjunct is the
new numeric content threaded through the run.\<close>

text \<open>The numeric structural invariant, the full-store analogue of @{const Lv_conds}: it is the
propositional @{const Lv_conds} content (length / head location / @{const planning_lock}) but with the
boundedness stated against the FULL numeric bounds @{const num_net_bounds}. It is factored OUT of the
numeric twins below and carried as a SEPARATE conjunct (@{text num_LvP}) throughout the numeric run,
exactly as @{const LvP} is carried through the propositional run.\<close>
definition "num_Lv_conds L v \<equiv>
  length L = Suc (length actions)
\<and> L ! 0 = planning_loc
\<and> Simple_Network_Language.bounded (map_of num_net_bounds) v
\<and> v planning_lock = Some 1"

fun num_LvP :: "(nat list \<times> (String.literal \<Rightarrow> int option) \<times> (String.literal \<Rightarrow> real)) \<Rightarrow> bool" where
  "num_LvP (L, v, c) = num_Lv_conds L v"

lemma num_Lv_condsI:
  assumes "length L = Suc (length actions)"
    "L ! 0 = planning_loc"
    "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    "v planning_lock = Some 1"
  shows "num_Lv_conds L v"
  using assms unfolding num_Lv_conds_def by blast

lemma num_Lv_conds_dests:
  assumes "num_Lv_conds L v"
  shows "length L = Suc (length actions)"
    "L ! 0 = planning_loc"
    "Simple_Network_Language.bounded (map_of num_net_bounds) v"
    "v planning_lock = Some 1"
  using assms unfolding num_Lv_conds_def by auto

lemma num_Lv_conds_maintained:
  assumes "num_Lv_conds L v"
    and "length L = length L'"
    and "L ! 0 = L' ! 0"
    and "v' planning_lock = v planning_lock"
    and "Simple_Network_Language.bounded (map_of num_net_bounds) v \<Longrightarrow> Simple_Network_Language.bounded (map_of num_net_bounds) v'"
  shows "num_Lv_conds L' v'"
  using assms unfolding num_Lv_conds_def by simp

definition "num_happening_pre M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_pre i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M i)))"

definition "num_happening_pre_pre_delay M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M i)))"

definition "num_happening_post M i Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> happening_post i (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M (Suc i))))"

definition "num_init_planning_state_props' M Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> init_planning_state_props' (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M 0)))"

definition "num_goal_trans_pre M Lvc \<equiv>
  (case Lvc of (L, v, c) \<Rightarrow> goal_trans_pre (L, v |` dom (map_of net_bounds), c)
    \<and> num_tracks v (snd (M (length planning_sem.htpl))))"

lemma num_happening_preI:
  assumes "happening_pre i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M i))"
  shows "num_happening_pre M i (L, v, c)"
  using assms by (simp add: num_happening_pre_def)

lemma num_happening_pre_propD: "num_happening_pre M i (L, v, c) \<Longrightarrow> happening_pre i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_trackD: "num_happening_pre M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M i))"
  by (simp add: num_happening_pre_def)

lemma num_happening_pre_pre_delayI:
  assumes "happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M i))"
  shows "num_happening_pre_pre_delay M i (L, v, c)"
  using assms by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_propD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_pre_pre_delay_trackD:
  "num_happening_pre_pre_delay M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M i))"
  by (simp add: num_happening_pre_pre_delay_def)

lemma num_happening_postI:
  assumes "happening_post i (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M (Suc i)))"
  shows "num_happening_post M i (L, v, c)"
  using assms by (simp add: num_happening_post_def)

lemma num_happening_post_propD: "num_happening_post M i (L, v, c) \<Longrightarrow> happening_post i (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_happening_post_def)

lemma num_happening_post_trackD: "num_happening_post M i (L, v, c) \<Longrightarrow> num_tracks v (snd (M (Suc i)))"
  by (simp add: num_happening_post_def)

lemma num_init_planning_state_props'I:
  assumes "init_planning_state_props' (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M 0))"
  shows "num_init_planning_state_props' M (L, v, c)"
  using assms by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_propD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> init_planning_state_props' (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_init_planning_state_props'_def)

lemma num_init_planning_state_props'_trackD:
  "num_init_planning_state_props' M (L, v, c) \<Longrightarrow> num_tracks v (snd (M 0))"
  by (simp add: num_init_planning_state_props'_def)

lemma num_goal_trans_preI:
  assumes "goal_trans_pre (L, v |` dom (map_of net_bounds), c)" and "num_tracks v (snd (M (length planning_sem.htpl)))"
  shows "num_goal_trans_pre M (L, v, c)"
  using assms by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_propD: "num_goal_trans_pre M (L, v, c) \<Longrightarrow> goal_trans_pre (L, v |` dom (map_of net_bounds), c)"
  by (simp add: num_goal_trans_pre_def)

lemma num_goal_trans_pre_trackD:
  "num_goal_trans_pre M (L, v, c) \<Longrightarrow> num_tracks v (snd (M (length planning_sem.htpl)))"
  by (simp add: num_goal_trans_pre_def)


end

end

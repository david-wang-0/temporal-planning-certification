# Plan: Retire the `temporal-pddl-semantics` submodule; re-point onto Formal-PDDL-Semantics `Temporal_Planning`

Status: draft (2026-06-25). This is **P0** (`GROUNDING_PLAN.md` §3). Companions:
[GROUNDING_PLAN.md](GROUNDING_PLAN.md) (links here from §3), [NUMERIC_PLAN.md](NUMERIC_PLAN.md)
(§5 expanded). The ROOT files remain authoritative.

## UPDATE (2026-06-30) — the grounded-temporal locale now lives in the GROUNDER; REUSE it (do not mirror)

The classical grounder (standalone repo `Isabelle-PDDL-Grounding`, branch `verified-sat-planner`) was
refactored into a reusable/classical/temporal "ladder". It now PROVIDES the §2b grounded-temporal
characterization in session **`Grounding_Temporal_Common`**
(`Temporal_Grounding/Common/Temporal_PDDL_Normalization.thy`, imports `Temporal_Planning.Temporal_Well_Formedness`
+ `Grounding_Common.{PDDL_Normalization,Formula_Utils}`):
- `grounded_temporal_ac` (nullary head), `grounded_temporal_dom`/`grounded_temporal_prob`,
  `locale grounded_temporal_domain`/`grounded_temporal_problem` (extend `wf_ast_temporal_*`),
  `typeless_temporal_domain`/`problem` (sublocale into the grounder's `typeless_*_signature`),
  `prec_normed_dom` + `normalized_*` + `grounded_normalized_temporal_*`.
- Grounded-ness allows **nullary numeric functions** (`grounded_func`), not `functions D = []`.
- `prec_normed_dom` uses the **classical right-deep `is_conj`** (Grounding_Common.Formula_Utils), NOT
  the project's tree `is_pos_conj`.

**Decision (David, "use that"):** when (re)building the temporal grounded target, **import + reuse**
`Grounding_Temporal_Common.Temporal_PDDL_Normalization`'s `grounded_temporal_problem` for the
grounded-ness layer instead of writing/mirroring a `Grounded_Temporal_PDDL_Locales`. The project's
NTA-reduction-input bundle = grounder `grounded_temporal_problem` (nullary/typeless grounded-ness,
positivity-free) + project `positive_temporal_problem` (`is_pos_conj`) + `integer_duration_problem`.
Using only `grounded_temporal_problem` (not `grounded_normalized_*`) avoids the right-deep-`is_conj`
vs tree-`is_pos_conj` clash, since `is_conj` only enters `prec_normed_dom`. The completed nullary
check (`num_exp_no_args` for numeric/duration atoms) belongs with this reuse too.

**Positivity also moves to the grounder (David, 2026-06-30): add `positive_temporal_problem`.** The
grounder's temporal tree has NO positivity locale; only the CLASSICAL side has `relaxed_*`, and that
bundles positivity with **delete-relaxation** (`relaxed_action = is_pos_conj (ac_pre a) ∧ dels = []`,
`Classical_PDDL_Normalization.thy:258/261`) for datalog reachability. The NTA reduction is the REAL
problem (keeps deletes), so it must reuse only the **positivity** half. Spec (for a grounder session):
add a positivity-only `positive_temporal_problem` (`is_pos_conj` preconditions + goal, deletes intact)
to `Temporal_PDDL_Normalization.thy`, mirroring the `is_pos_conj` conjunct of classical `relaxed_*`,
using the grounder's `is_pos_conj`. **DONE + committed** in the grounder (`positive_temporal_problem`
in `Temporal_Grounding/Common/Temporal_PDDL_Normalization.thy`; `Grounding_Temporal_Common` builds
green). The negation-elimination and grounder-into-FPS follow-ups are tracked in the grounder repo's
`HANDOVER.md`.

**Project-side adaptation ("adapt the project's input to the grounder's output", David 2026-06-30):**
re-point the NTA-reduction-input (today's bundled `ground_ast_problem`) to consume the grounder's
output — extend grounder `grounded_temporal_problem` + `positive_temporal_problem` (+ a project
`integer_duration_problem` for the numeric-free phase) — and **retire the project-local
`is_pos_conj`/`is_pos_lit`/`pred_no_args`/`act_no_params`/... in favour of the grounder's**. This means
the project ADOPTS the grounder's `is_pos_conj` (right-deep; `is_pos_lit` accepts `eqAtm`±), so the
project's positivity-dependent proofs are re-proved against it — incl. re-deriving the duration-fold
`acts_non_intrf` insensitivity (transfers: `eqAtm`/numeric still aren't in adds/dels) and the
`init_no_args` lemma. `init_no_args` becomes a lemma from `grounded_temporal_prob`, not an assume.

**Wiring needed (disruptive — heap rebuild; coordinate timing):** add `Grounding_Temporal_Common`
to `PDDL_TP_Reduction`'s `sessions` in `ROOT` (grounder already a registered component); rebuild heaps.

**STATUS 2026-06-30: grounder side COMMITTED + green.** `grounded_temporal_problem` +
`positive_temporal_problem` are in the green normalization ladder (`Grounding_Temporal_Common`,
`Temporal_Grounding/Common/Temporal_PDDL_Normalization.thy`). The grounder's
reachability/relaxation/numeric sessions are **placeholder/sorried** and SEPARATE — do NOT depend on
them (depend only on `Grounding_Temporal_Common`). Grounder is standalone but a **registered Isabelle
component**, so importable without the FPS-merge. Ready to wire. Concrete order:
1. (build check) verify `Grounding_Temporal_Common` builds green in this environment.
2. add `Grounding_Temporal_Common` to `PDDL_TP_Reduction` `sessions`; `isabelle components -u .` /
   `make register-components`; rebuild the base/`PDDL_TP_Reduction` heap; restart jEdit.
3. re-point `ground_ast_problem` -> extend grounder `grounded_temporal_problem` +
   `positive_temporal_problem` (+ project `integer_duration_problem`); retire project-local
   `is_pos_conj`/`is_pos_lit`/`pred_no_args`/`act_no_params`/...; `init_no_args` becomes a lemma.
4. re-prove the ~5 reduction consumers + finish the Plan_Defs grind (duration-fold `acts_non_intrf`
   bridge + `validity => durations_match`) against the grounder's `is_pos_conj` (right-deep,
   eqAtm-accepting).

## HANDOFF (2026-06-29) — Problem_Defs GREEN; Plan_Defs 148 -> 61 (mechanical sweep done; 3 design/proof blockers)

**Problem_Defs.thy GREEN** (fully_processed + consolidated, 0 errors): the `is_pos_conj -> is_conj`
swap was ABANDONED (`is_pos_lit`/`is_pos_conj` stay narrow). Fix was restating `inst_snap_act_pres_pos`
at `dc=[]` (snap specs already pass `[]`), dropping its `sorry`, and removing the dead
`duration_constraint_as_formula_conj` + the unused copied `is_conj`/`un_and`/`conj_induct*` machinery.
Grounder/eqAtm design recorded in **GROUNDING_PLAN.md §4/§6** (reuse classical `ground_fmla` in
re-expansion `chi` + a constant-fold/feasibility-prune stage; no standalone eqAtm pass;
`check_ground_problem` to be retired). `Ground_PDDL_Problem_Defs` already assumes eqAtm-removed via
`positive_act_pres`.

**Plan_Defs.thy: 148 -> 61 errors** (no sorry; fully_processed + consolidated). The mechanical recipe
sweep (set-coercion, `#>`-disambiguation, `res_inst` arity, head/body schema, `Effect adds dels num`,
world-model PAIR `fst`, open-world `valuation`, lemma renames `wf_*` -> `wf_temporal_*`,
`resolve_action_wf` -> `resolve_temporal_action_wf`) is DONE. Deleted dead `res_inst_pre_pos` +
`res_inst_snap_action_pre_pos` (broken/false, unused). The remaining 61 are 3 NON-mechanical blockers:

1. **Duration-fold mismatch: FPS semantics snap vs NTA-reduction-target snap** (~1086-1117, ~1310-1346:
   `acts_of_temporal_plan_at_no_args` durative cases, `at_start_snap_at_t`, `at_end_snap_at_t_if_durative`).
   NB both are ABSTRACT definitions (not "exec" vs "spec" -- the FPS layer is abstract semantics, not the
   executable `*_impl`). The **FPS plan-validity semantics snap** `res_inst_snap_action _ At_Start`
   (= `inst_temporal_snap_action`, what `valid_temporal_state_seq`/`acts_of_temporal_plan_at` use) FOLDS
   the duration constraints into the precondition as numeric atoms; the **NTA-reduction-target snap**
   `at_start_spec` (locale parameter of `temp_plan_finite`) uses `inst_snap_action_body_elements [] cond
   deff _ 0` (duration stripped, carried as the locale's `lower_spec`/`upper_spec`). So
   `ground_act_no_args (res_inst_snap_action _)` and `at_start_spec a = res_inst_snap_action _` are FALSE
   as literal statements. FIX = bridge the two abstract snaps at the `to_literals`/predicate level
   (duration atoms drop under `to_literals`; predicate cond/adds/dels coincide), mirroring the green
   `over_all_spec_eq_res_inst_temporal_inv` bridge. (Duration-atom design family.)
2. **Missing `wf_world_model I`** (~1829, `abstr_state_list_nth_wf_world_model`): temporal wf-problem
   locale does NOT assume init wf (`wf_temporal_problem_def` has `wf_world_model (set (init P))`
   commented out, FPS `Temporal_Well_Formedness.thy:63`); FPS has `wf_I` only continuous-side. Add a
   temporal `wf_I` or route via `ast_cont_problem` `I_equiv`.
3. **Missing `valid_temporal_state_seq_app_iff`** (~1704-1705, `state_at_is_state_at`): the state-seq
   split lemma (`valid... M (xs@ys) ... <-> exists Mm. valid... M xs Mm /\ valid... Mm ys ...`) no longer
   exists by that name; re-prove over the 3-case `valid_temporal_state_seq` recursion.

(2)+(3) are self-contained lemma gaps and likely unblock downstream cascades; (1) is the design cluster.
The `validity => durations_match` carve-out (~2884) is currently blocked upstream, no sorry needed yet.



**Headline:** `Ground_PDDL_Plan_Defs.thy` went from a non-elaborating ~616-error wreck to **214 errors**,
fully elaborating, **0 sorry**, reprocess ~41s (a 114s `blast` at the old line 2476 was replaced by
`by (rule abstr_state_list_nth_Suc[OF i', symmetric])` — keep reprocesses fast). All foundational and
design-hard pieces are GREEN; what remains is a uniform mechanical grind over the `valid_ground_plan`
locale body plus one known derivation.

**GREEN (do not re-touch):**
- imports + const-renames + the bulk mechanical pass (resolve/schema-constructor/res_inst-arity/
  Ground_Action->GroundAction/subgoal-binder).
- `in_acts_of_temporal_plan_atE`, the wf-preservation cluster, the **list_pairwise de-duplication**
  (project `ListMisc.list_pairwise` REMOVED -> FPS `Utils.list_pairwise`; helpers
  `count_list_gt1_two_indices`/`two_indices_count_list_gt1` live in `ListMisc`).
- the **FULL duration cluster**: `duration_matches`/`durations_match`/`is_Func_Const \<equiv> \<not> dc_no_func`
  defined on the new types; all 6 bound lemmas green.
- `ground_act_pres_conv_pre_spec`/`add_preds`/`del_preds`, `acts_non_intrf_imp_mutex_snap_action`
  (the snap-mutex lemma), `ground_non_action_*` (now **nullary** `ground_non_action`).
- the early `valid_ground_plan` body: validity unpacking is **open-world** already, and — important —
  the **MUTEX RE-BRIDGE is already done**: `htps_acts_list_pairwise` / `all_htps_acts_non_intrf{,'}`
  via `valid_temporal_state_seq_list_pairwise_acts` + `list_pairwise_acts_distinctD`.
- `res_simple_act_name`/`res_durative_act_name`, `in_simple_actsE'`, `in_durative_actsE{,'}`
  (FIXME stubs / diverging `by auto` replaced by structured `is_act_simple_def`+`cases` proofs).

**REMAINING (214 errors, all in `valid_ground_plan` body ~line 1000-3162, densest 2451-2830):**
This is now *volume, not design*. The recurring fix patterns (the recipe below) applied lemma-by-lemma:
- `res_inst a b` (old 2-arg) -> `res_inst a` (1-arg); `res_inst_snap_action a b` stays 2-arg (annotation).
- new ast_effect is `Effect adds dels numeric`; `GroundAction pre eff` accessors; schema head/body shape.
- world model is a PAIR -> `\<in> fst M`; `apply_eff` is a `definition` (`apply_eff_def`/`apply_eff_unfold`).
- `valid_temporal_state_seq.induct` has 3 cases; happening correspondence is `mset`-based.
- open-world `valuation M \<Turnstile>\<^sub>m \<phi>` (closed-world `^c\<TTurnstile>=` gone).
- the diverging `is_act_simple` elims want structured `unfolding is_act_simple_def by (cases a) auto`.
- FPS reuse: `wf_apply_happ`, `wf_ground_action_wf_fmla_atom`, `apply_ground_actions_same_mset_eq_intro`,
  `apply_ground_actions_no_effect_intro`.
- **The ONE design-dependent proof left:** `validity \<Rightarrow> durations_match` (~line 2860). The new FPS
  `wf_plan_action` only gives `d \<ge> 0`, NOT duration-matching; derive `durations_match d dcs ps as`
  from the PLAN VALIDITY (`valid_temporal_state_seq_plan tp`) instead. FPS folds each duration
  constraint into the snap precondition: `inst_snap_action_body_elements`
  (`Continuous_Planning/Instantiations.thy:132`) appends
  `map (\<lambda>(x,y). (x, duration_constraint_as_formula y)) d` to the conditions;
  `duration_constraint_as_formula (DurationConstraint EQ r) = Atom (numericEqAtm DurationExpr r)`
  (LEQ/GEQ analogues); `inst_formula ... dur` substitutes `DurationExpr -> ConstantExpr d`. So
  validity's `valuation M \<Turnstile>\<^sub>m precondition (at_start/at_end snap)` already verifies `d = r` /
  `d \<le> r` / `d \<ge> r` (mind `filter_time_spec ta` annotation routing). My `duration_matches` def matches.

**Setup:** split base heap built (`isabelle jedit -d . -l Temporal_Planning_Base`); FPS change this
session is `Temporal_State_Sequence_Semantics` imports `Temporal_Happening_Semantics` (lighter).
Verify via `get_document_info wait_until_processed:true` (~41s full reprocess). Work top-down; the
caret-perspective means `get_command_info wait` on far regions returns unprocessed — drive the frontier
by editing.

### DECISION (2026-06-28) — duration-atom positivity (NEW design issue, not in the original recipe)

Fixed this session: line 756 (`ground_non_action_non_intrf` — unfold the numeric accessors
`lvalues`/`rvalues`/`additive_lvalues`, which reduce to `[]` for the empty-effect non-action); the
slow `by fastforce` at ~1010 (`res_inst_pre_pos` obtain — replaced with
`res_simple_act_name[OF assms] unfolding a(1) by auto`, now timing 0); and the `res_inst_pre_pos`
simple cluster (1012-1018: `action_params_match` takes the **head** `ActionHead n ps`, not the whole
schema; consumer applied `instantiate_action_schema_pres_pos[OF pres_pos]` so its `is_pos_conj pre`
side-condition is discharged concretely). 214 -> ~211.

**Blocker (design):** FPS's `inst_snap_action` folds duration constraints into the At_Start/At_End
snap **precondition** as numeric atoms (`cond @ map (\<lambda>(x,y).(x, duration_constraint_as_formula y))
dcs`). The grounding-soundness layer wants positive conjunctions of **predicate** atoms; shared
`is_pos_lit` catch-alls numeric atoms to `False`. So `res_inst_snap_action_pre_pos`
(`ground_act_pres_pos (the (res_inst_snap_action a b))`, ~1023) is **false as stated** for
At_Start/At_End.

**Maintainer decision: use the grounder's ACTUAL contract; numeric is handled separately.**
- Grounder contract = monotonicity in the predicate fact set (`valuation_pos_conj_mono`,
  classical `Reachability_Analysis` ~457): predAtm literals persist; non-predAtm positive literals
  (eqAtm, numeric) are model-INDEPENDENT (`cond_lit_model_indep`), routed to the datalog bridge as
  static conditions. Numeric duration atoms are model-independent (truth fixed by the plan duration),
  so same category as eqAtm.
- The classical grounder is **not implemented for numeric problems**; do **NOT** edit shared
  `is_pos_lit` (would break `cond_lit_translates_or_bot`/`dl_cond_rh`). Keep **project-local**.
- All three temporal uses of the stale `wm_basic_entails_pos_conj_iff_superset'` (Plan_Defs
  2740/2836/2887) need only the **FORWARD** direction `valuation M \<Turnstile>\<^sub>m F \<Longrightarrow> set (to_literals F)
  \<subseteq> fst M` (the live lemma is `pos_conj_models_iff_superset`, Problem_Defs ~388). The reverse is
  what fails for numeric atoms and is not needed.

**KEY SIMPLIFICATION (found during impl):** the project defines its **OWN** `is_pos_lit`/`is_pos_conj`
(Problem_Defs ~131, **not** the shared classical one): only `predAtm` and `\<not>\<bottom>` are positive;
`eqAtm` and **all numeric atoms are already `False`**. So no numeric-aware predicate is needed — and
the FORWARD direction `valuation M \<Turnstile>\<^sub>m F \<Longrightarrow> set (to_literals F) \<subseteq> fst M` holds for **any** F with
NO positivity hypothesis once `to_literals` is total (it keeps only positively-occurring predAtms;
numeric/eq/negated/\<or>/\<rightarrow> drop to `[]`). The input gate `act_pres_pos` (predAtm-only) already rules out
negative predicate literals, so soundness is preserved.

**Implemented + GREEN (Problem_Defs, verified fully_processed+consolidated, 0 errors):**
1. `to_literals` (Problem_Defs ~31) made **total** — catch-all `_ = []` (was partial; numeric atoms
   left it `undefined`, stalling the chain). Existing green lemmas unaffected (their eqAtm/numeric
   cases are vacuous: `is_pos_conj` is `False` there).
2. Forward keystone `to_literals_subset_if_models` (Problem_Defs ~407):
   `valuation M \<Turnstile>\<^sub>m form \<Longrightarrow> set (to_literals form) \<subseteq> fst M`, by induction (no positivity).

**CHAIN REWRITE PROGRESS (Plan_Defs, error count 214 -> 186):**
- `abstr_state_list ! i :: world_model` (a PAIR, per FPS `valid_temporal_state_seq`); sites using it as
  a set need `fst`. `plan_state_list` REDEFINED to
  `map (\<lambda>M. \<Union>f \<in> fst M. set (map to_predicate (to_literals f))) abstr_state_list` (the old
  `(to_literals #> map to_predicate #> set)` form is ambiguous once the arg type is pinned: BOTH `#>`
  notations -- `TP_Utils.comb` and `Syntax_Utils.fcomb` -- are in scope in Plan_Defs; use an explicit
  `\<Union>f\<in>_. _` instead). GREEN.
- **GREEN (bodies):** `pres_sat` and the goal subgoal of `temp_plan_valid` -- rewritten open-world via
  `to_literals_subset_if_models` + new helpers; `wm_basic_entails_pos_conj_iff_superset'` (stale name)
  removed; `is_pos_conj`/`ground_act_pres_pos` derivations dropped. NOTE: both still show "Bad context"
  at the *statement* line purely as a CASCADE from `invs_sat`'s open `qed` -- their bodies + `qed` are
  `finished`. `plan_happ_seq_alt` `set`-coerced -> green.
- **New helper lemmas (GREEN, ~line 247 / before `pres_sat`):** `valid_temporal_state_seq_head_precond`
  (head precond at the initial M, case-split on `ts`), `valid_temporal_state_seq_head_inv` (interval
  invariant at `M'' = apply_eff(\<dots>)M`, 3-case only), `lwm_basic_to_predicate_subset` (the reusable
  literal->predicate coercion bridge -- candidate to promote).
- Did NOT delete `res_inst_snap_action_pre_pos`(~1023, FALSE)/`res_inst_pre_pos`(~999): pres_sat no
  longer uses them but `invs_sat`'s still-broken body may; delete once `invs_sat` lands.

**`invs_sat` APPROACH (chosen 2026-06-28: interval form + point-based redefinition):** `invs_of_plan_at`
was **orphaned** by the re-point (referenced via `invs_of_plan_at_def` but never defined). DONE+GREEN:
redefined project-local, point-based, on the **clash-free** `res_inst_temporal_inv` (= precondition of the
`Over_All` snap via temporal-interpreted `res_inst_snap_action`; = continuous `res_inst_inv` by
`res_inst_inv_refine`, no `ast_cont_action_schema` clash): `invs_of_plan_at t \<pi>s \<equiv> {inv. \<exists>t' a.
(t',a)\<in>durative_acts \<pi>s \<and> t'<t \<and> t\<le>t'+duration a \<and> Some inv = res_inst_temporal_inv a}` (replaces the
deleted broken continuous `inst_cond_alt`). DONE+GREEN this round (error count 186 -> 176):
- **temporal bridge** `over_all_spec_eq_res_inst_temporal_inv`: `set (over_all_spec (Durative\<dots>)) =
  set (map to_predicate (to_literals (the (res_inst_temporal_inv (DurativePlanAction n [] dur)))))` +
  6 helpers (`to_literals_BigAnd`, `map_formula_BigAnd`, `to_literals_map_formula_inst_duration`,
  `to_literals_inst_formula_dur` [the dur-drop: `inst_formula f dur = map_formula ((\<lambda>x.
  inst_duration_in_atom x dur) o map_atom f)`, `inst_duration_in_atom (predAtm p a) _ = predAtm p a`],
  `filter_time_spec_append`, `to_literals_map_atom_duration_constraint`).
- **`plan_inv_seq_alt` retargeted GREEN** (res_inst_inv->res_inst_temporal_inv, inst_cond_alt->bridge,
  `res` to `Some` form for `bridge[OF res]`).
- **`plan_acts_no_args` fixed** (it had the same `action_params_match`-takes-the-head bug at the
  Simple/Durative `pm` steps; it was the "Undefined fact" blocking plan_inv_seq_alt).

REMAINING — only **`invs_sat`** (~2758): replace the closed-world `\<^sup>c\<TTurnstile>\<^sub>=` `entails` + the broken
`res_inst_inv`/`inst_snap_action`/`is_pos_conj` `pos_conj` block + stale `wm_basic_entails_pos_conj_iff_superset'`
with the STEP-2 key lemma `inv \<in> invs_of_plan_at (htps!i) tp \<Longrightarrow> valuation (abstr_state_list ! i) \<Turnstile>\<^sub>m inv`,
then keystone + `lwm_basic_to_predicate_subset` + the new (fst-coerced) `plan_state_list` def. The STEP-2
lemma: durative start `t'\<in>set htps` (`htps_prop` ~2023 / `ref_plan_start_in_htps`); `sorted_wrt (<) htps`
gives `t' = htps!j`, `j<i`, so `t'\<le>htps!(i-1)` (`i=0`: `t'<htps!0` impossible -> invs empty, vacuous);
hence `inv \<in> set (invs_of_temporal_plan_in_interval (htps!(i-1), htps!i) tp)`; then
`valid_temporal_state_seq_head_inv` on `valid_temporal_state_seq (abstr_state_list!(i-1)) (drop (i-1) htps)
tp final_state` + `abstr_state_list_nth_Suc[OF (i-1)]` (= `abstr_state_list!i`). Canonical end-of-interval
pattern: `Temporal_Continuous_Reduction.valid_temporal_plan_equiv` case 3 `invariants:`.

**(superseded by the above) earlier notes:** the
invariant chain still cites the *continuous* hierarchy (`ast_cont_action_schema`, `inst_snap_action`,
`res_inst_inv`, `invs_of_plan_at`, `inst_cond_alt`, `plan_inv_seq_alt`) instead of the *temporal* one
(`ast_temporal_action_schema`, `inst_temporal_snap_action`, `res_inst_temporal_inv`,
`invs_of_temporal_plan_in_interval`). Decisive error: `Type unification failed: Clash of types
"ast_temporal_action_schema" and "ast_cont_action_schema"` (e.g. `inst_snap_action` applied to a
`DurativeActionSchema`). Also a semantic alignment: the project checks invariants `\<subseteq> M i` (PRE-state)
whereas FPS checks the interval-invariant conjunct at `M'' = apply_eff(\<dots>)M` (POST-state); align via
the FPS interval `(htps!(i-1), htps!i)` whose `M''` = `abstr_state_list ! i` (existing green
`abstr_state_list_nth_Suc`), `i=0` discharged by the invariant set being empty.
**Route for `invs_sat`:** (1) use the green `imp_defs.rat_impl.invs_at_plan_inv_seq_alt`
(`Temporal_Plans.thy`) to express `invs_at plan_inv_seq (htps!i)` via `over_all_spec`/`ran abstr_plan`,
sidestepping `invs_of_plan_at`; (2) a new `over_all_spec` <-> `res_inst_temporal_inv` bridge at the
`to_literals` level (duration-constraint atoms drop under `to_literals`), replacing the broken
`inst_cond_alt`; (3) `valid_temporal_state_seq_head_inv` + `abstr_state_list_nth_Suc[OF (i-1)]`; (4)
`to_literals_subset_if_models` + `lwm_basic_to_predicate_subset` to land in `plan_state_list ! i`.

Also stale (not targeted): `plan_state_list_nth_conv_abstr_state_list_nth` (~1767) needs the same `fst`
coercion. Other Plan_Defs clusters (1115-2003, 2169-2348, 3178) remain the mechanical recipe grind.

## Session update (2026-06-26, cont.) — base-heap SPLIT + Plan_Defs re-bridge underway (uncommitted)

**Prerequisite DONE (FPS side).** The `_Alt` state-seq strategy below was executed: FPS commit
`1a3e116` adds `Temporal_Planning/Temporal_State_Sequence_Semantics.thy` (the temporal numeric-free
derivative — `acts_of_temporal_plan_at` / `valid_temporal_state_seq` / `valid_temporal_state_seq_plan`
+ the proved equivalence `valid_temporal_state_seq_plan_eq_valid_temp_plan2`), registered in the FPS
`Temporal_Planning` ROOT. No FPS `_Alt` registration needed after all — a fresh temporal theory was
written instead.

**Base heap RESTRUCTURED into two layers (build-iteration fix).** The old single
`Temporal_Planning_Base = Temporal_Planning + Munta-on-top` re-elaborated the **entire Munta tower
(~610 theories, ~33 min)** into the base heap on *every* rebuild — i.e. every time any FPS
`Temporal_Planning` theory changed — because Munta sat *above* the changing FPS layer and the cached
Munta session heaps live in a different heap tree (can't be inherited, only re-elaborated). Fix (in
`ROOT`):
- `Temporal_Munta_Base = Continuous_Planning + (List-Index + Munta_Certificate_Checker theories)` —
  the expensive, **stable** layer; built once (~32 min); NOT invalidated by `Temporal_Planning` edits.
- `Temporal_Planning_Base = Temporal_Munta_Base + (FPS Temporal_Planning.* theories)` — thin layer;
  rebuilds in **~1.5 min** on an FPS `Temporal_Planning` edit (Munta untouched).
- Added `sessions "Temporal_Planning"` to `PDDL_TP_Reduction` (its theories qualified-import
  `Temporal_Planning.Temporal_{Instantiations,Happening_Semantics,PDDL_Checker_Explicit}`); new
  `Temporal_Munta_Base/` dir (`.gitkeep`). Launch line UNCHANGED: `isabelle jedit -d . -l
  Temporal_Planning_Base`. **Net: FPS-edit -> project iteration drops from ~35 min to ~3 min.**
  (Caveat: editing `Continuous_Planning` itself still rebuilds the big layer; the state-seq work is in
  `Temporal_Planning`, so that's rare.) Re-register after ROOT edits: `isabelle components -u .`.

**Verified on the new heap:** `Ground_PDDL_Problem_Defs.thy` still fully green
(`fully_processed`+`consolidated`, 0 errors) — the restructure didn't break the foundation.

### `Ground_PDDL_Plan_Defs.thy` re-bridge — recipe + progress

**CRITICAL ROOT-CAUSE (the real blocker behind "supply the 4 state-seq constants"):** the state-seq
constants (`acts_of_temporal_plan_at`, `valid_temporal_state_seq`, `apply_eff`) live in
`Temporal_State_Sequence_Semantics`, which Plan_Defs/Problem_Defs did **not** import (they import only
`Temporal_Instantiations` + `Temporal_Happening_Semantics`). So those names resolved as **free
variables** — statements parsed, but `..._def` / `.induct` / `.simps` were "undefined fact". **Fix:
Plan_Defs now imports `"Temporal_Planning.Temporal_State_Sequence_Semantics"`.** This unblocks the
whole state-seq portion.

**Mechanical const-renames DONE (disk sed, jEdit restarted):** `acts_of_plan_at` ->
`acts_of_temporal_plan_at`, `valid_state_seq` -> `valid_temporal_state_seq`, `valid_plan{,_from}` ->
`valid_temporal_state_seq_plan{,_from}` (used `\bvalid_plan` to protect `mutex_valid_plan*`). Note
`apply_eff`, `htps_seq`, `simple_acts`, `durative_acts`, `duration`, `res_inst`,
`res_inst_snap_action` are all FPS names that resolve as-is (no rename) — `simple_acts`/`durative_acts`
are `Continuous_Planning/Instantiations.thy` defs; `duration` is the `DurativePlanAction` selector;
`res_inst` is now **1-arg** (simple), `res_inst_snap_action` 2-arg (durative snap).

**Per-lemma structural re-bridge (the genuine work, not renames):**
1. **World model is a PAIR** `world_model = logical_world_model \times numeric_world_model`
   (`Worlds.thy`). `wf_world_model (M,_) = (\<forall>f\<in>M. wf_fmla_atom objT f)`. So `\<in> M` / `\<in> M'`
   over a world model become `\<in> fst M` / `\<in> fst M'`; `\<in> apply_eff A M` becomes
   `\<in> fst (apply_eff A M)`.
2. **`acts_of_temporal_plan_at` returns a LIST** (was a set): `a \<in> acts_of_temporal_plan_at t p`
   -> `a \<in> set (...)`; `\<forall>a\<in>acts_of_temporal_plan_at ...` -> `\<forall>a\<in>set (...)`.
   `apply_eff` takes a list, so `apply_eff (acts_of_temporal_plan_at ...) M` needs NO `set`.
3. **`apply_eff` is a `definition`** (`= apply_ground_actions`), not a `fun`: `apply_eff.simps` ->
   `apply_eff_def` / `apply_eff_unfold` (gives the pair `(fst M - \<Union>dels \<union> \<Union>adds, num)`).
4. **`valid_temporal_state_seq.induct` now has 3 cases** (`[]`, `[t\<^sub>i]`, `t\<^sub>i#t\<^sub>j#ts`),
   not 2 — every `induction ... rule: valid_temporal_state_seq.induct` proof must handle a THIRD case
   (singleton base vs recursive cons); the recursive call/IH is in case 3.
5. **Happening correspondence is `mset`-based:** `set A = acts_of_temporal_plan_at ...` ->
   `mset A = mset (acts_of_temporal_plan_at ...)` via `ind_happ_seq_htp_acts_of_temporal_plan_at`
   (`mset A = mset (...)`).
6. **Open-world goal/precond entailment:** closed-world `M \<^sup>c\<TTurnstile>\<^sub>= \<phi>` (notation
   removed with Problem_Defs's open-world rework) -> `valuation M \<Turnstile>\<^sub>m \<phi>` (matches the
   FPS `valid_temporal_state_seq_plan_from` goal check). The abstract-side sites (the
   `abstr_state_list ! i \<^sup>c\<TTurnstile>\<^sub>= ...` ones, ~lines 2380/2479) need care re. what
   `abstr_state_list ! i` is.
7. **Old schema constructors remain in the deeper proofs:** `Simple_Action_Schema n ps pre eff` ->
   `SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff)` (and the durative analog) — e.g.
   `acts_of_temporal_plan_at_wf`/`_no_args` (~lines 770/860), which also need `res_inst \<pi> At_Start`
   -> `res_inst \<pi>` and to consume the elim's new case hyp `a = the (res_inst \<pi>)`.

**FPS reuse lemmas (use these, don't reprove):** `wf_apply_happ`,
`wf_ground_action_wf_fmla_atom` (`wf_ground_action a ==> \<forall>x\<in>set (adds (effect a)). wf_fmla_atom
objT x`), `wf_world_model_when_fst_wf_intro` (all `Preservation_Of_Well_Formedness.thy`);
`apply_ground_actions_same_mset_eq_intro` (`mset A = mset B` + non-intrf ==> equal application — powers
the happening/mutex correspondence), `apply_ground_actions_no_effect_intro` (over_all `Effect [] [] []`
==> id) (`Happening_Semantics.thy`).

**Mutex re-bridge (`all_htps_acts_non_intrf{,'}`, currently stubbed `by simp`):** the new
`valid_temporal_state_seq` carries `list_pairwise acts_non_intrf A\<^sub>i` (position-based,
duplicate-preserving); derive non-interference from that (and plan-entry distinctness), NOT from the
dropped snap-value distinctness. `acts_non_intrf` is reflexively-false (a snap interferes with itself),
so a valid plan's concurrent-snap list has no interfering duplicates.
- **Mutex bridge lemma (maintainer guidance, 2026-06-28):** add a bridge lemma **in the ground PDDL
  locales** proving that under `PDDL_plan_no_self_overlap` (no durative action self-overlaps) with
  **0 separation** (concurrent snaps at the *exact same* htp `t`), the new position-based
  `list_pairwise acts_non_intrf (acts_of_temporal_plan_at t tp)` can be **restated** in the
  per-plan-entry form the NTA reduction's `mutex_valid_plan*` machinery consumes. No-self-overlap
  guarantees that distinct plan entries firing at the same `t` give distinct, non-interfering list
  positions (no snap-value collision masking), so the list-position mutex collapses to plan-entry-pair
  non-interference. This is the intended route to discharge `all_htps_acts_non_intrf{,'}`.

**Progress this session:** const-renames + import done; `in_acts_of_temporal_plan_atE` (the snap-source
elim) **re-bridged and GREEN** (reproved from `acts_of_temporal_plan_at_def` +
`simplified_res_inst_temporal_plan_action_at` cases; now provides `a = the (res_inst \<pi>)` /
`a = the (res_inst_snap_action \<pi> At_{Start,End})`). REMAINING (large, multi-session): the
wf-preservation cluster (3-case induction + world-model-pair), the `acts_of_temporal_plan_at_wf/_no_args`
schema-constructor retype, the mutex re-bridge, open-world consumers, then the rest of Plan_Defs, then
`Plan_Reduction -> Problem_Reduction -> Problem_Code -> NTA_Reduction_Correctness -> NTA_Reduction_Impl`.

## Session update (2026-06-26) — Phase A in progress (uncommitted)

- **`Ground_PDDL_Problem_Defs.thy` GREEN** (`fully_processed`+`consolidated`, 0 sorry). Retyped onto
  new datatypes; 4 snap-injectivity lemmas dropped; **world-model bridge reworked OPEN-WORLD** — the
  prior session's local closed-world block (`wm_basic`/total `valuation`/`close_world`/`^c\<TTurnstile>=`/
  `hide_const Worlds.valuation`) was REMOVED and replaced by `pos_conj_models_iff_superset`
  (`is_pos_conj form \<Longrightarrow> valuation M \<Turnstile>\<^sub>m form \<longleftrightarrow> set (to_literals form) \<subseteq> fst M`) + `val_predAtm_dom`,
  adapted from the classical grounder. **DO NOT reintroduce closed-world.** Header now also suppresses
  duplicate `|>`/`#>`/`\<Turnstile>` via `no_notation`. §1d corrected: re-adding the FPS imports is the fix
  (the `Utils`->`TP_Utils` rename already resolved the clash).
- **`Ground_PDDL_Plan_Defs.thy` PARTIAL** — parse cascade cleared (2868 -> ~150 errors): `context
  ast_problem`->`ground_ast_problem_defs`, `wf_ast_problem`->`ground_ast_problem`,
  `for P::ast_temporal_problem`, 95 `Simple_Plan_Action`/`Durative_Plan_Action`->`SimplePlanAction`/
  `DurativePlanAction` renames. Remaining: supply the 4 state-seq constants + world-model pair lift
  (`fst M`) + mutex re-bridge + open-world consumers.
- **`_Alt` strategy (corrected + decided with maintainer):** Plan_Defs needs `valid_state_seq`/
  `acts_of_plan_at`/`apply_eff`/`valid_plan`, which live in FPS `Continuous_Planning/
  TEMPORAL_PDDL_Semantics_Alt.thy` — but that theory is in **no FPS ROOT** (orphan) and is the
  **continuous** 5-arg version (`DurativeActionSchema … ceff`, continuous-effect list, invariants).
  Decision: **register `_Alt` (+ a temporal derivative) in the FPS `Temporal_Planning` ROOT**, then
  import; the derivative specializes the continuous state-seq to the temporal numeric-free setting
  (`PNEs = []`, no continuous effects). No FPS-internal name collisions; project-import collisions
  handled via `no_notation` as usual. Requires a `Temporal_Planning_Base` heap rebuild.
### NEW prerequisite step (before the Plan_Defs retype) — FPS state-seq registration + temporal derivative
**Authored by the assistant, then REVIEWED by the maintainer before rebuild/continue.** In FPS:
1. Register `Continuous_Planning.TEMPORAL_PDDL_Semantics_Alt` so it builds (it is currently orphaned in
   no ROOT).
2. Add a **temporal derivative** theory (in `Temporal_Planning/`) that specializes the continuous,
   5-arg `valid_state_seq'`/`valid_plan`/`acts_of_plan_at`/`apply_eff` to the **temporal numeric-free**
   setting (`PNEs = []`, no continuous effects / trivial invariants), exposed in a locale the project's
   `ground_ast_problem_defs` (= `ast_temporal_problem P`) can consume.
3. Register both in the FPS `Temporal_Planning` ROOT.
**Gate:** maintainer reviews the authored theory + ROOT change; only then rebuild `Temporal_Planning_Base`
(`-b`), restart jEdit, and proceed. No FPS-internal name collisions; project-import collisions handled
via `no_notation` as usual.

- **Then:** finish Plan_Defs (mutex re-bridge from `list_pairwise acts_non_intrf`; open-world consumers
  via `pos_conj_models_iff_superset`/`fst M`), then `Plan_Reduction` -> `Problem_Reduction` ->
  `Problem_Code` -> `NTA_Reduction_Correctness` -> `NTA_Reduction_Impl`. No commit (per maintainer).

## Status (live, 2026-06-25)

**Both integration blockers resolved; abstract stack green; the `Ground_PDDL_Exec_Imp` retype is the
remaining work.** Branch `numeric-conditions-effects`, commits: `c7b266d` (Step 1 plumbing),
`31a9e17` (blocker resolution).

- **Step 1 DONE** — submodule removed; base heap re-rooted on `Temporal_Planning` (+ Munta_Certificate_Checker
  + List-Index), **built green**; launch `isabelle jedit -d . -l Temporal_Planning_Base`.
- **Blocker 1 (Utils name clash) RESOLVED** — renamed project `Temporal_Planning_Common.Utils` ->
  `TP_Utils` (it collided with FPS `Continuous_Planning.Utils`).
- **Blocker 2 (`prod`-arity conflict `(linorder,linorder) sup` vs `(sup,sup) sup`) RESOLVED** — the
  abstract reduction pulled Munta's code-export theory `Simple_Network_Language_Export_Code`
  (lexicographic `Product_Lexorder`), incompatible with FPS's analysis `Product_Order`. Fix:
  `TP_NTA_Reduction_Defs` now imports `Munta_Model_Checker.Simple_Network_Language_Model_Checking`
  (network semantics: `graph_impl`, `step_u'`, `reachable`) **+ `Munta_Base.Error_List_Monad`** (for the
  `|>` operator) instead. `Export_Code` is kept **only** in `Check_Unsolvability.thy` (executability).
- **Verified green on the new heap**: `Temporal_Plans`, `TP_NTA_Reduction_Defs`,
  `TP_NTA_Reduction_Model_Checking`. (`sat_comp` is now a pattern-matching `fun` using `lift2_option`;
  the 2 downstream `sat_comp_def` sites in `TP_NTA_Reduction_Correctness_Numeric_{Tracking,StepInfra}`
  were adapted to `sat_comp.simps` but the heavy numeric-correctness chain is **not yet re-verified**.)
- **NEXT — Step 2/2b retype of `Ground_PDDL_Exec_Imp`.** `Ground_PDDL_Problem_Defs.thy` (~1340 lines) is
  the bulk; current real errors: `ast_action_schema` -> `ast_temporal_action_schema` (head/body
  constructors `SimpleActionSchema (ActionHead n ps) ...` / `DurativeActionSchema ... (DurativeActionBody
  dc cond deff)`); `Time_Const|No_Const|Func_Const` -> `DurationConstraint d_op expr` (now an **annotated
  list** `(temporal_annotation \times term duration_constraint) list`, numeric-free `expr = ConstantExpr`);
  `Ground_Action n anno pre eff` -> `GroundAction pre eff` (reuse it; mutex stays list-based, §2b);
  `Effect adds dels` -> `Effect adds dels []`. Then `Plan_Defs`/`Plan_Reduction`/`Problem_Reduction`/
  `Problem_Code`/`NTA_Reduction_Correctness`/`NTA_Reduction_Impl`, and the `grounded_temporal_problem`
  redesign (§2b).
- **Step 3 risk (noted)** — the same `prod` tension recurs where `Check_Unsolvability` needs `Export_Code`
  **and** the FPS-typed ground problem; needs an isolation strategy (a code-export theory that does not
  import the FPS semantics in the same theory).
- **DEEPEST-WORK FINDING (scoped 2026-06-25) — `Ground_PDDL_Plan_Defs.thy` (~2900 lines) needs a genuine
  RE-BRIDGE, not a retype.** Its `all_htps_acts_non_intrf` / `all_htps_acts_non_intrf'`
  (`Plan_Defs.thy:583,600`) derive snap non-interference from the **old** state-sequence semantics
  `valid_state_seq` / `valid_plan` (`TEMPORAL_PDDL_Semantics_Alt`), which is **set-based with
  snap-VALUE distinctness** (`a \<in> acts_of_plan_at t tp`, `b \<in> ...`, `a \<noteq> b`). The new FPS
  validity is `valid_temp_plan2` with **position-based** `list_pairwise acts_non_intrf`
  (`acts_non_intrf` = FL03, `Continuous_Planning/Numeric_Update_Functions.thy:64`; a snap interferes
  with itself, so identical concurrent snaps are genuinely rejected). Consequence:
  - The mutex proof (`Plan_Defs.thy:2772-2892`) currently uses `inj_on_at_start_spec` /
    `inj_on_at_end_spec` / `at_start_spec_at_end_spec_disj` / `start_spec_end_spec_neq` (snap-value
    distinctness, which the old `Ground_Action name anno` field provided) to get `a \<noteq> b` at the
    snap level. With `GroundAction pre eff` these are **unprovable AND unneeded**: distinct plan
    entries give distinct list POSITIONS, and `list_pairwise acts_non_intrf` delivers
    non-interference per-position regardless of snap value.
  - **Action:** drop the 4 snap-injectivity lemmas from `Ground_PDDL_Problem_Defs.thy`; re-derive
    `all_htps_acts_non_intrf` from `valid_temp_plan2`'s `list_pairwise acts_non_intrf` (position-based),
    and rework `Plan_Defs.thy:2772-2892` to invoke it by plan-entry distinctness, not snap-value
    distinctness. This is the single hardest sub-task of Step 2.
- **Execution tactic — Phase A then Phase B.** Phase A: retype to green keeping the bundled locale
  (rebased `ground_ast_problem_defs = ast_temporal_problem P`, `ground_ast_problem` on
  `wf_ast_temporal_problem`), numeric-free; commit a green baseline. Phase B: §2b locale split
  (`grounded_temporal_problem` etc., signature sublocales, intro/dest, 3-file split). The bulk work
  (snap builder, `*_spec` funcs, wf/positivity/in-props lemmas, the Plan_Defs re-bridge) is done once
  in Phase A and carries into Phase B unchanged; only the locale wrapper is touched twice.
- **Confirmed new-API reference (for the retype):**
  - snap builder (numeric-free): the new `inst_temporal_snap_action` folds duration-constraint atoms
    into the precondition (numeric atoms) via `inst_snap_action_body_elements`, which would break
    positivity/no-args. So build snaps from the condition/effect lists ONLY with an **empty** duration
    list: `inst_snap_action_body_elements [] cond deff (tsubst h []) 0 ta` (duration bounds stay
    separate in `lower_spec`/`upper_spec` via the annotated duration list). over_all eff is
    `Effect [] [] []` (`wf_over_all_empty_eff`).
  - instantiation: `instantiate_temporal_action_schema sch args` (Simple, no annotation arg now);
    `inst_temporal_snap_action sch dur args ta` (Durative); `resolve_temporal_action_schema` (in
    `ast_temporal_domain`); `action_params_match`, `res_inst_snap_action`, `wf_plan_action` (via the
    `action_instantiations` sublocale, `Temporal_Instantiations.thy:64`).
  - locales: base `ast_temporal_problem P` (= `ast_temporal_domain (domain P) + problem_signature ...`),
    wf bundle `wf_ast_temporal_problem` (sublocales `wf_ast_temporal_domain` + `wf_problem_signature`);
    `wf_temporal_problem`/`wf_temporal_domain` defs; `wf_temporal_action_schema`, `wf_ground_action`,
    `wf_effect`/`wf_fmla`/`wf_fmla_atom`, `objT`/`constT`/`sig`/`func_sig` all inherited.
  - schema shape: `SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff)` /
    `DurativeActionSchema (ActionHead n ps) (DurativeActionBody dc cond deff)`; case rules
    `ast_temporal_action_schema_{induct,cases}_unfold`; name via `ast_temporal_action_schema_name`.

## Context

`temporal-planning-certification` currently builds on a **vendored** temporal-semantics
submodule — `lib/temporal-pddl-semantics` (session `Temporal_AI_Planning_Languages_Semantics`,
theories `TEMPORAL_PDDL_Semantics` / `TEMPORAL_PDDL_Checker` / `TEMPORAL_PDDL_Semantics_Alt`). The
sibling repo **Formal-PDDL-Semantics** now provides a unified, actively-maintained, numeric-aware
semantics stack (`Continuous_Planning_Base -> Continuous_Planning -> Temporal_Planning ->
Classical_Planning -> Planning`). The classical grounder (`Isabelle-PDDL-Grounding`) already
de-submoduled the same way: it has **no semantics submodule of its own** and consumes
`Classical_Planning` / `Continuous_Planning` purely via session-qualified imports, with
Formal-PDDL-Semantics registered as an Isabelle **component**.

This is exactly **P0** in `GROUNDING_PLAN.md` §3 (also called "the long pole" in §8) and a shared
prerequisite of the numeric plan: unify this project onto the **new** `Temporal_Planning` semantics.
Intended outcome: the whole development builds green on `Temporal_Planning`, the old submodule is
gone, and the project's temporal task lives in the same semantic family as the grounder (whose
`Classical_Temporal_Reduction` already bridges classical <-> temporal), unblocking the grounding and
numeric work.

**Decisions (confirmed with the user):**
- **Sibling component, no submodule** — drop `lib/temporal-pddl-semantics` entirely; Formal-PDDL-Semantics
  is a separate clone alongside the repo, registered via `isabelle components -u`, mirroring the grounder.
- **Full migration, ending green** — the swap breaks the build until the downstream development is
  retyped; this plan covers that retype, not just the plumbing.
- **Re-point numeric-free first, then add numerics as the final phase.** The new types carry numeric
  fields (`ast_effect.numeric_effects`, `duration_constraint`'s `numeric_expression`). Steps 0-4 map
  them to the empty / non-numeric path to reach green while preserving today's behavior exactly; then
  **Step 5** (part of this plan) threads real numerics through on top of that green base.

> **Scope reality check.** This is **not** a 3-file change. `Temporal_Planning_Base` loads the old
> semantics into a heap the entire development sits on, so old types/constants are referenced across
> **all four** project sessions (~30 files). Re-pointing forces a genuine retype: `ast_effect` gains a
> `numeric_effects` field, `duration_constraint`'s `Time_Const` carries a `numeric_expression`, the
> action-schema is restructured (head + body), and the validity predicate/locale are renamed and
> retyped. The numeric fields are satisfied with the empty / non-numeric path (Step 2) — no numeric
> semantics is implemented here. Do it on a dedicated branch, fully green, before any grounding work
> (`GROUNDING_PLAN.md` §8).

---

## Step 0 — Verify the new API against source (do this FIRST)

The old->new mapping below was assembled by reading source, but the new-semantics shapes
(`object`, the head/body action-schema split, what `_Alt` mapped to) **must be confirmed against the
actual Formal-PDDL-Semantics source before edits**, since they drive every downstream change. Use
`isabelle-search` / read the new theories directly:

- `Formal-PDDL-Semantics/Temporal_Planning/Temporal_Abstract_Syntax.thy` — `temporal_plan`,
  `ast_temporal_domain` / `ast_temporal_problem`, `ast_temporal_action_schema`, `ast_effect`,
  `duration_constraint`, `predicate`, `term`, `object`.
- `.../Temporal_Happening_Semantics.thy` — `valid_temp_plan2`, `valid_temp_plan_from2`,
  `valid_temporal_plan`, `ind_temporal_plan`, `happening`.
- `.../Temporal_Well_Formedness.thy` + `.../Temporal_Instantiations.thy` — the
  `ast_temporal_problem` / `wf_ast_temporal_problem` locales (fixed params + assumptions) and the
  snap/instantiation helpers.
- `.../Temporal_PDDL_Checker_Explicit.thy` — the verified checker + correctness theorem to replace
  the old `TEMPORAL_PDDL_Checker`.
- Confirm what `TEMPORAL_PDDL_Semantics_Alt` provided (used by `Ground_PDDL_Plan_Defs.thy`) and its
  new counterpart.

Record the confirmed mapping; correct the table in this plan if reality differs.

**Step 0 status: done.** Confirmed: the datatypes (see the corrected mapping table); validity targets
`valid_temp_plan2` / `valid_temp_plan_from2` (`Temporal_Happening_Semantics.thy:213,219`); the new
happening mutex is **list-based** `list_pairwise acts_non_intrf` (so `GroundAction` is reused — see
§2b); the old `TEMPORAL_PDDL_Semantics_Alt` (state-transition `valid_plan` / `valid_state_seq`, with
the *set*-based mutex at line 170) maps onto `Temporal_Happening_Semantics`. Checker (Step 3): the new
checker is `check_temporal_plan P \<pi>s` with correctness `check_temporal_plan_return_iff`
(`Temporal_PDDL_Checker_Explicit.thy:145,150`; also `check_cont_plan_from_temporal_return_iff`).

---

## Step 1 — Dependency re-point (plumbing)

### 1a. Remove the submodule
- `git submodule deinit -f lib/temporal-pddl-semantics`
- `git rm -f lib/temporal-pddl-semantics` (drops the gitlink **and** the `.gitmodules` stanza)
- `rm -rf .git/modules/lib/temporal-pddl-semantics`
- Confirm `.gitmodules` keeps the other four submodules (`ML/lib/mlunta`, `ML/lib/cmlib`,
  `ML/lib/parcom`, `examples/pddl-instances`) and the temporal stanza is gone.

### 1b. Register Formal-PDDL-Semantics as a component
- No superproject here (unlike the grounder), so registration is a documented setup step using the
  README's existing `<path-to>` placeholder idiom — **no machine-specific path in any committed file**
  (per CLAUDE.md). The user clones Formal-PDDL-Semantics adjacent to this repo and runs
  `isabelle components -u <path-to>/Formal-PDDL-Semantics`.
- Optional convenience: a root `make register-components` target (mirrors the grounder superproject's
  Makefile) that registers the AFP, Formal-PDDL-Semantics, and `.` — but keep paths as variables, not
  hardcoded. Not required for green; README step suffices.

### 1c. Rewire `ROOT` (`Temporal_Planning_Base`, lines 1-14)
> **Superseded (2026-06-26):** the single-layer `Temporal_Planning_Base` below was later **split** into
> `Temporal_Munta_Base` (stable, Munta-bearing) + a thin `Temporal_Planning_Base` so FPS
> `Temporal_Planning` edits no longer re-elaborate the Munta tower — see the top session update.
> The original single-layer rationale is kept below for context.
- Drop `"Temporal_AI_Planning_Languages_Semantics"` from `sessions`; add `"Temporal_Planning"`
  (transitively pulls `Continuous_Planning` / `Continuous_Planning_Base`).
- Replace the two old `theories [document = false]` loads with the new heap-preloaded set, e.g.
  `Temporal_Planning.Temporal_Abstract_Syntax`, `Temporal_Planning.Temporal_Happening_Semantics`,
  `Temporal_Planning.Temporal_Well_Formedness`, `Temporal_Planning.Temporal_Instantiations`,
  `Temporal_Planning.Temporal_PDDL_Checker_Explicit` (final set confirmed in Step 0).
- Update the `description` text — remove "(old) temporal PDDL semantics".
- **Heap parent = `Temporal_Planning`, NOT Munta (Step-1 finding).** Munta and Temporal_Planning live in
  **different heap trees**; a Munta-rooted base that pulls in the temporal theories re-elaborates the
  *entire* HOL-Analysis / ODE / algebraic-numbers tower on top of Munta (the cached `Temporal_Planning`
  image cannot be reused across trees) — this blew the 900s timeout. Fix: root the base on
  `Temporal_Planning` (inherits that tower free) and load `Munta_Certificate_Checker.*` (its 8 session
  theories) + `List-Index` on top, re-elaborating only the smaller Munta tower. Bumped `timeout` to
  7200. The Temporal_Planning theories need no explicit listing (inherited from the parent image); the
  children pick up Munta names from this base heap exactly as before.

### 1d. Rewire the explicit imports (3 files in `Ground_PDDL_Exec_Imp/`)
**Drop the old-semantics imports entirely — do NOT re-import `Temporal_Planning.*` explicitly.** Since
the base heap is now rooted on `Temporal_Planning`, the whole project chain already inherits every
Temporal_Planning name; importing them explicitly *alongside* the project chain double-loads shared
theories and triggers a **`Utils` theory-name clash** (project `Temporal_Planning_Common.Utils` vs FPS
`Continuous_Planning.Utils`) -> `Duplicate theory name` (a single import-level failure that cascades into
~1000 spurious "missing theory context" errors). Net edits (verified in jEdit):
- `Ground_PDDL_Problem_Defs.thy`: imports just `"TP_NTA_Reduction.TP_NTA_Reduction_Model_Checking"`.
- `Ground_PDDL_Plan_Defs.thy`: imports just `Ground_PDDL_Problem_Defs`.
- `Ground_PDDL_NTA_Reduction_Impl.thy`: imports just `Ground_PDDL_NTA_Reduction_Correctness`.
The `ast_temporal_problem` / `ground_action` / `GroundAction` / `check_temporal_plan` names all resolve
from the base heap without explicit import.

---

## Step 2 — Downstream retype onto the new types (the bulk)

Drive bottom-up, one session at a time, each fully green (`0 sorry`, `consolidated`) before the next.
Order follows the ROOT dependency chain.

**Old -> new entity mapping** (confirm/adjust in Step 0):

| Entity | Change | Action |
|---|---|---|
| `predicate`, `term`, `temporal_annotation` | drop-in (identical) | none |
| `valid_plan2` / `valid_plan_from2` | renamed + retyped | `valid_temp_plan2` / `valid_temp_plan_from2` |
| `wf_ast_problem` locale | renamed + signature change | `ast_temporal_problem` / `wf_ast_temporal_problem` (adds `problem_signature` inheritance) |
| `ast_effect` | **shape change** (+`numeric_effects`) — *confirmed Step 0* | `Effect (adds) (dels) (numeric_effects)`. **numeric-free path**: `Effect adds dels` -> `Effect adds dels []`; pattern matches gain a 3rd field discharged as `[]`. Real numeric effects are Step 5. |
| `duration_constraint` | **shape change** — *corrected Step 0* | new is a **single** ctor `DurationConstraint (d_op: EQ\|LEQ\|GEQ) (expr: 'ent numeric_expression)`, held in a durative body as an **annotated list** `(temporal_annotation \times term duration_constraint) list` — **not** the old `No_Const\|Time_Const\|Func_Const`. Rewrite `lower_spec`/`upper_spec` to fold the annotated list; numeric-free phase restricts `expr` to `ConstantExpr r` (integer `r`). |
| `ast_action_schema` | **structural rewrite** — *confirmed Step 0* | `SimpleActionSchema (head: ast_action_head) (SimpleActionBody pre eff)` / `DurativeActionSchema (head) (DurativeActionBody dc cond deff)`; `head = ActionHead (name) (parameters)`; durative `cond`/`deff` are **annotated lists** `(temporal_annotation \times _) list`. Use `ast_temporal_action_schema_{induct,cases}_unfold`. |
| `object` | **confirmed: plain `Obj name`** — *corrected Step 0* | new `object = Obj (name)` only; the old `FuncEnt`/`TimeEnt` constructors are **gone**. Numeric fluents are `PNE func args` / `numeric_expression`; time is `rat`. Re-express old `FuncEnt`/`TimeEnt` uses (numeric ones defer to Step 5; time uses `rat`/`time`). |
| `ground_action` / `happening` | **shape change; reuse confirmed** — *Step 0* | new `ground_action = GroundAction (precondition) (effect)` — **no `ga_name`, no `timing`** (old `Ground_Action name timing pre eff`); `happening = time \times ground_action list`. **Reuse `GroundAction` directly.** The old `name`/`timing` existed *only* to disambiguate the **mutex** check, which the old code asserted over a *set* of snap pairings — so two syntactically-equal snaps from different ground actions collapsed and were wrongly treated as non-interfering. The new mutex is over a *list* of pairings (duplicates preserved), so name/timing are unneeded. Timing/duration are tracked **structurally** by the grounded target (per-action snap slots), not in `GroundAction`. See §2b. |

> **Scope finding (verified in jEdit on the new heap).** The abstract layers are **semantics-agnostic**
> and build green with **no retype**: `Temporal_Planning_Common` (Utils 0 errors),
> `Temporal_Planning_Semantics` (`Temporal_Plans` 0 errors, 2951 cmds), and `TA_Network`
> (`NTA_Temp_Planning_Sem` 0 errors — Munta names resolve from the re-rooted base heap). Old<->new
> semantics only meet at the **instantiation boundary**, so the retype is concentrated in
> **`Ground_PDDL_Exec_Imp`** (+ Step 2b). Any pre-existing numeric `sorry` in TA_Network is in-flight
> numeric work (abstract; carries over unchanged), not re-point breakage.

**Per-session work (by impact):**
- `Temporal_Planning_Common/` (Utils, ListMisc, Sequences) — expected **no** semantics references; build to confirm.
- `Temporal_Planning_Semantics/` (`Temporal_Plans`, lemmas) — **light** (~`valid_plan2`, `happening`):
  rename validity predicate, retype any plan/problem signatures.
- `TA_Network/` (the `TP_NTA_Reduction_*` family, ~15 files) — **moderate** (~80 `happening` sites):
  `happening` is drop-in, so most is insulated; fix wherever proofs destructure `ground_action`'s
  effect (now 3-field) or touch action-schema/duration shapes.
- `Ground_PDDL_Exec_Imp/` (~10 files) — **heaviest** (~157 refs; `Ground_PDDL_Problem_Defs.thy` and
  `Ground_PDDL_Plan_Defs.thy` worst). This is more than a mechanical retype: the grounded-problem
  structure is **redesigned** here as the explicit grounder target — see **Step 2b**. In brief:
  - Replace the bundled `ground_ast_problem` locale with the factored `grounded_temporal_problem`
    stack on `ast_temporal_problem` / `wf_ast_temporal_problem` (Step 2b).
  - Re-derive the snap-split defs `at_start_spec` / `at_end_spec` / `over_all_snap` /
    `ground_non_action` against the new `ast_effect` (3-field; numeric-free `Effect adds dels []`) and
    the new action-schema head/body shape, and the duration accessors against the new
    `duration_constraint`.
  - Update `ground_action` effect accessors (`adds`/`dels`/`numeric_effects`) at every use.

---

## Step 2b — Grounded temporal problem target structure (factored like the classical grounder)

Set up **now**, ahead of the grounder, the structure that the (later) **temporal grounder will
produce** and the existing NTA reduction consumes. Decisions confirmed: **rename** to
`grounded_temporal_problem`; **full grounder-style split** — signatures reused, grounded-ness and
positivity as separate locales, intro/dest bundles. Template:
`Isabelle-PDDL-Grounding/Grounded_PDDL/Grounded_PDDL.thy` + `Common/Normalization_Definitions.thy`.

> **Why now / relation to the later grounder.** A temporal grounder is a later phase
> (`GROUNDING_PLAN.md` §4-6: `Ground_Temporal_PDDL` session). Its output post-condition *is* the
> `grounded_temporal_problem` locale defined here, exactly as the classical grounder's `wf_grounder`
> discharges `grounded_problem` (`Grounded_PDDL.thy` lines 187-209, 646-649). Defining the target
> first means the grounder is later written to *hit a fixed, already-proven interface*, and the NTA
> reduction is rewired onto it once.

### Reuse verbatim — Formal-PDDL-Semantics signature layer (do NOT rebuild)
The signature is already factored and shared across Classical/Temporal/Continuous. Today's code
inlines `sig`/`func_sig` and folds signature restrictions into `ground_ast_problem` assumptions —
**drop that** and reuse:
- `Continuous_Planning/Signatures.thy`: `domain_signature` (fixes `ty_decl predicates functions
  consts`; `constT`, `wf_type`, `wf_domain_signature`), `problem_signature` (adds `objs`;
  `objT = map_of objs ++ constT`, `wf_problem_signature`), and the `wf_*` assertion variants.
- `Continuous_Planning/Well_Formedness.thy`: `sig`, `func_sig`, `is_of_type`, `wf_pred_atom`,
  `wf_fmla`, `wf_effect`.
- `Temporal_Planning/Temporal_Well_Formedness.thy`: `ast_temporal_domain`/`ast_temporal_problem`
  (already extend the signature locales) + `wf_ast_temporal_domain`/`wf_ast_temporal_problem`.
- `Temporal_Planning/Temporal_Instantiations.thy`: the generic `action_instantiations` already
  sublocaled in `ast_temporal_problem` with `resolve_temporal_action_schema` /
  `instantiate_temporal_action_schema` / `inst_temporal_snap_action` — reuse for the snap split.

### New — grounded-ness layer (mirror `Grounded_PDDL.thy`)
Definitions in the `ast_temporal_domain` / `ast_temporal_problem` context:
- `grounded_pred (PredDecl n args) <-> args = []` (identical to grounder; reuse).
- `grounded_temporal_ac` — nullary action schema: pattern-match the new `SimpleActionSchema (head,
  body)` / `DurativeActionSchema (head, body)` and require `parameters (head) = []` (confirm head
  accessor name in Step 0).
- `grounded_temporal_dom == types D = [] /\ (ALL p : set (predicates D). grounded_pred p) /\
  consts D = [] /\ functions D = [] /\ (ALL a : set (actions D). grounded_temporal_ac a)`
  (`functions D = []` is the numeric-free phase; **Step 5** relaxes to allow nullary numeric functions).
- `grounded_temporal_prob == grounded_temporal_dom /\ objects P = []`.
- Locales: `grounded_temporal_domain = wf_ast_temporal_domain + assumes grounded_temporal_dom`;
  `grounded_temporal_problem = wf_ast_temporal_problem + assumes grounded_temporal_prob`;
  `sublocale grounded_temporal_problem subseteq grounded_temporal_domain D`.
- **intro/dest bundles** per the conjunctive-bundle rule (model on `grounded_domI`/`grounded_domD` /
  `grounded_probI`/`grounded_probD`): `grounded_temporal_domI [intro]` / `grounded_temporal_domD
  [dest]`, `grounded_temporal_probI` / `grounded_temporal_probD`. Consumers use the dest rules, not
  `unfold ..._def`.

### New — signature-restriction view (the "especially signatures" ask)
Grounded-ness already forces `types=[]`, nullary preds, `consts=[]`, so the grounded signature *is*
the typeless/nullary signature — express that by reusing the grounder's signature-restriction
locales rather than re-stating it inline:
- mirror `typeless_domain_signature` / `typeless_problem_signature`
  (`Common/Normalization_Definitions.thy`) and prove
  `sublocale grounded_temporal_domain subseteq typeless_domain_signature ...` (resp. problem). This
  collapses the shared `wf_fmla`/`objT`/`sig` to their nullary form for free and keeps signature
  concerns orthogonal to actions (the §2 reuse lever in `GROUNDING_PLAN.md`).

### New — positivity layer (separate, mirror grounder `relaxed_*`)
Positivity is an NTA-reduction *input* requirement, not grounded-ness:
- `positive_temporal_problem = wf_ast_temporal_problem + assumes positive_act_pres and positive_goal`
  (model on `relaxed_problem` in `Normalization_Definitions.thy`). The integer/constant-duration
  restriction lives in its own small locale (`integer_duration_problem`) for the numeric-free phase.
- **NTA-reduction input locale** = `grounded_temporal_problem + positive_temporal_problem +
  integer_duration_problem` — exactly the bundle today's `ground_ast_problem` lumps into one `assumes`.

### Snap-split machinery rebuilt on new types (the `_defs` layer)
- `grounded_temporal_problem_defs` (was `ground_ast_problem_defs`) carries `at_start_spec` /
  `at_end_spec` / `over_all_snap` / `ground_non_action` on the new `ast_effect` (numeric-free
  `Effect adds dels []`) and the new `DurativeActionSchema (head) (DurativeActionBody dc cond deff)`
  shape; `lower_spec` / `upper_spec` fold the **annotated duration list**
  `(temporal_annotation \times term duration_constraint) list`, each entry
  `DurationConstraint d_op (ConstantExpr r)` (integer `r`, numeric-free).
- **Snap representation: reuse the new `GroundAction` directly.** It carries only `precondition` +
  `effect` — and that suffices. The old `Ground_Action`'s `name`/`timing` existed *only* to
  disambiguate the **mutex** condition: the old reduction asserted non-interference over a **set** of
  snap pairings, so two syntactically-equal snaps from different ground actions collapsed in the set
  and were wrongly treated as non-interfering; `name`/`timing` kept them distinct. The new reduction
  asserts the mutex over a **list** of pairings (duplicates preserved), so the disambiguation is no
  longer needed. Compute each snap's `pre`/`eff` with `inst_temporal_snap_action sch dur args ta` /
  `res_inst_snap_action \<pi> ta` (`Temporal_Instantiations.thy`; the annotation `ta` is an argument);
  the grounded target tracks at_start/at_end/over_all + duration bounds **structurally** (per-action
  snap slots), not inside `GroundAction`. Bridge to the new semantics' `temporal_plan` /
  `valid_temp_plan2` for the validity statement. (A well-formed over_all snap has
  `effect = Effect [] [] []` — `wf_over_all_empty_eff`.)
- **Mutex must stay list-based.** When rebuilding the NTA mutex / non-interference check, keep it over
  the *list* of concurrent snaps (duplicates preserved), matching the new semantics — do **not** revert
  to a set-based pairing (that is exactly what made `name`/`timing` necessary before). *Confirmed (Step
  0):* the new happening validity uses `list_pairwise acts_non_intrf A`
  (`Temporal_Happening_Semantics.thy:27,36`; `list_pairwise` in `Continuous_Planning/Utils.thy:230`,
  duplicate-preserving), and the validity targets are `valid_temp_plan2` / `valid_temp_plan_from2`
  (`Temporal_Happening_Semantics.thy:213,219`).

### Plan target (`Ground_PDDL_Plan_Defs.thy`)
Rename `ground_plan_defs` -> `grounded_temporal_plan_defs`, `valid_ground_plan` ->
`valid_grounded_temporal_plan`; retype onto `valid_temp_plan2` / `happening`; keep the
`(rat * plan_action)` input and the integer `ref_plan` refinement.

### File layout (three-file pattern, mirror the grounder)
Split `Ground_PDDL_Problem_Defs.thy` into `Grounded_Temporal_PDDL_Locales.thy` (signature reuse +
grounded-ness/positivity predicates, locales, sublocales, intro/dest), `Grounded_Temporal_PDDL_Defs.thy`
(executable snap-split defs), `Grounded_Temporal_PDDL_Semantics.thy` (well-formedness preservation +
plan-equivalence). Update `ROOT` (`PDDL_TP_Reduction` theory list) accordingly.

### Old -> new locale mapping (replaces today's bundled `ground_ast_problem`)

| Today (`ground_ast_problem` assume) | New home |
|---|---|
| `wf_ast_problem P` (parent) | `wf_ast_temporal_problem P` (parent) |
| `no_consts`, `no_functions`, `preds_no_args`, `acts_no_params` | `grounded_temporal_dom` conjuncts (via `grounded_pred` / `grounded_temporal_ac`) |
| `init_no_args` | **prove as a lemma** from `grounded_temporal_prob` (objects=[] + nullary preds); drop the assume |
| `acts_dcs_integers`, `acts_no_func_dcs` | `integer_duration_problem` locale (numeric-free phase) |
| `positive_act_pres`, `positive_goal` | `positive_temporal_problem` |
| signature concerns (`sig`/`func_sig` inlined) | reuse `domain_signature` / `problem_signature` (+ `typeless_*` view) |

### Consumer rewiring
The ~5 `context ground_ast_problem(_defs)` sites — `Ground_PDDL_Problem_Reduction.thy` (the
`tp_nta_reduction_model_checking'` sublocale), `Ground_PDDL_NTA_Reduction_Correctness.thy`,
`Ground_PDDL_NTA_Reduction_Impl.thy` — move onto the new NTA-reduction input locale
(`grounded_temporal_problem + positive_temporal_problem + integer_duration_problem`). Mechanical, but
re-proves where the bundled `assumes` were previously pulled apart by hand.

---

## Step 3 — Re-establish the checker + code export

- Re-point `check_ground_problem` and the `Ground_PDDL_NTA_Reduction_Impl` codegen onto
  `Temporal_PDDL_Checker_Explicit` and re-prove `Ground_PDDL_NTA_Reduction_Correctness` against the
  new checker correctness theorem (`GROUNDING_PLAN.md` §3, third P0 bullet).
- Re-run the code export: `Unsolvability_Code_Compile` / `Check_Unsolvability.ML` export in the
  `PDDL_TP_Reduction` session must still land; verify the exported ML compiles via the existing
  `ML/` Makefile path.

---

## Step 4 — Docs

**Keep docs current as each step lands** — don't defer to a big end pass. Each edit below is tied to
the step that makes it true (ROOT description with 1c; the component/submodule wording with Step 1;
the grounded-target naming in `GROUNDING_PLAN.md` §4/§6 with Step 2b; the checker note with Step 3;
the numeric items with Step 5). This Step 4 is the **final consistency sweep**: confirm no doc still
refers to the old submodule, the old `Temporal_AI_Planning_Languages_Semantics` session, the
`ground_ast_problem` name, or "mechanical retype" framing.

- `Readme.md`: rewrite the "Add Temporal Planning Semantics as Isabelle component" section
  (lines 53-57) to instruct cloning Formal-PDDL-Semantics and
  `isabelle components -u <path-to>/Formal-PDDL-Semantics`; the `git submodule update --init` step
  (line 30) stays for the remaining four submodules.
- `ROOT`: `Temporal_Planning_Base` description (done in 1c).
- `GROUNDING_PLAN.md` — already aligned for the decisions made here (§3 P0 bullets reframed to
  redesign+retype / sibling-component-no-submodule; §4/§6 renamed to `grounded_temporal_problem`; §7
  numeric-free-first note; §8 risk reframe; cross-link to this plan). Re-confirm in the sweep.
- `ARCHITECTURE_pipeline.md`: flip the "PDDL semantics" row from "[planned P0] re-point" to done;
  rename the `ground_ast_problem` mentions (rows describing the now-in-tree state) to
  `grounded_temporal_problem` once Step 2b lands.
- `CLAUDE.md` (gitignored) heap note: `Temporal_Planning_Base` now bundles the new semantics;
  `-l Temporal_Planning_Base` launch line unchanged.
- `HANDOVER.md`: update the inventory + sorry status.
- Scan [NUMERIC_PLAN.md](NUMERIC_PLAN.md) / `HANDOVER.md` for the same stale phrasings
  (`ground_ast_problem` naming, "mechanical retype", submodule wording) and align them too.

---

## Step 5 — Numeric version (final phase of this plan)

Full design in [NUMERIC_PLAN.md](NUMERIC_PLAN.md). Once Steps 0-4 are green with the numeric-free
executable, thread real numerics through the executable implementation, exploiting the new semantics'
native numeric support. Because Step 2 left the numeric fields *present and well-typed but empty*, this
is a pure extension on top of the green base, not another retype:
- populate `ast_effect.numeric_effects` (replace the `[]` placeholder) and carry numeric assignment
  effects through the snap split (`at_start_spec` / `at_end_spec` / `over_all_snap`) and the codegen;
- carry genuine `numeric_expression` duration constraints (replace the constant-injection adaptation
  from Step 2) and re-prove the affected NTA-reduction obligations;
- re-establish the numeric simulation proof (the salvaged run-lift design in
  [NUMERIC_PLAN.md](NUMERIC_PLAN.md) §3) on the retyped network;
- extend the checker/codegen (Step 3) and the export so the verified pipeline accepts numeric ground
  temporal tasks end-to-end.

Land this as its own commit series after Steps 0-4 are committed green, so the numeric-free re-point is
a clean, separately-revertable baseline.

---

## Verification

Build the base heap once, then verify incrementally in jEdit (never a blind batch build mid-work; see
CLAUDE.md / `jedit-status`):

1. After Step 0 component registration: `isabelle components -u <path>/Formal-PDDL-Semantics`, then
   `isabelle build -b Temporal_Planning_Base` (persist the heap with `-b`); confirm it lands with
   `ls "$(isabelle getenv -b ISABELLE_HEAPS)"/*/Temporal_Planning_Base`.
2. Launch `isabelle jedit -d . -l Temporal_Planning_Base`; authenticate; via the `jedit-status` skill
   walk the sessions bottom-up (`Temporal_Planning_Common` -> `Temporal_Planning_Semantics` ->
   `TP_NTA_Reduction` -> `PDDL_TP_Reduction`), declaring each file clean only when
   `fully_processed: true` **and** `consolidated: true` with `0 sorry`.
3. Whole-development green: `isabelle build -d . -e PDDL_TP_Reduction` (and
   `PDDL_TP_Reduction_Index`), with `Check_Unsolvability.ML` exported under `ML/`.
4. End-to-end smoke test of the pipeline on a known-unsolvable instance (numeric-free, after Step 4):
   `./run.sh examples/ground/MatchCellar-impossible/instance_03_domain.pddl examples/ground/MatchCellar-impossible/instance_03_problem.pddl`.
5. After **Step 5**: rebuild green with `numeric_effects` populated, re-export the checker, and run the
   pipeline end-to-end on a ground instance that exercises numeric effects / a numeric duration
   constraint (confirm the verified checker accepts/rejects it correctly).

---

## Sequencing & risks

- **Dedicated branch off `main`; two clean commit series.** Steps 0-4 (numeric-free re-point) land
  green and committed first as a separately-revertable baseline; Step 5 (numerics) is the second
  series on top. Coordinate the in-flight numeric work on branch `numeric-conditions-effects`: rather
  than continuing it on the **old** semantics, fold its substance into Step 5 / [NUMERIC_PLAN.md](NUMERIC_PLAN.md)
  on the **new** semantics so effort isn't duplicated — decide this before branching.
- **Step 0 is load-bearing** — verify the new shapes before mass edits; the `object` /
  action-schema-split / `_Alt` mappings are the highest-uncertainty items.
- **Action-schema restructure (head/body)** is the costliest single change (~52 sites in
  `Ground_PDDL_Exec_Imp`); expect `ground_ast_problem` locale assumptions and the codegen to need
  re-typing.
- Keep the four remaining submodules and the Munta/AFP setup untouched.
- **Planned next phase: the temporal grounder.** After Steps 0-5, a verified temporal grounder is the
  next major effort (`GROUNDING_PLAN.md` §4-6, new `Ground_Temporal_PDDL` session reusing the classical
  grounder's normalization / relaxation / datalog-certificate stages). It is **out of scope here**, but
  Step 2b deliberately fixes its output interface now: the grounder will *produce* a
  `grounded_temporal_problem` (the way `wf_grounder` produces `grounded_problem`), so this plan's target
  structure is what it will be proven to hit.

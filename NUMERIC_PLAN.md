# Numeric plan — numeric conditions/effects on the new `Temporal_Planning` semantics

Status: draft (2026-06-25). Companion: [SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md) (this
is its §5 expanded) and [GROUNDING_PLAN.md](GROUNDING_PLAN.md) (interlock, §7). **Supersedes** the
retired `RUN_LIFT_PLAN.md` (numeric run-lift against the old `Temporal_AI_Planning_Languages_Semantics`);
its proof *design* is salvaged in §3 below, with the old line/lemma anchors dropped because the
re-point retype invalidates them.

---

## 1. Context / scope

The re-point ([SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md) Steps 0-4) lands **numeric-free
first** on the new `Temporal_Planning` semantics: `ast_effect.numeric_effects` is set to `[]` and
`duration_constraint` carries a constant `numeric_expression`. This plan is the **numeric phase**
(re-point §5): thread real numerics through, exploiting the new semantics' **native** numeric model
(`Continuous_Planning` numeric effects, `numeric_expression` durations, `wf_numeric_effect`) instead of
the old hand-rolled bounded-`int` encoding.

Two halves:
- **(A) semantics + reduction** — carry numerics through the grounded target and the NTA reduction.
- **(B) run-lift correctness** — re-prove "the timed-automata network simulates a temporal plan
  **with** numeric fluents".

Prerequisite: the numeric-free re-point is green and committed first; this lands as its own commit
series on top.

## 2. Semantics + reduction (re-point §5, half A)

- Populate `ast_effect.numeric_effects` (replace the `[]` placeholder) and carry numeric assignment
  effects through the snap split (`at_start_spec` / `at_end_spec` / `over_all_snap` in the
  `grounded_temporal_problem_defs` layer — see [SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md)
  §2b) and the code export.
- Carry genuine `numeric_expression` duration constraints (replace the constant-injection placeholder
  from re-point Step 2); relax the grounded target's `integer_duration_problem` /
  `functions D = []` restriction to admit nullary numeric functions.
- NTA reduction: encode numeric fluents as bounded `int` network variables; numeric updates/guards on
  the augmented action edges (`num_start_edge` / `num_end_edge` carry `num_upd`; `num_edge_2` is
  guard-only). Reuse the new semantics' numeric well-formedness rather than re-deriving it.

## 3. Run-lift correctness core (salvaged design, retargeted; half B)

The numeric simulation theorem reduces to a single **run-lift** obligation (on the old semantics this
was the lone `sorry` `num_happening_steps_possible`). The concrete lemma names/line numbers below are
**conceptual** — re-anchor them against the *retyped* `TA_Network/TP_NTA_Reduction_Correctness.thy`
when this phase starts; the **strategy** carries over verbatim.

**Strategy — one generic whole-list lift (not a per-phase mirror).** Add a single generic lemma that
lifts a whole propositional `graph_impl.steps` run to a `num_graph_impl.steps` run, parameterized by a
per-step `num_data` dispatcher and a carried valuation `w`; apply it once to the propositional
happening run. Do **not** mirror the five per-phase forward constructors — the lift only needs to
*invert* each step, never re-deriving the propositional invariant chain.

**Grounder-match assumption (the only real gap).** In the numeric reduction locale assume the
**static, grounder-checkable** closure properties (exact-division / discrete-fragment restriction):
- `num_val_ok w` — every fluent reads a defined integer;
- `snap_upds_nexp_ok` / `snap_guards_comp_ok` — every snap update RHS and guard comparison evaluates
  with declared, integer reads and exact `NDiv` along the run;
- `fluent_range_closed` — applying a snap keeps every fluent within `[fluent_lo, fluent_hi]`.

Discharging these for a concrete grounded problem is the **grounder's** job (abstract-locale decision,
out of scope here) — they tie directly to the grounded target's `integer_duration_problem` + numeric
well-formedness ([SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md) §2b) and to the grounding
interlock (§4).

**Helper lemmas to re-establish** (Run-lifting subsection of `TP_NTA_Reduction_Correctness.thy`):
- `num_val_ok_run` — the running fold of snap updates over `snd (M i)` stays `num_val_ok` + in-range.
- `happening_snap_nexp_ok` — transfer the static `nexp_ok` to the running valuation via non-interference.
- `num_tracks_bounded` (R2) — in-range `w` gives the fluent sub-store within `num_net_bounds`.
- `fired_edge_dispatch` (**the crux**) — invert the fired propositional edge, recover the matching
  augmented numeric edge + the `num_data` conclusion, next-`w` = `apply_upds (set us) w` on an update
  edge, `w` otherwise (case on source location: off/starting/running/ending → one of five action edges).
- `num_step'_lift` — lift one whole `step_u'` (delay + internal).
- `num_run_lift` (**the heart**) — list induction producing a numeric run with identical locs/clks,
  store extension `v' \<subseteq>\<^sub>m vn'`, `num_tracks` of the running `happening_num_update`, and
  boundedness.
- `run_order_snaps_distinct_enum` (R4) — the update-edges of `delay_and_apply i` fire a distinct
  enumeration of the happening's snap set, so the fold equals `happening_num_update` (=`snd (M (Suc i))`).

**Proof skeleton.** Name the prop run/tail; build the per-pair dispatch via `fired_edge_dispatch`;
apply `num_run_lift` → numeric run; obtain `w_final = snd (M (Suc i))` via the run-order fold; conclude
`num_happening_post` (propositional half transported by store equality, tracking half from the lift) +
`num_LvP`.

**Hardest sub-steps:** R1 integrality transfer (resolved by the grounder-match assumption), R2
per-step boundedness, R3 fired-edge identification (5 edges × 4 source locations), R4 run-order ↔
`happ_at` enumeration distinctness.

## 4. Interlock with grounding ([GROUNDING_PLAN.md](GROUNDING_PLAN.md) §7)

Datalog reachability tracks **definedness** (`defined!f`: EDB from init, head from numeric
assignments, body from `pre_s`/duration PNEs) but **not** comparison *values* (treating the test as
`True` is a sound over-approximation — a numeric guard only ever prunes). Grounding carries numeric
fluents + numeric effects + the duration constraint through `χ`; the **value** semantics (this plan,
half B) and the NTA integer variables evaluate them.

## 5. Critical files (re-anchor line numbers after the retype)

- `TA_Network/TP_NTA_Reduction_Correctness.thy` — the run-lift obligation + all new helpers
  (Run-lifting subsection).
- `TA_Network/TP_NTA_Reduction_Defs.thy` — the numeric reduction locale (add the Step-0 grounder-match
  assumptions); numeric edges + action edge list.
- `TA_Network/TP_NTA_Reduction_Correctness_Steps.thy` / `_Edges.thy` — per-phase `*_possible` shapes
  (reference only) and `delay_and_apply` run-order (for R4).
- `Temporal_Planning_Semantics/Temporal_Plans.thy` — `num_valid_state_sequence`, `snap_num_update` /
  `apply_upds`, `eval_nexp`: the abstract guards + tracking target.

## 6. Verification

- jEdit incremental (`jedit-status`), never a blind batch build; build the `Temporal_Planning_Base`
  heap once with `-b`.
- Each landed lemma: `TP_NTA_Reduction_Correctness.thy` reports `fully_processed: true` **and**
  `consolidated: true`, sorry count strictly decreasing.
- Final: no `sorry` anywhere in `TA_Network/*.thy` + `Temporal_Planning_Semantics/*.thy`; the numeric
  simulation theorem green; pipeline end-to-end on an instance exercising numeric effects / a numeric
  duration constraint.

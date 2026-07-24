# Numeric plan — numeric conditions/effects on the new `Temporal_Planning` semantics

**Status: REALIZED** — halves A/B are built, proven, executable and driven end-to-end (see
`HANDOVER.md`; the executable sequel is `NUMERIC_EXEC_PLAN.md`, also completed). Kept because the
theories cite this plan's A.x/B section numbers in doc comments; treat as the design/contract
record. (Original draft 2026-06-25. The formerly-referenced `SEMANTICS_REPOINT_PLAN.md` was
completed and removed in `ec10369` — see git history.) Companion:
[GROUNDING_PLAN.md](GROUNDING_PLAN.md) (interlock, §7). **Supersedes** the
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

## 3b. Numeric-net completeness capstone — the missing consumer of `num_plan_steps_possible`

> **STATUS UPDATE (2026-07-06) — rungs 0/1 CLOSED & COMMITTED; executable work split out.** The
> numeric-net certificate `num_valid_plan_imp_form_holds : num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula`
> is now proved **hypothesis-free** and **committed** (post the 2026-07-05 file reorg it lives in
> `TA_Network/TP_NTA_Reduction_Correctness_Numeric.thy:2784`, inside locale
> `numeric_tp_nta_reduction_correctness`). The `num_valid`/`num_seq_in_bounds`/`num_goal_comp_ok`
> assumptions now live in `TP_NTA_Reduction_Numeric_Model_Checking.thy` (was `Numeric_Tracking.thy`).
> **Rung 4 (the Ground_PDDL lift over the NUMERIC net) is still MISSING** — the only Ground_PDDL
> numeric lemmas (`Ground_PDDL_NTA_Reduction_Correctness.thy:37,44`) certify over the *propositional*
> `net_impl` via the additive-tracking shortcut, not over `num_net_impl`. Rung 4 plus the whole
> **executable** numeric layer (numeric `check_ground_problem`, `num_make_network_impl`, numeric
> `export_code`) are now planned in [NUMERIC_EXEC_PLAN.md](NUMERIC_EXEC_PLAN.md) (WP-A..E); the
> boundedness discharge (`num_seq_in_bounds` / `fluent_lo`/`fluent_hi`) is reserved for human design
> (WP-E). The line/file anchors in the rest of §3b predate the reorg — see NUMERIC_EXEC_PLAN §0/§3 for
> current names.

**Diagnosis (2026-07-03).** `num_plan_steps_possible`
(`TA_Network/TP_NTA_Reduction_Correctness_Numeric_Plan.thy:198`) is the top **completed** rung of the
numeric forward ladder: a valid numeric state-sequence `M` ⟹ the numeric net `num_graph_impl` has a
step run reaching a `num_goal_trans_pre` config. It mirrors the propositional `plan_steps_possible`,
but it has **zero consumers** and is the last lemma in its context. The rungs above it were never
built — git history confirms no numeric file ever referenced `reach_formula`/`a0`/`models`, and no
commit ever removed a consumer, so the ladder was simply left unfinished at this rung (not dropped in
the re-point).

Propositional ladder (the template), all in `TP_NTA_Reduction_Correctness.thy`:

```
plan_steps_possible (206) -> all_steps_possible (504) -> goal_run_is_run (512)
  -> valid_plan_imp_form_holds (575):  net_impl.sem, a0 |= reach_formula
  -> ref_correctness.valid_plan_imp_form_holds (636)
  -> (lifted) valid_ground_plan_imp_form_holds   [Ground_PDDL_NTA_Reduction_Correctness.thy]
```

**Why it matters.** The committed capstone `num_form_not_sat_imp_no_valid_ground_plan` takes the
additive-tracking shortcut (valid numeric plan ⟹ valid *propositional* plan ⟹ *propositional* net
`|= reach_formula`), so its certificate is over `net_impl` and never touches the numeric net — which is
exactly why the `Numeric_{Happening,Plan,Projection,Tracking}` machinery and `num_plan_steps_possible`
sit unused by it. But the net actually exported and model-checked in Munta (bounded-`int` fluent vars)
is the **numeric** net `num_net_impl`. To turn a Munta *numeric-net* unreachability result into "no
valid numeric plan", you need `num_valid_plan ⟹ num_net_impl |= reach_formula`, whose input is
`num_plan_steps_possible`. `reach_formula` is location-only (`loc 0 goal_loc`), so it is reused verbatim
on the numeric net.

**KEY refinement (2026-07-03, from the Phase-1 attempt).** `num_plan_steps_possible` deliberately stops
at `num_goal_trans_pre M (last …)`, which is still at `planning_loc` (`num_goal_trans_pre_propD` descends
to `goal_trans_pre`, whose `goal_trans_preE` fixes `L ! 0 = planning_loc \<noteq> goal_loc`). Reaching
`goal_loc` needs a **separate numeric goal-edge step** — the twin of the propositional `final_step_possible`
(`TP_NTA_Reduction_Correctness.thy:384`), which fires `main_auto_goal_edge` from `goal_trans_pre` to
`goal_state_conds`. On the numeric net that edge is `num_main_auto_goal_edge = augment_edge num_goal_guard []
main_auto_goal_edge` (`TP_NTA_Reduction_Defs.thy:560`), and its extra data guard
`num_goal_guard` (`…Defs.thy:490`) is discharged by `check_bexp_comps_guard` (`Numeric_Tracking.thy:316`)
**only from `sat_comps (snd (M (length planning_sem.htpl))) (set num_goal)`** — the numeric goal holding at
the final valuation. That conjunct is in `num_valid_plan` (`Temporal_Plans.thy:1554`) but **NOT** in
`num_valid_state_sequence` (`…:1450`), so it must be threaded in as `goalsat` (ultimately supplied by
`num_valid` / the plan-layer at rung 1).

**Ordered build** (mirror `TP_NTA_Reduction_Correctness.thy:384` + `504-631` on `num_graph_impl`/`num_net_impl`):
1. **[DONE, green — Phase 1]** `num_a0` (= numeric net initial config; `(init_locs, map_of num_init_vars,
   \<lambda>_. 0)`, mirroring `a0`) + numeric `num_goal_run` (self-loop stream). Still TODO here: `num_goal_run_is_run`.
2. `num_goal_state_conds` predicate (twin of `goal_state_conds`, `Happenings:779-802`) with `\<And>`-shaped
   I/E rules, + `num_final_step_possible` (twin of `final_step_possible:384`): from `num_goal_trans_pre M cfg`
   + `goalsat` (+ `comp_ok num_goal`), fire `step_int` at p=0 on `num_net_impl.sem` (skeleton via
   `num_main_auto_goal_edge_effect_loc/_clk`, StepInfra:194-195; guard via
   `check_bexp_comps_guard[OF num_goal_trans_pre_trackD … goalsat]`; `num_net_bounds` boundedness for the
   `planning_lock \<mapsto> 2` update) reaching a `num_goal_state_conds` config (`L ! 0 = goal_loc`).
   **[DONE, green — Phase 2]** conclusion shape `\<exists>cfg'. num_graph_impl.steps [cfg, cfg'] \<and>
   num_goal_state_conds cfg'`; needs extra hyps `num_LvP cfg` + `goalok: \<forall>c\<in>set num_goal.
   comp_ok (snd (M (length htpl))) c`. **Cleanup flag:** no `num_goal`-level `comp_ok` locale assumption
   exists (unlike `snap_pre_comp_ok_start/_end`); a `num_goal_comp_ok` assumption on
   `numeric_tp_nta_reduction_correctness` is the natural home if rung-1 can't derive `goalok` cheaply.
3. **[DONE, green — Phase 3; `num_plan_steps_possible` is now CONSUMED]**
   `num_valid_state_seq_imp_form_holds : num_net_impl.sem, num_a0 |= reach_formula` (+ `num_goal_run_is_run`;
   and `num_plan_steps_possible`'s `shows` strengthened to also return `num_LvP (last …)`, which its proof
   already established). Extends the `num_plan_steps_possible` run by the `num_final_step_possible` step, then
   `@- num_goal_run …`; run from `num_a0` via `num_graph_impl.extend_run'`/`run_alt`; `form_holds` via
   `num_goal_state_condsE`; unfold `reach_formula_def models_def formula.case num_graph_impl.Ex_ev_def
   Sequence_LTL.ev_alt_def`. Keeps `goalsat`/`goalok` + `num_a0`'s `num_LvP`/`num_init_planning_state_props'`
   as hypotheses (discharged at rung 4/1).
**CORRECTION (2026-07-03, Phase-4a attempt).** The Phase-3 `num_valid_state_seq_imp_form_holds` is stated
with `num_LvP num_a0` / `num_init_planning_state_props' M num_a0` as hypotheses — but these are **FALSE**:
`num_a0` is the config **before** the init edge (`init_locs!0 = init_loc = 0 \<noteq> planning_loc = 1`;
`num_init_vars` sets `planning_lock` to its lower bound 0, not 1). So that lemma is a vacuous vehicle at
the real `num_a0`. The propositional capstone avoids this because `plan_steps` (`Correctness_Edges.thy:200`)
**includes the init edge** via `initial_step_possible` (`Correctness_Steps.thy:24`) — the numeric ladder is
missing that BOTTOM rung too. Revised remaining build:

4. **Rung 0 (init edge) — DONE 2026-07-04, green:** `num_initial_step_possible` (mirror
   `initial_step_possible:24`): from `m0`, `num_graph_impl.steps [num_a0, cfg1] \<and> num_LvP cfg1 \<and>
   num_init_planning_state_props' M cfg1`, traversing the numeric init edge (`num_main_auto_init_edge_effect`,
   `StepInfra:160`; `num_init_upd` writes `num_init` into each fluent var, matched to `m0`). Then **rewrite**
   `num_valid_state_seq_imp_form_holds` to prepend this init step (drop the false `num_a0` `lvp`/`pres`
   hyps; keep `vss`/`m0`/`goalsat`/`goalok`).
5. **Rung 1 (discharge from the locale) — DONE 2026-07-04, green:** `num_valid_plan_imp_form_holds` (hypothesis-free): obtain `M`
   from the `num_valid` locale assumption (via `num_valid_plan_def`; bridge `num_rat_impl.htpl \<leftrightarrow>
   planning_sem.htpl`) → `vss`/`m0`/`goalsat`; `goalok` needs a NEW locale assumption `num_goal_comp_ok`
   (no `num_goal` well-formedness exists; discharge at the final valuation via `num_seq_in_bounds` →
   `fluent_in_bounds_imp_num_val_ok`, `Defs:529`). `num_seq_in_bounds` is already a locale assumption, so
   no bound-inference code is pulled in.
6. **Rung 4 (Ground_PDDL lift):** expose in the numeric model-checking locale and lift to
   `num_valid_ground_plan_imp_num_form_holds` + its contrapositive `num_form_not_sat_imp_no_valid_ground_plan`
   **over the numeric net** — the numeric analog of `valid_ground_plan_imp_form_holds`, routed through the
   (numeric) `abstr_model_checking` sublocale.

**STATUS 2026-07-04: rungs 0 + 1 COMPLETE (green, uncommitted).** `num_valid_plan_imp_form_holds :
num_net_impl.sem, num_a0 |= reach_formula` (hypothesis-free) is proved in
`numeric_tp_nta_reduction_correctness` (`Numeric_Plan.thy:1142`) — so `num_plan_steps_possible` is now
fully consumed and the numeric net certifies `reach_formula`. Two things landed with it:
(i) the frozen-consolidate DIVERGER was two proof-futures inside `num_initial_step_possible` doing
`dom (map_of ...)`/big-store reasoning via `dom_map_of_conv_image_fst`/`variables_unique` — fixed by
routing through the element-level `map_of_net_bounds_init_goal` instead of unfolding the full store
(found by sorry-bisection; the `num_goal_run` primcorec was a red herring, only blocked behind them).
(ii) `num_goal_comp_ok` was ADDED as a locale assumption (`Numeric_Tracking.thy:71`, mirroring
`snap_pre_comp_ok_*`) — a NEW grounder-match obligation for `num_goal`'s comparisons, discharged in the
lemma via `num_seq_val_ok`. REMAINING: rung 4 (Ground_PDDL lift). Cleanup flags: brittle raw
`dom_map_of_conv_image_fst` dom-membership steps over the big store (the divergence source — candidate
for a named exact-domain lemma set); stale `TA_Network/*.thy~` backups.

**Relationship to the committed capstone.** Both are sound. The committed one certifies over `net_impl`
(propositional) via additive tracking; this one certifies over `num_net_impl` (numeric) and is the
certificate that matches the exported/checked net. Keep both; this one supersedes the additive-tracking
capstone as the *primary* numeric unsolvability certificate.

**Scaffolding already present:** `num_graph_impl` (Graph_Defs, `Numeric_Tracking.thy:78`),
`num_steps_seq: sequence_rules` + `num_steps_extend` (`Numeric_Projection.thy:1036-1044`),
`num_goal_trans_pre_propD` / `_trackD` (`Numeric_Tracking.thy:638/641`), and the whole run-lift core
(§3). **Missing:** `num_a0`, numeric `goal_run`, and rungs 1 / 3 / 4.

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

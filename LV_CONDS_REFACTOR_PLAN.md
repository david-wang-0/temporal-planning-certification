# Plan: Refactor — factor `Lv_conds` out of the propositional invariants

Status: **DONE (2026-06-24)** — all 4 phases landed; whole build green, **0 errors / exactly 1 sorry** (the
`num_happening_steps_possible` run-lift core, unchanged). `Lv_conds` carried as `LvP` through the propositional
run; `num_Lv_conds` carried as `num_LvP` through the numeric run (the §3 plan below is the executed spec; see
[HANDOVER.md](HANDOVER.md) 2026-06-24 for the as-built summary + next steps). Originally: implementation plan
(2026-06-23). Prerequisite cleanup for [RUN_LIFT_PLAN.md](RUN_LIFT_PLAN.md)
(it removes the store-projection friction from the numeric twins); part of [NUMERIC_PLAN.md](NUMERIC_PLAN.md)
§7 P4 (Layer-B forward correctness). Live per-lemma state in [HANDOVER.md](HANDOVER.md). Touches the
propositional correctness proof in `TA_Network/TP_NTA_Reduction_Correctness{,_Happenings,_Steps}.thy`.

---

## 1. Context / goal

`Lv_conds L v` (`TA_Network/TP_NTA_Reduction_Correctness_Happenings.thy:41`) =
```
length L = Suc (length actions) ∧ L ! 0 = planning_loc ∧ bounded (map_of net_bounds) v ∧ v planning_lock = Some 1
```
is currently bundled as a conjunct **inside** the per-step invariant predicates (`happening_pre`:165,
`happening_post`:195, `happening_invs`:215, `init_planning_state_props`:78, `init_planning_state_props'`:100,
`goal_trans_pre`:121), and is inherited transitively by ~40 more (`end_start_invs`, the
`*_cond`/`*_pre`/`*_post` family). Its `bounded (map_of net_bounds) v` clause is **domain-exact**
(`dom v = dom net_bounds`), which forces every numeric "twin" invariant to be stated on a **projected**
store `v |` dom (map_of net_bounds)` and to thread that projection everywhere — the main friction in the
numeric run-lift.

**This refactor factors `Lv_conds` OUT of those predicates and carries it as a separate conjunct
throughout a run.** The value/lock/clock conditions are each guarded to propositional variables
(`prop_to_var p ∈ dom (map_of net_bounds)`) and so agree on `v` and `v |` dom net_bounds` — once
`Lv_conds` is removed they become predicates that **hold on the full store**, and a single stronger
`num_Lv_conds` (full store, `num_net_bounds`-bounded) carries the numeric well-formedness — itself
factored out of the numeric twins and **carried as a separate conjunct throughout the numeric run,
symmetric to `Lv_conds` in the propositional run**. Outcome: `Lv_conds`/`num_Lv_conds` are first-class
run invariants of their respective layers, the propositional value-predicates and the numeric twins are
projection/boundedness-free (value + tracking only), and the numeric run-lift can thread value conditions
on the full store. (Chosen: the full "remove from inside" refactor — clean the propositional layer too —
over a non-invasive decompose variant that adds parallel value-only predicates.)

## 2. Approach — the `LvP`-conjunction seam

The run is threaded by the **generic** `sequence_rules` combinators in
`Temporal_Planning_Common/Sequences.thy` (`ext_seq_comp_seq_apply_induct_list_prop_composable`,
`fold_…composable`, `ext_seq'_induct_list_prop_and_post`, `seq_apply_ConsI`) over config predicates
`('a ⇒ bool)`. The combinators stay **unchanged**. Instead:

1. Add `fun LvP (L, v, _) = Lv_conds L v` (right after `Lv_conds_def`).
2. Drop the `Lv_conds L v` conjunct from the 6 base predicate **definitions** (the transitive ones
   inherit, so their defs need no edit).
3. Instantiate every combinator's `R/P/Q/S` (and the threading lemmas' assumptions/conclusions) with
   `(λs. <pred> s ∧ LvP s)` — carrying `Lv_conds` as a separate conjunct.

**Preservation is reused, not re-proved.** `Lv_conds_maintained` (`Happenings:1324`) already exists and
is already invoked inline in every group lemma. The refactor relocates those invocations from inside the
nested `happening_invs` to the separate `LvP` conjunct — the facts proved/consumed are identical, only
their syntactic home moves. No new preservation lemma.

## 3. Phases (each verified green in jEdit before the next; commit per phase)

### Phase A — definitions + rules (`..._Happenings.thy`)
- Add the `LvP` abbreviation.
- Drop `Lv_conds L v` from `happening_pre`, `happening_post`, `happening_invs`,
  `init_planning_state_props`, `init_planning_state_props'`, `goal_trans_pre`.
- **Leave `init_state_props` and `goal_state_conds` unchanged** — they inline a standalone `bounded`
  clause (not `Lv_conds`) and sit outside the `Lv_conds`-carrying region (init pre-state / goal post-state).
- Rule edits (pattern): each `*I` drops the `Lv_conds L v` assumption; each `*_dests` drops conclusion
  **(1)** (→ downstream `*_dests(n)` callers re-index −1); each `*E` drops the `Lv_conds` premise.
  `happening_invs_maintained` loses its `Lc` premise (becomes clock/loc-only). `Lv_conds` itself and
  `Lv_condsI/E/D/dests/maintained` stay (now consumed at the threading sites).

### Phase B — group lemmas + `happening_steps_possible`
Validated pattern (template = `end_starts_possible`, `..._Steps.thy:253`): conjoin `LvP` to the lemma's
assumption + conclusion and to the combinator's `R/P/Q/S`. The forward-step case gains a short
`Lv_conds`-preservation lift (copied from the existing inline `Lv_conds_maintained` block); the transfer
cases are `LvP`-passthrough. Extraction chains that reached `Lv_conds` through `happening_invs` become
`Lv_conds_dests[OF lv]` (the locally-extracted threaded conjunct). Order: `end_starts_possible` →
`start_starts_possible` → `end_ends_possible` → `start_ends_possible` → **`instant_actions_possible` last
(highest risk:** nested `seq_apply_ConsI`, two intermediate predicates, three edge types). Then
`happening_steps_possible` chains them (seed `LvP (delay …)` from the in-scope `Lv_conds`; expose
`∧ LvP (last …)` in its conclusion).

### Phase C — `plan_steps_possible` + `pp_*` + `initial/final_step_possible`
- `plan_steps_possible` (`Correctness:194`): conjoin `LvP` to `R/P/Q/S`; case 2 reuses
  `happening_steps_possible`; cases 3/5/6 read `Lv_conds` from the threaded conjunct (not
  `happening_post_dests(1)` / `init_planning_state_props'E`) and drop the `Lv_conds` arg from `*I` calls.
- `initial_step_possible`: build `Lv_conds` via `Lv_condsI` into the threaded `LvP` conjunct.
- `final_step_possible`: `goal_trans_pre` is `LvP`-free; `Lv_conds` arrives via the threaded conjunct.
- `pp_*` transfers: gain an explicit `Lv_conds`/`LvP` premise (no threaded conjunct in scope).

### Phase D — numeric layer: carry `num_Lv_conds` separately (mirror of Phases A–C)
Symmetric to the propositional refactor: factor `num_Lv_conds` OUT of the numeric twins and carry it as a
separate conjunct throughout the numeric run, exactly as `LvP` is carried in the propositional run.
- Define the stronger `num_Lv_conds L v ≡ length L = Suc (length actions) ∧ L!0 = planning_loc ∧
  bounded (map_of num_net_bounds) v ∧ v planning_lock = Some 1` (full store) and
  `fun num_LvP (L, v, _) = num_Lv_conds L v`. Prove
  `num_Lv_conds L v ⟹ Lv_conds L (v |` dom (map_of net_bounds))` (via `prop_proj_bounded` +
  `planning_lock ∈ dom net_bounds`) — the bridge that supplies `LvP` on the projection when the numeric
  run invokes the propositional `happening_steps_possible`.
- Slim the 5 twins to `<value-pred> i (L, v|`pv, c) ∧ num_tracks v (snd (M ?))` (numeric value + tracking
  only) — the old `bounded (map_of num_net_bounds) v` conjunct moves into `num_Lv_conds`. Keep
  `_propD`/`_trackD`; drop `_boundD` (boundedness now comes from the carried `num_LvP`).
- Carry `num_LvP s` as a SEPARATE conjunct throughout the numeric run — `num_plan_steps_possible`,
  `num_happening_steps_possible` (the run-lift core), and the 4 `num_*` transfers — mirroring `LvP`.
  Preservation: a `num_Lv_conds_maintained` analog of `Lv_conds_maintained` (the augmented numeric edges
  keep locations/`planning_lock`; `bounded (map_of num_net_bounds)` is established per step by the
  run-lift's `num_int_step_lift` bound output / the §B INV obligation). `num_LvP` passes through the
  transfers unchanged (same store) and bridges to the propositional `LvP` via the implication above.
- Knock-on: this slims the twins consumed by [RUN_LIFT_PLAN.md](RUN_LIFT_PLAN.md), so the run-lift threads
  `num_LvP` alongside its value + tracking invariant (update that plan's Part-2/3 invariant accordingly).

## 4. Verification

Incremental jEdit only (no batch build): each phase/lemma to **0 errors** before the next, ending
`fully_processed ∧ consolidated`. The whole `TP_NTA_Reduction_Correctness.thy` (and Happenings/Steps)
must stay green with **still exactly 1 sorry** — the run-lift core `num_happening_steps_possible` is
untouched by this refactor. Commit a green checkpoint after each phase; keep local `*.bak` copies.

## 5. Risks / fallbacks

- **Highest risk: `instant_actions_possible`** (Phase B) — do it last, after the pattern is proven on the
  other four group lemmas.
- The refactor is **fundamentally mechanical**: preservation is already proved inline; facts are
  relocated, not re-derived.
- **Fallback 1** (if group-lemma re-threading is intractable): keep `Lv_conds` inside `happening_invs`
  but *also* conjoin a redundant (derivable) `LvP` at the combinator boundary — passthrough only,
  near-zero `Steps.thy` churn; numeric + boundary layers still get the clean separate conjunct.
- **Fallback 2** (narrower): factor `Lv_conds` out of only the boundary predicates, leaving the internal
  `happening_invs` nest carrying it — isolates churn to `Correctness.thy`.

## Follow-on ideas (revisit after this refactor lands)

- **Factor out other always-preserved conditions, the same way as `Lv_conds`.** Several predicates bundle
  structural/invariant conjuncts that hold throughout a run and could likewise be hoisted into a
  separately-carried predicate to further slim the per-step value predicates — notably the **`*_invs`
  family** (`happening_invs` / `end_start_invs` / `instant_action_invs`), which carry the
  non-happening-action clock/location invariants threaded across every step. Same `LvP`-style treatment
  (drop from the predicates, carry as a separate conjunct, preserve via a `*_maintained` lemma) is a
  candidate if it would further simplify the numeric layer / run-lift. (User-flagged 2026-06-24.)

## Phase-B idioms discovered (for the remaining group lemmas + future)

Beyond the LvP-threading recipe (§3 Phase B), converting `end_starts_possible` / `instant_actions_possible`
surfaced these (load-bearing for the clock-heavy lemmas):
- **Passthrough cases:** `apply (insert N)` + `apply (rule conjI)` (NOT `thus ?case apply (rule conjI)`);
  insert `apply (elim conjE)` right after `unfolding comp_def` so `*_dests` fire on atomic premises; the
  new `LvP` conjunct closes `by simp` off the conjoined hypothesis.
- **Forward case:** extract `lvp: LvP s` / `lv: Lv_conds L v` early; split `show ?case` with `rule conjI`s
  into `[<post>, LvP, steps]`; prove the edge's `LvP` via `Lv_conds_maintained[OF lv]` (edge touches only
  `L!Suc n`; `length`/`L!0` by `simp`; `planning_lock` via `map_upds_apply_nontin`/`fun_upd_other` +
  `variables_unique`; `bounded` reuses the proof's own `bounded_after`/`upds_map_bounded`).
- **`*_dests` index shift −1** (the `Lv_conds` concl was dropped): `happening_invs_dests(2,3,4,5)`→`(1,2,3,4)`, etc.
- **`last_ConsR` double-subst:** with threading, `last (seq_apply …)` appears twice (in `<post>` and in `LvP`)
  — rewrite BOTH or `seq_apply_ConsI` unification breaks.
- **Source `Lv_conds` through `LvP.simps`:** after `elim conjE` the premise is `LvP (L,v,c)` (a `fun` eqn),
  so use `prems(k)[unfolded LvP.simps]` for `Lv_conds_maintained`/`Lv_conds_dests`.
- **CRITICAL — clock-maintenance diverges:** the old `apply (rule clocks_unique); (use iij_ran in simp)+`
  idiom hangs (PIDE `running`, 800s+) under the new goal shape. Replace with targeted
  `clocks_unique(9)[OF nth_mem nth_mem nth_actions_unique]` (end/end) / `clocks_unique(7)[…]` (start/start),
  discharging `<` side-goals by `assumption`/`rule iij_ran` and the action-index `≠` by
  `(use … index_case_disj in blast)`. Find such silent hangs via `get_document_info(timing_threshold_ms=…)`.
- NB `start_starts_possible` has a pre-existing diverging `apply fastforce` (~line 1710) independent of the refactor.

## 6. Critical files

- `TA_Network/TP_NTA_Reduction_Correctness_Happenings.thy` — defs, intro/dest/elim rules,
  `Lv_conds_maintained`, `happening_invs_maintained`, the `LvP` abbreviation site, `steps_seq`.
- `TA_Network/TP_NTA_Reduction_Correctness_Steps.thy` — the five group lemmas (`end_starts_possible`
  is the template; `instant_actions_possible` the risk), `initial_step_possible`.
- `TA_Network/TP_NTA_Reduction_Correctness.thy` — `happening_steps_possible`, `plan_steps_possible`,
  `final_step_possible`, the numeric twins, the `pp_*`/`num_*` transfers, `num_plan_steps_possible`.
- `Temporal_Planning_Common/Sequences.thy` — generic combinators (read-only reference, no edits).
- `TA_Network/TP_NTA_Reduction_Correctness_Edges.thy` — boundedness/edge facts (read-only reference).

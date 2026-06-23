# Plan: Numeric run-lift — closing `num_happening_steps_possible`

Status: implementation plan (2026-06-23). Sub-plan of [NUMERIC_PLAN.md](NUMERIC_PLAN.md) §7 P4
(Layer-B forward-direction correctness); live per-lemma state in [HANDOVER.md](HANDOVER.md). This
closes the **single remaining `sorry`** in the numeric reduction: the per-happening run-lift core
in `TA_Network/TP_NTA_Reduction_Correctness.thy`.

---

## 1. Goal

`num_happening_steps_possible` must show: from a combined config `cfg = (L, v, c)` whose store
satisfies `num_happening_pre_pre_delay M i cfg`, there is a numeric run
`num_graph_impl.steps (cfg # ns)` ending in a config satisfying `num_happening_post M i`, i.e.

- the propositional `happening_post i` on the **projected** store `v |` dom (map_of net_bounds)`,
- **plus** `num_tracks (final store) (snd (M (Suc i)))` (the numeric valuation is tracked correctly),
- **plus** `bounded (map_of num_net_bounds) (final store)`.

Everything else in the numeric forward direction is already green
(0 err / 1 sorry / 2333 cmds, consolidated): the keystone per-step lift, the per-edge `num_data`
dischargers, the projection infra, the delay/urgency lifts, `num_plan_steps_possible`, and the
capstone scaffold. Closing this `sorry` finishes the numeric forward direction for non-empty
problems. (The §B `INV` bounds and the discreteness side-conditions remain *hypothesized* at this
layer, per the NUMERIC_PLAN design.)

## 2. Architecture decision — constructive route via the `sequence_rules` locale

Two architectures were considered for producing the numeric run:

| | Existential lift | **Constructive via `sequence_rules` (chosen)** |
|---|---|---|
| How | walk the prop run as a black box, invert each `step_u'` and re-fire numerically | re-run the prop combinator skeleton over the **numeric** edge-effects, with a strengthened invariant |
| Inversion lemma (`net_step_internal`) | needed | **not needed** |
| Reuse | per-step lifting | reuses the proven prop `*_possible` group lemmas + the existing threading machinery |
| Cost | brittle per-step position/snap alignment over the flattened run | mirrors the five group lemmas (volume), builds a closed-form numeric run |

The decisive finding: **engaging `delay_and_apply`'s `seq_apply`/`ext_seq` structure is unavoidable
either way**, and the genuinely hard part — the *abstract fold connection* (the tracked valuation of
the final store equals `snd (M (Suc i))`) — is identical for both. The constructive route reuses the
existing `sequence_rules` threading and the proven propositional group lemmas, so it is preferred.

> **↩ Revisit later — the existential-lift approach.** If the constructive route's volume (the five
> mirrored group lemmas, item 7) proves painful, or for a cleaner / more reusable result, try the
> existential lift: a generic `num_run_lift` engine that walks the prop run `cfg # delay_and_apply i cfg`
> and lifts each `step_u'` (delay + internal) numerically. It needs `net_step_internal` (a non-`Del`
> step of `net_impl.sem` is `Internal` — every edge is `Sil ''''`, `net_broadcast = []`, so
> `step_bin`/`step_broad` are vacuous; the action-automaton `trans` is computed by `nth_auto_trans`)
> and a single-`step_u'` lift `num_step_u'_lift` composing `num_step_t_lift` (delay) + `num_int_step_lift`
> (internal) via `step_u'.intros`. It realises the "combination theorem at run level" framing and avoids
> mirroring the group lemmas, at the cost of brittle per-step position/snap alignment over the flattened
> run. The delay-half (`num_step_t_lift`) and the bound-exposing `num_int_step_lift` already built this
> session are directly reusable for it. The shared abstract core (Part 1) is identical, so this is a swap
> of Part 2 only.

## 3. Reused, already-green bricks (do NOT re-prove)

`TA_Network/TP_NTA_Reduction_Correctness.thy`: `num_step_int_lift` (builds an augmented-edge
Internal numeric step), `num_int_step_lift` (per-step lift; now also exposes `bounded vn'`),
`num_data_upd_edge` / `num_data_no_write_edge` (per-edge providers),
`sat_comps_happening_num_update_set` (intra-happening guard invariance), `num_step_t_lift`
(leading-delay lift), `num_urgent_eq`, `num_steps_delay_replace`,
`edge_effect_augment_loc`/`_clk` (numeric run shares locations/clocks with the prop run),
`check_bexp_comps_guard` / `is_upds_num_upd`, the projection infra `store_decomp` / `prop_proj_bounded`
(relocated before the run-lift), the twin rules `num_happening_post{I,_propD,_trackD,_boundD}`,
and the `num_*_edge_effect` definitions.

`Temporal_Planning_Semantics/Temporal_Plans.thy` (reached as `num_plan.num_rat_impl.*`):
`snap_num_update` = `apply_upds (upds s)`, `happening_num_update` (list fold),
`happening_num_update_set` + `_empty`/`_insert`, `comp_fun_commute_on_snap_num_update`,
`num_valid_state_sequence`. `Temporal_Planning_Semantics/Temporal_Plans_Lemmas.thy`:
`happ_at_is_union_of_starting_ending_instant` and the `*_actions_at`/`*_snaps_at`/`is_*_action` defs.
Propositional run + skeleton: `happening_steps_possible`, the five group lemmas in
`TA_Network/TP_NTA_Reduction_Correctness_Steps.thy`
(`start_ends_possible`/`end_ends_possible`/`start_starts_possible`/`instant_actions_possible`/
`end_starts_possible`), `delay_and_apply`/`apply_nth_happening` in
`TA_Network/TP_NTA_Reduction_Correctness_Edges.thy`, and the `sequence_rules` locale in
`Temporal_Planning_Common/Sequences.thy`.

## 4. Work items (dependency order)

### Part 1 — abstract fold connection (the mathematical core; engine-independent)

1. **`happ_at_index_decomp`** (FACT-1 bridge). State `S = happ_at plan_happ_seq (time_index i)` as
   a union over action *indices*:
   `{at_start (actions!j) | j<len. is_starting_index (t i) j ∨ is_instant_index (t i) j}
   ∪ {at_end (actions!j) | j<len. is_ending_index (t i) j ∨ is_instant_index (t i) j}`.
   Proof: `happ_at_is_union_of_starting_ending_instant` + the `*_actions_at` and `is_*_index` defs
   + `set_conv_nth`, using the existing `image_end_indices_conv_actions` template and `at_start`/
   `at_end` injectivity. Also export `finite S` and pairwise-`¬ num_mutex_snap_action` on `S`
   (from `num_mutex_valid_plan` / ε-separation — co-occurring snaps don't numerically interfere).

2. **`happening_num_update_set_eq_fold_list`** (FACT-2 wrapper, in `num_rat_impl`):
   `distinct xs ⟹ (functional on set xs) ⟹ (pairwise ¬num_mutex on set xs) ⟹
   happening_num_update_set (set xs) w = happening_num_update xs w`.
   Proof: `comp_fun_commute_on_snap_num_update` then HOL `comp_fun_commute_on.fold_set_fold`
   (or a short `finite_induct` over `happening_num_update_set_insert`, mirroring
   `happening_num_update_set_id`).

3. **`run_order_fold_eq_happening_num_update_set`** (the heart). The run-order left-fold of
   `snap_num_update` over the run's update-snaps, from `snd (M i)`, equals
   `happening_num_update_set S (snd (M i)) = snd (M (Suc i))`. Build the run-order update-snap list
   `enum` (instant `at_start`/`at_end`, then starting `at_start`, then ending `at_end`); no-write
   edges contribute identity. `set enum = S` (item 1), `distinct enum` (`distinct actions` +
   injectivity + index-class disjointness `index_case_disj`), then item 2 gives
   `happening_num_update enum (snd(M i)) = happening_num_update_set S (snd(M i))`; close with
   `num_valid_state_sequence M` at `i`.

4. **`num_upd_guard_discharge`** (per-edge numeric-guard precondition). For an update snap `s ∈ S`
   fired at the running (partially-updated) store `vn` tracking a partial fold of `S`, the `gn`/`fn_ok`
   hypotheses of `num_data_upd_edge` hold: `check_bexp vn (num_pre_guard s) True` via
   `check_bexp_comps_guard` reduced to `sat_comps vn (n_pre s)`, bridged from `sat_comps (snd(M i)) (n_pre s)`
   (from `num_valid_state_sequence`) by `sat_comps_happening_num_update_set` (guard reads only
   `snap_reads s`, co-snaps non-interfering); `fn_ok` from `upds_functional_*` / `nexp_ok_is_val`.

### Part 2 — constructive numeric engine (via `sequence_rules`)

5. **`sublocale num_steps_seq: sequence_rules num_graph_impl.steps`** — axioms are
   `num_graph_impl.steps.Single` + `num_graph_impl.steps_append` (already in use). One-liner;
   mirrors the propositional `steps_seq`.

6. **Define the numeric happening run** `num_apply_nth_happening` / `num_delay_and_apply` (numeric
   analog of `apply_nth_happening`/`delay_and_apply`), substituting the `num_*_edge_effect`s for the
   prop effects. This is the existential witness `ns`. (Inline in the correctness file for now; the
   numeric-file split is a later refactor.)

7. **Five numeric group lemmas** — `num_{start_ends,end_ends,start_starts,instant_actions,end_starts}_possible`,
   each the numeric strengthening of its prop counterpart. Carried invariant: the prop invariant on
   the projected store **and** `v ⊆⇩m vn` (projection commutes with each augmented edge-effect via
   `edge_effect_augment_loc`/`_clk` + prop updates touching only prop vars) **and**
   `num_tracks vn (running partial fold)` **and** `bounded num_net_bounds vn`. Per-edge step
   `num_graph_impl.steps [s, num_X_edge_effect n s]`: feed the propositional per-edge step (so the
   heavy `check_bexp` guard proofs are *not* re-derived) to `num_int_step_lift`, with `num_data`
   chosen by edge type — `num_data_upd_edge` (start/end, advancing the fold; numeric guard via item 4)
   or `num_data_no_write_edge` (edge_2/edge_3/instant_trans, fold unchanged). Leading delay via
   `num_step_t_lift` + `num_steps_delay_replace`.
   *Reuse check (resolve early):* whether `..._Steps.thy` exposes per-edge prop step lemmas to feed
   `num_int_step_lift`; if only the group lemmas exist, extract the per-edge prop step from the prop
   group run.

### Part 3 — assembly

8. **`num_happening_steps_possible`** (close the `sorry`). Keep the existing extraction of
   `ppd`/`tr`/`bnd` and `happening_steps_possible[OF i ppd]` (for `ppost`). Witness
   `ns := num_delay_and_apply i cfg`; chain the five numeric group lemmas through `num_steps_seq`
   to get `num_graph_impl.steps (cfg # ns)` with the strengthened invariant at `last`. Then: the
   projection conjunct of `num_happening_post` follows from `ppost` (numeric run projects to the
   prop run); the tracking conjunct from item 3; the bound from the invariant. Conclude via
   `num_happening_postI`.

## 5. Verification

- Develop incrementally against the running jEdit (the `jedit-status`/`isabelle-prove` workflow);
  build each lemma to green before the next. The file must stay **0 errors**, with the `sorry`
  count dropping to **0** at item 8. Do **not** batch-build.
- Final gate: diagnostics report `fully_processed: true` **and** `consolidated: true` with
  `errors: 0` and no `sorry`.
- `num_plan_steps_possible` (already green) consumes `num_happening_steps_possible`, so closing this
  `sorry` completes the numeric forward-direction chain to the capstone.

## 6. Risks / phasing

- **Highest-volume:** the five numeric group lemmas (item 7) — mostly mechanical mirroring of
  `..._Steps.thy`; the instant-action group is fiddliest (three edges, two updates with a no-write
  between, fold advances twice). Mitigation: prop content is reused (projection/strengthening), not
  re-derived; prove one group lemma end-to-end first to lock the invariant shape, then replicate.
- **Highest-novelty:** items 1–3 (the fold connection). All dependencies exist; residual risk is the
  `distinct enum` / `set enum = S` finite-set bookkeeping across the concatenated index groups.
- **Per-edge reuse uncertainty:** whether prop per-edge step lemmas exist to feed `num_int_step_lift`
  (item 7) — resolve early; otherwise extract per-edge prop steps from the prop group run.
- **Working discipline:** commit a green checkpoint before starting and after every green milestone
  (each completed Part / group lemma) so there is always a recoverable state; keep local `*.bak`
  copies of the files under edit. (`*.bak` is gitignored.)
- Suggested order: Part 1 (items 1–4) → items 5/6 → one group lemma (item 7) → remaining group
  lemmas → item 8.

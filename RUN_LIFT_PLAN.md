# Numeric run-lift plan — close `num_happening_steps_possible`

## Context

The project proves that a timed-automata network *simulates* a temporal plan. The propositional
(no numeric fluents) case is fully proven: `valid_plan_imp_form_holds`
(`TA_Network/TP_NTA_Reduction_Correctness.thy`, ~line 575) and its plan-level wrapper. The numeric
extension (fluents encoded as bounded `int` network variables) is **green except for a single
`sorry`** — `num_happening_steps_possible` (`TA_Network/TP_NTA_Reduction_Correctness.thy`,
~lines 2555–2590). Everything downstream is already wired up: `num_plan_steps_possible` (the
happening chain, ~2786–2844), the index-transfer lemmas (`pp_post_imp_pre_pre_delay_Suc` etc.), and
the top-level `numeric_valid_temp_plan_imp_form_holds` (~line 663). Closing this one `sorry` makes
the entire numeric simulation green.

The input is a **grounded** problem; per decision, we prove inside the abstract numeric locale and
take integer-valuedness as a grounder-match assumption (see Step 0). `nfluents` is a concrete list,
`fluent_to_var` injective on it, values are `int`-encoded via `const_to_int`.

**Goal:** replace the `sorry` in `num_happening_steps_possible` (adding the helper lemmas it needs
and one well-formedness assumption), keeping the file green at every checkpoint.

## What the proof must do (the run-lift core)

Before the `sorry`, the proof already has: `cfg = (L,v,c)`; the propositional pre-state
`ppd: happening_pre_pre_delay i (L, v |` dom (map_of net_bounds), c)`;
`tr: num_tracks v (snd (M i))`; the full-store bound `bnd`; `lvpr: LvP (...)`; and the
**propositional happening run**

```
prun:  graph_impl.steps ((L, v |` dom (map_of net_bounds), c) # delay_and_apply i (...))
ppost: happening_post i (last (delay_and_apply i (...)))
```

from `happening_steps_possible[OF i ppd lvpr]` (template at lines 6–199).

The remaining work is a **run-lift**: lift `prun` config-by-config to a numeric run over the *full*
store `v`, threading `num_tracks` with the running `happening_num_update` partial fold, so the last
config tracks `snd (M (Suc i))` (the witness `num_happening_post` needs) and stays `num_LvP`.

Confirmed structural facts:

- `prun` is a pure-internal run with the leading `delay (get_delay i)` already absorbed into step 1
  by the propositional proof (line 118). Each consecutive pair is one Munta `step_u'`
  (`Del`-then-`Internal a`).
- The numeric net shares **locations and clocks** with the propositional net at every config; only
  the store extends (`v' \<subseteq>\<^sub>m vn'`). Loc/clk equality of augmented edges is already
  proven: `edge_effect_augment_loc/clk` (1471/1475), `num_*_edge_effect_loc/clk` (1489–1499).
- Numeric action-automaton edges (`TP_NTA_Reduction_Defs.thy:519`):
  `[num_start_edge a, num_edge_2 a, edge_3 a, num_end_edge a, instant_trans_edge a]`.
  `num_start_edge`/`num_end_edge` carry a numeric **update** (`num_upd` of the at_start/at_end snap);
  `num_edge_2` (guard-only), `edge_3`, `instant_trans_edge` carry **no** numeric write.
- In `delay_and_apply` run order the update-carrying edges enumerate the happening's snaps
  distinctly; folding their `snap_num_update`s over `snd (M i)` gives `snd (M (Suc i))` — already
  proven as `run_order_fold_eq_happening_num_update_set` (~2118), with the happening's
  index-decomposition `happ_at_index_decomp` (~1935, FACT-1).

## Approach: one generic whole-list lift (not a per-phase mirror)

Add a single generic lemma that lifts a whole propositional `graph_impl.steps` list to a
`num_graph_impl.steps` list, parameterized by a per-step `num_data` dispatcher and a carried
valuation `w`. Apply it once to `prun`. **Do not** mirror the five per-phase `*_possible` lemmas
(`end_starts_possible` 266, `instant_actions_possible` 739, `start_starts_possible` 1620,
`end_ends_possible` 2149, `start_ends_possible` 2593 in `..._Steps.thy`) — those are *forward
constructors* that re-derive the propositional invariant chain; the lift only needs to *invert*
each step from `prun`, never touching the `ext_seq`/`seq_apply'` composition. Mirroring would roughly
double the proof for no gain.

All per-step primitives already exist and are proven:

- `num_int_step_lift` (1664) — lift one `Internal a` given a `num_data` provider.
- `num_step_t_lift` (2517) — lift one `Del`.
- `num_data_no_write_edge` (1740) / `num_data_upd_edge` (1770) — discharge `num_data` for
  no-write vs update edges.
- `num_steps_delay_replace` (2220) + `num_no_urgent` (2300) — delay handling (fallback path).
- `num_Lv_conds_maintained` (1223), `num_LvP_imp_LvP` (2467), `prop_proj_bounded` (2380),
  `num_tracks_pres_unwritten` (1718), `is_upds_num_upd` (1109).
- Guard transfer to the running fold: `sat_comps_happening_num_update_set` (~2171),
  `check_bexp_comps_guard` (984), `check_bexp_comp_to_bexp` (926).
- `num_graph_impl.steps` plumbing: `steps_append`, `num_steps_replace_Cons_hd` (2199),
  `num_single_step_intro` (1431).

## Step 0 — Grounder-match assumption (resolves the only real gap)

Faithfulness (`nexp_ok`, Correctness.thy:826; `const_to_int_*` homomorphism lemmas 772–823) requires
each snap update/guard RHS to evaluate to a **defined, integer** value (exact division) along the
run, and the value to stay within `[fluent_lo, fluent_hi]`. Nothing currently guarantees this.

Add to locale `numeric_tp_nta_reduction` (`TP_NTA_Reduction_Defs.thy:602`, alongside
`upds_functional_*`/`fluent_bounds_valid`/...). Introduce an auxiliary
`num_val_ok w \<equiv> (\<forall>f \<in> set nfluents. \<exists>r. w f = Some r \<and> r \<in> \<int>)`
and assume (one-for-one with what a sound grounder guarantees):

- `snap_upds_nexp_ok`: for every `a \<in> set actions` and every `w` with `num_val_ok w`, every
  RHS `e` in `upds (at_start a)` / `upds (at_end a)` is `nexp_ok w e` (declared+integer reads,
  exact `NDiv`).
- `snap_guards_comp_ok`: same closure for the comparisons in `n_pre (at_start a)` /
  `n_pre (at_end a)` / `n_inv a` (each `comp_ok w c`).
- `fluent_range_closed`: applying a snap's updates to a `num_val_ok` valuation keeps every fluent
  within `[fluent_lo, fluent_hi]` (and `num_val_ok`) — the int-variable bound (R2).

These are *static, grounder-checkable* closure properties (capturing exactly the documented
exact-division / discrete-fragment restriction). Discharging them for a concrete grounded problem is
**out of scope** (abstract-locale decision); here they are hypotheses, mirroring 603–609.

## New helper lemmas (all in `TP_NTA_Reduction_Correctness.thy`, Run-lifting subsection ~after 2546)

Land as `sorry`-stubs top-down, fill bottom-up.

- **`num_val_ok_run`** — the running partial fold of snap updates over `snd (M i)` stays
  `num_val_ok` and within fluent bounds. *Sketch:* induction over the snap prefix using
  `fluent_range_closed`; base `snd (M i)` is `num_val_ok`.
- **`happening_snap_nexp_ok`** — for a snap `s` in happening `i` and the running valuation `w`,
  every `(f,e) \<in> set (upds s)` has `nexp_ok w e`. *Sketch:* `snap_upds_nexp_ok` at `w` via
  `num_val_ok_run`; reads are the snap's own fluents, on which `w` agrees with `snd (M i)` by
  non-interference, so the assumption transfers.
- **`num_tracks_bounded`** (R2) — `num_tracks vn w` + in-range `w` gives the fluent sub-store of
  `vn` within `num_net_bounds`. Discharges the `bnd` providers of `num_data_*_edge`. *Sketch:*
  per-fluent from `fluent_range_closed` + `fluent_bounds_valid` + `num_tracks_varD`.
- **`fired_edge_dispatch`** (the crux) — given the inverted propositional fired edge
  (`p`, `L!p=l`, `b`, `g`, `f`, `is_upds v f v'`) recover the matching augmented numeric edge and
  the `num_data` conclusion, with next-`w` = `apply_upds (set us) w` on an update edge
  (`num_start_edge`/`num_end_edge`, snap `at_start`/`at_end` of `actions!(p-1)`), `w` otherwise.
  *Sketch:* `cases p`; `p=0` → only `main_auto_loop`/`num_main_auto_goal_edge` (no-write); `p=Suc n`
  → source `L!p` (off/starting/running/ending) pins one of five action edges. No-write →
  `num_data_no_write_edge` (`num_edge_2`'s `num_inv_guard` from `snap_guards_comp_ok` +
  `check_bexp_comps_guard`); update → `num_data_upd_edge` with `us = upds s`, guard from `n_pre`,
  `upds_functional_list`/`upds_no_cross_read_list` from the locale, `nexp_ok` from
  `happening_snap_nexp_ok`, freshness from `fluent_vars_fresh`, bound from `num_tracks_bounded`.
- **`num_step'_lift`** — lift one whole `step_u'` (delay + internal). *Sketch:* `step_u'_elims`
  splits into `Del` (store unchanged) and `Internal a`; `num_step_t_lift` for the Del,
  `num_int_step_lift[OF _ _ fired_edge_dispatch]` for the internal; recompose with `step_u'.intros`.
- **`num_run_lift`** (the heart) — by induction on the propositional tail, produce a numeric `steps`
  list with identical `map fst`/`map (snd o snd)` (locs/clks), `v' \<subseteq>\<^sub>m vn'` on the
  last store, `num_tracks vn_last w_final`, and `bounded num_net_bounds vn_last`. Loop invariant
  ties: prop config k ↔ numeric config k (same loc/clk), store extension, tracking of
  `w_k = happening_num_update (update-snaps fired so far) (snd (M i))`, boundedness. *Sketch:*
  `steps.cases` peels the first `step_u'`; `num_step'_lift` advances one config; prepend with
  `num_single_step_intro`/`num_steps_replace_Cons_hd`; recurse.
- **`run_order_snaps_distinct_enum`** (R4) — the update-edges of `delay_and_apply i` fire, in order,
  a *distinct enumeration* of the happening's snap set `happ_at ...`. *Sketch:* read off the
  `delay_and_apply` order (instant start/end, then start-starts, then end-ends) and match
  `happ_at_index_decomp`; distinctness from action distinctness. Feeds
  `run_order_fold_eq_happening_num_update_set`.

## Proof skeleton for `num_happening_steps_possible`

Replace the `sorry` (~line 2589); keep everything above it.

1. Name the prop run/tail (`pss = delay_and_apply i (proj store)`), get `L_len` from `LvP`.
2. Build the per-pair dispatch obligation via `fired_edge_dispatch`, sourcing guards from `vss`
   (`num_valid_state_sequence`) + `sat_comps_happening_num_update_set`, `nexp_ok` from
   `happening_snap_nexp_ok`, bound from `num_tracks_bounded`.
3. Apply `num_run_lift` (with `le0`: `v |` dom (map_of net_bounds) \<subseteq>\<^sub>m v`; `tr0 = tr`;
   `bnd0 = bnd`) → numeric run `nss`, with `tr_last`, `bnd_last`, same locs/clks, store extension.
4. `w_final = snd (M (Suc i))` via `run_order_snaps_distinct_enum` +
   `run_order_fold_eq_happening_num_update_set`.
5. Conclude `\<exists>ns ...` with `ns = nss`:
   - `num_graph_impl.steps` from step 3;
   - `num_happening_post` via `num_happening_postI`: propositional half transported from `ppost`
     using store equality (`vn_last |` dom (map_of net_bounds)` = prop run's last store, from
     `prop_proj_bounded` + the store extension + `happening_post` boundedness), tracking half from
     `tr_last` + step 4;
   - `num_LvP` via `num_Lv_conds_maintained` (length/`L!0`/`planning_lock` preserved across the
     happening; bound = `bnd_last`).

Delay note: with `num_step'_lift` the leading `get_delay i` rides inside the first lifted pair's
`Del` (its `not_urgent` premise from `num_no_urgent`). Fallback if `num_step_t_lift`'s signature is
awkward: lift only `Internal`s and strip the leading delay once with
`num_steps_delay_replace[OF _ _ num_no_urgent]`, exactly mirroring prop line 118.

## Ordered landing checklist (sorry-driven; verify in jEdit, never batch-build)

1. Step 0 assumptions + `num_val_ok` def in `numeric_tp_nta_reduction`; re-register components, relaunch jEdit.
2. `num_val_ok_run`, `num_tracks_bounded` (R2), `happening_snap_nexp_ok` (R1) — stub then fill.
3. `fired_edge_dispatch`: no-write cases first (only `num_data_no_write_edge`), then the two update cases.
4. `num_step'_lift` (small composition).
5. `num_run_lift` (list induction; with 3–4 as black boxes this is plumbing).
6. `run_order_snaps_distinct_enum` (R4).
7. Replace the `sorry` in `num_happening_steps_possible`; discharge post/LvP.

## Risks / hardest sub-steps

- **R1 (integrality `nexp_ok`)** — resolved by Step 0. Hardest *proof* content is now just
  transferring the static assumption to the running fold (`happening_snap_nexp_ok`).
- **R2 (per-step `num_net_bounds` boundedness)** — `num_tracks_bounded` + `fluent_range_closed`.
- **R3 (fired-edge identification)** — enumerating 5 action edges × 4 source locations cleanly;
  reuse the prop net's existing source-location lemmas rather than re-deriving.
- **R4 (run-order ↔ `happ_at` enumeration)** — distinctness of start/end snaps of distinct indices.

## Critical files

- `TA_Network/TP_NTA_Reduction_Correctness.thy` — the `sorry` (2555–2590); all per-step primitives
  (1664/1740/1770/2220/2300/2517), fold bridge (~2118), FACT-1 (~1935), projection lemmas
  (2380–2470); **all new helpers go here**, in the Run-lifting subsection.
- `TA_Network/TP_NTA_Reduction_Defs.thy` — locale `numeric_tp_nta_reduction` (575–611): **add the
  Step-0 assumptions** in the `assumes` block (after line 609); numeric edges (506–526),
  action edge list (519).
- `TA_Network/TP_NTA_Reduction_Correctness_Steps.thy` — prop `*_possible` per-phase lemmas
  (266/739/1620/2149/2593): reference for the per-step `step_int` shape only (not to be mirrored).
- `TA_Network/TP_NTA_Reduction_Correctness_Edges.thy` — `delay_and_apply` (165) /
  `apply_nth_happening` (132) run-order definitions (for R4).
- `Temporal_Planning_Semantics/Temporal_Plans.thy` — `num_valid_state_sequence` (1454),
  `snap_num_update`/`apply_upds` (~355–390), `eval_nexp` (52): the abstract guards + tracking target.

## Verification

- Edit only via `mcp__isabelle__write_file` on files open in jEdit; ROOT/locale assumption changes
  need `isabelle components -u .` then a jEdit relaunch (build the `Temporal_Planning_Base` heap
  once with `-b`).
- After each checklist item, confirm with the `jedit-status` skill that
  `TP_NTA_Reduction_Correctness.thy` reports `fully_processed: true` **and** `consolidated: true`
  with `0 errors`, and the sorry count strictly decreases. Final state: **0 errors, 0 sorries**.
- Final end-to-end check: `numeric_valid_temp_plan_imp_form_holds` (~line 663) and the numeric
  happening chain (`num_plan_steps_possible`, ~2786) build with no remaining `sorry` anywhere
  (`grep -rn sorry TA_Network/*.thy Temporal_Planning_Semantics/*.thy` → empty). This is the
  "network simulates a temporal plan **with** numeric fluents" theorem going green.

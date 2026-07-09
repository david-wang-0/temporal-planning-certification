# Numeric over-all invariant redesign (backlog task #8)

**Goal.** Replace the current *restrictive, static* numeric over-all contract
(`n_inv_eq` + `n_inv_readonly` + `n_inv_init_sat`, discharged via a "read-only ⇒ constant = initial
value" shortcut) with an **enforcing, lock-based** design that mirrors how the propositional over-all
invariants are handled ("no deletion while active"), and **generalizes** the fragment: *global*
read-only becomes *while-active* read-only, and the "holds at the problem's initial valuation"
restriction (`n_inv_init_sat`) is dropped entirely.

This is a **net-structure change to green, committed abstract code** (`TA_Network/`), comparable in
depth to the original propositional invariant/lock proof. All line anchors are on branch
`numeric-conditions-effects` as of 2026-07-09; re-anchor if files move. Paths are repo-relative.

Design confirmed with David (2026-07-09):
> "any update to a fluent should check that it is not updating a locked fluent. We don't need to check
> at the end."

---

## 1. The new (enforcing) mechanism

- **Over-all VALUE checked once, at start** — the existing `num_inv_guard a` on `num_edge_2`
  (`TP_NTA_Reduction_Numeric_Defs.thy:58,115`). **No end re-check** (nothing added on edge_3/end).
- **Per-fluent invariant lock** `fluent_inv_lock f` — a counter var = number of active durative
  actions whose `n_inv` mentions `f`. **Incremented on edge_2** (start, `starting→running`) for every
  `f ∈ (⋃ c ∈ set (n_inv a). comp_fluents c)`; **decremented on edge_3** (end, `running→ending`).
  Exactly parallel to `prop_to_lock` (which counts active over-all *propositions*).
- **Write-guard on the fluent-writing edges** — on `num_start_edge` and `num_end_edge`, each
  `(f, e) ∈ num_upd (…)` is guarded by `fluent_inv_lock f == 0` (the numeric twin of the propositional
  `is_prop_lock_ab 0` delete-guard). A snap may not write a locked (active-invariant) fluent.
- **Plan-validity condition (PDDL-syntax, non-interference)** — a valid numeric plan does **not**
  modify a fluent of an *active* invariant. This is the numeric twin of the propositional
  "no net-delete of an active over-all proposition", and it is what **discharges** the write-guard in
  the forward-direction proof (mirroring `snap_does_not_delete_inv`). Reuse FPS
  `numeric_effects_non_intrf` / `acts_non_intrf` (`Temporal_State_Sequence_Semantics.thy:1117,1120`).

**Why it's correct (and why the edge order matters).** The invariant holds at start (edge_2 guard,
evaluated against the *settled post-happening* valuation — see §3), and its fluents are frozen while
active (write-guard) ⇒ it holds throughout the active window. `num_edge_2` is applied **last** in the
happening and carries **no** fluent writes, so its guard sees the full effect of the happening — this
is David's edge-ordering argument, verified in §3.

---

## 2. The propositional template to mirror (verified anchors)

- `prop_to_lock p ≡ STR ''lock_'' + prop_to_name p` — `TP_NTA_Reduction_Defs.thy:77`.
- **Increment** on edge_2 (`starting_loc→running_loc`, at start): `upds = map (inc_prop_lock_ab 1)
  (over_all a)` — `TP_NTA_Reduction_Defs.thy:172–179`; effect form `TP_NTA_Reduction_Edges.thy:55–58`.
- **Decrement** on edge_3 (`running_loc→ending_loc`, the duration edge, at end):
  `map (inc_prop_lock_ab (-1)) (over_all a)` — `TP_NTA_Reduction_Defs.thy:195–209`; `…Edges.thy:65–69`.
- **Delete-guard** on `start_edge`/`end_edge` (`…Defs.thy:161,246`):
  `not_locked_check = map (is_prop_lock_ab 0) (filter (λp. p ∉ set (adds snap)) (dels snap))`,
  where `is_prop_lock_ab 0 p ≡ (lock p == 0)` (`…Defs.thy:115–118`). A snap may net-delete `p` only
  when `p`'s lock is 0.
- **Semantic lock count**: `locked_by`/`locked_during` — `Temporal_Plans_Lemmas.thy:2183–2190`;
  `active_actions t = {a | tt<t≤tt+d ∧ (a,tt,d)∈ran π}` — `Temporal_Plans.thy:1440–1441`.
- **Plan clause** ("held while active"): `valid_state_sequence M` has `invs ⊆ M i` at every active
  index — `Temporal_Plans.thy:970–986`; `plan_inv_seq :886–888`.
- **Discharge bridge**: `snap_does_not_delete_inv` (`Temporal_Plans_Lemmas.thy:3021`),
  `in_invs_during_iff_locked_during` (`:2844`); composed at net level in
  `TP_NTA_Reduction_Steps.thy:898–905, 1809–1820` (net-delete ⇒ `∉ plan_invs_during` ⇒ `locked_during
  = 0` ⇒ the `is_prop_lock_ab 0` guard passes).
- **Net tracking invariant** (abbreviation, everywhere): `v (prop_to_lock p) = Some (int
  (planning_sem.locked_during t p))` — `TP_NTA_Reduction_Happenings.thy:290,332,471,664`.
- **Per-phase maintenance lemmas** (lock unchanged ⇒ bundle maintained) —
  `TP_NTA_Reduction_Properties.thy`: `happening_invs_maintained` (:569),
  `end_start_invs_maintained` (:586), `instant_action_invs_maintained` (:604),
  `start_start_invs_maintained` (:619), `end_end_invs_maintained` (:631),
  `start_end_invs_maintained` (:647).
- **Count bookkeeping**: `partially_updated_locked_before` — `TP_NTA_Reduction_Prelims.thy:132–133,
  169, 211, 1588–1612` (`updated_locked_during`).

**Template shape**: a per-key counter incremented last (edge_2, start) / decremented first (edge_3,
end); a `lock == 0` guard on the state-mutating edges discharged from validity + the count bridge;
per-phase "counter unchanged ⇒ bundle maintained" frame lemmas. Mirror all of this, keyed on
**fluents** (`⋃ c∈n_inv a. comp_fluents c`) instead of propositions (`over_all a`).

---

## 3. Numeric net edge structure + order (verified)

`num_action_to_automaton a` edges: `[num_start_edge a, num_edge_2 a, edge_3 a, num_end_edge a,
instant_trans_edge a]` — `TP_NTA_Reduction_Numeric_Defs.thy:120–126`. Each numeric edge is
`augment_edge` of a propositional edge (`:107–115`): conjoin a numeric bexp guard, append `(var,exp)`
updates, locations/clocks/label untouched.

| Edge | src→tgt | numeric guard | `num_upd` (fluent writes) | prop-lock | def |
|---|---|---|---|---|---|
| `num_start_edge a` | off→starting | `num_pre_guard (at_start a)` | **writes** `num_upd (at_start a)` | — (checks `is_prop_lock_ab 0` on dels) | Defs:111–112 |
| `num_edge_2 a` | starting→running | **`num_inv_guard a`** (the `n_inv` check) | `[]` (**no write**) | **increments** for `over_all a` | Defs:115 |
| `edge_3 a` | running→ending | — | — | **decrements** for `over_all a` | Defs:195–209 |
| `num_end_edge a` | ending→off | `num_pre_guard (at_end a)` | **writes** `num_upd (at_end a)` | — (checks `is_prop_lock_ab 0` on dels) | Defs:113–114 |
| `instant_trans_edge a` | starting→ending | — | — | — | Defs:214–234 |

- `num_inv_guard a = bexp_and_all (map (comp_to_bexp …) (n_inv a))` — `…Numeric_Defs.thy:58–59`:
  **the only** place `n_inv` is checked in the net; lives on `num_edge_2`.
- `num_upd s` (fluent writes) — `…Numeric_Defs.thy:64`: only on `num_start_edge`/`num_end_edge`.
- **Application order per happening** (`apply_nth_happening n s`, `TP_NTA_Reduction_Steps.thy:11–25`):
  1. `apply_edge_3_effects` (edge_3, lock **decrement**, ending actions)
  2. `apply_instant_actions` (`[start_edge, instant_trans_edge, end_edge]`)
  3. `apply_start_edge_effects` (start writes + not-locked delete guard)
  4. `apply_end_edge_effects` (end writes + not-locked delete guard)
  5. `apply_edge_2_effects` (edge_2, lock **increment** + over_all guard) — **LAST**
  The numeric run reuses this order verbatim — `TP_NTA_Reduction_Correctness_Numeric.thy:701–705`
  (`?seq`), proved `= delay_and_apply`/`apply_nth_happening` by `da_eq_tl` (`:721–725`).

⇒ **At `num_edge_2`'s pre-valuation, every fluent write of the happening is already folded in** (edge_2
is last and write-free). This is the `wagree` fact the over-all-value discharge needs, and the reason
the write-guard (§1) belongs on the start/end edges (which run before edge_2), NOT on edge_2.

---

## 4. The current proof being replaced

### Assumptions to delete (both locales)
`TP_NTA_Reduction_Numeric_Defs.thy:247–260` — `n_inv_eq`, `n_inv_readonly`, `n_inv_init_sat`; and the
verbatim copies in the leaf `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_Problem_Defs.thy:168–174`.
Note `n_inv_eq` is **already dead** (no proof consumer — only cited in the doc comment at
`…Numeric_Defs.thy:242`).

### Shortcut lemmas to delete
- `num_seq_inv_const` — `TP_NTA_Reduction_Numeric_Projection.thy:523–553` (over-all fluents pinned to
  `M 0`; the "read-only ⇒ constant" lemma).
- `happening_num_update_inv_unchanged` — `…Numeric_Projection.thy:504–521` (the **sole** consumer of
  `n_inv_readonly`, at `:517`).
- `inv_sat_at_fold` — `TP_NTA_Reduction_Correctness_Numeric.thy:15–37` (the **sole** consumer of
  `n_inv_init_sat`, at `:36`).

### The edge_2 over-all discharge chain to rewire
`inv_sat_at_fold` → `sat5` (`Correctness_Numeric.thy:1201–1206`) → `RLP_edge_2_single`'s `sat_inv`
premise (`TP_NTA_Reduction_Numeric_Steps.thy:2133–2141`) → `num_edge_2_step_lift` (`…Numeric_Steps.thy:
1990–2069`, discharged by `check_bexp_comps_guard[OF … sat_inv]` ~`:2069`) → `num_edge_2_phase_lift`
(`…Numeric_Steps.thy:2184–2199`).

### Existing lemmas to build the new discharge on
- `num_valid_state_sequence` already carries the "held while active" clause:
  `∀a ∈ active_actions (t i). sat_comps (snd (M i)) (n_inv a)` — `Temporal_Plans.thy:1450–1462`.
- `active_action_inv_sat` — `…Numeric_Projection.thy:555–566`.
- `num_inv_guard_sat_at` — `…Numeric_Projection.thy:568–585` (transports `sat_comps` along any `w`
  agreeing with `M i'` on the over-all fluents — the `wagree` obligation, discharged from §3).

---

## 5. Implementation plan (ordered)

1. **Lock + edges** (`TP_NTA_Reduction_Numeric_Defs.thy`): define `fluent_inv_lock` naming + the lock
   variable(s) in the numeric var list (`num_fluent_vars`/`num_all_vars` neighborhood, `:47–50`);
   augment `num_edge_2` to increment `fluent_inv_lock f` for each `f ∈ ⋃c∈n_inv a. comp_fluents c`;
   augment `edge_3` (numeric layer) to decrement; add the `fluent_inv_lock f == 0` write-guard to
   `num_start_edge`/`num_end_edge` for each written `f`.
2. **Plan validity** (numeric plan-defs layer / `num_valid` in `Temporal_Plans*`): add the
   non-interference condition (no active-invariant fluent modified), reusing FPS
   `numeric_effects_non_intrf`. Add the numeric analogues of the count bridge
   (`in_invs_during_iff_locked_during` → a fluent-keyed version) and `snap_does_not_delete_inv`.
3. **Net tracking + maintenance**: add the numeric lock-count tracking invariant (mirror the
   `prop_to_lock` abbreviation) and per-phase maintenance lemmas (mirror `happening_*_invs_maintained`).
4. **Rewire discharges**: (a) over-all value at edge_2 via `num_inv_guard_sat_at` +
   `active_action_inv_sat` + the edge-ordering `wagree`; (b) write-guard via the non-interference
   condition (step 2). Delete the shortcut lemmas (§4).
5. **Drop assumptions**: remove `n_inv_eq`/`n_inv_readonly`/`n_inv_init_sat` from
   `…Numeric_Defs.thy:247` and the leaf `Ground_PDDL_Numeric_Problem_Defs.thy:168`.
6. **Re-verify** the whole `TA_Network` numeric chain + the leaf green (jEdit, fully_processed +
   consolidated, 0 errors/sorries).

### Soundness note
The forward theorem `num_valid_plan_imp_form_holds` is what's proved (net reaches goal from a valid
plan); the unsolvability guarantee is its contrapositive (net-unreachable ⇒ no plan). The design keeps
the theorem: invariant held at start + frozen while active ⇒ held throughout, and the write-guard is
discharged from the plan's non-interference. Generalizes the admitted fragment vs. the old global
read-only.

---

## 6. Cleanup flags spotted during the survey (not fixed — project rule is flag-don't-fix)
- `TP_NTA_Reduction_Happenings.thy:414` — stray `find_theorems name: "locked_during*and"` diagnostic
  left in the theory body.
- `TP_NTA_Reduction_Correctness_Numeric.thy:684–690` — stale `TODO (the run-lift core)` comment block
  (the lemma below it is complete).
- `n_inv_eq` — dead assumption (no proof consumer) even before this rework.

## 7. Files touched
- `TA_Network/TP_NTA_Reduction_Numeric_Defs.thy` — lock var, edge augmentation, write-guard, drop 3 assumptions.
- `TA_Network/TP_NTA_Reduction_Numeric_Projection.thy` — delete shortcut lemmas; add count/maintenance.
- `TA_Network/TP_NTA_Reduction_Numeric_Steps.thy` — edge_2 rewire + write-guard threading.
- `TA_Network/TP_NTA_Reduction_Correctness_Numeric.thy` — delete `inv_sat_at_fold`; rewire `sat5`.
- `Temporal_Planning_Semantics/Temporal_Plans*.thy` — the non-interference plan clause + fluent-keyed
  count bridge (mirror `locked_during`/`snap_does_not_delete_inv`).
- `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_Problem_Defs.thy` — drop the 3 assumptions from the leaf.

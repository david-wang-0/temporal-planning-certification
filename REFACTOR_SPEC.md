# TA_Network reduction — reorganization spec (review draft, 2026-07-05)

One source of truth for the structural refactor of `TA_Network/` (propositional + numeric reduction
files). Assembled from a read-only classification sweep.

**STATUS 2026-07-05: EXECUTED and green; COMMITTED `11707ff` (2026-07-06).** All seams landed and re-verified (0 errors)
— see `HANDOVER.md` "FILE REORGANIZATION" and `ARCHITECTURE_dependencies.md` for the final layout.
Deviations from the original plan below: (1) numeric chain was NOT re-layered — `Numeric_Happenings`
and `Numeric_Properties` proved infeasible because numeric Edges/Projection consume the conditions and
step-props, so those stay in `Numeric_Prelims`/`Numeric_Edges`; (2) the 2 `is_upds_set_vars_*` lemmas
stayed in Edges (they use the locale abbreviation `set_var`, so they're not context-free). The rest of
the spec was realized as written.

Legend: **DECIDED** = agreed in discussion. **OPEN** = needs your call (see §9). Line numbers are
current-tree anchors and will drift as blocks move.

---

## 1. Naming convention — DECIDED

`Correctness` survives **only** on the two top capstone files. Every stage file is
`TP_NTA_Reduction_[Numeric_]<Stage>`.

- Propositional stages: `TP_NTA_Reduction_<Stage>`
- Numeric stages: `TP_NTA_Reduction_Numeric_<Stage>`
- Tops: `TP_NTA_Reduction_Correctness` (prop), `TP_NTA_Reduction_Correctness_Numeric` (numeric)

## 2. Target file list

**Propositional** (top→down = import order, top of list imports those below):

```
TP_NTA_Reduction_Correctness              (top; capstone: happening_steps_possible, plan_steps_possible, valid_plan_imp_form_holds)
TP_NTA_Reduction_Steps                    (per-phase feasibility: *_possible)  + plan-stepping defs
TP_NTA_Reduction_Properties               (NEW: general automaton props + invariant-maintenance)   [name OPEN §9a]
TP_NTA_Reduction_Happenings               (all conditions/state-predicates + I/E/D, incl. clock conds)
TP_NTA_Reduction_Edges                    (edge effects + boundedness + run-construction)
TP_NTA_Reduction_Prelims                  (planning-semantics equivalence)
TP_NTA_Reduction_Utils                    (NEW: Munta-typed generic helpers)   [scope OPEN §9c]
TP_NTA_Reduction_Model_Checking           (naming locales, a0, sublocales)
TP_NTA_Reduction_Defs                     (propositional reduction defs)
NTA_Temp_Planning_Sem
```
(Pure-HOL generics lift further up into `TP_Utils`/`ListMisc` in `Temporal_Planning_Common`.)

**Numeric** (sits on top of prop `Correctness`):

```
TP_NTA_Reduction_Correctness_Numeric      (top; = old _Plan capstone + merged num_happening_steps_possible)
TP_NTA_Reduction_Numeric_Steps            (was _PhaseLifts)
TP_NTA_Reduction_Numeric_Properties       (NEW, symmetry: num general-automaton props)   [OPEN §9d]
TP_NTA_Reduction_Numeric_Happenings       (NEW: gathered numeric conditions)
TP_NTA_Reduction_Numeric_Projection       (kept whole; run-lift engine — no prop twin)
TP_NTA_Reduction_Numeric_Edges            (was _StepInfra)
TP_NTA_Reduction_Numeric_Prelims          (was _Tracking: tracking + faithfulness)
TP_NTA_Reduction_Numeric_Model_Checking   (NEW: numeric correctness locale + num_a0)
TP_NTA_Reduction_Numeric_Defs             (NEW: split from TP_NTA_Reduction_Defs L434-690)
```

---

## 3. Edges decomposition — the main cut (DECIDED)

`TP_NTA_Reduction_Correctness_Edges.thy` (1877 L) splits four ways. Dependency-verified: the bounds
block (368+) and conditions block (1463+) do **not** use the general-properties block (214-367), and
the four plan defs are not used in Edges below 213 — so all cuts are clean.

| Lines | Bucket | Destination | Contents |
|---|---|---|---|
| 10–16 | UTILS | `TP_Utils` | `dom_map_of_map`, `map_of_NoneI` (pure `map_of`) |
| 18–143 | STAY | `Edges` | `edge_effect` + per-edge `*_edge_effect` + `*_alt` + `apply_*_edge_effects`/`apply_snap_action`/`apply_instant_actions` |
| **144** | **PLANDEF** | **`Steps`** | `apply_nth_happening` |
| 164, 170 | STAY | `Edges` | `delay`, `get_delay` (used by `steps_delay_replace`@1378 & `time_index_Suc_and_delay`@216 → must stay upstream) |
| **177, 200, 209** | **PLANDEF** | **`Steps`** | `delay_and_apply`, `plan_steps`, `plan_state_sequence` |
| 190 | STAY | `Edges` | `goal_run` (primcorec; not a plan phase) |
| **214–367** | **GENPROP** | **`Properties`** | `time_index_Suc_and_delay`, `conv_trans`, `conv_committed`, `no_committed`, `conv_invs`, `no_invs'`, `no_invs`, `cval_add_0`, `step_t_possible`, `single_step_intro`, `non_t_step_intro` |
| 368–1462 | STAY | `Edges` | "Relating maps and bounds" + "bounds of net_bounds" + "initial transition" + "Rules for constructing a run" (`init_vars_alt`, `a0_alt`, `steps_extend`, `steps_replace_Cons_hd`, `steps_delay_replace`, `nth_auto_trans`, `main_auto_trans`) |
| **1463–1877** | **COND** | **`Happenings`** | subsection "Definitions for conditions": `act_clock_pre_happ`(+simps), Mutex block (`mutex_0_constraint_sat`, `mutex_eps_constraint_sat`), Duration block (`check_bexp_all(+_append/_Cons)`, `l_dur_sat_if`, `u_dur_sat_if`), action-sat lemmas (`ending_actions_sat_*`, `instant_action_sat_*`, `starting_action_sat_*`) |

Note the PLANDEF defs (144/177/200/209) are interleaved with STAY defs (164/170/190) — the pass
extracts the four named defs, leaving `delay`/`get_delay`/`goal_run`.

## 4. The NEW `Properties` file (between Happenings and Steps)

Holds two coherent groups that are neither conditions nor per-phase proofs:
1. **General automaton properties** — Edges GENPROP block (214–367), above.
2. **Invariant-maintenance lemmas** — moved out of `Happenings` (they're properties, not
   condition/rule defs): `Lv_conds_maintained`(1306), `happening_invs_maintained`(1315),
   `end_start_invs_maintained`(1332), `instant_action_invs_maintained`(1350),
   `start_start_invs_maintained`(1403), `end_end_invs_maintained`(1544),
   `start_end_invs_maintained`(1652). These depend on the conditions → so `Properties` imports
   `Happenings` (order `Edges → Happenings → Properties → Steps` holds).

`Happenings`'s `sublocale steps_seq`(1730) stays in Happenings (framework scaffolding).

## 5. Other moves

- **`Steps`**: receives the 4 plan defs (§3). Move OUT: `v_pl_cond_sat`(259, an `Lv_conds` helper) →
  `Happenings`. `apply_instant_actions_alt`(239) is structural (edge-effect vocab) → keep in Steps or
  → `Properties` [minor, OPEN §9e].
- **`Defs` split** — DECIDED, clean: prop part (L1–433, locale `tp_nta_reduction_defs`,
  `tp_nta_reduction_defs'`, `length_net_automata`) **stays**; numeric part (L434–690, locales
  `numeric_tp_nta_reduction_defs` + `numeric_tp_nta_reduction`) → new `TP_NTA_Reduction_Numeric_Defs`.
  The pure helpers `bexp_and_all`/`nexp_to_exp`/`comp_to_bexp` (L33–55) **stay in prop Defs**; the
  numeric file imports them (no duplication).
- **`Model_Checking`**: the `*_unique`/`*_inj` naming lemmas (`variables_unique`, `clocks_unique`,
  `locations_unique`, …) reference reduction naming fns → **stay** (not utils).

## 6. Numeric chain — mapping (DECIDED except §9d)

| Current | → Target | Content move |
|---|---|---|
| _(Defs L434–690)_ | `Numeric_Defs` | new |
| `_Numeric_Tracking` L19–73 + `_Plan` `num_a0`(276) | `Numeric_Model_Checking` | numeric correctness locale + `num_a0` |
| `_Numeric_Tracking` (tracking+faithfulness) | `Numeric_Prelims` | rename+trim |
| `_Numeric_StepInfra` | `Numeric_Edges` | rename |
| `_Numeric_Projection` | `Numeric_Projection` | kept whole |
| `_Numeric_Tracking` L518–650 + `_Plan` `num_goal_state_conds`(698) | `Numeric_Happenings` | gather numeric conditions (`num_Lv_conds`, `num_happening_pre[_pre_delay]`, `num_happening_post`, `num_init_planning_state_props'`, `num_goal_trans_pre`, `num_goal_state_conds`; I/E/D at Tracking 611–645 / Plan 718–742 move with them) |
| `_Numeric_PhaseLifts` | `Numeric_Steps` | rename |
| `_Numeric_Happening` | _dissolved_ | `num_happening_steps_possible` merges into top ↓ |
| `_Numeric_Plan` | `Correctness_Numeric` | top; + merged Happening; − `num_a0`, − `num_goal_state_conds` |

## 7. UTILS candidates (consolidated)

**P = pure HOL → `TP_Utils`/`ListMisc`.** **M = mentions Munta/TA library types → new
`TP_NTA_Reduction_Utils`** (`TP_Utils` has no Munta import).

| Name | file:line | P/M | note |
|---|---|---|---|
| `fold_union`, `fold_union'` | Prelims:8,12 | P | set/fold |
| `set_nthI` | Prelims:99 | P | list index |
| `sum_list_eq` | Prelims:146 | P | sum over distinct lists |
| `foldr_assoc` | Prelims:248 | P | fold accumulator |
| `prop_state_simps/D/cases/iff` | Prelims:307–321 | P? | **verify `prop_state` is generic, not reduction-defined (§9f)** |
| `in_setE` | Steps:250 | P | membership→index |
| `sum_list_pos_if_ex_pos` | Steps:255 | P | sum_list positivity |
| `Suc_lessI` | Steps:737 | P | nat arithmetic |
| `GreatestI_time` | NTA_Temp_Planning_Sem:7 | P | `time`-class Greatest |
| `dom_map_of_map`, `map_of_NoneI` | Edges:10,14 | P | map_of |
| `map_const_eq_conv_length_eq` | Edges:427 | P | list/length |
| `all_zip_replicate` | Edges:600 | P | zip/replicate |
| `map_of_determ` | Edges:625 | P | map_of |
| `distinct_map_upds` | Edges:767 | P | distinct/zip |
| `map_upds_with_replicate`, `map_upds_with_map` | Edges:663,683 | M | `map_upds` |
| `is_upds_set_vars_replicate/_map`, `is_upds_inc_vars` | Edges:420,442,449 | M | `is_upds`/`set_var`/`var` |
| `single_upd_bounded`, `upds_bounded` | Edges:490,523 | M | `bounded`/`is_upds` |
| `check_bexp_all(+_append/_Cons)` | Edges:1616,1629,1645 | M | `check_bexp`/`bexp_and_all` (currently in COND block — could stay in Happenings, or hoist to Utils; §9c) |

## 8. ROOT / import rewiring

- `ROOT` session `TP_NTA_Reduction`: replace the `theories` list with the §2 order (both new files
  `TP_NTA_Reduction_Utils`, `TP_NTA_Reduction_Properties`, `TP_NTA_Reduction_Numeric_*`).
- Every `imports` header in the chain updates to the renamed predecessors.
- Downstream importers to check/patch: `Ground_PDDL_Exec_Imp/*` (they import the two *top* files,
  whose names are unchanged, so blast radius should be small — verify).
- After ROOT edit: `isabelle components -u .` then restart jEdit.

## 9. OPEN decisions

**RESOLVED 2026-07-05:** (a) → `TP_NTA_Reduction_Properties`. (c) → create
`TP_NTA_Reduction_Utils` for the M-class helpers; `check_bexp_*` stay in `Happenings`. (d) → add
mirror `TP_NTA_Reduction_Numeric_Properties`, keep `Numeric_Projection` whole. (b) → pure-HOL →
`TP_Utils`/`ListMisc`. (e) → `apply_instant_actions_alt` stays in `Steps`. (f) → verify `prop_state`
genericity before moving. (g) → leave the Prelims lock/snap/index lemmas in place. Original options
retained below for reference.

a. **Name of the new prop intermediate file** — `TP_NTA_Reduction_Properties` /
   `_Automaton_Properties` / `_Step_Properties`? (It holds general automaton props + invs-maintenance.)
b. **Pure-HOL utils destination** — `TP_Utils` (rebuilds the whole editable layer above it) vs a new
   TA_Network-local file. Recommend `TP_Utils`/`ListMisc` for P-class (that's their proper home).
c. **`TP_NTA_Reduction_Utils` scope** — create it for the M-class (Munta-typed) helpers? And do the
   three `check_bexp_*` lemmas go there or stay in `Happenings` with the duration block?
d. **Numeric symmetry** — add `Numeric_Properties` (mirror) and split `Numeric_Edges`'s general
   step-props out, or keep the numeric side coarser (Projection already has no prop twin)?
e. **`apply_instant_actions_alt`** (Steps:239) — keep in Steps or move to Properties?
f. **`prop_state_*`** — confirm `prop_state` is a generic indicator (→ utils) vs reduction-defined
   (→ stays). Low-confidence; verify before moving.
g. **Low-confidence Prelims flags** — an agent suggested moving `partially_updated_locked_before`,
   `locked_during_and_by`, `is_*_index`, `apply_snaps`, `*_snaps_before`, `updated_*` to *numeric*
   files. These look **propositional** (lock/snap/index helpers). Recommend **leave them** unless a
   deeper check says otherwise — flagged only for the record.

## 10. Cleanup flags (from the sweep)

- Stray backups not in any ROOT: `TA_Network/TP_NTA_Reduction_Correctness.thy~`,
  `TA_Network/TP_NTA_Reduction_Correctness_Numeric_Plan.thy~` → delete (don't `git mv`).
- Missing I/E/D coverage on several `Happenings` predicates (e.g. `happening_pre`, the `*_cond`
  predicates have **no** rules) — candidate follow-up per the project's I/E/D preference; not part of
  this structural pass.

## 11. Execution order (once §9 is settled)

1. Authenticate; `jedit-status` the 3 modified files → confirm green (`fully_processed` +
   `consolidated`).
2. Commit the green numeric state locally (branch `numeric-conditions-effects`, no push).
3. `isabelle-refactor`: one mechanical pass — `git mv` renames, `Defs` split, block moves
   (Edges→{Steps,Properties,Happenings,Utils}; Happenings→Properties; numeric gather+merge),
   header + `ROOT` rewire. Delete the `.thy~` backups.
4. `isabelle components -u .`, restart jEdit, re-verify every file green; fix boundary breakage.
5. Update `HANDOVER.md` + `ARCHITECTURE_dependencies.md` to the new layout; commit.

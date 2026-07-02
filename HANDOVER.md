# HANDOVER — semantics + positivity RE-POINT (active) · numeric run-lift (dormant appendix)

Living inventory + ordered next-steps for the RE-POINT of the development onto Formal-PDDL-Semantics (FPS)
`Temporal_Planning` + the grounder's grounded/positive temporal locales (session `Grounding_Temporal_Common`,
a registered Isabelle component). Design docs: `SEMANTICS_REPOINT_PLAN.md`, `GROUNDING_PLAN.md`,
`ARCHITECTURE_pipeline.md`, `ARCHITECTURE_grounding.md`. The numeric run-lift is DORMANT (appendix below); it
resumes once this re-point lands green.

## HEADLINE STATUS (2026-07-02)
- **`Ground_PDDL_Problem_Defs.thy`: GREEN** — fully_processed + consolidated, 0 errors, 0 sorries. The whole
  positivity re-point is done and verified.
- **`Ground_PDDL_Plan_Defs.thy`: GREEN** — fully_processed + consolidated, 0 errors, **0 sorries**, 9283
  commands (2026-07-02). `temp_plan_valid` and `acts_non_intrf_simplified_of_fps` are done; the whole
  reduction (Problem_Defs + Plan_Defs) is now green. How the endgame closed:
    - **§A mutex** — reworked off the (now-false) snap injectivity onto POSITION-based non-interference:
      distinct ref-plan entries at the same htp occupy distinct positions in the snap list, so
      `list_pairwise acts_non_intrf` (from FPS `htps_acts_list_pairwise`, transferred to the project snaps
      via a position-preserving `list_all2` bridge + `acts_non_intrf_mono`) gives non-interference without
      needing `at_start_spec a \<noteq> at_start_spec b`. `acts_non_intrf_simplified_of_fps` rebuilt the same way
      (the unprovable `a_ne_b` hole and the phantom `acts_of_plan_snap_full_bridge'` are gone). New helpers:
      `acts_of_plan_at_simplified_fps_list_all2`, `all_htps_acts_non_intrf_simplified`,
      `list_pairwise_concat_{distinct_blocks,same_block}`, `at_{start,end}_block_of_ref_plan`,
      `acts_non_intrf_simplified_{distinct_entries,same_entry}`.
    - **§B durations** — `durations_match d (map snd dcs) ps as` derived from PLAN VALIDITY (FPS
      `wf_plan_action` gives only `0 \<le> d`), via new `durations_match_of_valid`: the At_Start/At_End snaps
      fold the `filter_time_spec`-routed duration atoms into their preconditions, and plan validity
      (`valid_temporal_state_seq_head_precond`) makes the valuation model them at value `d`, yielding
      `d = r`/`\<le>`/`\<ge>` per dc. Helper chain: `valid_temporal_state_seq_some_state_precond`,
      `htp_{start,end}_of_durative`, `inst_formula_{And,BigAnd_conjunct}`,
      `duration_matches_of_{inst_atom,snap_precond}`, `res_inst_snap_action_eq`, `at_{start,end}_snap_mem`.
- UNCOMMITTED. The pre-session green commit is intact in git; the mutex/durations rework is on disk, verified
  green in jEdit, not yet committed.
- Base heap: build `Temporal_Planning_Base` once, launch `isabelle jedit -d . -l Temporal_Planning_Base`
  (it now also preloads `Grounding_Temporal_Common.Temporal_PDDL_Normalization`).

## WHAT LANDED (all green)
### Step 1 — grounder wired into the base heap
`Grounding_Temporal_Common` added to `Temporal_Planning_Base`'s `sessions` + preloaded `theories` in `ROOT`
(mirrors how FPS `Temporal_Planning` is baked in, so jEdit resolves grounder imports fast); also added to
`PDDL_TP_Reduction`'s `sessions`. Base rebuilt green.

### Step 2 — positivity re-point (Problem_Defs, GREEN)
Project `is_pos_lit`/`is_pos_conj` RETIRED; the grounder's adopted (right-deep `is_pos_conj`; `is_pos_lit`
accepts `eqAtm`+-). Two design forks (decided):
- **eqAtm gap** -> grounder positivity + an explicit eqAtm-free SIDE ASSUMPTION, realised as the locale
  predicate `act_conds_no_args` (parallel to `act_pres_pos`) + locale assumption `conds_no_args` +
  `act_conds_no_args_spec`, threaded through the `*_snap_pre_pos_conj` and `*_no_params` lemmas. To be
  DISCHARGED once the grounder adds an eqAtm-elimination stage (recorded in the grounder repo's HANDOVER).
- **right-deep vs nested `BigAnd`** -> a nesting-tolerant, project-local
  `pos_conj_form form == (Atom \` atoms form = set (to_literals form))`;
  `ground_act_pres_pos (GroundAction pre eff) = pos_conj_form pre`.
New Problem_Defs lemmas (green): boundary bridge `pos_conj_form_inst_formula` / `pos_conj_form_map_atom`
(from `is_pos_conj` + `form_preds_no_args`), the `inst_formula`/`map_atom` preservation lemmas,
`pos_conj_form_BigAnd`, `inst_formula_BigAnd`, `pos_conj_form_predicates`, `wf_fmla_imp_wf_to_literals`,
locale `integer_duration_problem`. DELETED `wf_fmla_no_args` (false under the grounder's `is_pos_conj`);
`wf_fmla_atom_no_args` / `wf_ground_action_pres_in_props` re-proved from well-formedness alone.

### Step 3 — Plan_Defs Blocker A (duration-fold snap mismatch) RESOLVED
FPS `res_inst_snap_action` FOLDS duration constraints into the snap precondition as numeric atoms; the
project's `at_start_spec`/`at_end_spec` are at `dc=[]`, `dur=0` (durations carried by the network clock bounds
`lower_spec`/`upper_spec`, not the precondition). Fix (the `acts_of_plan_at_simplified` design): a simplified
plan-actions-at-t using the project snaps + snap bridges — FPS and project snaps have EQUAL `adds`/`dels`
and EQUAL `to_literals(precondition)` (the numeric duration atoms + the duration value drop under
`to_literals`). Re-pointed `at_start_snap_at_t` / `at_end_snap_at_t` / `acts_of_temporal_plan_at_no_args` /
`plan_happ_seq_alt` / `apply_effects_subseq` / mutex-membership onto it. Mirrors the green
`over_all_spec_eq_res_inst_temporal_inv`.

## temp_plan_valid endgame — RESOLVED (2026-07-02, green; see HEADLINE STATUS for how §A/§B closed)
The section below is the original problem analysis, kept as historical record — both (A) and (B) are DONE.
### (A) mutex — a semantic regression the re-point surfaced
The mutex proof relied on snap INJECTIVITY (`inj_on_at_start_spec`: distinct schema => distinct snap). Now
FALSE: FPS builds the snap via `tsubst (ActionHead n ps) []` = `subst_term (psubst (parameters h) [])`,
depending ONLY on the parameters, NEVER the schema name (and `acts_no_params` forces `ps=[]`) — so two
distinct schemas sharing a body give the SAME snap. **FIX: rework the mutex onto position-based
`list_pairwise acts_non_intrf (acts_of_plan_at_simplified t tp)`** (distinct plan entries => distinct
positions in `concat (map ..)`; `list_pairwise` gives non-interference even when two snaps are equal, which
validity precludes since `acts_non_intrf s s = False`). This also dissolves the `a_ne_b`/functional-bridge
need. Position/count-preserving transfer from FPS `htps_acts_list_pairwise` + a clean `acts_non_intrf_mono`,
using the green numeric-effect-trivial helpers below + the `to_literals`/`adds`/`dels` bridges. (Rejected
alternative: embed a name-guard atom in each snap — that changes snap semantics.)

Green helpers already added for this (numeric conjuncts of `acts_non_intrf` trivial, from the locale's
`no_functions`): `no_func_sig`, `no_wf_func_args`, `no_wf_numeric_effect`, `wf_effect_numeric_effects_Nil`,
`wf_ground_action_numeric_effects_Nil`, `wf_ground_action_lvalues_Nil`, `wf_ground_action_additive_lvalues_Nil`.

### (B) `durs_valid` — `durations_match` from PLAN VALIDITY (a ~100-line lemma)
FPS `wf_plan_action` gives only `d >= 0`. The FPS snap FOLDS `map (\<lambda>(x,y).(x, duration_constraint_as_formula y)) dcs`
(routed by `filter_time_spec ta`) into its precondition; `duration_constraint_as_formula (DurationConstraint EQ r)
= Atom (numericEqAtm DurationExpr r)` (LEQ/GEQ analogues); `inst_formula f d` sends `DurationExpr -> ConstantExpr d`.
So plan validity (`valuation M models precondition` of the At_Start/At_End snap) already verifies `d = r` / `<= r`
/ `>= r`. Derive `durations_match d (map snd dcs) ps as` from the satisfied snap duration atoms via the validity
hook `pres_sat` / `valid_temporal_state_seq_head_precond`. NOTE `dcs :: (temporal_annotation, term
duration_constraint) list`, so `durations_match d dcs` / `dc_list_lower dcs` / `dc_list_upper dcs` need
`map snd dcs`. Also: `resolve_action_wf` -> `wf_ast_temporal_domain.resolve_temporal_action_wf` (FPS
`Temporal_Instantiations.thy`); verify `temp_plan_valid`'s conclusion constants are the actual
`imp_defs.rat_impl.` names (`valid_plan` / `valid_state_sequence` / `valid_plan_def`).

## GOTCHAS / RULES
- Do NOT commit (per current instruction). Do NOT leave a `sorry`.
- Do NOT disturb the green `acts_of_plan_at_simplified` / snap-bridge machinery, the green helpers, or
  the green `Ground_PDDL_Problem_Defs.thy`.
- When a `.thy` is open in jEdit, mutate through the buffer (`mcp__isabelle__write_file`); declare green only
  when `fully_processed: true` AND `consolidated: true`.
- Stray `find_theorems "inst_of_plan_action"` in Plan_Defs (~line 1527, green territory) — cleanup candidate.

---

# APPENDIX (DORMANT) — numeric run-lift (closing `num_happening_steps_possible`)

> This appendix is the PRIOR handover for the (dormant) numeric run-lift. Its "Git state" and
> "ORDERED NEXT STEPS" below are STALE relative to the active re-point above; ignore until the re-point is
> green. The numeric run-lift resumes only after `temp_plan_valid` closes.

Living inventory + ordered next-steps for the numeric-fluent extension of the
"timed-automata network simulates a temporal plan" proof. The propositional case is fully
green; this work extends it to numeric fluents. The whole effort funnels into one lemma,
`num_happening_steps_possible` (`TA_Network/TP_NTA_Reduction_Correctness_Numeric_Happening.thy`).

> **Current active work is the semantics RE-POINT (P0), not this numeric run-lift.** The development
> is being re-pointed onto Formal-PDDL-Semantics' `Temporal_Planning`; see the **HANDOFF (2026-06-28)**
> at the top of [SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md). `Ground_PDDL_Plan_Defs.thy` is
> at 214 errors (down from ~616), all foundational/design-hard pieces green, remaining is a mechanical
> body grind + one `validity \<Rightarrow> durations_match` derivation. The numeric run-lift below resumes once the
> re-point lands green.

## File layout — numeric split (2026-06-25)

Layer B was carved out of `TP_NTA_Reduction_Correctness.thy` (now propositional-only, ~675 lines)
into six per-concern files in `TA_Network/`, all in locale `numeric_tp_nta_reduction_correctness`,
chained linearly (each imports the previous), all verifying green:
`…_Numeric_Tracking` (locale def + sublocales + tracking/encoding/invariants) →
`…_Numeric_StepInfra` (numeric net-step infra, non-interference, delay) →
`…_Numeric_Projection` (REL projection + run-lift engine + forward framework; holds `num_steps_seq`) →
`…_Numeric_PhaseLifts` (REL/RELC/RLP defs, per-edge step-lifts, per-phase lifts) →
`…_Numeric_Happening` (struct exports + `num_happening_steps_possible`) →
`…_Numeric_Plan` (pre/post bridges + `num_plan_steps_possible`).
Verify/launch commands below that name `TP_NTA_Reduction_Correctness.thy` now apply to the relevant
split file (the numeric run-lift is in `…_Numeric_Happening` / `…_Numeric_PhaseLifts`).

## Headline status (2026-06-25)

**The last `sorry` is CLOSED on disk — 0 sorries across `TA_Network/*.thy` +
`Temporal_Planning_Semantics/*.thy`.** The numeric simulation theorem is *logically* complete:
all five phase-lifts are assembled, the `happening_num_update` fold is threaded to
`snd (M (Suc i))`, and `num_happening_post` + `num_LvP` are concluded.

**NOT yet consolidation-verified.** This is the one open item. Sequence of events:
1. The closure was built in a single ~2.5h agent session (hundreds of `write_file` reprocesses).
2. That left jEdit's PIDE in a wedged state (`unprocessed: 1002, running: 3`, frozen 30+ min) — so
   the file never reached `fully_processed: true` + `consolidated: true`. Per project rule, a
   `0 errors` over an unprocessed tail is a FALSE green, so this is NOT declared done.
3. A full audit of the ~640-line new proof (lines 6222–7244) found **no diverging tactic** — every
   `auto`/`blast`/`simp` is over a fixed/finite goal, none over a recursive predicate
   (`graph_impl.steps`/`RLP`/`RELC`/`num_tracks`). Diagnosis: degraded prover state from the
   marathon session (possibly compounded by earlier failed `repl_connect` attempts leaving stray
   `ML_Repl`/`poly` helpers), NOT a logic bug.
4. jEdit was restarted clean (`jedit-down` then
   `jedit-up Temporal_Planning_Base TA_Network/TP_NTA_Reduction_Correctness.thy`). During the
   cold-start reprocess, **a command was observed to "take too long" in the editor** — likely one
   of the known slow combinator proofs (below), but possibly a genuine slow/divergent spot that only
   the clean prover surfaces. This is where work paused.

## Git state

- Last commit: `2bc7113` — *STEP 4 (partial): assembly framework + 3 of 5 phase-lifts*.
- **Uncommitted:** the `edge_phases` closure (edge_3 + edge_2 RLP phases) — `git status` shows
  `M TA_Network/TP_NTA_Reduction_Correctness.thy`. **Commit only after consolidated-green.**
- Commit map of the numeric run-lift (newest first):
  - `2bc7113` STEP 4 partial — assembly + instant/start/end phase-lifts
  - `01451d7` STEP 3 — per-phase struct-exports + `graph_impl_steps_nth_bounded`
  - `6015814` struct-export foundation (run-bound + target-pinning)
  - `c41934e` edge_2 phase-lift + `n_inv_init_sat` + `inv_sat_at_fold`
  - `9aa9e73` writing-edge kernels + start/end/instant phase-lifts
  - `98cb1e5` contract + foundation + lifting framework + edge_3 phase

## ORDERED NEXT STEPS

1. **Let the cold-start fully process.** `jedit-up` is done (port up); the file has ~14.5k commands
   and reprocesses the whole `TP_NTA_Reduction_*` chain on top of the `Temporal_Planning_Base` heap —
   expect several minutes. Verify with `mcp__isabelle__get_diagnostics`
   (`severity=error, scope=file, wait_until_processed=true`) + `get_sorry_positions`. Use `jedit-status`.
2. **Identify the "takes too long" command.** If processing stalls, the stuck command is at the
   `unprocessed` boundary inside `num_happening_steps_possible` (everything past its `qed` ~line 7244
   waits on it). Candidates are the known slow combinator proofs (5–11s, over `ext_seq`/`fold`, NOT
   recursive predicates — they DO terminate):
   - line ~6284 `by simp`; ~6306 `apply (subst hd_ext_seq, simp)+`; ~6798 `by (auto simp: <edge defs>)`;
     ~6806 `by simp`; phase-head `last` simps ~6882/6913.
   Tighten each with `(simp only: <named lemmas>)` / explicit `rule` chains (user wants FAST proofs —
   no eternal `auto`/`simp`). If a command genuinely diverges on the clean prover (still `running`
   after minutes), that is a real bug to fix at that line — but the audit predicts only slowness.
3. **Confirm green:** `fully_processed: true` AND `consolidated: true`, 0 errors, 0 sorries.
4. **Commit** (locally, no push) — message e.g. *"Numeric run-lift STEP 4: close edge_phases —
   numeric simulation theorem complete (0 sorries)"*. Then the end-to-end theorem
   `numeric_valid_temp_plan_imp_form_holds` is fully green.

## STRUCTURE OF THE CLOSED PROOF (for whoever resumes)

`num_happening_steps_possible` (~6222–7244) mirrors the propositional `happening_steps_possible`
(lines 6–199), but LIFTS the propositional happening run config-by-config instead of reconstructing it:
- **Setup (≤6247):** `cfg=(L,v,c)`, `ppd`/`tr`/`bnd`/`lvpr`, the propositional run `prun` +
  `ppost` from `happening_steps_possible`.
- **SEED + prop-run rebuild:** seed `RELC` from `tr`/`bnd`; rebuild the delay-headed prop run
  `prun_seq` by replaying the five propositional phase constructors from `pres'`.
- **Segment decomposition:** `SEG1..SEG4` / heads `h1..h5` peel each phase's prop sub-run.
- **Five phase-lifts** in `delay_and_apply` order edge_3 → instant → start → end → edge_2:
  - instant/start/end (RELC-style, fold GROWS): `num_{instant,start,end}_phase_lift` discharged by the
    GREEN `{instant,start}_phase_struct` / `end_phase_struct` (source-loc via target-pinning, length +
    `L!0` preserved along `seq_apply`, post-bound via `graph_impl_steps_nth_bounded`).
  - **edge_3 + edge_2 (RLP-style, fold FIXED) — the final `edge_phases` `have` (~6857):** these are
    no-FLUENT-write edges (they increment/decrement the propositional `prop_to_lock` over_all vars but
    not the numeric fluents, so the fold `w` is unchanged). Discharged via `num_edge_3_phase_lift`
    (`rlp3`, ~6606) / `num_edge_2_phase_lift` (`rlp5`, ~6730) with `P`/`Q` PINNED to the actual run
    position (`P j s ≡ s = run!j`), so the per-step source-loc/length/post-bound are all run-lookups
    (`graph_impl_steps_nth_bounded`, `RLP_edge_3_single`/`RLP_edge_2_single`). edge_3 source `running_loc`
    from `pres'` (`happening_pre_end_starts_dests(3)`) + a `loc_pres` propagation; edge_2 source
    `starting_loc` by target-pinning (only edge_2 targets `running_loc`).
- **Splice + delay-absorb:** `num_graph_impl.steps_append` chain (`by (simp only: append_Cons append_assoc)`)
  + `num_steps_delay_replace[OF _ _ num_no_urgent]`.
- **Conclude:** terminal fold `= snd (M (Suc i))` via `run_order_fold_eq_happening_num_update_set`;
  `num_happening_post` via `num_happening_postI` (prop half from `ppost` through the net_bounds
  projection); `num_LvP` via `num_Lv_conds_maintained`.

## KEY REUSABLE LEMMAS ADDED (all GREEN, committed)

- `graph_impl_steps_nth_bounded` — every non-head config of a prop run is `net_bounds`-bounded (from
  the internal step's `''bounded''` post-premise; `Simple_Network_Language.thy` step_int, lines 80–92).
- `graph_impl_steps_nth_step` — extract the step `xs!k → xs!Suc k` from a `graph_impl.steps` run.
- `step_u'_net_impl_post_bounded`; `prop_step_source_off`/`_ending` (+ `prop_step_edge_at_Sucn`) —
  target-based edge pinning.
- `start_phase_struct` / `end_phase_struct` / `instant_phase_struct` — discharge the RELC-style structs.
- (uncommitted, in the closure) `rlp3`/`rlp5`/`loc_pres`/`struct3` inside `edge_phases`.

## CONTRACT / SCOPE NOTES

- The supported numeric fragment is fixed by locale assumptions in `numeric_tp_nta_reduction`
  (`TP_NTA_Reduction_Defs.thy`): integer-encoding faithfulness (`snap_*_nexp_ok`/`comp_ok`,
  `num_init_val_ok`), reachability range invariant `num_seq_in_bounds`, and numeric over_all =
  equalities + read-only (`n_inv_eq`/`n_inv_readonly`/`n_inv_init_sat`). No Gigante benchmark has a
  numeric over_all, so this is not a practical restriction. See the auto-memory
  `numeric-run-lift-contract` for the htpl-accessor + M0-anchor gotchas.

## GOTCHAS

- `happening_num_update` is a `fold`; grow it via `subst happening_num_update_Cons` /
  `unfolding ..._def`+`fold_append`+`o_apply`, NEVER `simp add: ..._Cons`.
- No I/R REPL in this jEdit (the `iq` component isn't loaded); develop via `write_file` +
  `get_diagnostics`. Do not `repl_connect` (it spawns helpers that can degrade the prover).
- Restarting jEdit: `jedit-down`, then from the repo root
  `jedit-up Temporal_Planning_Base TA_Network/TP_NTA_Reduction_Correctness.thy`. The MCP bridge
  reconnects automatically on the next `mcp__isabelle__*` call (re-`authenticate`); `/mcp` only if not.

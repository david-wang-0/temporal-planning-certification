# HANDOVER — verified temporal/numeric unsolvability certification, end to end

## ⭐ SESSION STATUS (2026-09-23) — FPS re-base in progress, read this first

**Goal:** make the whole development build again against the current Formal-PDDL-Semantics (FPS)
layout. FPS was split along the HOL-Analysis boundary a second time (FPS branch `add-temporal-state-sequence-semantics`
@ `d7d28c5`, PR #10, stacked on `analysis-free-split` 4349ad8 / PR #9; both open): the sessions this repo used (`Analysis_Free_Base`,
`Temporal_Planning_Discrete`) were replaced by `Discrete_Planning_Common` and
`Discrete_Temporal_Planning`; theories `World_Model_Discrete` -> `Worlds`, `Happening_Semantics_Discrete`
-> `Happening_Semantics`, `Continuous_Effects_Discrete` -> `Invariant_Semantics`; the division-by-zero
layer (`divide_option`, `numeric_effects_defined`, the divisor enumerations) is NOT on that branch
(David is redoing it by hand on `division-by-zero-refactor`; `x / 0 = 0` again for now). This repo
never used those names (audited), so the port is renames + one proof hotspot.

**Plan (phases; status in brackets):**
0. *Isolated build environment* [DONE]: an FPS git worktree at `d7d28c5` (= `add-temporal-state-sequence-semantics`), and
   a private Isabelle user home (`USER_HOME=<private dir>`, own `etc/components` pointing the FPS line
   at the worktree and re-enabling this repo, own heap store seeded by copying the shared one).
   Reason: the shared FPS checkout is on David's division-by-zero WIP and its heap store serves his
   jEdit and a peer PIDE session; building the same session names from other sources there would
   clobber them. Source `temp/tpc-env.sh` before any `isabelle`/`jedit-up` call.
1. *Grounder port* [handed to the Isabelle-PDDL-Grounding session]: DECISION (David, 2026-09-23) --
   this repo consumes the STANDALONE `Isabelle-PDDL-Grounding` again (not the FPS `pddl-grounding`
   branch), and only the cone it needs must build: `Grounding_Base -> Grounding_Utils/Grounding_Common
   -> Grounding_Temporal_Base -> Temporal_Grounding_Utils -> Grounding_Temporal_Common`. The port =
   the five renames (sed sweep over every ROOT/.thy so all ROOTs parse) + one lemma edit
   (`Grounding_Common/Common/PDDL_Sema_Supplement.thy` `formula_atoms_in_dom_valuation_iff` loses its
   divisor conjunct). Validated green in a scratch FPS worktree (about 1 min); the diff against the
   standalone repo's `main` is `temp/grounder-port-to-analysis-free-split.diff` (gitignored). The
   classical grounder sessions still reference removed names and are out of scope. Once the grounder
   session reports its branch/commit, point the private components file at the standalone repo and
   drop the scratch `PDDL_Grounding/` copy from the worktree (same session names + identical sources,
   so no heap rebuild).
2. *Munta heap* [build running]: `Munta_Certificate_Checker` (pure AFP) into the private store.
3. *This repo's renames* [DONE]: `Temporal_Munta_Base = Discrete_Temporal_Planning +`, imports in
   `ListMisc`, `PDDL_Checker_Common`, `Temporal_Continuous_Reduction_Free`, `Ground_PDDL_Problem_Base`,
   `Ground_PDDL_Plan_Defs`, the `@{const Worlds.valuation}` antiquotations.
4. *Heaps + verification* [heaps DONE; lower tower GREEN]: private-store heaps built with `-b`:
   `Temporal_Munta_Base` (35 min), `Temporal_Planning_Base`, and the frozen grounder cone
   `Grounding_Temporal_Common` from the standalone repo. A single headless sweep (stopped early at
   David's request; he wants incremental PIDE checks instead of batch builds) showed
   `Temporal_Planning_Common`, `Temporal_Planning_Semantics`, `TP_NTA_Reduction` and `PDDL_TP_Reduction`
   all GREEN with NO proof repair (the `Ground_PDDL_Plan_Defs` hotspot included); their heaps are in
   the private store. Then (jEdit on the `PDDL_TP_Reduction` heap, Opus xhigh prover, 2026-09-23) `TP_NTA_Reduction_Numeric`,
   `Numeric_Ground_PDDL_Exec_Imp` (bar the export-side-effect `Numeric_Unsolvability_Code_Compile`) and
   `Index.thy` all GREEN untouched, no command over 10 s except the 31 s `export_code`. `Numeric_Bound_Inference`
   sits on HOL-IMP and imports nothing from FPS, so it is unaffected. **WHOLE TOWER GREEN: the re-base cost
   only the renames.** The headless PIDE MCP server is now armed for
   this repo (`claude mcp add -s local isabelle_pide -e USER_HOME=<private dir> -- isabelle pide_mcp
   -l PDDL_TP_Reduction -d <repo>`), so the numeric files are checked file by file through
   `mcp__isabelle_pide__*` (takes effect in a NEW Claude session). Old text of this item follows.
4'. *Heaps + verification* [original plan]: build `Temporal_Munta_Base` (~35 min Munta re-elaboration) and
   `Temporal_Planning_Base`; launch jEdit on it; drive the tower green with prover agents. Expected
   hotspot: `Ground_PDDL_Plan_Defs.thy` (inducts on `valid_temporal_state_seq`, whose
   `numeric_effects_defined` conjunct is gone -- obligations only get weaker) and any auto/blast
   slowed by FPS's `valuation_eq_SomeI` now being a default `[intro]` rule. Then the numeric sessions,
   then `PDDL_TP_Reduction_Index`.
4b. *Export + run* [DONE 2026-09-23]: `isabelle build -e Numeric_Ground_PDDL_Exec_Imp` on the re-based
   theories regenerates `ML/Check_Unsolvability.ML` BYTE-IDENTICAL to the pre-rebase export (the FPS
   change is invisible to the generated code), so the existing `ML/out/plan_cert` is the re-based
   binary. Verified verdicts, `-certify numeric-tchecker`, smallest instance each: MatchCellar 0.25 s,
   sync 0.20 s, majsp-2 0.21 s, painter 43 s -- all "Certificate was accepted / unsolvable".
5. *Docs/commit* [PENDING]: update `ARCHITECTURE_dependencies.md` session names, this section,
   commit; push the FPS branch `pddl-grounding-split` for David's review (it is the grounder's new home
   on the split layout).

## ⭐ SESSION STATUS (2026-07-24) — read this first

**Relational fluent-vs-fluent guards are DONE (variants A + B) and ALL benchmark runs emit nets on
their TRUE-guard problems.** `ML/out/plan_cert -certify numeric`: painter (both `QUANT_EXPAND`
strategies; `counter [0,2]`, `item_id` point boxes transferred across the `=` guards), majsp-1
(`battery [0,2]`, true `>=`-distance guards), **majsp-2 emits its FIRST net ever** (`battery [1,1]`;
it is impossible BECAUSE battery < distance — the AI derives an EMPTY guard-refined interval and the
new emptiness escape accepts the unfireable snap), sync + MatchCellar byte-identical. tck-reach on
majsp-2's net: parses the new difference guards, 17 states, `REACHABLE false`. All green + committed.

**Landed & committed (overnight, git `1e6f0d1 … fca03cc` + `9534ef8`):**
- **Step 0** (`1e6f0d1`): grounder `norm_cmp` — const-left comparisons normalized fluent-left.
- **Step 1a** (`454ed30`): L4 `refine_comp` var-vs-var POINT-BOX arms (both orientations) +
  `refine_comp_pres` case; **`is_gbound_inv'` emptiness escape** (+ bridge case via
  `refine_box_sound`) fixing majsp-2's spurious rejection; exec twins mirrored.
- **Step 1b** (`e70f1d3`): LOSSLESS guard projection — `g_int = GCmp_i cmp_op e_int e_int`, total
  `comp_to_gint`; compute side `gcomp = GCmp cmpop nexp nexp` (5 comparators native, no strictness
  collapse) refined via HOL-IMP's proven `inv_less_ivl` (`refine_pair` + bare-`NVar` write-back);
  **v0-based threshold extraction** (caps = `eval v0` of the other side, offsets `±eval v0 e`,
  landings = cap+offset — mandatory for convergence); glue `pOp`/`pGint`; relational selftest
  (painter-mini → `counter [0,2]`); `glue_demo` retired.
- **Step 1c** (`e813347`): **guards-only unfold** — statics still fold in DURATIONS (net needs
  constant int clock bounds; now folded BEFORE integer scaling) and EFFECT RHSs (**forced deviation**
  from the planned durations-only scope: the mlunta update grammar `x:=c|x:=x±c|x:=v±c` cannot
  express `battery := battery - distance`), but guard comparisons stay true fluent-vs-fluent;
  dead statics dropped (sync unchanged). Net plumbing: var-vs-var guards compile to variable
  DIFFERENCE constraints (`l - r ⊳ 0`, `network_conversion.sml`); `convert_models/convert.py`
  clamps declaration inits into `[min,max]` (point-bounded statics like `item_id[1:1]`).
- **Step 2** (`fca03cc`): **general aeval-based refinement** (variant B) — `refine_left`/
  `refine_right`/`refine_comp = right ∘ left` tighten a bare-`NVar` side by the WHOLE other side's
  `aeval` interval (subsumes const arms, point-box rule, and `item_id + 1`-style operands; realizes
  NUMERIC_BOUND_INFERENCE.md §1e exactly); `refine_left_pres`/`refine_right_pres` proved; exec twins
  mirrored. All six benchmark runs byte-identical to 1c.
- **nemo reachability pruning, task #22b** (`9534ef8`): `ML/plan_cert/src/nemo_reach.sml` —
  TFD-relaxed lifted datalog → `nmo` → per-schema instantiation filter; painter 37→17 automata
  (+ a TIGHTER box: `counter_last_t [0,0]`), majsp-1 48→20, majsp-2 16→9; fail-open without `nmo`.

**LATER THE SAME DAY (`0e48091`/`d8b8de6` + mlunta nested-repo `b81a64f`): the VERIFIED NUMERIC
CAPSTONE.** `check_and_cert_numeric_pddl_problem(_no_return)` (Numeric_Unsolvability_Export) mirrors
the propositional capstone: verified gate + admission + net build, the net handed IN-PROCESS to an
untrusted SML `certifier` callback (external tck-reach oracle), certificate checked by Munta's
verified `convert_check`; Hoare triple `Result Sat ⟹ no valid numeric ground plan` with NO residual
hypotheses — the exec gate now PROVABLY equals `nred'.is_gbound_inv'` (`is_gbound_inv_exec_eq` etc.,
closing the old unproven-twin gap). SML: `-certify numeric-tchecker` drives it with per-stage
profiling (`+ STAGE <name>: <ms> ms`); the historical MLunta↔Munta renaming skew (why `064aa58`
abandoned the capstone) is fixed: hyphen-free identifiers at the grounder mangle choke points,
`_urge` special-cased, per-process location renamings totalized. **Verified end-to-end verdicts:
majsp-2 0.18s, MatchCellar 0.35s, sync 0.28s** ("The numeric planning problem is unsolvable.").
Benchmark harness: the NEW sibling repo `unsolvability-benchmarks` (setup.sh provisions the five
gitignored families; `bench.py` collects per-stage CSVs; private GitHub repo).

Note: the plain `parse_convert_check`/muntac JSON path CANNOT serve numeric nets — the muntax
format has no initial-variable section, and point-bounded statics violate its implicit all-zeros
start. The capstone's in-process net hand-off is what makes numeric certification possible at all.

## OPEN WORK (the live list)

1. **painter oracle certification** — even after nemo pruning (37→17 automata) a 20-min covreach
   run doesn't finish (~2.6GB zones; the LCM-250-scaled duration constants 1000–3751 dominate zone
   granularity, and `15.004` makes the ×250 scaling semantically unavoidable). aLU-covreach copes
   with large constants but its certificates are NOT admissible to the verified checker (only
   covreach's are). Levers: a checker extension for LU-subsumption certificates, or accept painter
   as oracle-hard.
2. **majsp-1 is certificate-SCALE-bound**: covreach terminates (~4 min, 921,881 states) but the
   3.5GB graph certificate costs ~13 min to convert (python) and the in-process verified check did
   not finish within a 30-min total cap (~32GB RSS); a ~60-min budget would likely land it.
   Certificate-side engineering (compression/streaming conversion) is the lever.
3. **#9 — replace the over-approximating numeric mutex with the CORRECT FPS `acts_non_intrf`
   condition** (MEDIUM–HARD, ~1–2 days, deep in the commutation core). Lifts the deliberate
   "design B" soundness shortcut (`d809a59`) to accept additive co-writers (painter-style
   `counter`). By hardness: (2-HARD) re-prove the commutation stack `snap_num_update_commute` /
   `happening_num_update_swap` / `comp_fun_commute_on_snap_num_update`
   (`Temporal_Plans.thy:437–519`) — the disjoint-support argument dies for additive co-writes;
   needs `+` assoc/comm on `'r` and reconciling the abstract COMBINED update form with FPS's
   UNCOMBINED one (they agree under `lvalues ∩ rvalues = {}`, threaded as a hypothesis);
   (1-LOW/MED) refined def `snap_additive_writes` + strip the additive self-read from `snap_reads`
   (`Temporal_Plans.thy:342–365`); (3-MED) re-thread ~43 uses (the ε-guard generator emits fewer
   guards → interleaved zero-delay additive edges must reproduce the simultaneous accumulate);
   (4-MED payoff) executable bridge — the grounder side already uses FPS `acts_non_intrf`
   (`Ground_PDDL_Plan_Defs.thy:660`); prove the numeric bridge and lift the fail-closed
   `wf_ground_action_*_Nil` restriction; (5-LOW) migrate the `_empty` lemmas.
4. **Deferred WP-D code-gen tail** (only if the numeric NETWORK builder ever needs to code-gen
   standalone, outside the unified `Converter`): the `Code_Cardinality.finite'` clash from the
   snaps-disjointness `set … ∩ set … = {}` + the `proper_interval`/`Abs_literal` `String.literal`
   block that `Check_Unsolvability` keeps commented out.
5. **Benchmarks**: full sweeps via the sibling `unsolvability-benchmarks` repo (`bench.py`); only
   smoke rows exist so far.

## CLEANUP flagged (do not silently skip — per project preference)

- **Dedup the RAW-level refine stack.** WP-C re-proved ~40 `ndefs_*` refine lemmas because the
  prop `*_refine` are gated behind `no_functions`; a shared RAW-level refine stack in
  `ground_ast_problem_core` would dedup. Memory `numeric-exec-impl-layer-status`.
- **Stray `find_theorems "inst_of_plan_action"`** in `Ground_PDDL_Plan_Defs.thy` (~:1527).
- **Stray `.thy~` editor backups** (in no ROOT): `TA_Network/` (incl.
  `TP_NTA_Reduction_Numeric_Defs.thy~`), `Ground_PDDL_Exec_Imp/`, `Numeric_Bound_Inference/`.
- **Stale `SORRY (WP-E)` doc labels** in `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy` above
  `refine_box_sound` (~:1026) and `is_gbound_inv'_imp_num_bound_inv` (~:1051) — those proofs are
  complete; the `text` labels lie. (The section-status header at ~:505 was already fixed.)
- **Hoist the `_bnd` S-property lemmas** (`happening_finite_bnd`/… in
  `TP_NTA_Reduction_Numeric_Bounds.thy`) to a shared ancestor so `_bounds`/`_correctness` share
  one copy.
- **Stale Isabelle component registrations** (`~/.isabelle/Isabelle2025-2/etc/components`): the
  retired verified-classical-sat-based-pddl-planner (+ its Isabelle-Graph-Library submodule),
  `isabelle-assistant`, `hugo-0.152.0` — every `isabelle` run warns "Missing Isabelle component".
  Non-blocking; prune the dead lines.
- **`code/` untracked but build-linked** (`Numeric_Bound_Inference.ML` is linked by
  `numeric_code.mlb`; plus `Makefile`, `widen_nbi_sig.py`) — decide
  whether to commit at least the source-like pieces (`widen_nbi_sig.py`, `Makefile`).
- **`check_numeric_ground_problem_diag`** is still labelled temporary; retire or bless.

## Doc map

`ARCHITECTURE_pipeline.md` / `ARCHITECTURE_grounding.md` / `ARCHITECTURE_dependencies.md` —
design of the verified reduction; `ARCHITECTURE_sml.md` — the untrusted `plan_cert` SML harness
(modules, trust boundary, end-to-end data flow); `FORMALISATION_MAP.md` — theory inventory; `NUMERIC_PLAN.md` — the numeric contract the
theories cite (A.x/B section numbers appear in `.thy` comments; keep); `GROUNDING_PLAN.md` —
grounder plan incl. the recorded eqAtm/future-grounder decisions; `NUMERIC_BOUND_INFERENCE.md` —
the bound-inference stack map (§1e = the implemented relational refinement);
`gigante_benchmarks_conditions_effects.md` — benchmark fragment survey;
`FEASIBILITY_alu_subsumption.md` / `FEASIBILITY_rational_durations.md` /
`FEASIBILITY_grounding.md` — 2026-07-25 feasibility studies (aLU certificate admission ~weeks via
the Extra_LU-widen route, kernel already ⪯-parametric; rational durations = leaf retype, useless
for speed, the valuable bit is a scaling-isomorphism lemma; net-shape levers ranked, single-clock-
per-action first). The dated session logs formerly appended to this file live in git history
(pruned 2026-07-24; earlier doc-pruning round: `ec10369`).

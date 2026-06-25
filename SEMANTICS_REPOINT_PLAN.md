# Plan: Retire the `temporal-pddl-semantics` submodule; re-point onto Formal-PDDL-Semantics `Temporal_Planning`

Status: draft (2026-06-25). This is **P0** (`GROUNDING_PLAN.md` §3). Companions:
[GROUNDING_PLAN.md](GROUNDING_PLAN.md) (links here from §3), [NUMERIC_PLAN.md](NUMERIC_PLAN.md)
(§5 expanded). The ROOT files remain authoritative.

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

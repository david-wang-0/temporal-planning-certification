# Plan: Datalog Delete-Relaxation Grounding for Temporal PDDL

Status: draft (2026-06-18); **partially realized 2026-07-24** — the UNVERIFIED harness grounder
(`ML/plan_cert/src/grounder.sml`) now does the TFD-style relaxation AND nemo datalog reachability
pruning (`9534ef8`, task #22b; per-schema applicability predicates, fail-open); the VERIFIED
datalog-certificate grounding this plan designs remains the Isabelle-PDDL-Grounding
`Temporal_Grounding` effort. Companion: [NUMERIC_PLAN.md](NUMERIC_PLAN.md) — the two interlock
(see §7). This plan covers bringing the classical grounder's *datalog certificate / delete-
relaxation* grounding procedure into this project so that **lifted** temporal PDDL problems can be
grounded to the nullary ground temporal PDDL that the NTA reduction already consumes.

---

## 1. Goal

Today this project only accepts **ground** temporal PDDL (`ground_ast_problem` in
`Ground_PDDL_Exec_Imp/Ground_PDDL_Problem_Defs.thy`): durative actions already split into
`at_start` / `over_all` / `at_end` snap actions with `pre/adds/dels` and integer duration bounds,
and grounding is assumed to have happened upstream (the Python `run.py` harness does it untrusted).

The goal is a **verified grounder** for lifted temporal PDDL, reusing the Helmert-2009-style
pipeline from `Isabelle-PDDL-Grounding`:

```
lifted temporal PDDL  ──normalize──▶ delete-relax ──▶ datalog program ──▶ untrusted oracle
        │                                                  │  model M + certificate (M, dc)
        │                          verified kernel re-checks┘
        ▼
  ground (prune by certified reachable set) ──▶ nullary ground temporal PDDL
        ▼
  ground_ast_problem ──▶ TP_NTA_Reduction (existing) ──▶ Munta network + unsolvability cert
```

The grounder's correctness must compose with the existing
`Ground_PDDL_NTA_Reduction_Correctness` so the end-to-end statement is: *a certificate of
unsolvability of the produced Munta network implies unsolvability of the original lifted temporal
problem.*

## 2. What we reuse vs. what is new

The grounder (`Isabelle-PDDL-Grounding`) is **fully proven (0 sorry)** for classical PDDL:
normalization stages, delete relaxation (`PDDL_Relaxation`), the generic positive-datalog
certificate kernel (`Datalog/`, `Datalog_Graph/`), the PDDL reachability certificate
(`Reachability_Analysis/PDDL_Reachability_*`), the grounder core (`Grounded_PDDL/`), and the
executable `ground_via_cert`. See its `ARCHITECTURE_pipeline.md` /
`ARCHITECTURE_datalog_certification.md`.

**Reuse verbatim** (no temporal changes needed — they are generic, signature-level, or
classical-projection only):

| Component | Why reusable |
|---|---|
| `Datalog_Certification` + `Datalog_Graph` | PDDL-free generic certificate kernel |
| **Normalized signatures** — `Continuous_Planning/Signatures.thy` (`domain_signature` / `problem_signature` / `wf_problem_signature`) + the grounder's `Common/Normalization_Definitions.thy` (`restrict_domain_signature` / `restrict_problem_signature`, single-typing, `wf_action_params`) | **the signature of a problem is identical for classical and durative tasks** — same types, predicates, functions, consts/objects; durative-ness lives only in the *action* representation. The new semantics shares `Signatures.thy` across the whole stack (`Continuous → Temporal → Classical`), so these locales are instantiated by the temporal problem unchanged |
| `Type_Normalization` (detype → unary preds) | acts purely on the signature + parameter types; reusable **verbatim** (produces the normalized single-typed signature both sides consume) |
| Goal / definedness / DNF precondition normalization | operate on conditions/effects; reused for the classical *projection* of temporal schemas (§4). Only the *action-level* split (start/over-all/end) is durative-specific |
| `PDDL_Relaxation`, `PDDL_Reachability_*`, `certified_pddl` | reachability of the relaxed classical projection over-approximates temporal reachability (§4, soundness lemma) |
| `Datalog_Evaluation.dl_eval` / external Nemo oracle | unchanged transport |

> **Signature-vs-action split is the key reuse lever.** Everything that depends only on the
> *signature* (typing, predicate/function decls, constants/objects, well-formedness of the
> signature, detyping) is shared verbatim because durative actions do not touch it. Only the
> *action body* (the three condition slots, two effect slots, duration constraint) is new — and §4
> reduces even that to a classical action for the datalog. So the genuinely new Isabelle is small
> relative to the grounder's size.

**New work** (this project): the temporal ↔ classical *projection* bridge (§4), the re-expansion of
grounded instances into ground durative actions, the temporal plan-preservation proof, and the
executable + code-export wiring into `Ground_PDDL_Exec_Imp`.

## 3. Prerequisite (shared with the numeric plan): re-point onto the new semantics

The grounder sits on **Formal-PDDL-Semantics `Classical_Planning`**; this project's ground defs sit
on the **old** `Temporal_AI_Planning_Languages_Semantics` (`lib/temporal-pddl-semantics`,
`TEMPORAL_PDDL_Semantics` / `TEMPORAL_PDDL_Checker`). These must be unified on the **new**
`Temporal_Planning` semantics first. Crucially the new layering is

```
Continuous_Planning_Base → Continuous_Planning → Temporal_Planning → Classical_Planning → Planning
```

i.e. **classical is defined on top of temporal**, and `Classical_Planning/Classical_Temporal_Reduction.thy`
already proves `ast_temporal_problem.valid_temp_plan2 (ast_classical_plan_to_plan π) =
valid_classical_plan2 π`. This bridge is the backbone of the grounding reuse: the grounder's
classical task and our temporal task live in the **same** semantic family.

**P0 tasks** (blocking; tracked in both plans) — full step-by-step in
[SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md):
- [ ] Port `Ground_PDDL_Exec_Imp/*` and `TA_Network/*` off `Temporal_AI_Planning_Languages_Semantics`
  onto `Temporal_Planning` (new abstract syntax `Temporal_Abstract_Syntax`, semantics
  `Temporal_Happening_Semantics`, checker `Temporal_PDDL_Checker_Explicit`). This is **more than a
  retype**: it includes a **redesign of the grounded target** — rename `ground_ast_problem` →
  `grounded_temporal_problem` and split it grounder-style into reused signature locales + grounded-ness
  + positivity (see [SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md) §2b) — plus the retype onto
  the new types (`ast_effect` gains `numeric_effects`, `duration_constraint` carries a
  `numeric_expression`, the action schema is head/body). Done **numeric-free first**; the numeric path
  is a later phase (re-point plan §5).
- [ ] Update `ROOT`: re-point the `Temporal_Planning_Base` heap off
  `Temporal_AI_Planning_Languages_Semantics` onto `Temporal_Planning`. Dependency mechanism:
  **sibling component, no submodule** — retire the `lib/temporal-pddl-semantics` submodule and register
  the standalone Formal-PDDL-Semantics via `isabelle components -u` (mirrors the classical grounder).
- [ ] Re-establish `check_ground_problem` (`Ground_PDDL_NTA_Reduction_Impl`) against the new checker
  *as an interim runtime gate*. It is slated for **retirement** once the verified grounder (§4) lands:
  the grounder discharges the `grounded_temporal_problem` assumptions (incl. `positive_act_pres`, via
  the constant-fold/feasibility-prune step) *by construction*, replacing the runtime check.

## 4. Core design — temporal grounding via the classical projection

The grounder needs, per lifted durative action schema, only (i) which parameter bindings produce a
**reachable** ground instance, and (ii) the ground atoms/fluents that are reachable. The temporal
condition/effect *placement* (start vs over-all vs end) is irrelevant to delete-relaxed
reachability. So:

**Projection `π_C` (temporal schema → classical schema)** — for a durative action `a`. This is
**exactly** what Temporal Fast Downward's translator does when it builds its Datalog exploration
rules (`Fast Downward's translate/normalize.py`, `ActionConditionProxy.build_rules` /
`EffectConditionProxy.build_rules` / `condition_to_rule_body`), confirmed by reading the source:
- classical precondition (rule **body / RHS**) =
  `positive(pre_s)` ∪ `static_positive(inv)` ∪ `static_positive(pre_e)`
  ∪ `defined!(pne)` for every PNE in a numeric comparison of `pre_s`
  ∪ **`defined!(pne)` for every PNE occurring in the duration constraint** (see below);
  i.e. **pre_s is used in full** (positive atoms; negatives dropped), but from `inv`/`pre_e` only
  the **non-fluent (static)** positive atoms survive — **every fluent atom and numeric comparison of
  `inv`/`pre_e` is dropped**. Existential-parameter type atoms are kept from all three.
- classical add-effects (rule **heads / LHS**) = `adds_start ∪ adds_end`
  ∪ `defined!(f)` for every numeric **assignment** effect (start and end) — **collapsed** onto the
  single "action-reachable" predicate, which is gated only by the precondition above;
  classical del-effects = `dels_start ∪ dels_end` (for the real-deletes target `P_N`; dropped under
  the relaxation `P_R`);
- parameters/types unchanged. The duration constraint's *value* is dropped from reachability, **but
  the definedness of its PNEs is required in the precondition** (a normalized durative action has
  `(= ?duration expr)`; the action cannot execute unless `expr`'s fluents are defined, so each such
  `defined!(pne)` gates applicability — TFD enforces this in `remove_duration_variable`).

**Definedness as a datalog predicate** (`fluents ↔ PNEs`). A numeric fluent *is* a ground PNE
(`PNE func args`); its definedness is the propositional predicate `defined!func(args)`. It threads
through the *same* datalog program as ordinary atoms: an **EDB fact** for every init
`FunctionAssignment`; a **derived head** for every numeric assignment effect; a **body atom** for
every numeric comparison condition (in `pre_s`/effect-conditions) and every PNE in the duration
constraint. This is exactly the grounder's `Definedness_Normalization` + `Definedness_Translation`
stages — reused verbatim; the numeric *value* semantics is **not** in datalog (see §7 and
[NUMERIC_PLAN.md](NUMERIC_PLAN.md)).

> **Why dropping `inv`/`pre_e` fluents is required for soundness, not just precision.** An over-all
> or end fluent condition may only become achievable *during* the action's own duration — via its own
> `add_s`, or via a concurrent action. Requiring it in the static delete-relaxed exploration (which
> has no notion of the action's own mid-execution effects) would spuriously prune a genuinely
> reachable instance ⇒ **incomplete** grounding. Static atoms never change, so requiring them cannot
> drop a reachable instance; keeping them only tightens precision. So the fluent/static split above is
> the *unique* sound-and-maximally-precise classical projection — and it coincides with TFD.

Run the **existing** classical pipeline on `π_C(P)`:
1. normalize → relax → `dl_program_of` → oracle → `dl_certified_model` re-check →
   `certified_facts_eq_achievable`;
2. `wf_grounder` produces the grounded classical task pruned to the certified reachable set,
   i.e. the set `G` of *applicable ground parameter bindings* per schema and reachable ground atoms.

**Soundness of the over-approximation** (new lemma): the delete-relaxed reachable set of `π_C(P)`
**contains** every ground atom reachable by any valid temporal plan of `P`. Proof sketch: a temporal
happening sequence executing snap actions only adds atoms that are adds of some snap; the start snap
fires under `pre_s` (its static atoms hold throughout, its fluents are exactly `π_C`'s precondition),
and every fluent that `inv`/`pre_e` need is itself produced by some earlier add in the relaxed model —
so each temporal add is dominated by the single classical relaxed step on `π_C` (precondition weaker
because `inv`/`pre_e` fluents were *dropped*, adds stronger because `add_s ∪ add_e` were *collapsed*).
Hence grounding against `G` drops no instance that any temporal plan could use → grounding is
plan-preserving (no spurious incompleteness). This mirrors the classical argument that grounding
targets the *real-deletes* problem `P_N`, not the relaxation — and reproduces TFD's exploration.

**Re-expansion `χ` (grounded classical instance → ground durative action)**: for each binding in
`G`, instantiate the **original** temporal schema (not the projection) to obtain the ground durative
action, then split into `at_start/over_all/at_end` snaps exactly as `at_start_spec` /
`at_end_spec` / `over_all_snap` do today, but over the **lifted** schema instantiated at the binding.
Assemble the resulting `grounded_temporal_problem`.

**Constant evaluation + feasibility prune (`eqAtm` and other constant literals).** `χ` instantiates
conditions over the binding's constants, so any object-equality `eqAtm` becomes a *constant*. **Reuse
the classical grounder's `ground_fmla`** (`Grounded_PDDL/Grounded_PDDL.thy`) to evaluate it —
`Atom (eqAtm a b) ↦ (if a = b then ¬⊥ else ⊥)` (and the negated case). Sound because `eqAtm` is
**model-independent** — FPS values `Atom (eqAtm a b)` as `Some (a = b)` (`Continuous_Planning/Worlds.thy`)
— so replacing it by its truth value is a per-condition logical equivalence. So there is **no bespoke
`eqAtm` problem→problem pass**; equality is gone *by construction* in the grounded problem.

`ground_fmla` leaves `⊥`/`¬⊥` constants, and the classical grounder does **not** simplify them: `¬⊥`
is kept (`un_and` flags removing it as an undone optimization, `Common/Formula_Utils.thy`; its
`is_pos_lit` accepts both `⊥` and `¬⊥`), and a `⊥` condition is dropped only later in the *datalog
reachability* (`Reachability_Analysis/PDDL_Reachability_Locales.thy` — a `⊥` clause is statically
unsatisfiable). The temporal NTA path does **not** inherit that, and this project's **narrow
`is_pos_lit` rejects `⊥`** (only `predAtm`/`¬⊥`). So add a small, general **constant-fold +
feasibility-prune** step in `χ`/assembly: fold `φ ∧ ¬⊥ = φ`, `φ ∧ ⊥ = ⊥`, …, and **drop any action
whose condition reduces to `⊥`** (never enabled). The result is a positive `predAtm` conjunction,
discharging the grounded target's `act_pres_pos` / `positive_act_pres` obligation for the numeric-free
fragment — which is exactly what lets the runtime `check_ground_problem` be retired (the grounder
establishes the assumption *by construction* rather than checking it). It is semantics-preserving
(constant folding = logical equivalence; dropping unsatisfiable-condition actions preserves valid
plans) and general (any constant literal, not just `eqAtm`-derived). `numericEq`/numeric comparisons
are **not** evaluated here — state-dependent, kept for the numeric path (§7).

> **Decision (per the "whichever is faster" call):** use the projection. A "direct per-snap datalog"
> that put `inv`/`pre_e` *fluent* conditions into rule bodies would be **unsound** (it prunes
> instances whose end-conditions are achieved mid-duration — see the soundness box above), which is
> precisely why TFD does *not* do that. The projection above already *is* TFD's exploration, so it is
> both the faster route and the established-precision one; there is no looser-but-correct or
> tighter-but-still-sound delete-relaxed variant to chase. Any further precision would require
> temporal/ordering reasoning beyond delete relaxation — out of scope for grounding.

## 5. Plan-preservation theorem

Target statement (in this project, new session):

```
lifted temporal problem P,  G = ground_via_cert_temporal P (M, dc) accepted
  ⟹  (∃ valid temporal plan of P)  ⟷  (∃ valid temporal plan of the grounded task G)
```

Decomposition:
- (⇐) every ground durative action of `G` is `χ` of a real instance of `P`, so a plan of `G` lifts
  to a plan of `P` (reuse the grounder's `reconstruct_plan_norm` analog, lifted through
  `Classical_Temporal_Reduction`).
- (⇒) every instance used by a valid plan of `P` is reachable (§4 over-approx lemma) hence retained
  in `G`; the plan is therefore a plan of `G`. Mutex/duration handling is unchanged because `χ`
  preserves snap structure and duration bounds verbatim.

This is the temporal analog of the grounder's `plan_by_cert_sound`. Compose with the existing
`Ground_PDDL_NTA_Reduction_Correctness` to reach the unsolvability-certificate conclusion.

## 6. Work breakdown (sessions / theories in this repo)

New session `Ground_Temporal_PDDL` (parent: `PDDL_TP_Reduction` after P0, + the grounder sessions
`Grounded_PDDL`, `Reachability_Analysis`, `Datalog_Certification`):

1. `Temporal_Classical_Projection.thy` — `π_C`, well-formedness preservation, instance-set equality.
2. `Temporal_Reachability_Soundness.thy` — the over-approximation lemma (§4).
3. `Ground_Temporal_PDDL_Defs.thy` — `χ` re-expansion, `ground_via_cert_temporal`, assembly into
   `grounded_temporal_problem` (the target structure fixed by SEMANTICS_REPOINT_PLAN.md §2b),
   including the **constant-fold + feasibility-prune** step (§4): reuse classical `ground_fmla` for
   `eqAtm`, fold `⊥`/`¬⊥`, drop `⊥`-condition actions ⟹ positive `predAtm` conjunctions discharging
   `act_pres_pos`/`positive_act_pres`.
4. `Ground_Temporal_PDDL_Plan.thy` — the plan-preservation theorem (§5).
5. `Ground_Temporal_PDDL_Code.thy` — executable refinement + code export; extend `run.sh`/`run.py`
   to call the verified grounder instead of (or cross-checking) the untrusted Python grounder.
6. `ROOT` updates + an `Index.thy` entry pointing at the capstone theorem.

Order: P0 (§3) → 1 → 2 → 3 → 4 → 5. Each as its own session for warm-heap iteration, mirroring the
grounder's per-stage session split.

## 7. Interlock with the numeric plan

The grounder currently *rejects* numerics (`grounding_checks_exec` includes a numeric-free check).
When [NUMERIC_PLAN.md](NUMERIC_PLAN.md) lands, the seam is:
- **Reachability tracks definedness but ignores comparison *values***. Datalog carries the
  `defined!f` predicate (EDB from init, head from numeric assignments, body from `pre_s`/duration
  PNEs — see §4); it does **not** evaluate the `≤/≥/=` test. Treating the comparison *value* as
  `True` is a sound over-approximation (a numeric guard only ever *prunes* applicability), while
  keeping definedness in the program prunes instances whose fluents can never be defined.
- **Grounding must carry numeric fluents and numeric effects through** `χ` (ground the `PNE`
  instances like predicate atoms; keep `numeric_effect`s and the duration constraint in the ground
  durative action) — they are evaluated by the numeric temporal semantics / the NTA integer
  variables, not by datalog.
- The grounder's `Definedness_Normalization` + `Definedness_Translation` stages (numeric definedness
  → propositional `defined!f` predicates) are reused **as-is** for definedness reachability — extend
  only to pull definedness out of the **duration constraint** too; the **value** semantics is the
  numeric plan's job.
- Net dependency: §3 (P0) is shared and itself stages **numeric-free first** (the re-point reaches
  green with empty `numeric_effects`; re-point plan §5 then adds numerics on the new semantics). The
  numeric plan should land **the semantics + reduction** on the new `Temporal_Planning` first, then
  this plan flips the grounder's numeric-free check into "ground numerics through".

## 8. Risks / open questions

- **Semantics re-point (P0) is the long pole** — redesign of the grounded target + numeric-free
  retype of `Ground_PDDL_Exec_Imp` and `TA_Network` (see
  [SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md)). Do it first, on its own branch, fully green,
  before any grounding work.
- The grounder assumes positive, DNF preconditions; temporal `over_all` conditions and the union in
  `π_C` must respect the same normalization — verify the normalization stages accept the projected
  schema unchanged.
- Whether to **trust** the Python grounder and only *certify* (current pipeline style) or **replace**
  it with the verified `ground_via_cert_temporal`. Recommend: verified grounder produces the task,
  Python retained only as an unverified convenience/cross-check.
- Projection over-approximation precision on real IPC temporal instances (MatchCellar etc.) — measure
  ground-task size; it should match TFD's (the projection *is* TFD's exploration), so this is a
  sanity check, not a design fork.

## 9. Documentation conventions (mirror the classical grounder)

Document this development in the **same idiom** as `Isabelle-PDDL-Grounding` so the two read as
one project. Concretely, produce/maintain:

- **`ARCHITECTURE_pipeline.md`-style** one-pager: the ASCII pipeline diagram (§1), a **stage table**
  (stage → session/theory → status), and a **trust story** (which oracles are untrusted and which
  verified kernel re-checks each — here: the datalog reachability oracle, re-checked by the generic
  certificate kernel; the Munta model-checker certificate, re-checked by `muntac`).
- **`ARCHITECTURE_datalog_certification.md`-style** design note for any non-obvious layer (here: the
  temporal→classical projection §4 and its soundness §4/§5), with the check/direction tables the
  grounder uses.
- **`HANDOVER.md`-style** living inventory: per-session contents, the exact `sorry` inventory, known
  gotchas, and an ordered next-steps list. Keep `README.md` as the layout tree + per-component
  `0 sorry` status, and the **ROOT files authoritative**.
- **Per-stage three-file pattern** with `text \<open>…\<close>` theory headers, exactly as the grounder's
  normalization stages: `X_Locales.thy` (abstract locale + signature constants + assumptions),
  `X.thy` (executable implementation), `X_Semantics.thy` (plan-equivalence / well-formedness proofs),
  composing via `sublocale` + rewrites. The temporal grounder's new theories (§6) follow this shape.
- **Reuse callouts in headers**: where a theory reuses a shared signature/normalization locale
  (`domain_signature`, `restrict_problem_signature`, `Type_Normalization`, …), say so in the header
  so the signature-vs-action reuse split (§2) is visible in the source, not just here.

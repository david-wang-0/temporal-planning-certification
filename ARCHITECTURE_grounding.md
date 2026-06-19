# Architecture: datalog delete-relaxation grounding for temporal PDDL

How the **planned** grounding front-end turns a *lifted* temporal PDDL problem into the ground
`ground_ast_problem` the NTA reduction consumes, by reusing the classical grounder
(`~/work/Isabelle-PDDL-Grounding`) through a **temporal → classical projection**. This is the
`ARCHITECTURE_datalog_certification.md` analog for this repo. See
[ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md) for where it sits, and
[GROUNDING_PLAN.md](GROUNDING_PLAN.md) for the work breakdown. Last updated 2026-06-18.

## The idea

Delete-relaxed reachability is insensitive to *when* a condition/effect of a durative action fires.
So for grounding we **project** each durative action to a single classical action, run the classical
grounder's certified datalog reachability on the projection, then **re-expand** the reachable ground
instances back into ground durative actions. The projection is not an approximation we invented — it
is **exactly** Temporal Fast Downward's translator behaviour, confirmed against
`~/work/tfd/downward/translate/normalize.py`.

## The projection `π_C` (durative action → classical action)

For a normalized durative action with conditions `[pre_s, inv, pre_e]`, start/end effects, and a
duration constraint `(= ?duration expr)`:

| Classical part | Built from | Rule role |
| --- | --- | --- |
| precondition | `positive(pre_s)` ∪ `static_positive(inv)` ∪ `static_positive(pre_e)` ∪ `defined!(pne)` for each PNE in a `pre_s` comparison ∪ `defined!(pne)` for each PNE in the duration constraint | **body / RHS** |
| add-effects | `adds_start ∪ adds_end` ∪ `defined!(f)` for each numeric assignment effect (start+end) — **collapsed** onto one action-reachable predicate | **head / LHS** |
| del-effects | `dels_start ∪ dels_end` (real-deletes target `P_N`; dropped in the relaxation `P_R`) | — |

The decisive rules (TFD `normalize.py`):

- `ActionConditionProxy.build_rules` — **`pre_s` is used in full** (`condition_to_rule_body` with
  `fluent_preds=None`: all positive atoms, plus `defined!f` for numeric comparisons); **`inv` and
  `pre_e` contribute only their non-fluent (static) positive atoms** (`fluent_preds` set drops every
  fluent atom and numeric comparison). Existential-parameter types kept from all three.
- `EffectConditionProxy.build_rules` — delete relaxation (negated effects skipped); each positive
  effect atom is a head with body `[action-reachable-pred] + effect-conditions`, so **`add_s` and
  `add_e` collapse** onto the single action predicate gated by the precondition above. A numeric
  assignment effect's head is `defined!f`.
- `remove_duration_variable` — `(= ?duration expr)`; `?duration` is substituted by `expr` and each
  PNE of `expr` is forced into the action, so the **duration's fluents must be defined** for the
  action to apply.

## Why this is the *unique* sound-and-precise projection

Dropping `inv`/`pre_e` **fluent** conditions is **required for soundness**, not an optimization: an
over-all/end fluent may only become achievable *during* the action's own duration (via `add_s` or a
concurrent action). Requiring it in the static delete-relaxed exploration — which has no notion of
the action's mid-execution effects — would spuriously prune a genuinely reachable instance and yield
an **incomplete** grounding. Static atoms never change, so requiring them cannot drop a reachable
instance; keeping them only tightens precision. Hence the fluent/static split is forced, and it
coincides with TFD. There is no looser-but-correct or tighter-but-still-sound delete-relaxed variant
to chase; more precision would need temporal/ordering reasoning beyond delete relaxation.

## Definedness as a datalog predicate (`fluents ↔ PNEs`)

A numeric fluent *is* a ground `PNE func args`; its definedness is the propositional predicate
`defined!func(args)`. It threads through the *same* datalog program as ordinary atoms:

| Where | Source | Role |
| --- | --- | --- |
| init `FunctionAssignment` | `translate_init` | **EDB fact** |
| numeric assignment effect | `EffectConditionProxy.build_rules` | derived **head** |
| numeric comparison in `pre_s` / effect-conditions | `condition_to_rule_body` (`fluent_preds=None`) | **body** atom |
| every PNE in the duration constraint | `remove_duration_variable` | **body** atom |

This is precisely the grounder's `Definedness_Normalization` + `Definedness_Translation` stages,
reused — extended only to pull definedness out of the duration constraint. Datalog tracks **fluent
definedness but never evaluates the comparison value** (treating the `≤/≥/=` test as `True` is a
sound over-approximation — a numeric guard only prunes).

## Re-expansion `χ` and the soundness obligations

For each reachable binding, instantiate the **original** temporal schema (not the projection) and
split into `at_start` / `over_all` / `at_end` snaps exactly as `at_start_spec` / `at_end_spec` /
`over_all_snap`, then assemble `ground_ast_problem`. The proof obligations:

- **Over-approximation lemma**: the delete-relaxed reachable set of `π_C(P)` contains every ground
  atom any valid temporal plan of `P` can produce ⟹ grounding drops no needed instance.
- **Plan preservation**: `(∃ valid temporal plan of P) ⟷ (∃ valid temporal plan of the grounded
  task)` — the temporal analog of the grounder's `plan_by_cert_sound`, lifted through
  `Classical_Planning/Classical_Temporal_Reduction.thy`.

## What is reused vs new

Reused verbatim: the generic datalog certificate kernel (`Datalog_Certification`, `Datalog_Graph`),
the **shared signature locales** (`Continuous_Planning/Signatures.thy`:
`domain_signature`/`problem_signature`; the grounder's `restrict_*_signature`), `Type_Normalization`,
relaxation and the PDDL reachability certificate, the datalog evaluator/oracle. New: the projection
`π_C`, the over-approximation lemma, the re-expansion `χ`, the temporal plan-preservation proof, and
the executable + code-export wiring. The signature-vs-action reuse split keeps the genuinely-new
Isabelle small. See [GROUNDING_PLAN.md §2](GROUNDING_PLAN.md).

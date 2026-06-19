# Architecture: the verified temporal-planning certification pipeline at a glance

One-page summary of the end-to-end pipeline. Companion design notes:
[ARCHITECTURE_grounding.md](ARCHITECTURE_grounding.md) (the planned datalog grounding front-end) and
the two plans [GROUNDING_PLAN.md](GROUNDING_PLAN.md) / [NUMERIC_PLAN.md](NUMERIC_PLAN.md). Build/run
instructions live in [Readme.md](Readme.md); the ROOT files are authoritative. Last updated
2026-06-18.

Legend: **[done]** proven/in-tree today · **[planned]** designed in the plans, not yet built.

```text
 lifted temporal PDDL problem                                              [planned front-end]
   │  normalize (signature reuse: detype → degoal → definedness → DNF)
   │  project each durative action to a classical action (TFD-style, §ARCH_grounding)
   ▼
 P_C  ──relax (drop deletes)──► P_R ──dl_program_of──► datalog oracle (untrusted)
   │                              ▲                        │ model M + certificate (M, dc)
   │     verified kernel re-checks ┘ dl_certified_model
   ▼
 ground (prune by certified reachable set) ──re-expand to ground durative actions──►
   ▼
 GROUND temporal PDDL  (ground_ast_problem: at_start / over_all / at_end snaps,        [done ▼]
   │   pre / adds / dels, lower/upper duration bounds)
   ▼
 NTA reduction  (TP_NTA_Reduction: one timed automaton per action + a main automaton;
   │   propositions → bounded int vars, snap timing → clocks)
   ▼
 Munta network (Simple_Network_Language)  ──reachability query EX ⟨goal_loc⟩
   │                                          │ TChecker covering graph (untrusted)
   │              muntac re-checks certificate ┘
   ▼
 Result Sat  ⟹  ∄ tp. valid_ground_plan problem tp   (the original problem is UNSOLVABLE)
```

## Stages and where they live

| Stage | Session / theory | Status |
| --- | --- | --- |
| Abstract temporal plan semantics (snap actions, happenings, invariants) | `Temporal_Planning_Semantics/Temporal_Plans.thy` (`temp_planning_problem`, `temp_plan_defs`) | **[done]** (1 `sorry`, see HANDOVER) |
| NTA reduction spec / model-checking / correctness | `TA_Network/TP_NTA_Reduction_{Spec,Model_Checking,Correctness}.thy` (`tp_nta_reduction_correctness`) | **[done]** Thm 1 `valid_plan_imp_form_holds` |
| Ground PDDL problem defs + reduction impl | `Ground_PDDL_Exec_Imp/Ground_PDDL_{Problem,Plan}_*.thy` (`ground_ast_problem`) | **[done]** numeric-free, positive-precondition |
| Executable certificate check (capstone) | `Ground_PDDL_Exec_Imp/Check_Unsolvability.thy` (`check_and_cert_pddl_problem_okay`, `make_certified_net_okay`) | **[done]** |
| Code export → SML certifier | `Ground_PDDL_Exec_Imp/Unsolvability_Code_*.thy`, `ML/` | **[done]** plans MatchCellar-impossible instances |
| PDDL semantics | Formal-PDDL-Semantics `Temporal_Planning` (new) ⟵ migrating off old `Temporal_AI_Planning_Languages_Semantics` | **[planned P0]** re-point |
| Datalog grounding front-end (lifted → ground) | `Ground_Temporal_PDDL/*` (new) reusing `~/work/Isabelle-PDDL-Grounding` | **[planned]** see GROUNDING_PLAN |
| Numeric conditions / effects (semantics + reduction) | Layers A/B/C across the above | **[planned]** see NUMERIC_PLAN |

## Trust story

The conclusion `Result Sat ⟹ the problem is unsolvable` never depends on the untrusted components,
each of which is re-checked by a verified kernel:

1. **Model-checker / certificate (TChecker)** — TChecker explores the Munta network and emits a
   covering-graph certificate; **`muntac`** (the verified Munta certificate checker) re-checks it,
   and `make_certified_net_okay` turns "no run reaches `goal_loc`" into "no valid ground plan".
   Composed with the reduction's Thm 1 (`valid_plan_imp_form_holds`: a valid plan ⟹ the goal formula
   holds), the executable `check_and_cert_pddl_problem_okay` yields the boxed conclusion.
2. **Datalog reachability oracle** *(planned front-end)* — input is the serialized `dl_program`
   (transport only); the returned model + certificate `(M, dc)` is re-checked by the generic
   `dl_certified_model_exec`, and the reachable-fact set comes out *by theorem*
   (`certified_facts_eq_achievable`). The grounder targets the real-deletes problem, never the
   relaxation. See [ARCHITECTURE_grounding.md](ARCHITECTURE_grounding.md).
3. **Untrusted glue** — the Python `convert_models` harness and the external SAT/datalog solvers are
   transport only; nothing in a proof mentions them.

Everything in between (the reduction, grounding, plan reconstruction) is proven plan-preserving, so
an accepted answer is a sound statement about the *original* temporal problem.

## Reading order

1. This file. 2. [GROUNDING_PLAN.md](GROUNDING_PLAN.md) / [NUMERIC_PLAN.md](NUMERIC_PLAN.md) for the
two in-flight workstreams. 3. [ARCHITECTURE_grounding.md](ARCHITECTURE_grounding.md) for the
projection design. 4. [HANDOVER.md](HANDOVER.md) for the per-session inventory, `sorry` list, and
ordered next steps. 5. `Index.thy` maps the paper's theorems/locales to source.

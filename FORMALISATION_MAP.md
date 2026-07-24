# Formalisation map & wiring (inspection guide)

A short, current pointer into the formalisation and the end-to-end pipeline. Line numbers
verified against the working tree on 2026-07-18 — the 2026-07-24 work (relational guard
refinement in `TP_NTA_Reduction_Numeric_Bounds.thy`, the exec-twin equivalence +
`GCmp_i` projection in `bound_parsing/Ground_PDDL_Numeric_Code_Export.thy`, and the verified
capstone `check_and_cert_numeric_pddl_problem` in `bound_parsing/Numeric_Unsolvability_Export.thy`)
postdates that verification, so re-anchor those files via isabelle-search. For the narrative see
`HANDOVER.md`; this file is the navigation entry point.

---

## 1. End-to-end wiring (what runs, in order)

```
lifted PDDL (domain+problem, schematic ?vars)
   │  [EXTERNAL, TRUSTED grounder — OPTIC build "grounder", DO NOT DISTRIBUTE]
   │  grounder --write-pddl <gdom> <gprob> -- <dom> <prob>
   ▼
grounded PDDL  (propositional; for bounded-numeric domains OPTIC compiles fluents to props)
   │  plan_cert -domain <gdom> -problem <gprob> -model <muntax>
   │     └─ Isabelle-exported Converter.check_and_make_network_opt  (net builder + admission check)
   ▼
<muntax>  (Munta timed-automata network)
   │  python3 -m convert_models.convert         <muntax> → <tck>
   │  tck-reach -a covreach -C graph -s dfs -o   <tck>   → <dot>   (zone-graph certificate)
   │  plan_cert -model <muntax> -renaming <rnm>          (renaming table)
   │  python3 -m convert_models.convert_certificate      <dot>+<rnm> → <cert>
   ▼
muntac -m <muntax> -r <rnm> -c <cert> -i 3
   ▼
"Certificate was accepted"  ==  problem is UNSOLVABLE (no valid temporal plan)
```

Drivers: `run.sh` (shell) or the SML orchestration in
`ML/plan_cert/src/tchecker_certify.sml` (`certify_via_tchecker`, l.120), dispatched from
`ML/plan_cert/src/plan_cert.sml` (`certify_tchecker`, l.186).

### Trust boundary
- **Trusted / unverified:** the OPTIC grounder, `tck-reach`, `muntac`, the `convert_models`
  python, the MLton runtime, and the `plan_cert` PDDL parser/printer.
- **Verified in Isabelle:** the reduction (a valid plan ⇒ the network formula is reachable),
  the executable admission checks, and — for numerics — the bound re-check. So a network whose
  formula is **un**reachable proves **no** plan exists. The capstone is below.

---

## 2. Propositional reduction spine (sessions `TP_NTA_Reduction`, `PDDL_TP_Reduction`)

| What | File:line |
|---|---|
| Reduction-correctness locale | `TA_Network/TP_NTA_Reduction_Model_Checking.thy:187` `tp_nta_reduction_correctness` (primed `'` variant :214) |
| **Soundness capstone** (¬sat ⇒ ∄ valid_ground_plan) | `Ground_PDDL_Exec_Imp/Check_Unsolvability.thy:1054` `make_certified_net_okay` |
| End-to-end PDDL cert lemma | `Ground_PDDL_Exec_Imp/Check_Unsolvability.thy:1118` `check_and_cert_pddl_problem_okay` |
| Zone-graph cert check sound | `Ground_PDDL_Exec_Imp/Check_Unsolvability.thy:702` `certificate_check_okay` |
| Exec net builder | `Ground_PDDL_Exec_Imp/Check_Unsolvability.thy:1033` `check_and_make_network_opt` |
| Net-export (Containers-safe twin + codegen) | `Ground_PDDL_Exec_Imp/Ground_PDDL_Net_Export.thy:182` def, `:261` `export_code` (→ `Converter`, `code/Ground_PDDL_Net.ML`) |

---

## 3. Numeric bound-inference spine

Goal: infer sound integer bounds on numeric fluents so Munta's bounded-int obligation is
discharged, keeping numerics as int vars in the net (the *verified* numeric track).

### 3a. Compute side — session `Numeric_Bound_Inference` (standalone, on `HOL-IMP` heap; `ROOT:112`)
Threshold-interval abstract interpretation. All `sorry`-free.

| What | File:line |
|---|---|
| Interval eval / abstract step | `Numeric_Bound_Inference/Numeric_Bound_Inference.thy:119` `aeval`, `:196` `astep` |
| Bound-invariant + soundness | `…Numeric_Bound_Inference.thy:324` `is_bound_inv`, `:327` `bound_inv_sound` |
| Fixpoint driver + soundness | `…Numeric_Bound_Inference.thy:366` `infer`, `:386` `infer_sound` |
| Widening-with-thresholds | `…_Threshold.thy:136` `infer_thr`, `:150` `infer_thr_sound` |
| Guards (preconditions) | `…_Guards.thy:147` `is_gbound_inv`, `:150` `gbound_inv_sound`, `:202` `ginfer_thr`, `:216` `ginfer_thr_sound`, `:278` `thr_set` |
| **SML entry** + soundness | `…_Extract.thy:62` `infer_fluent_bounds`, `:70` `infer_fluent_bounds_sound`, `:95` reach-subset corollary |
| Code export | `…_Code_Export.thy:15` `export_code` → module `NumericBoundInference` → `code/Numeric_Bound_Inference.ML` |

### 3b. Reduction side — session `TP_NTA_Reduction`
Connects the inferred box to the Munta bounded-int obligation.

| What | File:line |
|---|---|
| Numeric reduction locale | `TA_Network/TP_NTA_Reduction_Numeric_Defs.thy:187` `numeric_tp_nta_reduction` |
| Numeric correctness locale | `TA_Network/TP_NTA_Reduction_Numeric_Model_Checking.thy:20` `numeric_tp_nta_reduction_correctness` |
| Reduction-native bound obligation | `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy:27` `num_bound_inv` |
| Discharge locale | `…_Numeric_Bounds.thy:75` `numeric_tp_nta_reduction_bounds`, `:427` `num_seq_in_bounds_derived` |
| Trusted static certificate | `…_Numeric_Bounds.thy:549` `is_gbound_inv'` |
| **Capstone** (cert ⇒ bound obligation) | `…_Numeric_Bounds.thy:1020` `is_gbound_inv'_imp_num_bound_inv` |

### 3c. Executable / export layer — session `PDDL_TP_Reduction`

| What | File:line |
|---|---|
| Executable trusted gate | `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_Code_Export.thy:86` `is_gbound_inv_exec`, `:113` `check_gbounds_opt` |
| Numeric net builder | `…_Numeric_Code_Export.thy:101` `check_and_make_numeric_network_opt` |
| **Untrusted** snap projection (re-checked, fail-closed) | `…_Numeric_Code_Export.thy:164` `numeric_draft_actions` |
| Code export | `…_Numeric_Code_Export.thy:205` `export_code` → module `NumericProjection` → `code/Numeric_Projection.ML` |
| Cert-bridge locales | `…_Numeric_NTA_Reduction_Bounds.thy:31` `numeric_ground_ast_problem_cert`, `:55` `numeric_valid_ground_plan_cert`, `:115` `num_net_form_not_sat_imp_no_valid_ground_plan` |
| WP-D capstone (refine + plan cert) | `…_Numeric_NTA_Reduction_Cert_Impl.thy:34` `num_model_checking_problem_refine_cert`, `:57` `check_and_make_numeric_network_and_plan_cert` |

**Dataflow:** `numeric_draft_actions` (reduction, untrusted) → SML `NumericBoundGlue.infer_box`
projects to `gcomp`/`nexp`, calls `thr_set` + `infer_fluent_bounds` (compute) → int box →
re-checked by the trusted `check_gbounds_opt` gate, whose soundness is
`is_gbound_inv'_imp_num_bound_inv`, discharging `num_bound_inv` / `num_seq_in_bounds`. A wrong
box is *rejected*, never unsound.

---

## 4. SML glue & generated code (`ML/`, `code/`)

| What | Path |
|---|---|
| Binary main / arg dispatch | `ML/plan_cert/src/plan_cert.sml` (`numeric_selftest` l.209) |
| External model-checking orchestration | `ML/plan_cert/src/tchecker_certify.sml` |
| Bound-inference bridge (entry `infer_box`) | `ML/plan_cert/src/numeric_glue/numeric_bound_glue.sml:71` |
| Network IR / printing | `ML/plan_cert/src/network_conversion/network_conversion.sml` |
| Generated code | `code/Numeric_Bound_Inference.ML`, `code/Numeric_Projection.ML`, `code/Ground_PDDL_Net.ML` |
| MLB wiring | `ML/plan_cert/src/numeric_code.mlb` (isolates the 2 generated modules), `…/plan_cert.mlb`, `ML/Makefile` (`build_certifier`) |

---

## 5. Sessions (`ROOT`)

`Temporal_Munta_Base` (1) → `Temporal_Planning_Base` (24) → `Temporal_Planning_Common` (49) →
`Temporal_Planning_Semantics` (55) → `TP_NTA_Reduction` in `TA_Network` (62) →
`PDDL_TP_Reduction` in `Ground_PDDL_Exec_Imp` (83). Separately:
`Numeric_Bound_Inference` on `HOL-IMP` (112) — standalone because HOL-IMP's option-lattice
arity clashes with the Munta/FPS tower.

---

## 6. Current numeric status (important)

- The **verified numeric net track** (§3) is complete and `sorry`-free, but the full
  **`-numeric` PDDL mode is not yet wired** in the binary: there is no
  `Converter → NumericProjection` AST coercion / numeric-net codegen. The runnable numeric
  smoke test today is `plan_cert -certify numeric-selftest` (a synthetic guarded counter that
  exercises projection + AI + trusted re-check).
- For the **bounded-numeric benchmarks** (Gigante `-impossible` families), the OPTIC grounder
  compiles the numeric fluents into propositional predicates, so the existing propositional
  pipeline (§2) certifies them without the numeric net. (Note the OPTIC "grounder" build is
  trusted-but-unverified; a verified SML grounder is future work.)

---

## 7. Numeric bounds: emission & cross-session hand-off

The bounds are **not** passed as a HOL term into the reduction — the two sides live in
**incompatible Isabelle heaps** (`Numeric_Bound_Inference` on `HOL-IMP`, whose `Abs_Int0`
option-lattice arity clashes with the Munta/FPS reduction tower), so the compute code *cannot
be imported* into the reduction. The box crosses the boundary as **plain `int` data marshalled
through SML**, and the reduction **re-checks** it. Trust flows one way: the inferred box is
untrusted; the reduction's static certificate validates it, fail-closed.

```
 COMPUTE SIDE  (session Numeric_Bound_Inference, HOL-IMP heap)
   infer_fluent_bounds        Numeric_Bound_Inference_Extract.thy:62   (env → extract_box :58 → per-fluent (int×int), or None if any endpoint ∞)
   soundness                  …_Extract.thy:70  infer_fluent_bounds_sound
   export  (regime A)         …_Code_Export.thy:15  export_code … file_prefix  → code/Numeric_Bound_Inference.ML  (module NumericBoundInference)
        │  (SML value: 'a -> int*int  via widened enum/equal dicts)
        ▼
 SML GLUE   ML/plan_cert/src/numeric_glue/numeric_bound_glue.sml
   infer_box : draft -> box option  (l.71)
     • input  = NumericProjection.numeric_draft_actions  →  (fluents, snaps=[(guards,updates)], init)
     • project reduction-side g_int/e_int → compute-side gcomp/nexp (l.45-59; strict comps → non-strict on ℤ)
     • bridge the two distinct SML int types (NP.int / NBI.int) through IntInf (l.36-41)
     • call NBI.thr_set then NBI.infer_fluent_bounds
     • read back a name-keyed box : (string × (int × int)) list          ← THIS plain list is what crosses
        │
        ▼
 REDUCTION SIDE  (session PDDL_TP_Reduction)  — re-check the box, fail-closed
   check_gbounds_opt P B      Ground_PDDL_Numeric_Code_Export.thy:113   (rebuild lo/hi from assoc list B, run trusted is_gbound_inv_exec)
   admission gate             …_Numeric_Code_Export.thy:101  check_and_make_numeric_network_opt P B
                                (same lo/hi, build net with check_and_make_numeric_network, gate on is_gbound_inv_exec;
                                 returns Some net ONLY if the box certifies)
   trusted static cert        …_Numeric_Code_Export.thy:86   is_gbound_inv_exec
   soundness capstone         TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy:1020  is_gbound_inv'_imp_num_bound_inv
                                (a certified box discharges num_bound_inv / num_seq_in_bounds)
```

**Why fail-closed is safe:** `numeric_draft_actions` (the projection feeding `infer_box`) is
explicitly *untrusted* — a lossy/partial projection only *widens* the box; `check_gbounds_opt`
then re-validates via `is_gbound_inv_exec`, so a wrong box is **rejected**, never accepted as
sound. The compute side may return `None` (∞ endpoint = "bound inference failed"); the reduction
needs finite `int` bounds, so such a problem is rejected up front.

**Wiring status:** today only `plan_cert.sml:209` `numeric_selftest` actually calls `infer_box`
(on a synthetic guarded counter). The path that would call `check_and_make_numeric_network_opt`
on a real parsed problem is the not-yet-wired `-numeric` mode (§6).

## 8. Code export: regimes, commands & current status

Two Isabelle export regimes are in play (the isabelle-repo gotchas apply — `file "…"` writes at
*process* time, `file_prefix` populates the store for `-e`):

| Module → file | Source theory | Regime | Reproduce |
|---|---|---|---|
| `NumericBoundInference` → `code/Numeric_Bound_Inference.ML` | `Numeric_Bound_Inference_Code_Export.thy` (`file_prefix`) | **A** store + `export_files` + `-e` | `cd code && make numeric-bound-inference` = `isabelle build -e -d .. Numeric_Bound_Inference` then `python3 widen_nbi_sig.py` (widens the opaque `equal`/`enum`/`finite` dicts). **Reproducible.** |
| `NumericProjection` → `code/Numeric_Projection.ML` | `Ground_PDDL_Numeric_Code_Export.thy:205` (`file "../code/…"`) | **B** side-effect | Emitted by processing the theory in **jEdit** (its session can't batch-build — blocked by broken `Check_Unsolvability`, can't be split off a shared dir). |
| `Converter` → `code/Ground_PDDL_Net.ML` | `Ground_PDDL_Net_Export.thy:261` (`file "../code/…"`; **not in ROOT**) | **B** side-effect | Emitted by processing the isolated export theory in **jEdit**. This is the net builder the binary links (`ML/converter.mlb`). |

**The propositional *checker* export** (`ML/Check_Unsolvability.ML`, the certified
network+cert-check code) is a third mechanism — `Unsolvability_Code_Export.thy`:
`compile_generated_files "code/Check_Unsolvability.ML" (in Check_Unsolvability)` + `export_files`
with a **shell post-processing hook** (`sed IntInf→Int`, splice a set-implementation destructor
for the `list_of_set'` placeholder, `mkdir ML`, move + copy into `ML/`).

**Current status (verified live in jEdit, 2026-07-18):** the checker export is **blocked**.
`Check_Unsolvability.thy` shows **726 failed commands** (the deferred WP-D code-gen tail the
`code/Makefile` header flags), so it does not consolidate; the export theories that import it —
`Unsolvability_Code_Export` and `Unsolvability_Code_Compile` — fail (2 errors each) **purely as
a cascade of that import** (the `compile_generated_files`/`export_files` command itself is
error-free). Consequences:
- The linked `ML/Check_Unsolvability.ML` on disk is the **older (Jan) good copy**, not
  regenerated from the current tree.
- The binary now links the **isolated `code/Ground_PDDL_Net.ML`** (`Converter`), which
  deliberately sidesteps the broken `Check_Unsolvability` via top-level `[code]` twins.
- Productionising (per the Makefile header): repair `Check_Unsolvability` (or relocate the
  numeric/net chain to a `Check_Unsolvability`-free session), then switch the two regime-B
  `file "…"` exports to `file_prefix` + `export_files` + `-e`.

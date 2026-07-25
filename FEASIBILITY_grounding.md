# Feasibility: grounding / net-shape improvements

Status 2026-07-25. Question: are there ways to "ground better" so the certification oracle
(tck-reach covreach) and the certificate tail (convert + verified check) handle more instances?

## Where the cost actually is (measured)

- The net emitted per ground problem: one 4-location automaton per ground action + `main`, and
  **two clocks per ground action** (`start_X`, `end_X`). painter `1_2`: 17 action automata,
  **34 clocks**; majsp-1 `1_2_3_1`: 20 action automata, **40 clocks**.
- Certificate size is zones × DBM², so clocks enter **quadratically**: majsp-1's 921,881 zones ×
  42×42 DBM ≈ the observed 3.5 GB dot certificate. Exploration cost also grows with clock count.
- `end_X` clocks exist only for strict-separation guards in OTHER actions (`end_X > 0`); they are
  never compared against a nonzero constant.
- The Gigante et al. (AAAI-22) UPPAAL encoding of the SAME problems uses ~1 clock per action
  (+2 aux), batches simultaneous events between strictly-positive waits, and UPPAAL solves
  painter `1_2` in ~1 s where our net does not finish in 10 h under covreach and ~15 min under
  aLU-covreach. tck-reach's covreach applies NO extrapolation (plain zones + inclusion), which
  accounts for part of the gap — but the aLU probe shows the encoding shape itself is the painter
  bottleneck, not just the subsumption.

## Levers, ranked by cost/benefit

1. **Single clock per action (verified reduction change) — best ratio.** Reset one clock at BOTH
   the start and end events. Separation guards remain sound: separation from an action's most
   recent event implies separation from all its earlier ones (elapsed times are ordered), and the
   duration guard still reads time-since-start at the end transition because the last event at
   that moment IS the start. Halves DBM dimension: certificates shrink ~4× (majsp-1: 3.5 GB →
   ~0.9 GB; combined with aLU admission, ~0.15 GB), zones get coarser too. Scope: `TP_NTA_Reduction`
   and its separation/duration lemmas — weeks of Isabelle work, no grounder change.
2. **Stronger untrusted pruning (cheap, incremental).** nemo currently does TFD-relaxed FORWARD
   reachability (painter 37→17, majsp-1 48→20, majsp-2 16→9 automata). Add:
   - *backward relevance* (regression from the goal through the same relaxation): drops actions
     that cannot contribute to any goal path; symmetric datalog pass, days of SML.
   - *value-aware datalog for box-bounded fluents*: encode a bounded integer fluent's value as a
     fact argument (successor relation seeded from the inferred box), letting nemo kill
     value-infeasible snaps. Sound as an over-approximation; does NOT help painter-impossible
     (its guard is relaxed-satisfiable — the instance is unsolvable for temporal-ordering
     reasons), but prunes elsewhere.
   Pruning has the same trust status as the rest of the untrusted grounder (the verified verdict
   is about the emitted ground problem; lifted-faithfulness is the grounder's contract).
3. **Clock sharing across mutex actions (verified, middle step).** Actions guarded by the same
   lock never overlap and could share one clock. Subsumed by 1 + harder bookkeeping; only worth
   it after 1 if profiles still show clock-dominated certificates.
4. **Paper-style re-encoding (verified, big).** A reduction in the style of the AAAI-22 UPPAAL
   encoding — simultaneous event batches separated by strictly-positive waits, one clock per
   action, fluents as bounded variables — is what makes painter 1-second-easy for UPPAAL. For us
   it is a NEW `TP_NTA_Reduction` with a new soundness proof (months). It is the only identified
   path to painter certification besides accepting it as oracle-hard.
5. **Certificate-tail engineering (no semantics).** The dot→binary conversion dominates large
   certs (majsp-1: 557 s pydot parse of 3.5 GB). Emitting the binary Munta certificate directly
   from the tck-reach graph (or a streaming converter) is untrusted glue — days — and combines
   multiplicatively with 1/aLU. The verified check itself already parallelizes (`-num-threads`).

## Non-levers

- Better third-party grounders (OPTIC/TFD/tflap) do not address this: our grounding is already
  reachability-pruned, and the blowup is in the NET SHAPE and oracle algorithm, not in ground
  action count (painter: 17 actions is already minimal-ish; its hardness survives any pruning).
- Rational-native arithmetic: see `FEASIBILITY_rational_durations.md` — scaling is a zone-graph
  isomorphism; nothing to gain.

## Cleanup flag (not fixed)

The emitted nets carry vacuous guard conjuncts: every separation guard `c > 0` is accompanied by
a trivially-true `c >= 0` twin (clock values are nonnegative by definition). Harmless for zones
but bloats every guard string and slows parsing of large nets; worth dropping at net emission
(verified-side simplification in the guard construction).

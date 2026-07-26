# Feasibility: grounding / net-shape improvements

Status 2026-07-25. Question: are there ways to "ground better" so the certification oracle
(tck-reach covreach) and the certificate tail (convert + verified check) handle more instances?

## UPDATE 2026-07-26: the snap-split shipped and painter now certifies

The nemo snap-action split (below, item 1's spirit but in the grounder's datalog) landed:
durative actions are split into start/end applicability predicates, so at-end/over-all conditions
on dynamic fluents can be required as sound reachability joins. painter drops from 17 to 11 ground
actions (matching POPF), its net from 18 automata/34 clocks to 12/22, and **covreach finishes in
~7 s where it previously did not finish in 10 h** — painter `instance_1_2` now certifies end-to-end
in ~46 s (verified checker accepts). painter is no longer oracle-hard; the sections below are
retained as the original analysis (their "painter is encoding-bound / oracle-hard" framing is
superseded for `instance_1_2`; larger painter instances are untested).

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
- **The constants are irrelevant to painter's hardness (measured 2026-07-25).** Editing the clip
  slack in `domain_container.pddl` and re-running the full pipeline: with `15.5` (LCM ×2,
  constants {8,10,12,31}) covreach still does not finish in ~10 min; with `15` exactly (ε = 0,
  ALL-integer constants ≤ 15, semantically a different, clip-broken problem — diagnostic only)
  it still does not finish in 5 min. So neither the ×250 scaling nor the fractional misalignment
  drives the blowup — the per-event interleaving structure with pairwise separation clocks does.

## Levers, ranked by cost/benefit

**Dead end — clock-count reduction (2026-07-25).** Merging `start_X`/`end_X` into one
per-action clock (or sharing clocks across mutex actions) is UNSOUND here: the separation sets
are snap-level and asymmetric — measured across the emitted nets, 27/27 of painter's
separation-carrying guards, 32/36 of majsp-1's and 9/9 of MatchCellar's constrain one of
`start_Y`/`end_Y` without the other. A merged clock cannot distinguish which happening it was
reset by, so it would forbid schedules the semantics allows (e.g. a snap at the instant of Y's
end when only separation from Y's start is required); excluding legal plans can flip a solvable
problem to "unsolvable", which is exactly the direction we certify. Both clocks stay.

1. **Stronger untrusted pruning (cheap, incremental).** nemo currently does TFD-relaxed FORWARD
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
2. **Paper-style re-encoding (verified, big).** A reduction in the style of the AAAI-22 UPPAAL
   encoding — simultaneous event batches separated by strictly-positive waits, one clock per
   action, fluents as bounded variables — is what makes painter 1-second-easy for UPPAAL. For us
   it is a NEW `TP_NTA_Reduction` with a new soundness proof (months). It is the only identified
   path to painter certification besides accepting it as oracle-hard. (Note its clock economy is
   bought by a DIFFERENT separation discipline — whole event batches at one instant, then a
   strictly positive wait — not by merging our per-snap clocks, so it does not contradict the
   dead end above.)
3. **Certificate-tail engineering (no semantics).** The dot→binary conversion dominates large
   certs (majsp-1: 557 s pydot parse of 3.5 GB). Emitting the binary Munta certificate directly
   from the tck-reach graph (or a streaming converter) is untrusted glue — days — and combines
   multiplicatively with aLU admission. The verified check itself already parallelizes
   (`-num-threads`); when RAM is the binding constraint (the majsp-1 in-process check has been
   OOM-killed at this scale), certificate size is the lever, not threads.

## Non-levers

- Better third-party grounders (OPTIC/TFD/tflap) do not address this: our grounding is already
  reachability-pruned, and the blowup is in the NET SHAPE and oracle algorithm, not in ground
  action count (painter: 17 actions is already minimal-ish; its hardness survives any pruning).
- Rational-native arithmetic: see `FEASIBILITY_rational_durations.md` — scaling is a zone-graph
  isomorphism; nothing to gain.
- Shrinking or removing painter's clip slack (`15.004` → `15.5`/`15`): measured above — the
  zone blowup survives all-integer constants, and ε = 0 additionally breaks the clip
  compilation's semantics (the container must end strictly after its inner pieces), so any
  verdict would be about a different problem than the benchmark.

## Cleanup flag (not fixed)

The emitted nets carry vacuous guard conjuncts: every separation guard `c > 0` is accompanied by
a trivially-true `c >= 0` twin (clock values are nonnegative by definition). Harmless for zones
but bloats every guard string and slows parsing of large nets; worth dropping at net emission
(verified-side simplification in the guard construction).

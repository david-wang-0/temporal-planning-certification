# Feasibility: aLU-subsumption certificates in the verified checker

Status 2026-07-25. Question: how hard is it to make the verified certificate checker (Munta's
`convert_check` path, vendored via AFP `Munta_Certificate_Checker`) accept state sets that are
closed only under **aLU subsumption** (Behrmann et al.'s coarser `Z ⊑_aLU Z'  ⟺  Z ⊆ aLU(Z')`),
which `tck-reach -a aLU-covreach` emits — instead of requiring plain zone inclusion, which only
`covreach` guarantees?

## Why we care (measurements)

- Today an aLU certificate is admitted only by luck — iff the aLU-closed set happens to also be
  inclusion-closed. Empirically (2026-07-25, `TCK_ALGO=aLU-covreach`): majsp-2 `1_1_2_1`
  **accepted** and fully certified; MatchCellar `2`, sync `1_2`, majsp-1 `1_2_3_1` **rejected**
  (fail-closed, no wrong verdict).
- majsp-1 `1_2_3_1`: aLU explores **155,873** discrete states vs covreach's **921,881** (5.9×),
  and tck time drops ~4 min → 110 s. The covreach certificate is ~3.5 GB; an admitted aLU
  certificate would shrink the whole convert+check tail proportionally. This is the main
  beneficiary.
- painter is **not** unlocked by aLU at the oracle: `aLU-covreach` (bfs and dfs) does not finish
  painter `1_2` exploration within ~15 min either (covreach: >10 h). painter's problem is the
  net encoding shape, not the subsumption test — see `FEASIBILITY_grounding.md`.

## What the formalization already provides (all references AFP 2025-2)

The exploration result is much better than feared: **the checker's soundness kernel is already
parametric in the subsumption relation.**

- The closedness spec uses an abstract preorder `⪯`, not `dbm_subset`
  (`Munta_Certificate_Checker/Certification/Unreachability_Misc.thy:383`):
  `check_invariant_spec L' ≡ ∀l∈L'. ∀s∈M l. ∀l' s'. E (l,s) (l',s') ⟶ l'∈L ∧ (∃s''∈M l'. s' ⪯ s'')`.
- The ONLY structural obligations on `⪯` are `preorder` plus monotonicity/simulation
  (`Simulation_Graphs_Certification.thy:690-704`):
  `s ⪯ s' ⟹ E (l,s) (l',t) ⟹ … ⟹ ∃t'. t ⪯ t' ∧ E (l,s') (l',t')` — exactly the property
  Behrmann et al. prove for aLU.
- `dbm_subset` is hard-wired only at the leaf instantiation
  (`Normalized_Zone_Semantics_Certification_Impl.thy:1021-1023, 1110-1114`), entering through a
  single refinement obligation per pipeline (imperative `dbm_subset_impl.refine` :1070; the pure
  IArray `lei`), NOT woven through the separation-logic proofs.
- The LU mathematics already exists, standalone: `TA_Simulation.thy` formalizes Li's FORMATS 2009
  LU-abstraction paper — `TA_LU` (:330-468) proves the LU relation is a `Time_Abstract_Simulation`,
  and `Time_Abstract_Simulation_Sandwich` (:763-773) captures `Z ⊆ β Z ⊆ α Z` with β a DBM
  extrapolation. Nothing imports it yet; it is not bridged to the DBM-level successor.
- Executable LU extrapolation already exists: `extra_lu`/`norm` (`DBM_Normalization.thy:52,104`)
  with executable `extra_lu_upd`/`norm_upd` (`DBM_Operations_Impl.thy:1328-1454`), generic over
  `'t :: linordered_ab_group_add`.
- There is even a commented-out `Reachability_Impl_simulation` locale
  (`Unreachability_Certification2.thy:510-534`) — an abandoned first attempt at exactly this
  generalization.

## What is missing

One bridging theory + six leaf obligations:

1. `⪯_aLU` reflexivity and transitivity (the `preorder` instance);
2. **E-monotonicity of the DBM successor `E_from_op_empty` w.r.t. `⪯_aLU`** — the real work:
   transport `TA_LU.sim` from the valuation level to DBMs through `dbm.zone_of`/`conv_M`
   (analogue of `op_precise.E_from_op_empty_mono'`, `…Certification_Impl.thy:1072`);
3. `F_mono` w.r.t. `⪯_aLU` (`:339-342`, re-discharged `:1051`);
4. executable refinement of the new comparison (imperative + pure `lei` twins);
5. sound per-clock L/U bounds computed **inside the checker** from the model (per-clock global
   bounds suffice; they must not be trusted from the producer);
6. producer glue: `tck-reach -a aLU-covreach` already emits aLU-closed sets, so only the checker
   side changes (`TCK_ALGO=aLU-covreach` is already plumbed through plan_cert and the benchmark
   harness).

## Two implementation routes

- **Extra_LU-widen (pragmatic, recommended): ~2-4 weeks.** Keep the executable inclusion test
  verbatim; before comparing, widen the STORED certificate DBM: check
  `dbm_subset n s (extra_lu_upd s' L U n)`, i.e. `Z ⊆ Extra_LU(Z')`. This is the convex DBM
  abstraction inside aLU — coarser than inclusion, finer than full aLU, and it sits exactly in
  the already-formalized sandwich `Z ⊆ β Z ⊆ α Z`. Reuses `dbm_subset_impl` unchanged; the new
  proof is that Extra_LU-widening satisfies the mono obligation (via `TA_LU` +
  `Abstraction_Simulation`). Caveat: Extra_LU-closedness is *slightly* stronger than
  aLU-closedness, so some aLU certificates could still be rejected; in practice Extra_LU is what
  UPPAAL-style engines store anyway.
- **Native aLU test: ~1-2 months.** Implement the non-convex `Z ⊆ aLU(Z')` check (Herbreteau et
  al.'s O(n²) test) as a new imperative/IArray operation with its own refinement proofs, then
  discharge the same six obligations. Admits everything `aLU-covreach` emits.

## Verdict

Moderate, genuinely worth doing for majsp-scale certificates: weeks (widen route), not months,
because the kernel is already parametric and the LU math + executable extrapolation already
exist. It does NOT rescue painter (the oracle itself cannot finish painter under aLU; that is an
encoding problem). Expected payoff: majsp-1-class instances go from 3.5 GB certificates at the
edge of feasibility to ~0.6 GB well inside it, and every aLU-covreach run becomes admissible
rather than admissible-by-luck.

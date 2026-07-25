# Feasibility: rational durations in the verified checker

Status 2026-07-25. Question: muntac (the verified Munta certificate checker) works over integer
clock constants, so rational PDDL durations (painter's `15.004`) are handled by LCM-scaling all
durations to integers in the untrusted grounder (`scale_durations`, ×250 for painter). How hard
would native rational support be — and would it help?

## Would it help performance? No.

Uniform scaling is a zone-graph isomorphism: multiplying every constant by the common
denominator L and every clock valuation by L maps runs to runs and zones to zones bijectively
(guards `x ⋈ c` become `x ⋈ L·c`, delays `d` become `L·d`). The scaled integer system explores
EXACTLY as many zones as a rational-native exploration of the original would. Empirically
confirmed harder than expected (2026-07-25, see `FEASIBILITY_grounding.md`): painter does not
even depend on the misalignment — variants with clip slack `15.5` (constants ≤ 31) and `15`
(all-integer, ≤ 15, diagnostic only) still blow up covreach. The hardness is the net's
per-event interleaving/separation shape; constants — big, fractional, or small — are a
non-factor. Native rationals would only change the arithmetic width of DBM entries, at extra
constant-factor cost (rational normalization vs machine/bignum integer compares).

## Would it be sound? Yes — the checker is already real-valued inside.

Findings from the AFP 2025-2 formalization:

- The semantic time domain is ALWAYS `real`: `'t DBMEntry` is generic
  (`Difference_Bound_Matrices/DBM.thy:19`), `class time = linordered_ab_group_add + dense +
  non_trivial` (:35-37) — `int` is deliberately NOT a `time` instance (not dense); the executable
  `int` layer embeds via `conv_M = map_DBMEntry real_of_int`
  (`Munta_Model_Checker/TA_Impl/Normalized_Zone_Semantics_Impl_Semantic_Refinement.thy:37`).
- The certificate successor is EXACT — `up_canonical_upd → abstr → FW' → abstr → reset'_upd →
  abstr` (`Normalized_Zone_Semantics_Certification.thy:11-15`); **no** `norm`/`extra_lu`/ceiling
  appears anywhere in the checker's successor or invariant check. The integral-ceiling machinery
  (`normalized_integral_dbms_finite`, region constructions) is used only for
  completeness/termination/Büchi arguments, never for reachability-certificate soundness.
- `int` is fixed only in the executable leaf: the `state_space` datatype
  (`Simple_Network_Language_Certificate_Code.thy:524-526`), the certificate input type
  (`…Certificate_Checking.thy:987`), ~250 lines of `_int`-specialized code equations
  (`…Certificate_Checking.thy:368-617`), and the `ri`/`RI` int↔real transfer relations.
- No scaling lemma exists anywhere in the entries (searched Timed_Automata,
  Difference_Bound_Matrices, Munta_Model_Checker).

## Options

1. **Keep frontend LCM scaling (current design) — recommended, already done.** Zero verified-side
   change. The one genuine gap: the scaling lives in the UNTRUSTED grounder, so the verified
   verdict is about the *scaled integer ground problem*; the step "rational original unsolvable ⟸
   scaled version unsolvable" is informal. Closing it = ONE new lemma (the scaling isomorphism at
   the ground-problem or net level, stated over our own `TP_NTA_Reduction` layer — days-to-a-week
   of proof work), plus moving the scaling inside the verified perimeter or certifying the scale
   factor. This is the highest-value piece of "rational support": correctness perimeter, not
   speed.
2. **Retype the executable layer to `rat`: ~2-4 weeks, mechanical, no benefit.** Swap
   `int DBMEntry` → `rat DBMEntry`, `real_of_int` → `real_of_rat`, rebuild the `_int` code
   equations and `ri`/`RI` for `rat`, regenerate code. Broad but shallow (the soundness theory is
   generic). Buys nothing on state count (isomorphism above) and slows the DBM arithmetic; only
   worth it if scaled constants ever overflow practical integer widths — they cannot, since Munta
   exports use arbitrary-precision integers.

## Verdict

Native rational durations are a "generalize the leaf types" job (weeks, mechanical), NOT a
"rewrite the decidability argument" job — but they are also pointless for performance. The
worthwhile follow-up is option 1's scaling-isomorphism lemma, which upgrades the informal
"×250 preserves unsolvability" step into the verified statement.

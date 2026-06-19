# Gigante et al. temporal benchmarks — conditions & effects survey

Survey of the PDDL constructs used in the `domain*.pddl` files of the
temporal-planning benchmark set of Gigante et al. (AAAI 2022), distributed as
the `expeval/benchmarks/` tree of that paper's artifact. Counts are
*number of domain files* using a construct, taken over the 50 domain files
(44 of which declare durative actions).

Benchmark families: `majsp`, `painter`, `sync-impossible`, `MatchCellar`,
`temporal-ipc/*` (Driverlog, Floortile, Mapanalyser, MatchCellar, Satellite,
TMS), `uncertainty-ipc/*`. Most families ship several encodings of the same
temporal structure: `tpp/` (untimed STRIPS-ish), `pddl21/` (durative), and
`_container` / `_clip` / `_integers` variants (different clipping encodings /
integer-typed fluents).

## Action types

| Construct | Files | Notes |
|---|---|---|
| `:durative-action` | 44 | the main encoding |
| `:action` (instantaneous) | 19 | mostly `tpp/` encodings + majsp `move`/`load`/`unload_at_depot` |
| `:uncontrollable-durative-action` | 7 | `uncertainty-ipc/*/with-uncertainty` — duration chosen adversarially |

## Temporal qualifiers (conditions)

| Qualifier | Files | Meaning |
|---|---|---|
| `at start` | 44 | precondition at action start |
| `at end` | 44 | precondition at action end |
| `over all` | 26 | invariant held across the whole interval |

Conditions are always built with `and`. No `or`, `imply`, or `exists`.
`forall` appears as a *universally-quantified condition* in 4 files (`sync`),
e.g. `(at end (forall (?p - Parallel) (pB ?r ?p)))`.

`:conditional-effects` is *declared* in 3 files (`sync-impossible/pddl`,
`sync-impossible/tpp`, `painter-impossible/pddl21/domain_container`) but **no
`when` clause is actually used anywhere** — the quantification in those
domains is plain `forall`, not conditional effects.

## Numeric-fluent comparisons (conditions)

| Comparison | Occurrences | Where |
|---|---|---|
| `(>= (battery-level ?r) (distance ?from ?to))` | 13 | majsp `move` — fluent ≥ fluent |
| `(= (item_id ?i) (counter ?t))` | 7 | painter — **equality between two numeric fluents** |
| `(not (= ?from ?to))` | — | object inequality (`:equality`) |

No `<` / `>` strict comparisons appear in conditions (only `>=`, `<=`, `=`).

## Duration constraints (a special class of numeric condition on `?duration`)

| Form | Occurrences | Where |
|---|---|---|
| fixed: `(= ?duration k)` | 239 | most actions |
| bounded interval: `(and (>= ?duration a) (<= ?duration b))` | 15 | uncontrollable actions, `sync` |
| fluent-defined: `(= ?duration (dur_c1 ?r))`, `(= ?duration (arrived-time))` | — | `sync`, Mapanalyser |
| arithmetic-defined: `(= ?duration (/ (distance ..) (speed ..)))`, `(* (distance ..) (build-time))` | — | Mapanalyser |

Arithmetic operators used inside duration expressions: `+`, `-`, `*`, `/`.

## Numeric effect operators

| Operator | Occurrences | Example | Where |
|---|---|---|---|
| `decrease` | 15 | `(decrease (battery-level ?r) (distance ?from ?to))` | majsp `move` |
| `increase` | 7 | `(increase (counter ?t) 1)` | painter `make_treatment1` |
| `assign` | 2 | `(assign (counter ?t) N)` | painter-impossible (counter reset) |
| `scale-up` | 0 | — | not used |
| `scale-down` | 0 | — | not used |

## Effect structure

- Timed add/delete effects `at start (P …)` / `at end (P …)`, deletes via `(not (P …))`.
- Timed *numeric* effects (`increase`/`decrease`/`assign`) attached to `at start` / `at end`.
- Universally-quantified effects via `forall` (`sync`), e.g.
  `(forall (?p - Parallel) (at start (not (pB ?r ?p))))`.
- No conditional (`when`) effects despite the requirement flag.

## Requirements flags seen (union)

`:typing`, `:durative-actions`, `:equality`, `:fluents` (numeric fluents),
`:strips`, `:conditional-effects` (declared, unused),
`:uncontrollable-durative-actions`.

## Takeaways for grounding/normalization

- Numeric side is modest: only `increase`, `decrease`, `assign` effects;
  comparisons restricted to `>=`, `<=`, and fluent-to-fluent `=`. No
  `scale-up`/`scale-down`, no strict `<`/`>`.
- Equality between two numeric fluents (`(= (item_id ?i) (counter ?t))`) is the
  only non-`?duration` `=` comparison and is the main numeric "guard".
- Temporal richness is in `over all` invariants and `forall`-quantified
  conditions/effects, plus uncontrollable durations (interval bounds) —
  not in conditional effects.

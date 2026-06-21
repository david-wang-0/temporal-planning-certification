# Plan: Numeric Conditions and Effects in the Temporal Reduction

Status: draft (2026-06-18). Companion: [GROUNDING_PLAN.md](GROUNDING_PLAN.md) — the two interlock
(see §6). This is the large refactor: extend the temporal planning **semantics**, the abstract
**plan model**, and the **NTA reduction** (+ correctness proofs) with numeric state, numeric
conditions, and numeric effects.

---

## 1. Goal

Add numeric fluents to the certified temporal-planning-unsolvability pipeline:
- numeric **conditions** (comparisons over numeric expressions) at `at_start` / `over_all` /
  `at_end`;
- numeric **effects** (`Assign | ScaleUp | ScaleDown | Increase | Decrease`) at `at_start` /
  `at_end`;
- numeric **duration constraints** (`d_op ∈ {EQ,LEQ,GEQ}` over a numeric expression).

…all the way through to the Munta timed-automata network, such that an unsolvability certificate of
the network still implies unsolvability of the original numeric temporal problem.

## 2. Scoping decision (read first) — what the timed-automata target can represent

The reduction target is Munta `Simple_Network_Language`. From `TA_Network/TP_NTA_Reduction_Defs.thy`
the network already carries **bounded integer state variables** (`all_vars :: (name × int × int)
list`), `(name, int) bexp` guards, `(name, int) exp` assignment updates, and real **clocks** with
difference constraints (`acconstraint`). Propositions are *currently* encoded as 0/1 int variables.

This fixes the realistic scope:

| Numeric feature | Representable? | How |
|---|---|---|
| **Bounded integer fluents** | ✅ | one Munta int variable per ground `PNE`, with declared bounds |
| Conditions `=,≤,≥,<,>` on int exprs | ✅ | `bexp` on edge guards; `over_all` → guard on the snap-internal transitions / location invariant |
| Effects: `Assign`, `Increase`, `Decrease` by an int expr | ✅ | edge `(var, exp)` updates |
| Effects: `ScaleUp`/`ScaleDown` (×), arith `Increase`/`Decrease` | ✅ (operator-wise) | `exp.binop (op)` takes an *arbitrary* `'b ⇒ 'b ⇒ 'b`, so `+ − × ÷` are all expressible (§5.1 resolved). Real constraint is **value type + bounds**, not the operator: results must stay integer-valued and within `[lo,hi]` |
| **Rational / real fluents** | ❌ (out of scope) | Munta variables are `int`; admit only via fixed-point scaling with bounded denominators — defer |
| **Continuous numeric change** (rates over a duration, the `Continuous_Planning` ODE layer) | ❌ (out of scope) | timed automata evolve only **clocks** continuously; arbitrary fluents cannot evolve continuously. Only **discrete** snap-point numeric effects are in scope |

**Decision:** scope this plan to **discrete, bounded-integer numeric fluents** with comparison
conditions and instantaneous (start/end) numeric effects, plus numeric duration constraints reduced
to integer clock bounds (the existing `lower_spec`/`upper_spec` machinery generalized). Continuous
numeric evolution is explicitly **not** reduced to timed automata. Record any input outside this
fragment as a well-formedness rejection in the checker (fail-closed), not silent unsoundness.

## A. Concrete type-level design (decided 2026-06-19)

Two decisions fix the shape of the refactor:

- **Boundary reuse.** `Temporal_Plans` stays PDDL-agnostic (props are an opaque `'proposition`; fluents
  become an opaque `'n`). Numeric expressions/comparisons are a **fresh** abstract datatype over
  `('n, 'r)` with `'r` a rational-like value sort (use `'r :: linordered_field`; the intended instance
  is `rat` — note `'r::rat` from the sketch is not literal Isabelle, `rat` is a type not a sort). PDDL's
  `numeric_expression` (`Continuous_Planning/Abstract_Syntax.thy`) is mapped **into** the abstract type
  only at the `Ground_PDDL` layer, exactly as PDDL atoms become `'proposition` today. Reuse therefore
  happens **at the boundary**, not inside the reduction proofs.
- **Comparisons are first-class and survive grounding.** A ground task still carries numeric
  conditions and effects; the reduction turns each comparison into a Munta `bexp` guard and each effect
  into a `(var, exp)` update. Grounding does **not** erase comparisons (it only adds *definedness*
  tracking on top — see §6 / GROUNDING_PLAN).

### A.1 Abstract numeric syntax (`Temporal_Plans`, fresh)

```
datatype ('n,'r) nexp =                       \<comment> over opaque fluents 'n, values 'r::linordered_field
    NConst 'r
  | NVar   'n                                  \<comment> a ground fluent (read its valuation)
  | NAdd "('n,'r) nexp" "('n,'r) nexp"
  | NSub "('n,'r) nexp" "('n,'r) nexp"
  | NMul "('n,'r) nexp" "('n,'r) nexp"
  | NDiv "('n,'r) nexp" "('n,'r) nexp"          \<comment> integer-division gap at the Munta boundary (spike)

datatype cmp_op = Ceq | Cle | Cge | Clt | Cgt
datatype ('n,'r) comp = Comp cmp_op "('n,'r) nexp" "('n,'r) nexp"
```

Explicit operator constructors (not Munta's `binop "'r⇒'r⇒'r"`): they code-export, give decidable
equality, and map 1:1 to `binop (+)/(−)/(×)/(div)`. No `DurationExpr`/`Sin`/`Cos`/`Exp`/`Pi` leaf —
durations are handled by the existing `lower`/`upper` bounds (§A.4); transcendental leaves are rejected
at the boundary (§A.3).

### A.2 State and snap/action fields

- **State** gains a partial fluent valuation (partial = definedness, aligning with PDDL "read of
  undefined fluent is an error" and the grounder's `defined!` predicate):
  `type_synonym ('p,'n,'r) state = "'p set × ('n ⇀ 'r)"`. Comparison eval against an undefined fluent
  is ill-defined → the condition fails (fail-closed).
- **`action_defs` locale** gains three fixed fields alongside `pre/adds/dels`:
  ```
  upds  :: "'snap_action ⇒ ('n × ('n,'r) nexp) set"   \<comment> numeric effects (at_start/at_end)
  n_pre :: "'snap_action ⇒ ('n,'r) comp set"           \<comment> numeric preconditions (at_start/at_end)
  n_inv :: "'action      ⇒ ('n,'r) comp set"           \<comment> over_all numeric invariants (per action, like over_all)
  ```
  A **set** is read conjunctively (all hold simultaneously); grounding produces the conjunction. No
  disjunctive invariants (Munta has no disjunctive location invariant either).

  **`upds` well-formedness — the authoritative rule (checked against Formal-PDDL-Semantics,
  2026-06-19).** The within-snap "self-interference" rule is PDDL's `numeric_effects_non_intrf`
  (`Continuous_Planning/Numeric_Update_Functions.thy:44`): two numeric effects of one action on the
  **same fluent** must be the **same operator type** *and* **neither an `Assign`**. So **two conflicting
  `Assign`s to one fluent are forbidden** (an `Assign` must be that fluent's only writer); but multiple
  `Increase`/`Decrease` (additive), or multiple `ScaleUp`/`ScaleDown` (scaling), on one fluent are
  **allowed and accumulate**. Assign-mixed-with-anything or additive-mixed-with-scaling → reject.

  **PDDL collapses each snap to one assignment per fluent** via `action_numeric_update_function_simplified`
  (`…:820`: `Assign` wins; else fold scalings `l*s1*s2…`; else fold additives `l+e1+e2−d1…`), all RHS
  read from the **pre-state**. That single-assignment-per-fluent form is *exactly* the abstract
  `(f, nexp)`. So the abstract `upds` is **functional by construction** — `upds_functional` is an
  *invariant established by the combination normalization* (§A.3), not a restriction; `apply_upds` reads
  every RHS from the pre-state, so the abstract layer is **faithful with no self-read condition**.
  Three corrections to the earlier draft: **(a)** `upds_functional`, not "no fluent assigned twice," is
  the condition — same-fluent additive (or scaling) effects of one action are **combined** into one
  assignment (§A.3), not rejected. **(b) The happening update is a sequential `fold`, not a set-union.**
  PDDL's `action_list_numeric_update_function = fold (∘) (map action_numeric_update_function A) id` (each
  action reads the *running* state), and Munta's interleaved zero-delay edges do the same. So **co-occurring
  additive writes of one fluent accumulate** (`f+ea` then `+eb`) — there is **no fail-closed restriction on
  additive co-writes** (my earlier "reject additive co-writes" caveat was wrong; the set-union dedup that
  motivated it was the wrong abstraction). The abstract `happening_num_update = fold snap_num_update`
  mirrors this. **(c) Non-interference is enforced by clocks, not by an update-level guard.** `mutex` /
  `acts_non_intrf` pairs are forced ε-apart and never co-occur, so a happening contains only **commuting**
  (non-interfering) snaps; the sole obligation is order-independence of the fold under non-interference
  (PDDL's `same_actions_then_happening_numeric_update_function_equal`).

  **Munta cross-reads (Layer-B obligation, *not* a PDDL rule).** Munta edge updates apply sequentially
  (`is_upds`/`mk_upds = fold`, each RHS read from the running store), so an update RHS reading a *different*
  update's LHS is order-sensitive. (Reading its **own** LHS is fine: `(f, f+e)` reads the old `f` — that's
  how additive effects encode.) Between two distinct co-occurring actions this **cannot** happen:
  `acts_non_intrf` already gives `lvalues_a ∩ rvalues_b = ∅` (FL03), so **no-cross-read is a theorem from
  PDDL non-interference**, not a check we add. The only residual is *within one action* — one snap's
  combined `(f, …g…)` reading another fluent `g` the same snap writes, which `numeric_effects_non_intrf`
  does not forbid: emit in a topological order, reject only a genuine read/write **cycle**. Gigante has none
  (RHS are constants or static fluents). The own-LHS exclusion matters: the Layer-B condition is
  `nexp_fluents e ∩ (writes − {f}) = {}`, *not* `∩ writes` (which would wrongly reject `(counter, counter+1)`).

### A.3 Boundary map (`Ground_PDDL`, Layer C): PDDL numeric_expression ⇒ abstract

With `'n := ground PNE`, `'r := rat`:

| PDDL | abstract | notes |
|---|---|---|
| `ConstantExpr c` | `NConst c` | |
| `FunctionExpr (PNE f args)` | `NVar (groundfluent f args)` | the fluent identity |
| `AddExpr/SubExpr/MulExpr/DivExpr` | `NAdd/NSub/NMul/NDiv` | |
| `DurationExpr` | — | only inside a duration constraint → bounds (§A.4); reject elsewhere |
| `SinExpr/CosExpr/ExpExpr/PiExpr` | **reject** | not in the supported (rational, bounded) fragment |
| `numericEqAtm/LEAtm/GEAtm/LessAtm/GreaterAtm` | `Comp Ceq/Cle/Cge/Clt/Cgt` | numeric conditions |
| `NumericEffect Assign  f e` | `(f, e)` | only writer of `f` (else reject — `numeric_effects_non_intrf`) |
| `NumericEffect Increase f e` | contributes `+e` to `f`'s combined rhs | combined, not a standalone set element |
| `NumericEffect Decrease f e` | contributes `−e` to `f`'s combined rhs | |
| `NumericEffect ScaleUp  f e` | contributes `×e` to `f`'s combined rhs | unused in Gigante |
| `NumericEffect ScaleDown f e` | contributes `÷e` to `f`'s combined rhs | unused in Gigante |

**Numeric-effect combination — a normalization stage (reuse, don't reinvent).** The rows above are
*per-effect contributions*: a snap's `upds` must hold **one `(f, nexp)` per fluent**, so multiple
same-fluent effects are first **combined** into a single assignment. PDDL already defines this and proves
it correct — `action_numeric_update_function_simplified` (`Continuous_Planning/Numeric_Update_Functions.thy`:
`Assign` wins; else fold scalings; else fold additives, via `combine_additive_numeric_effects` /
`combine_scaling_numeric_effects`). So the boundary reads each ground action's combined per-lvalue
expression straight from that function — this is **another normalization stage**, sibling to §D
time-rescaling, gated by `numeric_effects_non_intrf` (reject conflicting `Assign`s / mixed types,
fail-closed). It makes the abstract `upds_functional` hold by construction.

`at_start/at_end` conditions+effects attach to the corresponding snap; `over_all` numeric conditions →
`n_inv`. Per the Gigante survey (`gigante_benchmarks_conditions_effects.md`, copied into this repo) the
inputs use only `≥ ≤ =` and `increase/decrease/assign`, with `+ − × ÷` confined to duration
expressions — so the supported fragment covers every benchmark while the boundary map still *rejects*
anything outside it (fail-closed).

### A.4 Numeric duration constraints

`duration_constraint = DurationConstraint d_op expr`. After grounding, `expr` must reduce to a **value
constant** (Gigante: `(= ?duration k)`, or fluent-/arith-defined durations that ground to a constant —
spike 3 must confirm constant-ness, else reject). Feed the existing bounds: `EQ k` → `lower := GE k ∧
upper := LE k`; `GEQ k` → `lower := GE k`; `LEQ k` → `upper := LE k`. No new clock machinery — the
`lower_bound`/`upper_bound` reduction is reused; only its source (a numeric expr instead of a literal)
changes, plus the integer-value requirement at the Munta boundary.

### A.5 Reduction map (`TP_NTA_Reduction_Defs`, Layer B): abstract ⇒ Munta

Munta side is `(String.literal, int) bexp/exp` (§2). With `'r = rat` but Munta vars `int`, the boundary
additionally requires each reachable fluent value to be an **integer in `[lo,hi]`** (fail-closed
otherwise — spike 2):

- `fluent_to_var :: 'n ⇒ String.literal` (cf. `prop_to_var`); declare `(var, lo, hi)` in `all_vars`.
- `nexp ⇒ exp`: `NConst c ↦ exp.const ⌊c⌋`, `NVar f ↦ exp.var (fluent_to_var f)`,
  `NAdd/NSub/NMul ↦ binop (+)/(−)/(×)`, `NDiv ↦ binop (div)` — **integer-division semantic gap**: PDDL
  `/` is rational, `div` truncates; only sound when divisions are exact or the fragment excludes `NDiv`
  in effects/conditions (it only occurs in durations, which pre-evaluate to a constant). Flag in the
  checker.
- `comp ⇒ bexp`: `Comp Ceq ↦ bexp.eq`, `Cle ↦ le`, `Cge ↦ ge`, `Clt ↦ lt`, `Cgt ↦ gt`.
- `n_pre` (at_start/at_end) → guard appended to `start_edge`/`end_edge` `var_check`.
- `n_inv` (over_all) → guard replicated on the running-location transitions (`edge_2`/`edge_3`
  `check_invs`), exactly where the propositional `over_all` `is_prop_ab 1` guards already hang.
- `upds` → `(fluent_to_var f, nexp⇒exp)` appended **after** the propositional `set_prop_ab/inc_prop_ab`
  updates on the start/end edge, under the §A.2 well-formedness (no intra-snap read-after-write).

### A.6 Proof architecture (`TP_NTA_Reduction_Correctness`) — additive tracking, NOT a new bisimulation

**Decided 2026-06-19 (supersedes the earlier "state relation gains a numeric component / dominant
cost" framing).** The unsolvability capstone uses only the **completeness** direction
(`valid_temp_plan_imp_form_holds`: `valid_plan ⟹ ∃` goal-reaching network run). For *that* direction
numerics are an **additive, deterministic, pruning-only** layer on the run the existing reduction
already produces — so we **reuse** the 456 KB propositional bisimulation unchanged and add two small
lemmas on top, rather than re-relating the numeric valuation to the Munta store inside the
bisimulation. The mechanism (this is exactly what the Layer-A "collapse" machinery, the numeric twins
in `Temporal_Plans_Instances`, was built to support):

1. **Projection** `num_valid_plan ⟹ valid_plan` (Layer-A, new but easy): the propositional part of a
   numerically-valid state sequence is propositionally valid — numeric conditions only *add*
   constraints. (Non-empty generalization of the empty-case `collapse_num_valid_plan`.)
2. **Reuse**: feed that `valid_plan` to the existing capstone → the propositional goal-reaching run.
   The 456 KB proof is untouched; numerics only *enlarge* the variable store and *prune* via guards,
   so the propositional reachability is exactly the projection of the augmented net's (Munta networks
   are products over a shared store — confirm the existing proof tolerates the extra `fluent_to_var`
   vars; see §5.5).
3. **Tracking lemma** (the one genuinely new reduction lemma): along *that* run, the Munta numeric
   vars equal the abstract numeric valuation. Munta's `mk_upds`/`is_upds` is the sequential fold
   already shown to equal the abstract `happening_num_update` (verified against the source,
   2026-06-19); so the `(fluent_to_var f, nexp⇒exp)` edge updates reproduce the abstract valuation
   step for step. Then `num_valid_state_sequence` — which says those abstract valuations satisfy the
   numeric guards and reach `num_goal` — gives directly that the run satisfies the appended `bexp`
   guards and reaches the numeric goal. So the run survives in the augmented net.

Net result: `num_valid_plan ⟹` augmented-net goal run, i.e. a numeric capstone
`numeric_valid_temp_plan_imp_form_holds'` with a numeric `reach_formula`, **without** opening the
bisimulation. The two real costs move to (a) the additive *spec* augmentation (§A.5) arranged so
numeric vars never gate propositional edges, and (b) static **bounds** (§B) wide enough that the real
trajectory stays in-bounds (else fail-closed). Remaining `nexp⇒exp` obligations (effect application
commutes with `is_upds` under no-read-after-write; `comp` guard ⇔ `check_bexp`; over_all numeric
invariance across the open interval) are *local* facts about the edge encoding, not bisimulation
surgery.

> **Soundness direction** (`run ⟹ plan`) would still need the harder valuation-in-the-bisimulation
> argument — but the unsolvability capstone never uses it, so it is out of scope until/unless a
> *solvability* certificate is wanted.

## B. Static variable bounds — how to compute and prove them

**Why it is subtle.** Munta requires `bounded bounds s ∧ bounded bounds s'` on *every* transition
(`Simple_Network_Language.thy:206-207`), so an out-of-range update **disables** the edge (no wrap, no
clamp). The unsolvability capstone runs the **completeness** direction — *every valid plan* must map to
a goal-reaching network run. Hence a bound that is **too narrow blocks a real plan ⇒ false "unsolvable"
(unsound)**; a bound that is **too wide is always safe** (it only enlarges the state space, and any
extra spurious runs only make the goal *more* reachable, i.e. at worst we fail to certify —
conservative). **Conclusion: bounds must over-approximate the reachable value set; if a fluent is
unboundedly reachable, reject.**

**Why we bound at all, and why object bounds in particular.** Every numeric fluent we keep becomes a
Munta `int` variable, and Munta requires *every* variable to carry a declared `[lo,hi]`. So a fluent
with no provable finite bound is not representable → reject. For an **increment-only** fluent (painter's
`counter`) there is no constant cap; its only finite ceiling comes from the equality guard against the
**static, object-derived** `item_id` (case (b)) — that is the *object bound*. It matters because the
impossible instances are impossible *because of* that numeric guard: **painter-impossible is unsolvable
precisely because the `(= item_id counter)` matching can never complete.** To *certify* that
unsolvability the network must represent `counter` faithfully — drop or mis-bound it and the network
gains spurious runs, the goal looks reachable, and we fail to certify the very family we target. Note:
without object bounds we are never *unsound* (too-permissive is conservative for unsolvability), only
*incomplete* on exactly those instances. And this is about **provability, not tightness** — any
over-approximating bound works, but for an increment-only counter the static-fluent/object cap is the
*only* finite bound we can actually prove; a guessed constant is not justified.

**Split: untrusted compute, verified check** (mirrors the repo's certificate philosophy).

1. **Compute candidates (untrusted).** A static interval analysis over the ground task proposes
   `[lo f, hi f]` per fluent: start from each fluent's init value; for every ground snap effect `(f, e)`
   widen by interval arithmetic over the current box (`assign` → include `e`'s interval;
   `increase/decrease c` → shift); least fixpoint. Convergence to a finite box ⇒ candidate bounds; a
   diverging fluent (uncapped monotone counter) ⇒ no static bound. This computation is **not trusted** —
   it only proposes the box.

2. **Verify a decidable sufficient condition (trusted, in the checker).** The checker accepts the box
   only when the ground task matches one of these *syntactic* patterns, each of which **implies** the
   inductive invariant below:
   - **(a) finite-value fluents** — `f` is inited to a constant and only ever `assign`ed constants ⇒
     reachable `f ∈ {init} ∪ {assigned constants}` (finite; box = its hull). Trivial.
   - **(b) comparison-capped monotone fluents** — `f` is only increased (resp. only decreased) and every
     snap carrying an increasing (resp. decreasing) effect on `f` is guarded by an `n_pre` comparison
     (`f ≤/=/< g`, resp. `f ≥/=/> g`) where the cap `g` is either a **constant** or a **static** fluent
     (never an effect target). The guard disables the action once the cap is reached ⇒
     `f ∈ [init, capmax + Δ]`, where `capmax` is the constant, or `max` of the static fluent's value-set,
     and `Δ` the max single increment. **Object-counts enter here:** a static fluent assigned from the
     finite ground object universe has a *finite* value-set, so `capmax` exists and is computed from
     init. The painter counter is this case: `(increase (counter) 1)` guarded by `(= (item_id ?i)
     (counter ?t))` with `item_id` static ⇒ `counter ≤ max(item_id) + 1`.
   - **(c) domain-declared bounded-int fluents** — the `_integers` Gigante variants ship explicit ranges;
     still reduce to (a)/(b) to show effects+guards respect them.
   - **(d) otherwise reject** (fail-closed — we simply do not certify unsolvability, which is sound).

3. **Prove the bounds sound (once, generically, Layer A).** A single inductive invariant on the
   *abstract* happening semantics, independent of Munta:
   `INV s ≡ (∀f. lo f ≤ the (snd s f) ≤ hi f)` (on defined fluents). Meta-theorem
   `wf_bounds task ⟹ reachable task s ⟹ INV s`, where `wf_bounds` is the §B.2 side-condition: *base*
   from the init box (checkable); *step* — each snap preserves `INV` because (a)/(b) bound each effect's
   result, and in case (b) the snap is applicable only when its `n_pre` cap held. Layer B's
   completeness lemma then takes `INV` as a hypothesis: every reachable abstract state maps to a
   `bounded` Munta store, so no real plan's run is ever blocked.

So we never trust the interval fixpoint — we trust only the cheap, decidable `wf_bounds` check plus the
once-proved `INV` meta-theorem. `wf_bounds` lives in `Ground_PDDL_Problem_Defs` (Layer C); `INV` is
proved over the happening semantics (Layer A); the bisimulation (Layer B) consumes it.

## C. Coverage against Gigante (checked against the actual domain files, 2026-06-19)

*Source: the Gigante et al. AAAI 2022 artifact, `expeval/benchmarks/` tree (locally at
`~/Downloads/AAAI2022/expeval/benchmarks/`) — the same tree the survey
(`gigante_benchmarks_conditions_effects.md`) summarizes. Line numbers below are into those `.pddl`
files.*

The numeric **comparison conditions are fully covered** — every condition in the benchmark set is
`>=`/`<=`/`=` over fluents (no strict `< >`, no disjunction, no scale), so each maps to a Munta `bexp`.
Coverage gaps are **not** in the conditions; they are in durations and bound-provability:

| Item | Verified in | Status |
|---|---|---|
| `(>= (battery-level ?r) (distance ?from ?to))` + `(decrease battery distance)` | `majsp/pddl21/domain.pddl:45,51` | ✅ condition maps to `bexp.ge`; bound via **case (b)** — decrease guarded by the `>=`, so `battery ∈ [0, init]`. `distance` static ⇒ **case (a)** |
| `(= (item_id ?i) (counter ?t))` + `(increase (counter) 1)` / `(assign (counter) 0)` | `painter-impossible/pddl21/domain_container.pddl:69,80,56` | ✅ condition maps to `bexp.eq`; **bound fits the extended case (b)** — `counter` is increment-only, *equality-capped* against the **static** `item_id`, so `counter ≤ max(item_id)+1` (finite because `item_id` is assigned over the finite ground object set). `item_id` static ⇒ (a) |
| **Non-integer durations** `(= ?duration 0.1)`, `0.03`, `15.004` | `majsp:90,112`; `painter:126` | ❌ **biggest real gap.** Munta clock bounds are `int` (`acconstraint … int`). Either globally **rescale time** by the LCD of all durations (0.1,0.03→×100; 15.004→×1000 — a sound new pipeline step touching ε and every clock constant) or **reject**. Affects domains whose *conditions* are otherwise fine |
| Rational/arith durations `(/ distance speed)`, `(* distance build-time)` | Mapanalyser | ❌/⚠️ static-fluent operands ⇒ grounds to a *rational* constant ⇒ same int-clock gap; needs rescaling or reject (and the operand fluents must be **static** — spike 3) |
| `forall`-quantified conditions/effects (sync) | survey | out of scope here — **propositional**, expanded to conjunctions by the grounder, not numeric |
| `:uncontrollable-durative-action` (adversarial duration in `[a,b]`) | uncertainty-ipc | out of scope — timed-**game** semantics, orthogonal to numerics |

**Takeaway.** Conditions: covered everywhere. Bounds: majsp `battery` and the painter `counter` both
fit case (b) (constant-/static-capped). The remaining blocker to running majsp/painter end-to-end is the
single item **(i) time-rescaling** for non-integer durations (§D). Until it lands those domains are
**rejected** (fail-closed) — sound but not yet complete. MatchCellar / sync-impossible (the current
propositional examples) and any integer-duration domain are covered without it.

## D. Time-rescaling stage (non-integer durations)

**Current hook.** Durations already flow as `rat` through the pipeline: `dc_to_lb`/`dc_to_ub ::
term duration_constraint ⇒ rat lower_bound/upper_bound`, and `lower_spec`/`upper_spec` convert to `int`
via `map_lower_bound floor` / `map_upper_bound floor`
(`Ground_PDDL_Problem_Defs.thy:163-179,263-267`). The floor is only *exact* because `act_dcs_integers`
(via `duration_constraint_integer`, requiring `is_integer x`) **rejects** non-integer durations up front.
`ε :: int` (`TP_NTA_Reduction_Defs.thy:83`). So today majsp `0.1`/`0.03`, painter `15.004` are rejected
at `act_dcs_integers`. **Rescaling replaces that rejection with a normalization.**

**The transform** (a Layer-C, `rat ⇒ rat` preprocessing that lands on integers, *before* the `floor`):
1. Collect every duration constant `x` (the `rat` in `Time_Const _ x`) across all ground actions, plus
   `ε`. Let `k = lcm` of their denominators (a positive `int`).
2. `rescale_task k`: multiply every duration constant **and `ε`** by `k`. Everything else — props,
   numeric fluents, numeric conditions/effects, the §A `nexp`/`comp`/`upds` — is **untouched**;
   rescaling is purely temporal.
3. Now every duration is integer-valued ⇒ `act_dcs_integers` holds ⇒ the existing `floor` is exact ⇒
   the existing integer-clock reduction (Layer B) applies **unchanged**. `act_dcs_integers` stays as a
   post-condition (must pass after rescaling, else the input arithmetic was malformed).

**Soundness — a plan-time bijection.** Prove
`valid_ground_plan task π ⟷ valid_ground_plan (rescale_task k) (scale_time k π)`, where `scale_time k`
multiplies every plan timestamp by `k`. It holds because temporal validity is a conjunction of
constraints each **homogeneous of degree 1 in time**: duration bounds `t_end − t_start ∈ [l,u]`,
ε-separation `|t_i − t_j| ≥ ε` (and the `=` cases), and `over_all` open-interval membership. Scaling
time *and* all temporal constants by the same `k > 0` preserves each. Hence
`(∄π. valid task π) ⟷ (∄π'. valid (rescale_task k) π')` — **unsolvability is preserved**, so certifying
the rescaled task certifies the original.

**Scope notes / caveats.**
- This handles **time** only. **Rational *fluent values*** (a rational `distance`, `battery`, …) are a
  *separate* axis, still governed by the int-fluent restriction / a future fixed-point scaling (§2) —
  do not conflate. majsp's `0.1`/`0.03` are durations (fixed by §D); whether its `distance`/`battery`
  are integers is the other axis.
- `ε` scales with `k`, so the relative event-separation granularity is preserved; `ε·k` stays integral.
- `k` is the lcm of denominators — it can grow large (→ larger clock constants → bigger DBM/state
  space). Usually small in practice (`×100`, `×1000`); note it but do not optimize prematurely.
- Where it lives: a small new transform in/near `Ground_PDDL_Problem_Defs` with a self-contained
  plan-bijection lemma; slots into the pipeline just before `lower_spec`/`upper_spec`.

## 3. The three layers to extend

### Layer A — abstract plan model (`Temporal_Planning_Semantics/Temporal_Plans.thy`)

Currently purely propositional: `type_synonym 'p state = "'p set"`; snap actions are
`pre/adds/dels :: 'p set`; locales `action_defs`, `temp_planning_problem`, `temp_plan_defs`, …

Changes:
- Generalize state to carry a numeric valuation: `state = 'p set × ('f ⇒ int)` (or a record). Keep a
  propositional projection so existing lemmas degrade gracefully.
- Snap actions gain `num_pre :: numeric condition set`, `num_eff :: numeric assignment list`
  (ordered — effect order matters for `Increase`/`Decrease` chains within one snap).
- Define numeric-condition satisfaction and numeric-effect application; re-state the happening
  semantics (`apply` of a snap, `over_all` invariance across the open interval) over the extended
  state.
- Re-prove the structural lemmas that the reduction relies on (the `action_defs*` /
  `temp_plan_defs` hierarchy). Most propositional lemmas should be **orthogonal** to numerics; the
  risk is the mutex / no-moving-target invariants that assume `adds/dels` are the only state change.

This is where most *proof* churn lives: `Temporal_Plans.thy` is ~128 KB of locale theory and its
instances (`Temporal_Plans_Instances.thy`, `Temporal_Plans_Theory.thy`).

### Layer B — NTA reduction (`TA_Network/`)

`TP_NTA_Reduction_Defs.thy` builds one automaton per action plus a main automaton; props become int
vars; clocks track snap timing. Changes:
- **Variable set**: extend `all_vars` with one bounded int var per numeric fluent
  (`fluent_to_var`, alongside `prop_to_var`/`prop_to_lock`), with bounds from the problem's declared
  ranges.
- **Guards**: numeric `at_start`/`at_end` conditions → `bexp` on `start_edge`/`end_edge`;
  `over_all` numeric conditions → guard replicated on the internal/loop transitions of the running
  location (the existing `over_all` propositional handling shows the pattern).
- **Updates**: numeric effects → `(var, exp)` updates on the start/end edges, appended after the
  propositional `set_prop_ab`/`inc_prop_ab` updates, respecting effect order.
- **Duration**: generalize `l_dur`/`u_dur` to numeric duration constraints reduced to
  integer clock bounds (requires the durations to be integer-valued after grounding — see §5.2).
- **Correctness — additive tracking, NOT a bisimulation rewrite (see §A.6).** The augmentation is
  arranged so numeric vars only *prune* (never gate propositional edges), so the existing ~456 KB
  `TP_NTA_Reduction_Correctness` proof is **reused on the propositional projection**. On top of it:
  the Layer-A projection `num_valid_plan ⟹ valid_plan` reuses the existing capstone run, and a single
  **tracking lemma** (Munta numeric vars = abstract valuation along that run, via `mk_upds =
  happening_num_update`) plus `num_valid_state_sequence` discharge the numeric guards and goal. The
  real costs are the additive spec above and the static bounds (§B), not bisimulation surgery. This
  is the architecture the Layer-A "collapse" twins (`Temporal_Plans_Instances`) were built to feed.

### Layer C — ground PDDL defs + reduction wiring (`Ground_PDDL_Exec_Imp/`)

`Ground_PDDL_Problem_Defs.thy` today restricts to numeric-free (`act_no_func_dcs`, integer
durations, positive preconditions). Changes:
- Drop `act_no_func_dcs`; add ground numeric fluents to `init_spec`/`goal_spec` analogs (initial
  numeric assignment, numeric goal conditions).
- Generalize `pre_spec`/`adds_spec`/`dels_spec` snap projections to also project numeric
  conditions/effects (`num_pre_spec`, `num_eff_spec`).
- Re-establish `check_ground_problem` and the `Ground_PDDL_NTA_Reduction_Impl` codegen with the new
  fields; extend `Check_Unsolvability` / `Unsolvability_Code_Compile` exports.
- Compose with Layer A/B to keep `Ground_PDDL_NTA_Reduction_Correctness`.

## 4. Prerequisite (shared with the grounding plan): re-point onto the new semantics

Same P0 as [GROUNDING_PLAN.md §3](GROUNDING_PLAN.md): move `Ground_PDDL_Exec_Imp/*` and `TA_Network/*`
off the old `Temporal_AI_Planning_Languages_Semantics` onto Formal-PDDL-Semantics `Temporal_Planning`.
The new semantics **already defines** the numeric abstract syntax and a numeric checker
(`Temporal_PDDL_Checker_Numeric`, built on `Continuous_Planning`'s `numeric_effect`,
`numeric_expression`, `PNE`, numeric `duration_constraint`). So the **input/spec** side of numerics
is largely supplied by the new semantics — this plan's work is the abstract **model**, the
**reduction**, and the **proofs**, not re-deriving PDDL numeric syntax.

**Reuse the normalized signatures.** Function declarations live in the shared
`Continuous_Planning/Signatures.thy` (`domain_signature`/`problem_signature` already carry `func`
decls and `wf_function_decl`), so the numeric *signature* (which functions exist, their arg types)
and its normalization are reused exactly as in the grounding plan — see
[GROUNDING_PLAN.md §2](GROUNDING_PLAN.md). Numerics add no new signature machinery; they add
*state* (the fluent valuation), *conditions*, *effects*, and the reduction of those.

**Documentation** follows the classical grounder's conventions (stage table, trust story, HANDOVER
inventory, per-stage three-file pattern) — see [GROUNDING_PLAN.md §9](GROUNDING_PLAN.md).

## 5. Things to verify early (cheap, de-risks the big proofs)

1. **`Simple_Expressions.exp` arithmetic — RESOLVED (2026-06-19).** `exp = const 'b | var 'a |
   if_then_else | binop "'b⇒'b⇒'b" exp exp | unop "'b⇒'b" exp`, and `bexp = true | not | and | or |
   imply | eq | le | lt | ge | gt`. `binop` is an *arbitrary HOL function*, so `+ − × ÷` and every
   comparison `= ≤ ≥ < >` are all expressible over the (`int`) variable type. Operator set is **not**
   the limiter; the limiter is **`int` vs `rat`** (`numeric_expression` is `rat`-valued; Munta vars
   are bounded `int`) and **bound/overflow**. So the fragment restriction is on values/bounds, not on
   which arithmetic appears — see §A and spikes 2–3.
2. **Variable bounds — RESOLVED in shape (2026-06-19); see §B.** Munta **disables** any step whose
   update leaves a variable's `[lo,hi]` (`Simple_Network_Language.thy:206-207`: every transition
   requires `bounded bounds s ∧ bounded bounds s'`; it does *not* wrap). Because the capstone uses the
   **completeness** direction (plan ⟹ goal-reaching network run), a *too-narrow* bound blocks a real
   plan's run and would **falsely certify unsolvable** — so bounds must **over-approximate** the
   reachable value set (err wide; too-wide only costs state-space, spurious wide runs are conservative);
   if a value is unboundedly reachable, **reject** (fail-closed). See §B for how we compute and prove
   them.
3. **Integer durations after numeric durations** — `duration_constraint` is now a numeric expression;
   the clock-bound reduction needs an integer value. Confirm grounding yields integer-constant
   durations (or restrict the fragment).
4. **Over-all numeric invariants** — confirm the existing `over_all` propositional encoding (guard on
   the running location's transitions) is the right place to hang numeric invariants, and that the
   no-overlap/mutex argument still closes with numeric state.
5. **Existing proof tolerates extra net variables (the §A.6 keystone, do FIRST of the Layer-B
   spikes).** The additive-tracking architecture rests on: enlarging `all_vars` with
   `fluent_to_var` vars, and appending numeric `bexp` guards / `(var,exp)` updates to edges, does
   **not** disturb the existing ~456 KB propositional bisimulation — i.e. propositional reachability
   in the augmented net is exactly the projection of the propositional net's, because numeric vars are
   only read by numeric guards and written by numeric updates (they never gate a propositional edge,
   and Munta networks are products over a shared store). Probe cheaply: add one dummy bounded int var
   + a trivially-true guard to the spec and confirm the capstone still closes (or localize which
   lemmas inspect the *full* variable set vs. the propositional projection). If some lemma is brittle
   to the variable set, that lemma — not the whole proof — is the work; convert it to project first.

## 6. Interlock with the grounding plan

- The grounder must **ground numeric fluents and carry numeric effects/conditions through**. The
  **emitted ground task keeps every numeric condition and effect** (they become Layer C's `n_pre` /
  `n_inv` / `upds` and then Munta `bexp` guards + `(var,exp)` updates, §A) — grounding does *not* erase
  comparisons. Separately, the grounder's **internal reachability analysis** (deciding which ground
  actions to instantiate) **tracks fluent *definedness* but ignores comparison *values*** (sound
  over-approx — a numeric guard only ever prunes, so ignoring it keeps the action set a superset). Definedness `defined!f(args)` is a datalog predicate:
  EDB from init assignments, derived head from numeric assignment effects, body atom from `pre_s`
  numeric comparisons **and from every PNE in the duration constraint** (`(= ?duration expr)` needs
  `expr`'s fluents defined). `fluents ↔ PNEs`: a fluent is a ground `PNE func args`, its definedness
  is `defined!func(args)`. See [GROUNDING_PLAN.md §4, §7](GROUNDING_PLAN.md).
- Land order: **this plan's Layer A + B (+ C) first** (semantics + reduction can be exercised on
  hand-written ground numeric instances), **then** flip the grounder's numeric-free check into
  "ground numerics through". The grounder needs the ground numeric task *shape* (Layer C) to exist as
  its output type, so Layer C's `ground_ast_problem` extension is the shared contract.

## 7. Phase breakdown

- **P0** (shared): re-point onto `Temporal_Planning` (new semantics), green. [§4]
- **P1**: §5 verification spikes (Munta `exp`/`bexp`, bounds, durations). Small, decisive.
- **P2 (Layer A)**: extend `Temporal_Plans` state + snap numerics + happening semantics; re-prove the
  locale hierarchy. Largest *model* change. **DONE (2026-06-19)** incl. the abstract→reduction
  "collapse" twins in `Temporal_Plans_Instances` and the empty-numeric capstone
  `numeric_valid_temp_plan_imp_form_holds` (green). Remaining Layer-A piece: the general projection
  `num_valid_plan ⟹ valid_plan` (§A.6 step 1) — needed by P4.
- **P3 (Layer C)**: extend `Ground_PDDL_Problem_Defs` to numeric ground tasks + `check_ground_problem`
  (no proofs yet beyond well-formedness) — gives the grounder its output contract early. Includes the
  boundary map (§A.3), the `wf_bounds` static-bound check (§B), and the **time-rescaling** transform +
  plan-bijection lemma (§D, replaces the `act_dcs_integers` rejection).
- **P4 (Layer B) — additive tracking, reusing the existing bisimulation (§A.6)**: numeric
  variables/guards/updates in `TP_NTA_Reduction_Defs` arranged so numeric vars only *prune*; then the
  projection lemma + the single tracking lemma (`mk_upds = happening_num_update`) + bounds (§B) give
  the numeric capstone **without** reworking `TP_NTA_Reduction_Correctness`. Do §5.5 (extra-vars
  tolerance) first — it is the keystone assumption. Much smaller than the old "rewrite the
  bisimulation" plan.
- **P5**: re-close `Ground_PDDL_NTA_Reduction_Correctness`; regenerate code export
  (`Unsolvability_Code_Export`), update `run.sh`/Python harness, validate on a numeric instance
  (`Formal-PDDL-Semantics/examples/counters`, `expedition`, `transport`).
- **P6**: `Index.thy` entry for the numeric capstone theorem.

## 8. Risks

- **Keystone risk (replaces the old "456 KB bisimulation is the dominant cost"):** the additive-tracking
  architecture (§A.6) assumes enlarging the Munta variable store + appending numeric guards/updates
  leaves the existing ~456 KB propositional bisimulation **reusable on the propositional projection**.
  If some correctness lemma inspects the *full* variable set rather than the propositional projection,
  it breaks under the extra `fluent_to_var` vars. *Probe this first* (§5.5) — it decides whether the
  whole "reuse, don't rewrite" plan holds. If it fails for a few lemmas, those lemmas (convert to
  project-then-reason) are the cost — still far below rewriting the bisimulation. Keep the extension
  *additive*; never re-encode props as 0/1 numerics (that genuinely would destabilize the proof). The
  file is also ~18% long `apply`-chains (1609 lines), brittle under any change to what they see —
  convert the ones you touch to structured Isar first (see [HANDOVER.md](HANDOVER.md) next-step 5).
- **Bounded-int semantics gap** between PDDL numerics (unbounded ℤ/ℚ) and Munta (bounded ℤ): the
  fail-closed well-formedness fragment must be precisely stated and *proven* to be the exact domain
  where the reduction is faithful.
- **Continuous numerics are out of scope** but present in the new semantics (`Continuous_Planning`):
  the checker must reject continuous-change actions for the TA reduction, and this must be visible to
  the grounding pipeline.
- Effect ordering and start/end simultaneity (two snaps at the same time touching the same fluent) —
  the existing propositional mutex story must be re-examined for numeric read/write conflicts.

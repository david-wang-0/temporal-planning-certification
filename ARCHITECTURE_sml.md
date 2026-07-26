# ARCHITECTURE — the `plan_cert` SML harness

How the untrusted SML driver around the verified Isabelle core works. This is the *harness*: it
parses PDDL, grounds it, infers numeric bounds, drives the external timed-automata oracle, and
plumbs certificates in and out — but the **soundness-bearing steps are all in the Isabelle export**
(`Converter`), not here. Companion docs: `ARCHITECTURE_pipeline.md` / `ARCHITECTURE_grounding.md`
(the verified reduction), `NUMERIC_PLAN.md` / `NUMERIC_BOUND_INFERENCE.md` (the numeric contract).
All sources are under `ML/plan_cert/src/`; the Isabelle-generated code is `ML/Check_Unsolvability.ML`.

## The trust boundary (read this first)

Everything the harness does is **untrusted**. It can only ever produce a certificate that the
verified checker then *accepts or rejects*; it cannot make an unsound "unsolvable" verdict slip
through. Exactly two things are trusted, both inside `Converter`:

1. **The static bound gate** `is_gbound_inv_exec` (`check_gbounds_opt`) — re-checks any inferred
   fluent box before the net is built; fails closed.
2. **Munta's verified certificate checker** `convert_check` (via `check_and_cert_*` /
   `parse_convert_check`) — validates the returned zone-graph certificate against the built net;
   acceptance is a machine-checked proof of goal-unreachability, hence (by the Isabelle-proved
   reduction) of plan non-existence.

So when reading the harness, the useful question is never "is this sound?" (it can't break
soundness) but "does this produce a *checkable* certificate, and does it fail *closed* when it
can't?" Every untrusted stage below — nemo pruning, the box projection, the net→muntax→tck→cert
path — is fail-open or fail-closed by design, with the two trusted steps as the only gates.

## Build composition

`ML/plan_cert/src/plan_cert.mlb` links, in order: the Isabelle export (`../converter.mlb`), the
PDDL parser (`parsing/pddl_validate_plan.mlb`), the net + certificate converters
(`network_conversion/`, `certificate_conversion/`), the mlunta certificate (de)serializer
(`../imports/mlunta_certificate.mlb`), then the leaf modules `mlunta_adapter.sml`,
`tchecker_certify.sml`, the numeric bound glue (`numeric_glue/`), `nemo_reach.sml`, `grounder.sml`,
`inprocess_certify.sml`, and finally `plan_cert.sml` + `Mlton_Main.sml` (the `main ()` entry).
Built with MLton (`make -C ML out/plan_cert`).

`ML/converter.mlb` is the boundary: it splices `Check_Unsolvability.ML` (one large
Isabelle-generated file) under `ann "nonexhaustiveMatch ignore"`, plus a `term_stub.sml` so the
numeric export's typerep machinery type-checks (never called on the cert path), and exports exactly
three structures: `Timing`, `Tracing`, `Converter`. `Converter` is the **real** export structure,
not an alias — the alias goes the other way (`parsing/converter_alias.sml` defines
`Continuous_PDDL_Checker_Exported = Converter` so the vendored FPS parser compiles unchanged).

## `Converter` — the Isabelle export (the trusted core)

Everything verified lives in this one structure: the propositional and numeric net builders, the
reduction-side snap projection, the bound gate, and Munta's checker. Key entry points the harness
calls (SML signatures in `Check_Unsolvability.ML`):

- `check_and_make_network_opt : … ast_problem -> (…net…) option` — propositional net builder.
- `check_and_make_numeric_network_opt : … ast_problem -> box -> (…net…) option` — numeric net
  builder; re-checks the box with the trusted `is_gbound_inv_exec` gate before trusting it.
- `numeric_draft_actions : … ast_problem -> string list * ((g_int list * (string * e_int) list) list * (string * inta) list)`
  — reduction-side projection of a ground problem into the `(fluents, (snaps, init))` draft the
  bound glue consumes.
- `check_gbounds_opt : … ast_problem -> box -> bool` — the trusted static bound re-check
  (`is_gbound_inv'`), fails closed.
- `check_and_cert_numeric_pddl_problem_no_return : … ast_problem -> box -> mode -> nat -> (net -> (renaming * inta state_space) option) -> bool -> (unit -> unit)`
  — **the verified numeric capstone**. Re-checks the gate, builds the net, hands it *in-process* to
  the untrusted oracle closure (5th arg), then verifies the returned certificate with `convert_check`.
- `check_numeric_admission_diag_opt : … -> nat` — first-failing admission clause # for diagnostics.
- `parse_convert_check : mode -> nat -> bool -> string -> string -> inta state_space -> bool -> (unit -> unit)`
  — Munta's verified checker (same entry the external `muntac` binary wraps), used by the standalone
  `InProcessCertify.check_and_cert` path.

Datatypes the harness manipulates: the arbitrary-precision wrappers `inta = Int_of_integer of int`
(this is the int64 build, so `inta` is native), `nat`, `rat` (with `quotient_of`/`fract`); the
int-ified guard IR `cmp_op = Ceq|Cle|Cge|Clt|Cgt`, `e_int = EC|EV|EAdd|ESub|EMul|EDiv`,
`g_int = GCmp_i of cmp_op * e_int * e_int`; the whole PDDL AST (`ast_problem`, the
`SimpleActionSchemaa`/`DurativeActionSchema` schemas, `temporal_annotation = At_Start|Over_All|At_End`,
`ast_effect = Effect of …`); and the muntax net + certificate types (`bexp`, `exp`, `acconstraint`,
`dBMEntry = Le|Lt|INF`, `state_space = Reachable_Set|Buechi_Set`, `mode = Impl1|Impl2|Impl3|Buechi|Debug`).

## Front end — parse and ground

**`PddlParser` / `QAst` / `PDDL` (`parsing/`).** `pddl_refactor.sml` is the vendored
Formal-PDDL-Semantics parser-combinator grammar (on parcom), plus the quantifier-expansion passes.
`pddl_validate_plan.sml` translates PDDL into a `Converter … ast_problem` (the "C parse":
`Problem (Domain (types, preds, funcs, consts, actions), objs, init, goal)`).

- `get_prob D P : … ast_problem` — parse both files (BOM-stripped), then **Strategy B** (the
  default): `expandDomainQuant`/`expandProbQuant` eliminate every `forall`/`exists` over all problem
  objects *before* grounding, so the grounder sees quantifier-free formulas.
- `get_prob_q D P : QAst.qproblem` — **Strategy A** (`QUANT_EXPAND=grounded`): keep the binders in
  the intermediate `QAst` IR (`gform`/`geff`/`gteff`/`qschema`) and expand them *after* a schema's
  own params are substituted, so per-instance relaxation prunes more. `QAst` exists because
  `Converter` has no quantifier syntax — it sits between the PDDL→C translation and the grounder.

**`NemoReach` (`nemo_reach.sml`).** Builds a TFD-relaxed lifted datalog program from the parse, runs
the external `nmo` engine, and returns `reach_filter : … -> (string * object list -> bool) option` —
a predicate over ground object-tuples that keeps only datalog-reachable action instances. `NONE`
(binary missing / `NEMO_PRUNE=0` / any failure) = **fail-open**, no pruning, full cross-product;
pruning is a sound over-approximation of reachability, so it never removes a fireable instance.
Durative actions are *snap-split* (`a<i>s` start / `a<i>e :- a<i>s` end) so at-end/over-all
conditions on dynamic fluents prune soundly — see the module header and `ARCHITECTURE_grounding.md`.

**`Grounder` (`grounder.sml`).** Instantiates schemas over the type-consistent object cross-product
and propositionalises (objects inlined into hyphen-free 0-ary predicate/function names). Four
entries: `ground_problem[_q]` (propositional path — delete-relaxes numeric preconditions to
`def_<fluent>` definedness predicates, drops numeric effects) and `ground_problem_numeric[_q] filt`
(numeric path — **keeps** numeric pre/effects). The `filt` is the `NemoReach.reach_filter`,
applied as `List.filter (keep_tuple filt name) (cartesian cand)` before instantiation. Numeric-path
specifics: object-equality folding, static-fluent folding (statics inlined in *durations* and
*effect RHSs* only — guards keep fluent-vs-fluent for the verified relational bound layer),
`norm_cmp` operand normalization (constant to the right), and `scale_durations` (uniformly scale all
durations by the lcm of denominators to make them integer; strict no-op when already integer).
`problem_to_pddl` renders the ground problem back to PDDL for `-ground-out` inspection.

## Numeric bound inference — `NumericBoundGlue` (`numeric_glue/`)

Bridges the reduction-side draft to the compute-side interval AI. `numeric_code.mlb` isolates the
compute-side export `NumericBoundInference` (from `code/Numeric_Bound_Inference.ML`, an interval AI
over a HOL-IMP heap) so its top-level helpers don't clash with `Converter`. `infer_box : draft -> box option`
projects each reduction-side `g_int`/`e_int` snap into the compute-side `GCmp`/`nexp`, fabricates a
fluent-list-backed enum/equal dictionary, computes thresholds, calls `NBI.infer_fluent_bounds`, and
maps the per-fluent result back to `inta` (`NONE` = a fluent came out unbounded). The two exports
carry different `int` types, bridged through `IntInf`. **Untrusted**: the reduction re-checks any box
with `check_gbounds_opt`, so a wrong box is rejected, never unsound.

## Oracle plumbing — the in-process certifier

**`InProcessCertify` (`inprocess_certify.sml`).** Owns `oracle_certifier`, the closure handed
**in-process** to the verified capstone. Given the Isabelle-built `net`, it: writes the muntax JSON
(`NetworkConversion.convert_network`) and hyphen-sanitizes it; derives the renaming
(`MLuntaAdapter.parse_construct` + `CertConv.convert_renaming`, writing the renaming file); runs the
external tck-reach oracle to a binary certificate (`TCheckerCertify.make_cert`); deserializes it
(`Deserializer64Bit(Bound)`, `Bound` = `Converter.inta dBMEntry`) into a
`Converter.inta state_space`; and returns `SOME (renaming, state_space)` — or `NONE`, **fail-closed**.
It accumulates its own wall time in `oracle_ms` so plan_cert reports `STAGE check` = capstone total −
oracle time. `mode_of_str` maps the CLI mode string to `Converter.mode`. `check_and_cert` is the
standalone (non-capstone, propositional) driver using `parse_convert_check` directly.

Because the net is handed to the checker **in memory** (never round-tripping through the muntax JSON,
which has no initial-variable section), the explicit initial values of point-bounded static numeric
fluents survive — the reason numeric certification cannot use the JSON path.

**`TCheckerCertify` (`tchecker_certify.sml`).** The external orchestration: per-stage wall-clock
profiling (`timeStage` → `+ STAGE <name>: <ms> ms`), the muntax→tck→dot→cert pipeline (`make_cert`,
with `TCK_ALGO` selecting the tck-reach algorithm, default covreach), identifier sanitization, and
the retired external-muntac verdict path (`certify_via_tchecker`).

**`MLuntaAdapter` (`mlunta_adapter.sml`).** Thin wrapper over the vendored MLunta library's
*construction* side (`open Mlunta`): `parse_construct` (parse muntax → TA system + info, no check)
and `parse_rename` (parse + write the renaming file the external `convert_certificate` consumes).
Both the renaming and the tck certificate come from the same MLunta parse, so they are
index-consistent (no MLunta↔Munta skew). Re-exports MLunta's `Setup : CHECKING_SETUP` for the
certificate-conversion functor.

## Net and certificate conversion

**`NetworkConversion` (`network_conversion/`).** `convert_network : bool -> string -> clocks_name_network -> network`
takes the Isabelle net (an 8-tuple-core: clocks, automaton names/indices, broadcast, automata, vars
+ bounds, formula, init) and writes the muntax JSON, preserving index order for renaming
consistency. Fluent-vs-fluent guards become variable **difference** constraints
(`convert_comparison` emits `l - r <op> 0` via `Difference.Diff`); `network_to_string.sml`
serializes a difference as a **parenthesized** `(a - b)` because Munta's guard grammar only accepts a
parenthesized additive expression as atomic.

**`CertificateConversion` (`certificate_conversion/`).** A functor over `Setup`, instantiated with
`MLuntaAdapter.Setup`, that turns an MLunta in-memory certificate into `Converter`'s certificate
types: `convert_renaming` builds the six `nat`/`string` renaming functions from MLunta's
`IndexDict`s, `convert_passed` folds the passed-set into `Converter.Reachable_Set`. Two skew fixes:
the synthetic urgency clock `_urge` (Munta appends it last, `Suc`-shifted) maps to
`IndexDict.size clock_dict`; and per-process location renamings are **totalized over the location
union with an identity fallback** (Munta queries foreign location ids that MLunta's per-process dict
doesn't hold).

## Utilities and vendored imports

`util/` (in-repo): `ListUtils`, `ArrayUtils`, the `TO_STRING` functors, `writeln`. From
`imports/isalib.mlb`: the Isabelle-standard-basis emulation (pipeline infixes `|> #> |->`,
`the_default`, `apfst`/`apsnd`, `K`, `id`). From MLunta's own util (via `imports/mlunta.mlb`): `Log`,
`TextIOUtil` (`read_file`/`save_data`), `Benchmark` (`time_it`/`add_time`), `Either`.
`exit_fail`/`println` are defined at the top of `pddl_refactor.sml` / `plan_cert.sml`.

The `imports/*.mlb` wrappers, one line each: **parcom** — parser-combinator library the PDDL grammar
is built on; **cmlib** — CMU base library under parcom; **isalib** — Isabelle-basis emulation for
generated code + glue; **mlunta** — the full vendored MLunta (Wimmer): parsing, construction, DBM,
model-checking, `Setup`/`Network`/`Certify`; **munta** — Munta support helpers the `Converter` export
links against; **mlunta_certificate** — the binary-certificate (de)serializer (`BOUND`,
`Deserializer64Bit`) instantiated with `Converter`'s checker types.

## `plan_cert.sml` — the CLI hub

Parses flags (`dissect_arguments`), dispatches on the `-certify` mode (`check`), and wraps `main` in
`Benchmark.time_it`. The modes:

| `-certify` | function | flow |
|---|---|---|
| `numeric-tchecker` | `certify_numeric_tchecker` | the full verified numeric path (below) |
| `numeric` | `make_numeric_network` | ground + infer-box + build the numeric net, no oracle |
| `tchecker` | `certify_tchecker` | propositional net → external tck-reach + muntac verdict |
| `inprocess` | `certify_inprocess` | propositional net → tck-reach → verified `parse_convert_check` |
| `numeric-selftest` | `numeric_selftest` | exercises the bound-inference exports on hand-built drafts |
| (none) | `make_network` / `make_renaming` | build a net / renaming only |

Env knobs: `QUANT_EXPAND=grounded` (Strategy A), `SHOW_NET=1` (echo the net JSON), `NEMO_PRUNE=0`
(disable nemo), `TCK_ALGO`, `TCHECKER_PKG_ROOT` / `TCK_REACH_BIN` / `NMO` (tool locations).

## End-to-end: `plan_cert -certify numeric-tchecker -domain D -problem P`

`certify_numeric_tchecker` (via `numeric_ground_and_box`), each arrow naming the owner:

1. **parse** — `PddlParser.get_prob[_q]` → `ast_problem` / `qproblem`.
2. **nemo filter** — `NemoReach.reach_filter` → the reachable-instance predicate.
3. **ground(+nemo)** — `Grounder.ground_problem_numeric[_q] filt` → ground, numeric-keeping,
   propositionalised problem (`STAGE ground`).
4. **infer-box** — `NumericBoundGlue.infer_box (Converter.numeric_draft_actions …)` → box, then the
   diagnostic `Converter.check_gbounds_opt` re-check (`STAGE infer-box`).
5. **verified capstone** — `Converter.check_and_cert_numeric_pddl_problem_no_return`: re-checks the
   gate, **builds the net**, and hands it in-process to the oracle closure.
6. **in-process oracle** — `InProcessCertify.oracle_certifier`: net → muntax
   (`NetworkConversion`) → renaming (`MLuntaAdapter` + `CertificateConversion`) → external tck-reach
   cert (`TCheckerCertify`, `STAGE renaming`/`convert-tck`/`tck`/`convert-back`) → deserialize →
   `SOME (renaming, state_space)`.
7. **verified check → verdict** — back in the capstone, Munta's `convert_check` validates the
   certificate against the net; acceptance ⇒ goal unreachable ⇒ (proved reduction) no plan ⇒
   "The numeric planning problem is unsolvable." (`STAGE check` = total − oracle time).

The only soundness-bearing steps are #4's `check_gbounds_opt` gate and #7's verified `convert_check`;
everything else is untrusted plumbing that fails open (nemo) or closed (box projection, oracle).

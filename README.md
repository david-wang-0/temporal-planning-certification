# temporal-planning-certification

The source code for our paper "Formally Verified Certification of Unsolvability of Temporal Planning
Problems": the reduction of temporal planning to timed automata and its correctness proofs in
Isabelle/HOL, and `plan_cert`, the verified certifier of unsolvability built from them.
[Index.thy](Index.thy) maps the theorems, lemmas and definitions of the paper to the theories. This
version contains one correction made after the paper's experimental evaluation, the numeric
interference guards of the paper's Definition 20; see [What changed after the experimental
evaluation](#what-changed-after-the-experimental-evaluation).

The development also certifies unsolvability of **numeric** temporal problems end to end (this
part is not in the paper): interval bound inference with relational (fluent-vs-fluent) guard
refinement, nemo datalog-reachability pruning in the grounder, and a verified certifier capstone
(`check_and_cert_numeric_pddl_problem`) that hands the built network in-process to an external
tck-reach oracle and checks the returned certificate with Munta's verified checker
(`plan_cert -certify numeric-tchecker`, per-stage profiled). In the artifact, the benchmarks,
the solver binaries and our results are in the sibling folder `benchmarks/`.

The code exported from the theories (`ML/Check_Unsolvability.ML`) and the certifier built from it
(`ML/out/plan_cert`) are included, so the certifier can be run without Isabelle or MLton. This
README covers:

- [What is verified and what is trusted](#what-is-verified-and-what-is-trusted): what a verdict of
  `plan_cert` guarantees.
- [Checking the proofs and exporting the code](#checking-the-proofs-and-exporting-the-code-optional)
  (optional): building the Isabelle theories, regenerating `ML/Check_Unsolvability.ML`, and
  navigating the theories in Isabelle/jEdit.
- [Building the certifier](#building-the-certifier-optional) (optional): compiling `plan_cert`
  from the exported code with MLton.
- [Running the certifier](#running-the-certifier): `plan_cert -certify numeric-tchecker` on a PDDL
  problem.
- [Third-party components and licences](#third-party-components-and-licences).
- [What changed after the experimental evaluation](#what-changed-after-the-experimental-evaluation):
  the correction, and how this version differs from the one the paper's experimental evaluation
  used.

## What is verified and what is trusted

`plan_cert -certify numeric-tchecker` ends in the capstone
`check_and_cert_numeric_pddl_problem_okay`
(`Numeric_Ground_PDDL_Exec_Imp/Numeric_Unsolvability_Export.thy`): when it reports "The numeric
planning problem is unsolvable.", there is no `π` with `num_ground_plan_valid P π`, where `P` is the
**ground** problem handed to it.

- Untrusted, before the capstone: the PDDL parser and our own grounder
  (`ML/plan_cert/src/grounder.sml`, written for `plan_cert`, not taken from another planner),
  including the nemo datalog-reachability pruning (`ML/plan_cert/src/nemo_reach.sml`), static-fluent
  folding and the duration scaling below.
- Verified, inside the capstone: the executable admission check (it checks that `P` is a well-formed
  ground problem of the supported fragment, not that it is a faithful grounding of the lifted
  problem), the bound inference, the TA encoding, and Munta's certificate checker.
- Untrusted but harmless: the tck-reach oracle and the certificate conversions; a wrong
  certificate is rejected by the checker.

So the verified verdict is "the ground problem emitted by our grounder has no valid plan"; that the
lifted PDDL problem has none rests on the grounder being correct.

**Duration scaling.** The network builder and Munta's checker need integer constants. After
grounding, `scale_durations` (`grounder.sml`) multiplies every duration constant by K, the lcm of
their denominators (K = 1 if all are integers). For `painter-impossible`, the only family with
K ≠ 1, 15.004 = 3751/250 gives K = 250. The verified verdict is about the scaled problem; that the
original one is then unsolvable too is an informal argument (uniform scaling maps plans to plans),
not a formal lemma. It needs the durations to be the only time constants (no condition or effect
mentions `?duration`) and every duration to be a constant or a sum of constants, since the pass
scales constant leaves; both hold for the benchmarks.

## Checking the proofs and exporting the code (optional)

The sessions build on `formal-pddl-semantics`, `pddl-grounding` and `isabelle-provenance`, which
must be registered as Isabelle components (in the artifact they are sibling folders; its top-level
README, "Checking the proofs", shows how). From this directory:

```sh
isabelle build -d . PDDL_TP_Reduction_Index            # check all proofs and Index.thy
isabelle build -d . -e Numeric_Ground_PDDL_Exec_Imp    # regenerate ML/Check_Unsolvability.ML
```

`-d .` makes the export land in this folder.

### Navigating the theories

```sh
isabelle build -b -d . Numeric_Ground_PDDL_Exec_Imp
isabelle jedit -d . -l Numeric_Ground_PDDL_Exec_Imp Index.thy
```

The first command builds the heap jEdit loads (the full check already leaves it behind), so
jEdit does not build it at start-up. [Index.thy](Index.thy) maps the paper to the theories.

## Building the certifier (optional)

`ML/out/plan_cert` is included; this rebuilds it from the exported code. It needs GNU make
(https://www.gnu.org/software/make/#download) and MLton (http://www.mlton.org/Installation).

Navigate to the `ML` folder and build the certifier (`-B` forces the build: otherwise `make` sees
the included binary as up to date):

```sh
cd ML
make -B build_certifier
```

The binary is `ML/out/plan_cert`, overwriting the included one.

## Running the certifier

`plan_cert -certify numeric-tchecker` runs the whole pipeline in one call: it parses and grounds
the PDDL problem and runs the verified capstone, which builds the timed-automata network, hands it
to the external tck-reach oracle and checks the returned certificate with Munta's verified checker.

### Requirements

- `plan_cert`: `ML/out/plan_cert`, or build it as above. It is not the binary that produced the
  paper's results (see [What changed after the experimental
  evaluation](#what-changed-after-the-experimental-evaluation)).
- `tck-reach` from [TChecker](https://github.com/ticktac-project/tchecker). The artifact's results
  were produced with TChecker master built 2026-07-26, included as
  `benchmarks/tools/ours/tck-reach`.
- The `convert_models` Python package (in this directory; in the artifact also in
  `benchmarks/tools/ours/`) and `python3` on `PATH`. The two conversions `plan_cert` runs use only
  the Python standard library; pydot is needed only by `convert_models/model_to_dot.py`, which
  `plan_cert` does not call. So a direct call needs no virtual environment.
- `nmo` from [Nemo v0.10.0](https://github.com/knowsys/nemo/releases/tag/v0.10.0): the grounder
  keeps only the action instances that Nemo finds reachable in the delete relaxation; in the
  artifact, `benchmarks/tools/ours/nmo`.

`plan_cert` finds these through environment variables:

| variable | meaning | default | when the tool is not there |
|---|---|---|---|
| `TCHECKER_PKG_ROOT` | directory containing `convert_models`; `plan_cert` runs `python3 -m convert_models.…` there | `.` | `No module named 'convert_models'`, then `muntax->tck (convert) failed:`; no verdict |
| `TCK_REACH_BIN` | the `tck-reach` binary | `./tck-reach` | `unhandled exception: SysErr: No such file or directory [noent]`, exit status 1 |
| `NMO` | the `nmo` binary | `nmo`, looked up on `PATH` | grounding without pruning, silently (no `+ nemo reachability` line), so the ground problem can be much larger |
| `TCK_ALGO` | the algorithm passed to `tck-reach -a` | `covreach` | (not a tool) |

### Command

`plan_cert` reads lifted PDDL and grounds it itself. In the artifact, from its root directory:

```sh
P=$PWD/temporal-planning-certification/ML/out/plan_cert
T=$PWD/benchmarks/tools/ours
B=benchmarks/benchmarks/MatchCellar-impossible
W=$(mktemp -d)
env TCHECKER_PKG_ROOT=$T TCK_REACH_BIN=$T/tck-reach NMO=$T/nmo $P -certify numeric-tchecker \
  -domain $B/domain.pddl -problem $B/instances/instance_3.pddl \
  -model $W/model.muntax -renaming $W/renaming.json -certificate $W/cert.bin
```

Outside the artifact, from this directory, with `tck-reach` copied here and `nmo` on `PATH`, the
defaults apply; `DOMAIN` and `PROBLEM` are a PDDL domain and problem file, e.g. a benchmark
instance:

```sh
W=$(mktemp -d)
./ML/out/plan_cert -certify numeric-tchecker -domain DOMAIN -problem PROBLEM \
  -model $W/model.muntax -renaming $W/renaming.json -certificate $W/cert.bin
```

`-model`, `-renaming` and `-certificate` are output paths: the network (muntax), the renaming and
the binary certificate. Next to the certificate, `plan_cert` also writes the TChecker model
(`<certificate>.tck`) and the zone graph that tck-reach returns (`<certificate>.dot`). `-num-threads
N` (default 1) sets the threads of the certificate check.

### Output

On the instance above, the output ends with `Certificate was accepted`, then
`The numeric planning problem is unsolvable.` and the stage lines. The paper's MatchCellar
examples in `examples/matchcellar/` give no verdict: with the counter `matches-lit`, the bound
inference finds no upper bound, and `plan_cert` prints
`numeric bound inference failed (a fluent is unbounded or out of scope)`.

`The numeric planning problem is unsolvable.` is printed only by the verified capstone, after the
checker has accepted the certificate; it is the verdict. A rejected certificate is no verdict: it
does not mean that the problem is solvable. The lines `+ STAGE <name>: <ms> ms` give the wall time
of each stage in milliseconds, in the order `ground`, `infer-box`, `write-muntax`, `renaming`,
`write-renaming`, `convert-tck`, `tck`, `convert-back`, `read-cert`, `check` (in the artifact,
`benchmarks/results/README.md`, "Columns", says what each covers). The last line,
`+ Total Time: : <s>`, is the total in seconds.

The exit status does not tell the verdict: `plan_cert` exits with 0 also after a rejected
certificate and after a failed external stage (such as the converter not being found). Exit status
1 comes only from some errors: a parse error, or an uncaught exception such as a missing
`tck-reach`. Read the verdict from the output; our benchmark runs did so too.

## Third-party components and licences

Our sources are under the BSD-3-Clause licence (`LICENSE`). Third-party material is listed in
[NOTICE.md](NOTICE.md), with licence texts in `LICENSES/`. In short:

- A built `plan_cert` binary is distributed under **GPL-3.0-or-later**: its PDDL parser uses the
  GPL-licensed parcom library (`ML/lib/parcom`). The corresponding source is this repository.
- The Python package `convert_models/` is from the artifact of Wimmer, Herbreteau and
  van de Pol, FORMATS 2020 (https://doi.org/10.6084/m9.figshare.12620582, CC BY 4.0). Some of
  its files have been updated for compatibility with newer TChecker versions.
- The SML libraries in `ML/lib/` are mlunta (Joshua von Mutius, BSD-3-Clause), CMlib (MIT),
  parcom (GPL-3.0-or-later) and SML driver files of Munta from the AFP (`ML/lib/munta_util/`,
  Simon Wimmer, BSD). This code is not critical for our correctness proofs.
- `ML/Check_Unsolvability.ML` is generated from our theories together with Isabelle/HOL and
  AFP entries, which are under BSD licences except for Show and parts of Deriving (LGPL 2.1).

## What changed after the experimental evaluation

**The numeric interference guards.** The reduction used for the paper's experimental evaluation
added clock guards to the action automata's edges only for snap actions that interfere
propositionally; snap actions that interfere only numerically (one writes a fluent the other reads
or writes, conditions (v)–(vii) of the paper's Definition 13) got no guard, unlike Definition 20 of
the paper. This version guards both, in the formal model and in the executable certifier: an
action's start, end and instant edges check the clocks of every snap action that interferes with it
propositionally or numerically. With the old guards the network was a sound over-approximation with
respect to reachability/solvability (fewer guards only admit more runs, so an unreachable goal still
means no valid plan exists), so no result of the paper is invalidated; they could only leave some
unsolvable instances uncertified. The results of the paper's experimental evaluation in
`benchmarks/` were produced with the old binary; a rerun of all 410 `ours` runs with this folder's
binary (the artifact's `benchmarks-ours-rerun/`, kept apart from the paper's data) certifies the
same 75 instances, with no other change of outcome.

- Formal model: the interference relation is a parameter `mutex_effects` of the reduction
  (`tp_nta_reduction_defs`, `TA_Network/TP_NTA_Reduction_Defs.thy`); the propositional reduction
  instantiates it with `mutex_snap_action`, the numeric one with propositional-or-numeric
  interference (`numeric_tp_nta_reduction_defs'`, `Numeric_TA_Network/`). A valid plan separates
  interfering snap actions by `ε` (`eps_separated_happ_seq`, `TA_Network/NTA_Temp_Planning_Sem.thy`;
  numeric part `num_mutex_eps_separated`), which discharges the new assumption `mutex_effects_sep`
  of the correctness proof. `Index.thy`, Definitions 18 and 20, maps the changes to the paper.
- Executable certifier: `mutex_effects'`, `num_net_int_clocks'`, `start_edge_num'`, `edge_3_num'`
  and `instant_trans_edge_num'` (`Numeric_Ground_PDDL_Exec_Imp/`). `ML/Check_Unsolvability.ML` is
  re-exported from this version (sha256
  `18db4c263533cba009e58953c0c9abb9ba19bb20b06bb363b2eb523489f6ff11`; +155/−3 lines against the
  export of the version of the experimental evaluation).
- Binary: `ML/out/plan_cert` is the certifier built from this version (sha256
  `f5367170292fb62c33111255473171e8b78ddb30d9878abfa8674a4b29da04de`; Isabelle2025-2 with the AFP
  release afp-2026-10-06, MLton 20241230, GCC 16.2.1). It is not the paper's binary (sha256
  `611b70924b60…`, built from the version of the experimental evaluation; the artifact includes
  neither); `make -B -C ML build_certifier` rebuilds it. Networks for problems without numeric
  interference are identical; for the others the new guards add clock constraints to the edges.

The provenance tags (`provenance` commands, see the artifact's `PROVENANCE.md`) cover the changed
lines too: the fix was implemented by AI agents, so its lines are tagged `ai` and `ai_human`.

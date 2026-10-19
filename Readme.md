# This Repository

This contains the original source code for our paper: "Formally Verified Certification of Unsolvability of Temporal Planning Problems"

The theorems and lemmas from the paper can be found in [Index.thy](Index.thy).
Follow the instructions in [Checking Isabelle Proofs and Exporting Code](#checking-isabelle-proofs-and-exporting-code) to navigate the project with jEdit.

## This Readme
This `README` contains instructions for:
- Building, inspecting, and checking the Isabelle theories.
- Generating code from the verified theories (optional).
- Building a verified encoder for ground PDDL temporal planning problems to a network of timed automata.
- Running the certifier, `plan_cert -certify numeric-tchecker`, on a PDDL problem.

## Numeric extension (post-paper)

The development now also certifies unsolvability of **numeric** temporal problems end to end:
interval bound inference with relational (fluent-vs-fluent) guard refinement, nemo
datalog-reachability pruning in the grounder, and a verified certifier capstone
(`check_and_cert_numeric_pddl_problem`) that hands the built network in-process to an external
tck-reach oracle and checks the returned certificate with Munta's verified checker
(`plan_cert -certify numeric-tchecker`, per-stage profiled). In the artifact, the benchmark
harness is in the sibling folder `benchmarks/`.

## What is verified and what is trusted

`plan_cert -certify numeric-tchecker` ends in the capstone `check_and_cert_numeric_pddl_problem_okay`
(`Numeric_Ground_PDDL_Exec_Imp/Numeric_Unsolvability_Export.thy`): when it reports
"The numeric planning problem is unsolvable.", there is no `π` with `num_ground_plan_valid P π`,
where `P` is the **ground** problem handed to it.

- Untrusted, before the capstone: the PDDL parser and our own grounder (`ML/plan_cert/src/grounder.sml`,
  written for `plan_cert`, not taken from another planner), including the nemo datalog-reachability
  pruning (`ML/plan_cert/src/nemo_reach.sml`), static-fluent folding and the duration scaling below.
- Verified, inside the capstone: the executable admission check (it checks that `P` is a well-formed
  ground problem of the supported fragment, not that it is a faithful grounding of the lifted
  problem), the bound inference, the TA encoding, and Munta's certificate checker.
- Untrusted but harmless: the tck-reach oracle and the certificate conversions; a wrong
  certificate is rejected by the checker.

So the verified verdict is "the ground problem emitted by our grounder has no valid plan"; that the
lifted PDDL problem has none rests on the grounder being correct.

**Duration scaling.** The integer-clock network builder and Munta's checker need integer constants
(`is_int_rat` in `Numeric_Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Impl.thy`). After
grounding, `scale_durations` in `grounder.sml` multiplies every duration constant by K, the lcm of
their denominators (each rational in lowest terms). If all durations are integers, K = 1 and the
pass changes nothing. For `painter-impossible`, 15.004 = 3751/250, so K = 250 and the durations
4, 5, 6, 15.004 become 1000, 1250, 1500, 3751. The verified verdict is then about the scaled ground
problem. That the original problem is unsolvable when the scaled one is (scaling every time constant
uniformly maps plans to plans and is an isomorphism of zone graphs; the separation constant of the
PDDL reduction is 0) is an informal argument: there is no formal scaling lemma. The argument needs
the durations to be the only time constants: no numeric condition or effect may mention `?duration`,
since those are not scaled. This holds for `painter`, the only benchmark family with K ≠ 1.

The pass multiplies each constant *leaf* of a duration expression by K, which scales the duration by K
only when the expression is a single constant or a sum of constants: a product of two constants
would be scaled by K², a quotient not at all. Every duration in the benchmarks is a single constant
(after static fluents are folded), so this does not arise there.

# Third-party components and licences

Our sources are under the BSD-3-Clause licence (`LICENSE`). Third-party material is listed in
[NOTICE.md](NOTICE.md), with licence texts in `LICENSES/`. In short:

- A built `plan_cert` binary is distributed under **GPL-3.0-or-later**: its PDDL parser uses the
  GPL-licensed parcom library (`ML/lib/parcom`). The corresponding source is this repository.
- The Python files (`run.py`, `convert_models/`) are from the artifact of Wimmer, Herbreteau and
  van de Pol, FORMATS 2020 (https://doi.org/10.6084/m9.figshare.12620582, CC BY 4.0). Some of
  them have been updated for compatibility with newer TChecker versions.
- The SML libraries in `ML/lib/` are mlunta (Joshua von Mutius, BSD-3-Clause), CMlib (MIT),
  parcom (GPL-3.0-or-later) and SML driver files of Munta from the AFP (`ML/lib/munta_util/`,
  Simon Wimmer, BSD). This code is not critical for our correctness proofs.
- `ML/Check_Unsolvability.ML` is generated from our theories together with Isabelle/HOL and
  AFP entries, which are under BSD licences except for Show and parts of Deriving (LGPL 2.1).

# How to use

In the artifact, the instructions in the top-level README supersede this section: the PDDL
semantics and the grounder sessions it needs are in sibling folders and are passed to Isabelle
with `-d`, not registered as components.

## Checking Isabelle Proofs and Exporting Code

### Using Isabelle to check the formal proof and export code

To build and check the formal proof and export code:

```shell
isabelle build -d . -e PDDL_TP_Reduction
```

`-d .` is necessary to ensure the code is exported into the right folder.

### Navigating the contents of the files

Build the Munta component:

```
isabelle build -b Munta_Certificate_Checker
```
This avoids a long startup time.

Start Isabelle/jEdit in this directory with the Munta component loaded:

```shell
isabelle jedit -d . -l Munta_Certificate_Checker
```

Navigate to this directory in the jEdit UI.

Open [Index.thy](Index.thy) for some pointers to relevant files.

## Building the executable encoder

### Install GNU make

See: https://www.gnu.org/software/make/#download

### Install MLton

Install MLton. See: http://www.mlton.org/Installation

### Make Isabelle export code (optional)

Follow the above steps to make Isabelle export code.

### Build the Certifier

Navigate to the `ML` folder:

```shell
cd ML
```

Build the Certifier:

```shell
make build_certifier
```

The binary is `ML/out/plan_cert`.

## Running the certifier

`plan_cert -certify numeric-tchecker` runs the whole pipeline in one call: it parses and grounds
the PDDL problem and runs the verified capstone, which builds the timed-automata network, hands it
to the external tck-reach oracle and checks the returned certificate with Munta's verified checker.

### What it needs

- `plan_cert`: in the artifact, `benchmarks/tools/plan_cert` (a build of this repository);
  otherwise build it as above.
- `tck-reach` from [TChecker](https://github.com/ticktac-project/tchecker). The artifact's results
  were produced with TChecker master built 2026-07-26, included as `benchmarks/tools/tck-reach`;
  the earlier pipeline used commit
  [d711ace](https://github.com/ticktac-project/tchecker/commit/d711ace9ff754d8d952f5d491a31591115300c7f).
- The `convert_models` Python package (in this directory; in the artifact also in
  `benchmarks/tools/`) and `python3` on `PATH`. The two conversions `plan_cert` runs use only the
  Python standard library; pydot is needed only by `convert_models/model_to_dot.py`, which
  `plan_cert` does not call. So a direct call needs no virtual environment; the one that
  `benchmarks/setup.sh` creates is for the benchmark harness.
- Optionally `nmo` from [Nemo v0.10.0](https://github.com/knowsys/nemo/releases/tag/v0.10.0), which
  prunes unreachable action instances during grounding; in the artifact, `benchmarks/tools/nmo`.

`plan_cert` finds these through environment variables:

| variable | meaning | default | when the tool is not there |
|---|---|---|---|
| `TCHECKER_PKG_ROOT` | directory containing `convert_models`; `plan_cert` runs `python3 -m convert_models.…` there | `.` | `No module named 'convert_models'`, then `muntax->tck (convert) failed:`; no verdict |
| `TCK_REACH_BIN` | the `tck-reach` binary | `./tck-reach` | `unhandled exception: SysErr: No such file or directory [noent]`, exit status 1 |
| `NMO` | the `nmo` binary | `nmo`, looked up on `PATH` | grounding without pruning, silently (no `+ nemo reachability` line), so the ground problem can be much larger |
| `TCK_ALGO` | the algorithm passed to `tck-reach -a` | `covreach` | (not a tool) |

### Command

In the artifact, from its root directory:

```shell
T=$PWD/benchmarks/tools
E=temporal-planning-certification/examples/ground
W=$(mktemp -d)
env TCHECKER_PKG_ROOT=$T TCK_REACH_BIN=$T/tck-reach NMO=$T/nmo $T/plan_cert -certify numeric-tchecker \
  -domain $E/MatchCellar-impossible/instance_03_domain.pddl \
  -problem $E/MatchCellar-impossible/instance_03_problem.pddl \
  -model $W/model.muntax -renaming $W/renaming.json -certificate $W/cert.bin
```

Outside the artifact, from this directory, with `tck-reach` copied here and `nmo` on `PATH`, the
defaults apply:

```shell
W=$(mktemp -d)
./ML/out/plan_cert -certify numeric-tchecker \
  -domain examples/ground/MatchCellar-impossible/instance_03_domain.pddl \
  -problem examples/ground/MatchCellar-impossible/instance_03_problem.pddl \
  -model $W/model.muntax -renaming $W/renaming.json -certificate $W/cert.bin
```

`-model`, `-renaming` and `-certificate` are output paths: the network (muntax), the renaming and
the binary certificate. Next to the certificate, `plan_cert` also writes the TChecker model
(`<certificate>.tck`) and the zone graph that tck-reach returns (`<certificate>.dot`). `-num-threads N`
(default 1) sets the threads of the certificate check.

### Examples and output

| example in `examples/ground/` | expected lines near the end of the output |
|---|---|
| `MatchCellar-impossible/instance_03_domain.pddl`, `instance_03_problem.pddl` | `Certificate was accepted`, then `The numeric planning problem is unsolvable.` |
| `MatchCellar-possible/instance_solvable_domain.pddl`, `instance_solvable_problem.pddl` (solvable) | `Certificate was rejected`, then `Something went wrong.` |

`The numeric planning problem is unsolvable.` is printed only by the verified capstone, after the
checker has accepted the certificate; it is the verdict. A rejected certificate is no verdict: it
does not mean that the problem is solvable. The lines `+ STAGE <name>: <ms> ms` give the wall time
of each stage in milliseconds, in the order `ground`, `infer-box`, `write-muntax`, `renaming`,
`write-renaming`, `convert-tck`, `tck`, `convert-back`, `read-cert`, `check` (in the artifact,
`benchmarks/README.md`, "What is measured", says what each covers). The last line,
`+ Total Time: : <s>`, is the total in seconds.

The exit status does not tell the verdict: `plan_cert` exits with 0 also after a rejected
certificate and after a failed external stage (such as the converter not being found). Exit status
1 comes only from some errors: a parse error, or an uncaught exception such as a missing
`tck-reach`. Read the verdict from the output; the benchmark harness does so too.

### The earlier pipeline (`run.sh`, `run.py`)

`run.sh` runs the earlier multi-step pipeline: `plan_cert` writes the network and the renaming in
separate calls, the Python converters and tck-reach produce the certificate, and `muntac`, built from
the AFP entry Munta_Certificate_Checker, checks it. Neither this repository nor the artifact
includes `muntac`, and the verified check now runs inside `plan_cert`, so `run.sh` is kept for
reference only. `run.py` is the batch script of the FORMATS 2020 artifact; it calls a `muntac` build
as well and is not used here.

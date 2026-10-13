# This Repository

This contains the original source code for our paper: "Formally Verified Certification of Unsolvability of Temporal Planning Problems"

The theorems and lemmas from the paper can be found in [Index.thy](Index.thy).
Follow the instructions in [Checking Isabelle Proofs and Exporting Code](#checking-isabelle-proofs-and-exporting-code) to navigate the project with jEdit.

## This Readme
This `README` contains instructions for:
- Building, inspecting, and checking the Isabelle theories.
- Generating code from the verified theories (optional).
- Building a verified encoder for ground PDDL temporal planning problems to a network of timed automata.
- Building the pipeline and running it or individual components.

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

## Running the pipeline

### Install Python 3

Follow the instructions in: https://www.python.org/downloads/

### Install TChecker

Please refer to instructions here: https://github.com/ticktac-project/tchecker

We use commit: [d711ace](https://github.com/ticktac-project/tchecker/commit/d711ace9ff754d8d952f5d491a31591115300c7f)

Once completed, move `tck-reach` from the output directory into this folder.

### Install Isabelle and the AFP

Follow the steps above to install Isabelle and the AFP.

### Build muntac from the AFP

Build `muntac` from the AFP and move it here (`.`):
```shell
isabelle build -e Munta_Certificate_Checker
mv -t . <path-to-afp-2025>/thys/Munta_Certificate_Checker/muntac
```

### Running the entire pipeline

The pipeline needs names to be provided for every input and ouput file, namely: 
- Ground pddl domain
- Ground pddl problem
- Muntax network
- TChecker network
- TChecker dot certificate
- Muntac certificate
- Muntac renaming

```shell
chmod +x run.sh
./run <ground-domain>.pddl <ground-problem>.pddl
```

Example:
```shell
./run.sh examples/ground/MatchCellar-impossible/instance_03_domain.pddl examples/ground/MatchCellar-impossible/instance_03_problem.pddl
```

## Running individual components

### Install Python 3

Follow the instructions in: https://www.python.org/downloads/

### Install TChecker

Follow the steps above.

### Install Isabelle and the AFP

Follow the steps above.

### Build muntac from the AFP

Follow the steps above.

### Running the verified component
The checker is in `ML/out`.

From this directory:
```shell
./ML/out/plan_cert -domain <ground-domain>.pddl -problem <ground-problem>.pddl -model <network>.muntax
```

### Converting muntax to TChecker format

```shell
python -m convert_models.convert <model>.muntax <model>.tck
```

### Running TChecker on a model to ouput a certificate

```shell
./tck-reach -a covreach -C graph -s dfs -o <certificate>.dot <model>.tck
```

### Creating a renaming for the model
```shell
./ML/out/plan_cert -model <model>.muntax -renaming <model_renaming>.rnm
```

### Converting certificates

```shell
 python -m convert_models.convert_certificate -m <model>.muntax <certificate>.dot <model_renaming>.rnm <certificate>.cert
```

### Checking a certificate agains the network and renaming

```shell
./muntac -m <model>.muntax -r <renaming>.rnm -c <certificate>.cert
```


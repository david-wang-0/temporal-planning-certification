# How to use

## Obtain the dependencies

```shell
git submodule update --init
```

## Checking Isabelle Proofs and Exporting Code

### Install Isabelle 2025

More instructions here: https://isabelle.in.tum.de/installation.html

### Add the Isabelle AFP for Isabelle 2025

Download instructions can be found here: https://www.isa-afp.org/download/

Once a local copy is obtained, add the theories as Isabelle component
```shell
isabelle components -u <path-to>/afp-2025/thys
```

### Add Temporal Planning Semantics as Isabelle component

```shell
isabelle components -u lib/temporal-pddl-semantics
```

### Make Isabelle recognise the project's dependencies

Add the root directory of this project as Isabelle Component
```shell
isabelle components -u .
```

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

Open `Index.thy` for some pointers to relevant files

## Building the executable checker

### Install GNU make

See: https://www.gnu.org/software/make/#download

### Install MLton

Install MLton. See: http://www.mlton.org/Installation

### Make Isabelle export code

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

## Running the encoder


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

## Running TChecker

### Install TChecker

Please refer to instructions here: https://github.com/ticktac-project/tchecker

Once completed, move `tck-reach` from the output directory into this folder.

### Run TChecker on a model to ouput a certificate

```shell
./tck-reach -a covreach -C graph -s dfs -o <certificate>.dot <model>.tck
```

## Converting and checking certificates

### Install Isabelle and the AFP

Follow the steps above to install Isabelle and the AFP.

### Build muntac from the AFP

Build `muntac` from the AFP and move it here (`.`):
```shell
isabelle build -e Munta_Certificate_Checker
mv -t . <path-to-afp-2025>/thys/Munta_Certificate_Checker/muntac
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

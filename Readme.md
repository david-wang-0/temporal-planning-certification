# How to use

## Install GNU make

Find instructions here: https://www.gnu.org/software/make/#download

## Obtain the dependencies

```
git submodule update --init
```

## Checking Isabelle Proofs and Exporting Code

### Install Isabelle 2025

More instructions here: https://isabelle.in.tum.de/installation.html

### Add the Isabelle AFP for Isabelle 2025

Download instructions can be found here: https://www.isa-afp.org/download/

Once a local copy is obtained, add the theories as Isabelle component
```
isabelle components -u <path-to>/afp-2025/thys
```

### Add Temporal Planning Semantics as Isabelle component

```
isabelle components -u lib/temporal-pddl-semantics
```

### Make Isabelle recognise the project's dependencies

Add the root directory of this project as Isabelle Component
```
isabelle components -u .
```

### Using Isabelle to check the formal proof and export code

To build and check the formal proof and export code:

```
isabelle build -d . -e PDDL_TP_Reduction
```

`-d .` is necessary to ensure the code is exported into the right folders.

### Navigating the contents of the files

Build the Munta component:

```
isabelle build -b Munta_Certificate_Checker
```
This avoids a long startup time.

Start Isabelle/jEdit in this directory with the Munta component loaded:

```
isabelle jedit -d . -l Munta_Certificate_Checker
```

Navigate to this directory in the jEdit UI.

## Building the executable checker

### Install MLton

Install MLton. See: http://www.mlton.org/Installation

### Make Isabelle export code

Follow the above steps to make Isabelle export code.

### Build the Certifier

Navigate to the `ML` folder:

```
cd ML
```

Build the Certifier:

```
make build_certifier
```
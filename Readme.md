# How to use

## Install Mercurial
Find instructions here: https://www.mercurial-scm.org/install

## Install isabelle 2025
More instructions here: https://isabelle.in.tum.de/installation.html

## Add the Isabelle AFP
A working revision can be obtained from the mercurial repository:
```
hg clone --updaterev 9723ff25870aad1d692fcc4dab82ce1bfb97c2b0 https://foss.heptapod.net/isa-afp/afp-2025  
```

```
<isabelle> components -u afp-2025/thys
```
Where `<isabelle>` is the Isabelle command

## Add the code for the formalisation

```
<isabelle> components -u temp-planning-certification
```

## Buliding and Navigating

To build/check the project:

```
<isabelle> build -b TP_NTA_Reduction
```

### To look at the contents
Build the Munta component:

```
<isabelle> build -b Munta_Model_Checker
```
This avoids a long startup time.

Start Isabelle/jEdit with the Munta heap loaded:

```
<isabelle> jedit -l Munta_Model_Checker
```

Navigate to the `temp-planning-certification` folder in the jEdit UI.

# Building the executable checker
Install MLton. See: http://www.mlton.org/Installation

Install GNU make. See: https://www.gnu.org/software/make/#download

Get MLunta. 

Export the generated SML code:
```
isabelle build -e PDDL_TP_Reduction 
```

CMlib needs to be in version 2.3.0
```
cd ML/lib/cmlib
```

```
git checkout 7e58f90cc854788de66c623f7da9f7d4940eef21
```
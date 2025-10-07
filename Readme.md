# How to use

## Install isabelle 2025
More instructions here: https://isabelle.in.tum.de/installation.html

## Add the Isabelle AFP
Go to https://www.isa-afp.org/download/ and download the 2025 version of the AFP

```
<isabelle> components -u afp-2025/thys
```
Where `<isabelle>` is the Isabelle command

## Add the session for the formalisation

```
<isabelle> components -u .
```
This allows Isabelle to obtain the relevant external dependecies, i.e. the AFP.

`-u` updates the component described by the `ROOT` file in the `.` directory

## Buliding and Navigating

To build/check the project:

```
<isabelle> build -b TP_NTA_Reduction
```

`-b` tells Isabelle to store the heap image, i.e. compiled theories.
`-v` is verbose
`-c` tells isabelle to clean build
### To look at the contents
Build the Munta Model Checker:

```
<isabelle> build -b Munta_Model_Checker
```
This avoids a long startup time.

Start Isabelle/jEdit with the Munta heap loaded:

```
<isabelle> jedit -l Munta_Model_Checker
```

It's also possible to select the session in the right panel of the jEdit UI and then restart jEdit.

Navigate to the `temporal-planning-certification` folder in the jEdit UI.

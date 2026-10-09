# Origin and licence of `convert_models/`

This muntax/TChecker model and certificate converter is from the artifact of the FORMATS 2020
paper "Certifying Emptiness of Timed Büchi Automata":

> Simon Wimmer, Frédéric Herbreteau, Jaco van de Pol. *Certifying Emptiness of Timed Büchi
> Automata: Artifact.* figshare, 2020. <https://doi.org/10.6084/m9.figshare.12620582>
> (directory `FORMATS_2020_Artifact/convert_models/`)

It is used under that artifact's licence, CC BY 4.0
(<https://creativecommons.org/licenses/by/4.0/>).

Changes from the published version: `convert.py`, `convert_certificate.py`, `main.py` and
`read_dot.py` were modified for compatibility with newer TChecker versions, and the macOS
metadata file `._scc.py` was removed. The other files are unchanged.

`scc.py` is in turn from the ActiveState Code recipe 578507, "Strongly connected components of a
directed graph", by Mark Dickinson (2013), archived at <https://github.com/ActiveState/code>
(`recipes/Python/578507_Strongly_connected_components_directed/`), under the MIT licence of that
archive:

```
Copyright (c) 2017 ActiveState Software Inc.

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```

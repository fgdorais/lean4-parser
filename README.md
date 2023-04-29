# Lean 4 / Parser

A parser combinator library for [Lean 4](https://leanprover.github.io/).

## Installation

Add this dependency to your project's `lakefile.lean`:

```lean
require Parser from git "https://github.com/fgdorais/lean4-parser" @ "main"
```
Then add `import Parser` at the top of any Lean file where you plan to use this library.

## Acknowledgements

Original work for the Lean 4 Parser library was done by [François G. Dorais](https://github.com/fgdorais), [Kyrill Serdyuk](https://github.com/lliryk), and [Emma Shroyer](https://github.com/emma-shroyer).
This work was partly supported by the CEMS REU program at The University of Vermont.

-----

* The Parser library is copyright © 2022-2023 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.


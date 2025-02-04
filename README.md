# Lean 4 / Parser

A parser combinator library for [Lean 4](https://leanprover.github.io/).

Source documentation is available at [www.dorais.org/lean4-parser/doc/](https://www.dorais.org/lean4-parser/doc).

## Usage

Add this dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "Parser"
git = "https://github.com/fgdorais/lean4-parser"
rev = "main"
```
Then add `import Parser` at the top of any Lean file where you plan to use this library. 
For example:
```lean
import Parser

open Parser Char

/--
Parses a list of sign-separated integers (no spaces) from an input string and returns the sum.
-/
def parseSum : SimpleParser Substring Char Int := do
  let mut sum : Int := 0
  -- parse until all input is consumed
  while ! (← test endOfInput) do
    -- parse an integer (decimal only) and add to sum
    sum := sum + (← ASCII.parseInt)
  return sum

-- returns 42
#eval match parseSum.run "11-1+2-3+33" with
  | .ok _ sum => sum
  | .error _ e => panic! (toString e)
```

The `examples` directory contains more elaborate sample parsers.

## Acknowledgements

Original work for the Lean 4 Parser library was done by [François G. Dorais](https://github.com/fgdorais), [Kyrill Serdyuk](https://github.com/kyserd), and [Emma Shroyer](https://github.com/emma-shroyer).
This work was partly supported by the CEMS REU program at The University of Vermont.

-----

* The Parser library is copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. The library is released under the [Apache 2.0 license](http://www.apache.org/licenses/LICENSE-2.0). See the file LICENSE for additional details.


/-
Copyright © 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, François G. Dorais
-/
open IO.Process

/--
Run tests, via the Batteries test runner.

When https://github.com/leanprover/lean4/issues/4121
"allow using an upstream executable as a lake `@[test_runner]`"
is resolved, this file can be replaced with a line in `lakefile.lean`.
-/
def main (args : List String) : IO Unit := do
  let exitcode ← (← spawn { cmd := "lake", args := #["exe", "batteries/test"] ++ args }).wait
  exit exitcode.toUInt8

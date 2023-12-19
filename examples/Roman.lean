/-
Copyright © 2022-2023 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser

/-!
  Roman numeral parser
-/

namespace Roman

open Parser Char

/-- Roman parser monad -/
protected abbrev Parser := SimpleParser Substring Char

/-- Parse a roman numeral -/
protected def parse : Roman.Parser Nat := stepM >>= stepC >>= stepX >>= stepI
where

  stepM : Roman.Parser Nat :=
    (1000 * .) <$> countUpTo 3 (char 'M')

  stepC (n : Nat) : Roman.Parser Nat :=
    first [
      char 'C' *> char 'M' *> pure (n + 900),
      char 'C' *> char 'D' *> pure (n + 400),
      char 'D' *> (n + 500 + 100 * .) <$> countUpTo 3 (char 'C'),
      (n + 100 * .) <$> countUpTo 3 (char 'C')]

  stepX (n : Nat) : Roman.Parser Nat :=
    first [
      char 'X' *> char 'C' *> pure (n + 90),
      char 'X' *> char 'L' *> pure (n + 40),
      char 'L' *> (n + 50 + 10 * .) <$> countUpTo 3 (char 'X'),
      (n + 10 * .) <$> countUpTo 3 (char 'X')]

  stepI (n : Nat) : Roman.Parser Nat :=
    first [
      char 'I' *> char 'X' *> pure (n + 9),
      char 'I' *> char 'V' *> pure (n + 4),
      char 'V' *> (n + 5 + .) <$> countUpTo 3 (char 'I'),
      (n + .) <$> countUpTo 3 (char 'I')]

end Roman

/-- Read roman numeral from string -/
def String.toNatRoman? (s : String) : Option Nat :=
  match Parser.run (Roman.parse <* Parser.endOfInput) s with
  | .ok _ (n+1) => some (n+1)
  | _ => none

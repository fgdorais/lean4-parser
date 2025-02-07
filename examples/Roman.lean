/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser

/-! # Roman Numeral Parser

Roman numerals are composed from seven basic tokens:

  I = 1, V = 5, X = 10, L = 50, C = 100, D = 500, M = 1000.

These are combined using additive and subtractive notation to form decimal places:

* units: I = 1, II = 2, III = 3, IV = 4, V = 5, VI = 6, VII = 7, VIII = 8, IX = 9.
* tens: X = 10, XX = 20, XXX = 30, XL = 40, L = 50, LX = 60, LXX = 70, LXXX = 80, XD = 90.
* hundreds: C = 100, CC = 200, CCC = 300, CD = 400, D = 500, DC = 600, DCC = 700, DCCC = 800,
  CM = 900.
* thousands: M = 1000, MM = 2000, MMM = 3000.

These decimal places are then concatenated from highest to lowest in order to form any integer from
1 to 3999. For example, MCMLXXXVII = M + CM + LXXX + VII = 1987.
-/

namespace Roman

open Parser Char

/-- Roman parser monad -/
protected abbrev Parser := Parser Unit Substring Char

/-- Parse a roman numeral (uppercase) -/
protected def parse : Roman.Parser Nat :=
  stepM >>= stepC >>= stepX >>= stepI

where

  /-- Parse thousands (up to 3000) -/
  stepM : Roman.Parser Nat :=
    -- 0, M = 1000, MM = 2000, MMM = 3000
    (1000 * .) <$> countUpTo 3 (char 'M')

  /-- Parse hundreds and add to `n` -/
  stepC (n : Nat) : Roman.Parser Nat :=
    first [
      -- CM = 900
      char 'C' *> char 'M' *> pure (n + 900),
      -- D = 500, DC = 600, DCC = 700, DCCC = 800
      char 'D' *> (n + 500 + 100 * .) <$> countUpTo 3 (char 'C'),
      -- CD = 400
      char 'C' *> char 'D' *> pure (n + 400),
      -- 0, C = 100, CC = 200, CCC = 300
      (n + 100 * .) <$> countUpTo 3 (char 'C')]

  /-- Parse tens and add to `n` -/
  stepX (n : Nat) : Roman.Parser Nat :=
    first [
      -- XC = 90
      char 'X' *> char 'C' *> pure (n + 90),
      -- L = 50, LX = 60, LXX = 70, LXXX = 80
      char 'L' *> (n + 50 + 10 * .) <$> countUpTo 3 (char 'X'),
      -- XL = 40
      char 'X' *> char 'L' *> pure (n + 40),
      -- 0, X = 10, XX = 20, XXX = 30
      (n + 10 * .) <$> countUpTo 3 (char 'X')]

  /-- Parse units and add to `n` -/
  stepI (n : Nat) : Roman.Parser Nat :=
    first [
      -- IX = 9
      char 'I' *> char 'X' *> pure (n + 9),
      -- V = 5, VI = 6, VII = 7, VIII = 80
      char 'V' *> (n + 5 + .) <$> countUpTo 3 (char 'I'),
      -- IV = 4
      char 'I' *> char 'V' *> pure (n + 4),
      -- 0, I = 1, II = 2, III = 3
      (n + .) <$> countUpTo 3 (char 'I')]

end Roman

/-- Interpret the string as a roman numeral -/
def String.toNatRoman? (s : String) (upper : Bool := true) : Option Nat :=
  let s := if upper then s else s.map .toUpper
  match Parser.run (Roman.parse <* Parser.endOfInput) s with
  | .ok _ (n+1) => some (n+1)
  | _ => none

@[inline, inherit_doc String.toNatRoman?]
def String.toNatRoman! (s : String) (upper : Bool := true) : Nat :=
  s.toNatRoman? upper |>.get!

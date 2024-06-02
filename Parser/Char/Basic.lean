/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Basic
import Parser.RegEx.Basic

namespace Parser.Char
variable {ε σ m} [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m] [MonadExceptOf ε m]

/-- `char tk` accepts and returns character `tk`, otherwise fails -/
@[inline]
def char (tk : Char) : ParserT ε σ Char m Char :=
  withErrorMessage s!"expected {repr tk}" <| token tk

/-- `chars tks` accepts and returns string `tks`, otherwise fails -/
def chars (tks : String) : ParserT ε σ Char m String :=
  withErrorMessage s!"expected {repr tks}" do
    let mut acc : String := ""
    for tk in tks.data do
      acc := acc.push (← token tk)
    return acc

/-- `string tks` accepts and returns string `tks`, otherwise fails -/
def string [Parser.Error ε Substring Char] (tks : String) : ParserT ε Substring Char m String :=
  withErrorMessage s!"expected {repr tks}" do
    let ⟨str, start, stop⟩ ← StateT.get
    if start + tks.endPos < stop ∧ String.substrEq tks 0 str start tks.endPos.byteIdx then
      setPosition (start + tks.endPos)
      return tks
    else
      throwUnexpected

/-- `captureStr p` parses `p` and returns the output of `p` with the corresponding substring -/
def captureStr [Parser.Error ε Substring Char] (p : ParserT ε Substring Char m α) : ParserT ε Substring Char m (α × Substring) := do
  let ⟨str,_,_⟩ ← StateT.get
  let (x, start, stop) ← withCapture p
  return (x, ⟨str, start, stop⟩)

/-- `matchStr re` accepts and returns substring matches for regex `re` groups, otherwise fails -/
def matchStr [Parser.Error ε Substring Char] (re : RegEx Char) : ParserT ε Substring Char m (Array (Option Substring)) := do
  let ⟨str,_,_⟩ ← StateT.get
  let ms ← re.match
  return ms.map fun
    | some (start, stop) => some ⟨str, start, stop⟩
    | none => none

/-- Parse space (U+0020) -/
@[inline]
def space : ParserT ε σ Char m Char :=
  withErrorMessage "expected space (U+0020)" <| token ' '

/-- Parse horizontal tab (U+0009) -/
@[inline]
def tab : ParserT ε σ Char m Char :=
  withErrorMessage "expected horizontal tab (U+0009)" <| token '\t'

/-- Parse line feed (U+000A) -/
@[inline]
def ASCII.lf : ParserT ε σ Char m Char :=
  withErrorMessage "expected line feed (U+000A)" <| token '\n'

/-- Parse carriage return (U+000D) -/
@[inline]
def ASCII.cr : ParserT ε σ Char m Char :=
  withErrorMessage "expected carriage return (U+000D)" <| token '\r'

/-- Parse end of line -/
@[inline]
def eol : ParserT ε σ Char m Char :=
  withErrorMessage "expected newline" do
    (ASCII.cr *> ASCII.lf) <|> ASCII.lf

namespace ASCII

/-- Parse whitespace character -/
def whitespace : ParserT ε σ Char m Char :=
  withErrorMessage "expected whitespace character" do
    tokenFilter fun c => c == ' ' || c >= '\t' && c <= '\r'

/-- Parse uppercase letter character (`A`..`Z`) -/
def uppercase : ParserT ε σ Char m Char :=
  withErrorMessage "expected uppercase letter character" do
    tokenFilter fun c => c >= 'A' && c <= 'Z'

/-- Parse lowercase letter character (`a`..`z`)-/
def lowercase : ParserT ε σ Char m Char :=
  withErrorMessage "expected lowercase letter character" do
    tokenFilter fun c => c >= 'a' && c <= 'z'

/-- Parse alphabetic character (`A`..`Z` and `a`..`z`) -/
def alpha : ParserT ε σ Char m Char :=
  withErrorMessage "expected alphabetic character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c >= 'A' && c <= 'Z'

/-- Parse numeric character (`0`..`9`)-/
def numeric : ParserT ε σ Char m Char :=
  withErrorMessage "expected decimal digit character" do
    tokenFilter fun c => c >= '0' && c <= '9'

/-- Parse alphabetic letter or digit (`A`..`Z`, `a`..`z` and `0`..`9`) -/
def alphanum : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else if c >= 'A' then c <= 'Z' else c >= '0' && c <= '9'

/-- Parse control character -/
def control : ParserT ε σ Char m Char :=
  withErrorMessage "expected control character" do
    tokenFilter fun c => c.val < 0x20 || c.val == 0x7f

/-- Parse decimal digit (`0`-`9`) -/
def digit : ParserT ε σ Char m (Fin 10) :=
  withErrorMessage "expected decimal digit" do
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 10 then
          some ⟨val, h⟩
        else
          none

/-- Parse binary digit (`0`..`1`) -/
def binDigit : ParserT ε σ Char m (Fin 2) :=
  withErrorMessage "expected binary digit" do
    tokenMap fun
    | '0' => some ⟨0, Nat.zero_lt_succ 1⟩
    | '1' => some ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
    | _ => none

/-- Parse octal digit (`0`..`7`) -/
def octDigit : ParserT ε σ Char m (Fin 8) :=
  withErrorMessage "expected octal digit" do
    tokenMap fun c =>
      if c >= '0' then
        let val := c.toNat - '0'.toNat
        if h : val < 8 then
          some ⟨val, h⟩
        else
          none
      else
        none

/-- Parse hexadecimal digit (`0`..`9`, `A`..`F` and `a`..`f`) -/
def hexDigit : ParserT ε σ Char m (Fin 16) :=
  withErrorMessage "expected hexadecimal digit" do
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 10 then
          some ⟨val, Nat.lt_trans h (by decide)⟩
        else if c < 'A' then none else
          let val := val - ('A'.toNat - '9'.toNat - 1)
          if h : val < 16 then
            some ⟨val, h⟩
          else if c < 'a' then none else
            let val := val - ('a'.toNat - 'A'.toNat)
            if h : val < 16 then
              some ⟨val, h⟩
            else
              none

end ASCII

end Parser.Char

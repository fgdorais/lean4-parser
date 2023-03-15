/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Basic

namespace Parser.Char
variable {ε σ m} [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m] [MonadExceptOf ε m]

/-- `char tk` accepts and returns character `tk`, otherwise fails -/
@[inline] def char (tk : Char) : ParserT ε σ Char m Char :=
  withErrorMessage s!"expected {repr tk}" do
    tokenFilter (. == tk)

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
    let ⟨str, start, stop⟩ ← State.stream <$> StateT.get
    if start + tks.endPos < stop ∧ String.substrEq tks 0 str start tks.endPos.byteIdx then
      setPosition (start + tks.endPos)
      return tks
    else
      throwUnexpected

/-- parse space (U+0020) -/
@[inline] def space : ParserT ε σ Char m Char :=
  withErrorMessage "expected space (U+0020)" do
    tokenFilter (. == ' ')

/-- parse tab (U+0009) -/
@[inline] def tab : ParserT ε σ Char m Char :=
  withErrorMessage "expected tab (U+0009)" do
    tokenFilter (. == '\t')

/-- parse line feed (U+000A) -/
@[inline] def lf : ParserT ε σ Char m Char :=
  withErrorMessage "expected line feed (U+000A)" do
    tokenFilter (. == '\n')

/-- parse carriage return (U+000D) -/
@[inline] def cr : ParserT ε σ Char m Char :=
  withErrorMessage "expected carriage return (U+000D)" do
    tokenFilter (. == '\r')

/-- parse carriage return (U+000D) and line feed (U+000A) -/
@[inline] def crlf : ParserT ε σ Char m Char :=
  withErrorMessage "expected carriage return (U+000D) and line feed (U+000A)" do
    withBacktracking (cr *> lf)

/-- parse end of line -/
def eol : ParserT ε σ Char m Char :=
  withErrorMessage "expected newline" do
    crlf <|> lf

namespace ASCII

/-- parse whitespace -/
def whitespace : ParserT ε σ Char m Char :=
  withErrorMessage "expected whitespace" do
    tokenFilter fun c => c == ' ' || c >= '\t' && c <= '\r'

/-- parse uppercase letter -/
def uppercase : ParserT ε σ Char m Char :=
  withErrorMessage "expected uppercase letter" do
    tokenFilter fun c => c >= 'A' && c <= 'Z'

/-- parse lowercase letter -/
def lowercase : ParserT ε σ Char m Char :=
  withErrorMessage "expected lowercase letter" do
    tokenFilter fun c => c >= 'a' && c <= 'z'

/-- parse alphabetic letter -/
def alpha : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter" do
    tokenFilter fun c => c >= 'A' && c <= 'Z' ||  c >= 'a' && c <= 'z'

/-- parse alphabetic letter or digit -/
def alphanum : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit" do
    tokenFilter fun c => c >= '0' && c <= '9' || c >= 'A' && c <= 'Z' ||  c >= 'a' && c <= 'z'

/-- parse decimal digit -/
def digit : ParserT ε σ Char m (Char × Fin 10) :=
  withErrorMessage "expected digit" do
    tokenMap fun c =>
      if h : 48 <= c.toNat ∧ c.toNat <= 57 then
        let val := c.toNat - 48
        have h : val < 10 := by
          apply Nat.lt_succ_of_le
          apply Nat.le_of_add_le_add_right (b:=48)
          rw [Nat.sub_add_cancel h.left]
          exact h.right
        some (c, ⟨val, h⟩)
      else
        none

/-- parse hexadecimal digit -/
def hexDigit : ParserT ε σ Char m (Char × Fin 16) :=
  withErrorMessage "expected digit" do
    tokenMap fun c =>
      if hn : 48 <= c.toNat ∧ c.toNat <= 57 then
        let val := c.toNat - 48
        have h : val < 16 := by
          apply Nat.lt_succ_of_le
          apply Nat.le_of_add_le_add_right (b:=48)
          rw [Nat.sub_add_cancel hn.left]
          apply Nat.le_trans hn.right
          decide
        some (c, ⟨val, h⟩)
      else if hu : 65 <= c.toNat ∧ c.toNat <= 70 then
        let val := c.toNat - 55
        have h0 : 55 <= c.toNat := by
          apply Nat.le_trans _ hu.left
          decide
        have h : val < 16 := by
          apply Nat.lt_succ_of_le
          apply Nat.le_of_add_le_add_right (b:=55)
          rw [Nat.sub_add_cancel h0]
          exact hu.right
        some (c, ⟨val, h⟩)
      else if hu : 97 <= c.toNat ∧ c.toNat <= 102 then
        let val := c.toNat - 87
        have h0 : 87 <= c.toNat := by
          apply Nat.le_trans _ hu.left
          decide
        have h : val < 16 := by
          apply Nat.lt_succ_of_le
          apply Nat.le_of_add_le_add_right (b:=87)
          rw [Nat.sub_add_cancel h0]
          exact hu.right
        some (c, ⟨val, h⟩)
      else
        none

end ASCII

end Parser.Char

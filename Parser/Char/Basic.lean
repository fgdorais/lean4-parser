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

/-- parse whitespace -/
def whitespace : ParserT ε σ Char m Char :=
  withErrorMessage "expected whitespace" do
    tokenFilter Char.isWhitespace

/-- parse upper case letter -/
def upper : ParserT ε σ Char m Char :=
  withErrorMessage "expected uppercase letter" do
    tokenFilter Char.isUpper

/-- parse lower case letter -/
def lower : ParserT ε σ Char m Char :=
  withErrorMessage "expected lowercase letter" do
    tokenFilter Char.isLower

/-- parse letter -/
def letter : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter" do
    tokenFilter Char.isAlpha

/-- parse digit -/
def digit : ParserT ε σ Char m Char :=
  withErrorMessage "expected digit" do
    tokenFilter Char.isDigit

/-- parse letter or digit -/
def alphanum : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit" do
    tokenFilter Char.isAlphanum

end Parser.Char

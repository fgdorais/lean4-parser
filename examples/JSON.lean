/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser

/-!
  JSON Validator

  The function `JSON.validate` determines whether an input string represents
  a valid JSON value.

  The JSON data interchange syntax is defined in [ECMA Standard 404](https://www.ecma-international.org/publications-and-standards/standards/ecma-404/).
  A convenient visual representation of the syntax can be found at [json.org](https://www.json.org/json-en.html).
-/

namespace JSON

open Parser Char

/-- JSON parser monad -/
protected abbrev Parser := SimpleParser Substring Char

/-- Parse JSON white spaces -/
def ws : JSON.Parser Unit := dropMany <| tokenFilter fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t'

/-- Parse a JSON number -/
protected partial def number : JSON.Parser Unit :=
  withErrorMessage "expected number" do
    let _ ← optional (char '-')
    match ← ASCII.digit with
    | ⟨0, _⟩ => pure ()
    | _ => dropMany ASCII.digit
    optional do
      let _ ← char '.'
      dropMany1 ASCII.digit
    optional do
      let _ ← char 'E' <|> char 'e'
      let _ ← optional (char '+' <|> char '-')
      dropMany1 ASCII.digit

/-- Parse a JSON string -/
protected def string : JSON.Parser Unit :=
  withErrorMessage "expected string" do
    let _ ← char '"'
    let _ ← dropUntil (char '"') do
      match ← anyToken with
      | '\\' => escape
      | c =>
        if c.val ≥ 0x20 then
          pure ()
        else
          withErrorMessage "unexpected control character" throwUnexpected
where
  /-- Parse an escape character -/
  escape : JSON.Parser Unit :=
    withErrorMessage "expected escape" do
      match ← anyToken with
      | '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' => pure ()
      | 'u' => drop 4 ASCII.hexDigit
      | c => throwUnexpected c

mutual

/-- Parse a JSON object -/
protected partial def object : JSON.Parser Unit :=
  withErrorMessage "expected object" do
    let _ ← char '{'
    let _ ← sepBy (char ',') do
      let _ ← ws *> JSON.string
      let _ ← ws *> char ':'
      let _ ← ws *> JSON.value
    let _ ← ws <* char '}'

/-- Parse a JSON array -/
protected partial def array : JSON.Parser Unit :=
  withErrorMessage "expected array" do
    let _ ← char '['
    let _ ← sepBy (char ',') do
      let _ ← ws *> JSON.value
    let _ ← ws <* char ']'

/-- Parse a JSON value -/
protected partial def value : JSON.Parser Unit :=
  withErrorMessage "expected value" do
    let c ← lookAhead anyToken
    if c == 'f' then
      Char.string "false" *> pure ()
    else if c == 'n' then
      Char.string "null" *> pure ()
    else if c == 't' then
      Char.string "true" *> pure ()
    else if c == '\t' then
      JSON.string
    else if c == '{' then
      JSON.object
    else if c == '[' then
      JSON.array
    else if c == '-' || c.isDigit then
      JSON.number
    else
      throwUnexpected (some c)

end

/-- JSON validator -/
def validate (str : String) : Bool :=
  match Parser.run (JSON.value <* endOfInput) str with
  | .ok _ _ => true
  | .error _ => false

end JSON

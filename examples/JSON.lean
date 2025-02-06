/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser

/-! # A JSON Validator

The JSON data interchange syntax is defined in [ECMA Standard 404][ECMA]. A convenient visual
representation of the syntax can be found at [json.org][JSON].

For convenience, the syntax has been translated to BNF in the comments to the code below. The BNF
variant used does not allow character escape sequences. Instead, `""` inside a string represents the
double quotes character. Unicode code points can also be used in the form `U+` followed by at least
four (and at most six) uppercase hexadecimal digits for the code point (if more than four, the first
cannot be zero).

[ECMA]: https://www.ecma-international.org/publications-and-standards/standards/ecma-404/
[JSON]: https://www.json.org/json-en.html
-/

namespace JSON

open Parser Char

/-- JSON parser monad -/
protected abbrev Parser := SimpleParser Substring Char

/-- Parse JSON white spaces

JSON only recognizes four white space characters: space (U+0020), line feed (U+000A), carriage
return (U+000D), horizontal tab (U+0009).
```
<ws> ::= "" | U+00020 <ws> | U+000A <ws> | U+000D <ws> | U+0009 <ws>
```
-/
def ws : JSON.Parser Unit :=
  dropMany <| tokenFilter [' ', '\n', '\r', '\t'].contains

/-- Parse a JSON number

Specification:
```
<number> ::= <integer> <optional-fraction> <optional-exponent>
```
-/
protected partial def number : JSON.Parser Unit :=
  withErrorMessage "expected number" do
    /-
    ```
    <integer> ::= <optional-negative> "0" | <optional-negative> <positive-digit> <digits>

    <optional-negative> ::= "" | "-"

    <positive-digit> := "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

    <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

    <digits> ::= "" | <digit> <digits>
    ```
    -/
    optional (char '-')                         -- `<optional-negative>`
    first [
      drop 1 (char '0'),                        -- `"0" |`
      dropMany1 ASCII.digit,                    -- `<positive-digit> <digits>`
      throwUnexpected
    ]
    /-
    ```
    <optional-fraction> := "" | "." <digit> <digits>

    <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

    <digits> ::= "" | <digit> <digits>
    ```
    -/
    optional do                                 -- `"" |`
      drop 1 (char '.')                         -- `"."`
      dropMany1 ASCII.digit                     -- `<digit> <digits>`

    /-
    ```
    <optional-exponent> ::= "" | <exp> <optional-sign> <digit> <digits>

    <exp> ::= "e" | "E"

    <optional-sign> ::= "" | "+" | "-"

    <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

    <digits> ::= "" | <digit> <digits>
    ```
    -/
    optional do                                 -- `"" |`
      drop 1 (char 'e' <|> char 'E')            -- `<exp>`
      optional (char '+' <|> char '-')          -- `<optional-sign>`
      dropMany1 ASCII.digit                     -- `<digit> <digits>`

/-- Parse a JSON string

The only characters that must be escaped in a JSON string are `"` (U+0022), `\` (U+005C), and
control characters (U+0000 .. U+001F).

Specification:
```
<string> ::= """" <characters> """"

<characters> ::= "" | <character> <characters>

<character> ::= "\" <escape> | U+0020 .. U+10FFFF except """" (U+0022) and "\" (U+005C)
```
-/
protected def string : JSON.Parser Unit :=
  withErrorMessage "expected string" do
    char '"' *> dropUntil (drop 1 <| char '"') do
      first [
        char '\\' *> escape,                    -- `"\" <escape> |`
        drop 1 <| tokenFilter fun c => c ≥ ' ', -- `<character>`
        throwUnexpected
      ]
where
  /--
  ```
  <escape> ::= """" | "\" | "/" | "b" | "f" | "n" | "r" | "t"
      | "u" <hex-digit> <hex-digit> <hex-digit> <hex-digit>

  <hex-digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
      | "A" | "B" | "C" | "D" | "E" | "F" | "a" | "b" | "c" | "d" | "e" | "f"
  ```
  -/
  escape : JSON.Parser Unit :=
    withErrorMessage "expected escape" do
      first [
        drop 1 <| tokenFilter ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'].contains,
        char 'u' *> drop 4 ASCII.hexDigit,
        throwUnexpected
      ]

mutual

/-- Parse a JSON value

Specification:
```
<value> ::= <object> | <array> | <string> | <number> | "true" | "false" | "null"
```
The `object` and `array` parsers recursively
depend on `value` so they are in a mutual
declaration block.
-/
protected partial def value : JSON.Parser Unit :=
  first [
    JSON.object,
    JSON.array,
    JSON.string,
    JSON.number,
    drop 1 <| string "true",
    drop 1 <| string "false",
    drop 1 <| string "null",
    throwUnexpectedWithMessage none "expected value"
  ]

/-- Parse a JSON object

Specification:
```
<object> ::= "{" <ws> "}" | "{" <members> "}"

<members> ::= <member> | <member> "," <members>

<member> ::= <ws> <string> <ws> ":" <ws> <value> <ws>
```
-/
protected partial def object : JSON.Parser Unit :=
  withErrorMessage "expected object" do
    drop 1 <| char '{'
    let _ ← sepBy (char ',') do
      let _ ← ws *> JSON.string <* ws
      drop 1 <| char ':'
      let _ ← ws *> JSON.value <* ws
    drop 1 <| char '}'

/-- Parse a JSON array

Specification:
```
<array> ::= "[" <ws> "]" | "[" <elements> "]"

<elements> ::= <element> | <element> "," <elements>

<element> ::= <ws> <value> <ws>
```
-/
protected partial def array : JSON.Parser Unit :=
  withErrorMessage "expected array" do
    drop 1 <| char '['
    let _ ← sepBy (char ',') do
      let _ ← ws *> JSON.value <* ws
    drop 1 <| char ']'


end

/-- JSON validator -/
def validate (str : String) : Bool :=
  match Parser.run (ws *> JSON.value <* ws <* endOfInput) str with
  | .ok _ _ => true
  | .error _ _ => false

end JSON

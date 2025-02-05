/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser

/-!
  JSON Validator

  The function `JSON.validate` determines whether an input string represents a valid JSON value.

  The JSON data interchange syntax is defined in [ECMA Standard 404](https://www.ecma-international.org/publications-and-standards/standards/ecma-404/).
  A convenient visual representation of the syntax can be found at [json.org](https://www.json.org/json-en.html).
-/

namespace JSON

open Parser Char

/-- JSON parser monad -/
protected abbrev Parser := SimpleParser Substring Char

/-- Parse JSON white spaces

```
ws
  | ""
  | ' ' ws
  | '\n' ws
  | '\r' ws
  | '\t' ws
```
-/
def ws : JSON.Parser Unit :=
  dropMany <| tokenFilter fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t'

/-- Parse a JSON number

Specification:
```
number
  | integer fraction exponent
```
-/
protected partial def number : JSON.Parser Unit :=
  withErrorMessage "expected number" do

    /- Integer part

    Specification:
    ```
    integer
      | digit
      | onenine digits
      | '-' digit
      | '-' onenine digits

    onenine
      | '1' . '9'

    digit
      | '0'
      | onenine

    digits
      | digit
      | digit digits
    ```

    The following implementation uses an equivalent specification.
    A JSON integer consists of an optional negative sign ('-') followed by either the single
    digit '0' or a nonzero digjt ('1' . '9') followed by zero or more digits.
    In other words, we follow this alternative specification:
    ```
    integer
      | '0'
      | onenine decimals

    decimals
      | ""
      | decimal decimals

    decimal
      | '0' . '9'

    onenine
      | '1' . '9'
    ```
    -/
    let _ ← optional (char '-')                 -- "" | '-'
    match ← ASCII.digit with
    | ⟨0, _⟩ => pure ()                         -- '0'
    | _ => dropMany ASCII.digit                 -- onenine | onenine decimals

    /- Fraction part

    Specification:
    ```
    fraction
      | ""
      | '.' digits
    ```
    -/
    optional do                                 -- "" | ...
      let _ ← char '.'                          -- '.'
      dropMany1 ASCII.digit                     -- digits

    /- Exponent part

    Specification:
    ```
    exponent
      | ""
      | e sign digits
      | E sign digits

    sign
      | ""
      | '+'
      | '-'
    ```
    -/
    optional do                                 -- "" | ...
      let _ ← char 'e' <|> char 'E'             -- 'e' | 'E'
      let _ ← optional (char '+' <|> char '-')  -- "" | '+' | '-'
      dropMany1 ASCII.digit                     -- digits

/-- Parse a JSON string

Specification:
```
string
  | '"' characters '"'

characters
  | ""
  | character characters

character
  | U+0020 . U+10FFFF - '"' - '\'
  | '\' escape
```
Note that the code points before U+0020 (space) are control characters.
-/
protected def string : JSON.Parser Unit :=
  withErrorMessage "expected string" do
    let _ ← char '"'                            -- '"'
    let _ ← dropUntil (char '"') do             -- ... | '"'
      match ← anyToken with
      | '\\' => escape                          -- '\' escape
      | c =>                                    -- any other character
        if c.val ≥ 0x20 then
          pure ()
        else                                    -- except control characters
          withErrorMessage "unexpected control character" throwUnexpected
where

  /-- Escaped character

  Specification:
  ```
  escape
    | '"'
    | '\'
    | '/'
    | 'b'
    | 'f'
    | 'n'
    | 'r'
    | 't'
    | 'u' hex hex hex hex

  hex
    | '0' . '9'
    | 'A' . 'F'
    | 'a' . 'f'
  ```
  -/
  escape : JSON.Parser Unit :=
    withErrorMessage "expected escape" do
      match ← anyToken with
      | '"' | '\\' | '/' | 'b'
      | 'f' | 'n' | 'r' | 't' => pure ()        -- '"' | '\' | '/' | 'b' | 'f' | 'n' | 'r' | 't'
      | 'u' => drop 4 ASCII.hexDigit            -- 'u' hex hex hex hex
      | c => throwUnexpected c

mutual

/-- Parse a JSON value

Specification:
```
value
  | object
  | array
  | string
  | number
  | "true"
  | "false"
  | "null"
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
    string "true" *> pure (),
    string "false" *> pure (),
    string "null" *> pure (),
    throwUnexpectedWithMessage none "expected value"
  ]

/-- Parse a JSON object

Specification:
```
object
  | '{' ws '}'
  | '{' members '}'

members
  | member
  | member ',' members

member
  | ws string ws ':' ws value ws
```
-/
protected partial def object : JSON.Parser Unit :=
  withErrorMessage "expected object" do
    let _ ← char '{'                            -- '{'
    let _ ← sepBy (ws *> char ',') do           -- member loop
      let _ ← ws *> JSON.string                 -- ws string
      let _ ← ws *> char ':'                    -- ws ':'
      let _ ← ws *> JSON.value                  -- ws value ws
    let _ ← ws <* char '}'                      -- ws '}'

/-- Parse a JSON array

Specification:
```
array
  | '[' ws ']'
  | '[' elements ']'

elements
  | element
  | element ',' elements

element
  | ws value ws
```
-/
protected partial def array : JSON.Parser Unit :=
  withErrorMessage "expected array" do
    let _ ← char '['                            -- '['
    let _ ← sepBy (char ',') do                 -- element loop
      let _ ← ws *> JSON.value                  -- ws value ws
    let _ ← ws *> char ']'                      -- ws ']'


end

/-- JSON validator -/
def validate (str : String) : Bool :=
  match Parser.run (ws *> JSON.value <* ws <* endOfInput) str with
  | .ok _ _ => true
  | .error _ _ => false

end JSON

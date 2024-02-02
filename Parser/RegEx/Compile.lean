/-
Copyright © 2022-2023 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Char
import Parser.Char.Numeric
import Parser.RegEx.Basic

/-! ## RegEx Syntax

  We currently use a very simplified form for regular expression syntax.

  Operators:

  * A match of `α|β` consists of either a match of `α` or a match of `β`
  * A match of `αβ` consists of a match of `α` followed by a match of `β`
  * A match of `α?` consists of at most one match of `α`
  * A match of `α*` consists of zero or more back-to-back matches of `α`
  * A match of `α+` consists of one or more back-to-back matches of `α`
  * A match of `α{m}` consists of exactly `m` back-to-back matches of `α`
  * A match of `α{m,n}` consists of at least `m` but at most `n` back-to-back matches of `α`
  * A match of `α{m,}` consists of `m` or more back-to-back matches of `α`
  * A match of `α{,n}` consists of at most `n` back-to-back matches of `α`
  * A match of `(α)` consists of a match of `α`

  These are listed from lowest to highest precedence.

  Character matching:

  * `.` matches any character.
  * A single character matches itself with the exception of the special characters: `.`, `?`, `*`,
    `+`, `|`, `\`, `(`, `)`, `{`, `}`, `[`, `]`. These special characters can be matched by
    preceding them with an escape character `\`.
  * `[c]` matches one character from the class `c`.
  * `[^c]` matches one character not in the class `c`.

  Character classes support single characters and character ranges. The special characters `-`,
  `[`, `\`, `]` must be preceded by an escape character `\` within a class.
-/


namespace Parser.RegEx
open Char

private abbrev REParser := Parser Unit Substring Char

mutual

private partial def re0 : REParser (RegEx Char) :=
  re1 >>= loop
where

  loop (e : RegEx Char) := do
    if ← test (char '|') then
      loop (.alt e (← re1))
    else
      return e

private partial def re1 : REParser (RegEx Char) := do
  re2 >>= loop <|> return .nil
where

  loop (e : RegEx Char) := do
    match ← option? re2 with
    | some a => loop (.cat e a)
    | none => return e

private partial def re2 : REParser (RegEx Char) :=
  re3 >>= loop
where

  loop (e : RegEx Char) := do
    match ← option? <| first [star e, plus e, opt e, reps e] with
    | some e => loop e
    | none => return e

  opt (e : RegEx Char) := do
    char '?' *> return .opt e

  star (e : RegEx Char) := do
    char '*' *> return .repMany e

  plus (e : RegEx Char) := do
    char '+' *> return .repMany1 e

  reps (e : RegEx Char) : REParser (RegEx Char) :=
    withBacktracking do
      let _ ← char '{'
      let e ←
        match ← option? ASCII.parseNat with
        | some min =>
          let emin : RegEx Char := RegEx.rep min e
          match ← option? (char ',' *> option? ASCII.parseNat) with
          | some (some max) => pure <| RegEx.cat emin (.repUpTo (max - min) e)
          | some none => pure <| RegEx.cat emin (.repMany e)
          | none => pure <| emin
        | none =>
          let max ← char ',' *> ASCII.parseNat
          pure <| .repUpTo max e
      let _ ← char '}'
      return e

private partial def re3 : REParser (RegEx Char) := do
  first [tok, any, set, grp]
where

  any : REParser (RegEx Char) :=
    char '.' *> return .any

  grp : REParser (RegEx Char) :=
    withBacktracking do
      let _ ← char '('
      let n ← test (char '?' *> char ':')
      let e ← re0
      let _ ← char ')'
      return if n then e else .group e

  setLoop (filter : Char → Bool) : REParser (Char → Bool) := do
    match ← option? <| tokenFilter (!['-', '[', ']'].elem .) with
    | some c =>
      let c ← if c == '\\' then esc else pure c
      let f ← try withBacktracking do
          let _ ← char '-'
          let c' ← tokenFilter (!['-', '[', ']'].elem .)
          let c' ← if c' == '\\' then esc else pure c'
          pure <| fun x => c ≤ x && x ≤ c'
        catch _ =>
          pure <| fun x => x == c
      setLoop fun x => filter x || f x
    | none => return filter

  set : REParser (RegEx Char) :=
    withBacktracking do
      let _ ← char '['
      let n ← test (char '^')
      let f ← setLoop fun _ => false
      let _ ← char ']'
      if n then
        return .set (! f .)
      else
        return .set (f .)

  tok : REParser (RegEx Char) := do
    let special := ['.', '?', '*', '+', '|', '(', ')', '{', '}', '[', ']']
    let c ← tokenFilter (!special.elem .)
    let c ← if c == '\\' then esc else pure c
    return .set (. == c)

  esc : REParser Char := do
    match ← anyToken with
    | 't' => return '\t'
    | 'n' => return '\n'
    | 'r' => return '\r'
    | 'u' =>
      let n ← (·.val) <$> Parser.Char.ASCII.hexDigit
      let n ← ((n <<< 4) + ·.val) <$> Parser.Char.ASCII.hexDigit
      let n ← ((n <<< 4) + ·.val) <$> Parser.Char.ASCII.hexDigit
      let n ← ((n <<< 4) + ·.val) <$> Parser.Char.ASCII.hexDigit
      return Char.ofNat n
    | 'x' =>
      let n ← (·.val) <$> Parser.Char.ASCII.hexDigit
      let n ← ((n <<< 4) + ·.val) <$> Parser.Char.ASCII.hexDigit
      return Char.ofNat n
    | c => return c

end

/-- Compiles a regex from a string, returns `none` on faiure -/
protected def compile? (s : String) : Option (RegEx Char) :=
  match Parser.run (re0 <* endOfInput) s with
  | .ok _ r => some r
  | .error _ => none

/-- Compiles a regex from a string, panics on faiure -/
protected def compile! (s : String) : RegEx Char :=
  match RegEx.compile? s with
  | some r => r
  | none => panic! "invalid regular expression"

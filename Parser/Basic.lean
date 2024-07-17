/-
Copyright © 2022-2024 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Error
import Parser.Parser
import Parser.Stream

namespace Parser
variable [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m]

/-! # Token Functions -/

/--
`tokenCore next?` reads a token from the stream using `next?`.

This is a low-level parser to customize how the parser stream is used.
-/
@[inline]
def tokenCore (next? : σ → Option (τ × σ)) : ParserT ε σ τ m (ULift τ) := do
  match next? (← getStream) with
  | some (tok, stream) =>
    let _ ← setStream stream
    return ⟨tok⟩
  | none => throwUnexpected

/--
`tokenMap test` accepts token `t` with result `x` if `test t = some x`, otherise fails reporting
the unexpected token.
-/
@[specialize]
def tokenMap (test : τ → Option α) : ParserT ε σ τ m α := do
  let ⟨tok⟩ ← tokenCore Stream.next?
  match test tok with
  | some x => return x
  | none => throwUnexpected tok

/--
`anyToken` consumes and returns one token from the stream. Only fails on end of stream.
-/
@[inline]
def anyToken : ParserT ε σ τ m τ :=
  tokenMap some

/--
`tokenFilter test` accepts and returns token `t` if `test t = true`, otherwise fails reporting
unexpected token.
-/
@[inline]
def tokenFilter (test : τ → Bool) : ParserT ε σ τ m τ :=
  tokenMap fun c => if test c then some c else none

/--
`token tk` accepts and returns `tk`, otherwise fails otherwise fails reporting unexpected token.
-/
@[inline]
def token [BEq τ] (tk : τ) : ParserT ε σ τ m τ :=
  tokenFilter (. == tk)

/--
`tokenArray tks` accepts and returns tokens from `tks` in order, otherwise fails reporting the
first unexpected token.
-/
def tokenArray [BEq τ] (tks : Array τ) : ParserT ε σ τ m (Array τ) :=
  withBacktracking do
    let mut acc : Array τ := #[]
    for tk in tks do
      acc := acc.push (← token tk)
    return acc

/--
`tokenArray tks` accepts and returns tokens from `tks` in order, otherwise fails reporting the
first unexpected token.
-/
def tokenList [BEq τ] (tks : List τ) : ParserT ε σ τ m (List τ) :=
  withBacktracking do
    let mut acc : Array τ := #[]
    for tk in tks do
      acc := acc.push (← token tk)
    return acc.toList

/-! # Basic Combinators -/

/--
`lookAhead p` tries to parses `p` without consuming any input. If `p` fails then the stream is
backtracked with the same error.
-/
def lookAhead (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := do
  let savePos ← getPosition
  try
    let x ← p
    setPosition savePos
    return x
  catch e =>
    setPosition savePos
    throw e

/--
`peek` returns the next token, without consuming any input. Only fails on end of stream.
-/
abbrev peek : ParserT ε σ τ m τ := lookAhead anyToken

/--
`notFollowedBy p` succeeds only if `p` fails. Consumes no input regardless of outcome.
-/
@[inline]
def notFollowedBy (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit := do
  try
    let _ ← lookAhead p
  catch _ =>
    return
  throwUnexpected

/--
`endOfInput` succeeds only on end of stream. Consumes no input.
-/
abbrev endOfInput : ParserT ε σ τ m PUnit := notFollowedBy anyToken

/--
`test p` returns `true` if `p` succeeds and `false` otherwise. This parser ever fails.
-/
@[inline]
def test (p : ParserT ε σ τ m α) : ParserT ε σ τ m Bool :=
  optionD (p *> return true) false

/-! ### `foldr` -/

/-- `foldr f p q` -/
@[inline]
partial def foldr (f : α → β → β) (p : ParserT ε σ τ m α) (q : ParserT ε σ τ m β) :
  ParserT ε σ τ m β :=
  try
    let x ← withBacktracking p
    let y ← foldr f p q
    return f x y
  catch _ => q

/-! ### `take` family -/

/--
`take n p` parses exactly `n` occurrences of `p`, and returns an array of the returned values
of `p`.
-/
@[inline]
def take (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  withBacktracking do rest n #[]
where
  rest : Nat → Array α → ParserT ε σ τ m (Array α)
    | 0, xs => return xs
    | n+1, xs => do rest n <| xs.push (← p)

/--
`takeUpTo n p` parses up to `n` occurrences of `p`, and returns an array of the returned values
of `p`. This parser never fails.
-/
@[inline]
def takeUpTo (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  rest n #[]
where
  rest : Nat → Array α → ParserT ε σ τ m (Array α)
    | 0, xs => return xs
    | n+1, xs => do
      match ← option? p with
      | some x => rest n <| xs.push x
      | none => return xs

/--
`takeMany p` parses zero or more occurrences of `p` until it fails, and returns the array of
returned values of `p`. This parser never fails.
-/
@[inline]
def takeMany (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  foldl Array.push #[] p

/--
`takeMany1 p` parses one or more occurrences of `p` until it fails, and returns the array of
returned values of `p`. Consumes no input on error. -/
@[inline]
def takeMany1 (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  withBacktracking do foldl Array.push #[(← p)] p

/--
`takeManyN n p` parses `n` or more occurrences of `p` until it fails, and returns the array of
returned values of `p`. Consumes no input on error.
-/
@[inline]
def takeManyN (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  withBacktracking do foldl Array.push (← take n p) p

/--
`takeUntil stop p` parses zero or more occurrences of `p` until `stop` succeeds, and returns the
array of returned values of `p` and the output of `stop`. If `p` fails before `stop` is encountered,
the error from `p` is reported and no input is consumed.
-/
partial def takeUntil (stop : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) :
  ParserT ε σ τ m (Array α × β) :=
  have := Inhabited.mk do return ((#[] : Array α), (← stop))
  withBacktracking do rest #[]
where
  rest [Inhabited (ParserT ε σ τ m (Array α × β))] (acc : Array α) := do
    match ← option? stop with
    | some y => return (acc, y)
    | none => rest <| acc.push (← p)

/-! ### `drop` family -/

/--
`drop n p` parses exactly `n` occurrences of `p` (without backtracking), ignoring all outputs.
-/
@[inline]
def drop (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  match n with
  | 0 => return
  | n+1 => p *> drop n p

/--
`dropUpTo n p` parses up to `n` occurrences of `p` (with backtracking) ignoring all outputs. This
parser never fails.
-/
@[inline]
def dropUpTo (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  match n with
  | 0 => return
  | n+1 => do
    match ← option? p with
    | some _ => drop n p
    | none => return

/--
`dropMany p` parses zero or more occurrences of `p` (with backtracking) until it fails, ignoring
all outputs.
-/
@[inline]
def dropMany (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  foldl (Function.const α) .unit p

/--
`dropMany1 p` parses one or more occurrences of `p` (with backtracking) until it fails, ignoring
all outputs.
-/
@[inline]
def dropMany1 (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  withBacktracking p *> foldl (Function.const α) () p

/--
`dropManyN n p` parses `n` or more occurrences of `p` until it fails, ignoring all outputs.
-/
@[inline]
def dropManyN (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  withBacktracking do drop n p *> foldl (Function.const α) () p

/--
`dropUntil stop p` runs `p` until `stop` succeeds, returns the output of `stop` ignoring all
outputs from `p`. If `p` fails before encountering `stop` then the error from  `p` is reported
and no input is consumed.
-/
partial def dropUntil (stop : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m β :=
  withBacktracking loop
where
  loop := do
    match ← option? stop with
    | some s => return s
    | none => p *> loop

/-! `count` family -/

/--
`count p` parses occurrences of `p` (with backtracking) until it fails and returns the count of
successes.
-/
@[inline]
partial def count (p : ParserT ε σ τ m α) : ParserT ε σ τ m Nat :=
  foldl (fun n _ => n+1) 0 p

/--
`countUpTo n p` parses up to `n` occurrences of `p` until it fails, and returns the count of
successes. This parser never fails.
-/
@[inline]
def countUpTo (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m Nat :=
  loop n 0
where
  loop : Nat → Nat → ParserT ε σ τ m Nat
    | 0, ct => return ct
    | n+1, ct => do
      match ← option? p with
      | some _ => loop n (ct+1)
      | none => return ct

/--
`countUntil stop p` counts zero or more occurrences of `p` until `stop` succeeds, and returns
the count of successes and the output of `stop`. If `p` fails before encountering `stop` then the
error from  `p` is reported and no input is consumed.
-/
partial def countUntil (stop : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) :
  ParserT ε σ τ m (Nat × β) := do
  let _ := Inhabited.mk do return (0, ← stop)
  withBacktracking do loop 0
where
  loop [Inhabited (ParserT ε σ τ m (Nat × β))] (ct : Nat) := do
    match ← option? stop with
    | some s => return (ct, s)
    | none => p *> loop (ct+1)

/-! ### `endBy` family -/

@[specialize]
private def endByCore (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (init : Array α) (strict : Bool := false) :
  ParserT ε σ τ m (Array α) := do
  match ← efoldlP (fun xs x => sep *> pure (xs.push x)) init p with
  | (xs, e, true) => if strict then throw e else return xs
  | (xs, _, _) => return xs

/--
`endBy p sep` parses zero or more occurrences of `p`, separated and ended by `sep`, returns
the array of values returned by `p`.

The optional `strict` parameter controls error reporting:

* If `strict = false` then this parser never fails and returns the longest possible array.
* If `strict = true` then this parser returns the longest possible array but fails if there is a
  final occurrence of `p` without a trailing `sep`. Then the error of `sep` is reported.

No input is consumed on error.
-/
@[inline]
def endBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (strict : Bool := false) :
  ParserT ε σ τ m (Array α) := withBacktracking do endByCore sep p #[] strict

/--
`endBy1 p sep` parses one or more occurrences of `p`, separated and ended by `sep`, returns
the array of values returned by `p`.

The optional `strict` parameter controls error reporting after parsing the initial `p` and `sep`:

* If `strict = false` then this parser never fails and returns the longest possible array.
* If `strict = true` then this parser returns the longest possible array but fails if there is a
  final occurrence of `p` without a trailing `sep`. Then the error of `sep` is reported.

No input is consumed on error.
-/
@[inline]
def endBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (strict : Bool := False) :
  ParserT ε σ τ m (Array α) := withBacktracking do endByCore sep p #[← p <* sep] strict

/-! ### `sepBy` family -/

@[specialize]
private def sepByCore (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (init : Array α) (strict : Bool := false) :
  ParserT ε σ τ m (Array α) := do
  match ← efoldlP (fun xs _ => p >>= fun x => pure (xs.push x)) init sep with
  | (xs, e, true) => if strict then throw e else return xs
  | (xs, _, _) => return xs

/--
`sepBy p sep` parses zero or more occurrences of `p`, separated by `sep`, returns the array of
values returned by `p`.

The optional `strict` parameter controls error reporting:

* If `strict = false` then this parser never fails and returns the longest possible array.
* If `strict = true` then this parser returns the longest possible array but fails if there is a
  final occurrence of `sep` without a trailing `p`. Then the error of `p` is reported.

No input is consumed on error.
-/
@[inline]
def sepBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (strict : Bool := false) :
  ParserT ε σ τ m (Array α) := withBacktracking do
  match ← option? p with
  | some x => sepByCore sep p #[x] strict
  | none => return #[]

/--
`sepBy1 p sep` parses one or more occurrences of `p`, separated by `sep`, returns the array of
values returned by `p`.

The optional `strict` parameter controls error reporting after parsing the initial `p`:

* If `strict = false` then this parser never fails and returns the longest possible array.
* If `strict = true` then this parser returns the longest possible array but fails if there is a
  final occurrence of `sep` without a trailing `p`. Then the error of `p` is reported.

No input is consumed on error.
-/
@[inline]
def sepBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (strict : Bool := false) :
  ParserT ε σ τ m (Array α) := withBacktracking do sepByCore sep p #[← p] strict

/--
`sepNoEndBy p sep` parses zero or more occurrences of `p`, separated `sep` but without a trailing
`sep`, returns the array of values returned by `p`.
-/
@[inline]
def sepNoEndBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy sep p true

/--
`sepNoEndBy1 p sep` parses one or more occurrences of `p`, separated `sep` but without a trailing
`sep`, returns the array of values returned by `p`.
-/
@[inline]
def sepNoEndBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy1 sep p true

/--
`sepEndBy p sep` parses zero or more occurrences of `p`, separated by `sep` with an optional
trailing `sep`, returns the array of values returned by `p`. This parser never fails. -/
@[inline]
def sepEndBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy sep p <* optional sep

/--
`sepEndBy1 p sep` parses one or more occurrences of `p`, separated by `sep` with an optional
trailing `sep`, returns the array of values returned by `p`. This parser never fails.
-/
@[inline]
def sepEndBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy1 sep p <* optional sep

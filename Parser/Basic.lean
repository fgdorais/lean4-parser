/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Error
import Parser.Parser
import Parser.Stream

namespace Parser
variable {ε σ τ α β} [Parser.Stream σ τ] [Parser.Error ε σ τ] {m} [Monad m]

/-- `tokenAux next?` reads a token from the stream using `next?` -/
@[inline]
def tokenAux (next? : σ → Option (τ × σ)) : ParserT ε σ τ m τ := do
  match next? (← getStream) with
  | some (tok, stream) =>
    let _ ← setStream stream
    return tok
  | none => throwUnexpected

/-- `tokenMap test` accepts token `t` with result `x` if `test t = some x`, otherise fails -/
@[specialize]
def tokenMap (test : τ → Option α) : ParserT ε σ τ m α := do
  let tok ← tokenAux Stream.next?
  match test tok with
  | some x => return x
  | none => throwUnexpected tok

/-- `tokenFilter test` accepts and returns token `t` if `test t = true`, otherwise fails -/
@[inline]
def tokenFilter (test : τ → Bool) : ParserT ε σ τ m τ :=
  tokenMap fun c => if test c then some c else none

/-- `token tk` accepts and returns `tk`, otherwise fails -/
@[inline]
def token [BEq τ] (tk : τ) : ParserT ε σ τ m τ :=
  tokenFilter (. == tk)

/-- `tokenArray tks` accepts and returns `tks`, otherwise fails -/
def tokenArray [BEq τ] (tks : Array τ) : ParserT ε σ τ m (Array τ) :=
  withBacktracking do
    let mut acc : Array τ := #[]
    for tk in tks do
      acc := acc.push (← token tk)
    return acc

/-- `tokenList tks` accepts and returns `tks`, otherwise fails -/
def tokenList [BEq τ] (tks : List τ) : ParserT ε σ τ m (List τ) :=
  withBacktracking do
    let mut acc : Array τ := #[]
    for tk in tks do
      acc := acc.push (← token tk)
    return acc.toList

/-- `lookAhead p` parses `p` without consuming any input -/
def lookAhead (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := do
  let savePos ← getPosition
  try
    let x ← p
    setPosition savePos
    return x
  catch e =>
    setPosition savePos
    throw e

/-- `notFollowedBy p` succeeds only if `p` fails -/
@[inline]
def notFollowedBy (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit := do
  try
    let _ ← lookAhead p
  catch _ =>
    return
  throwUnexpected

/-- `anyToken` accepts any single token and returns that token -/
@[inline]
def anyToken : ParserT ε σ τ m τ :=
  tokenMap some

/-- `endOfInput` succeeds only when there is no input left -/
@[inline]
def endOfInput : ParserT ε σ τ m PUnit :=
  notFollowedBy anyToken

/-- `peek` returns the next token, without consuming any input -/
@[inline]
def peek : ParserT ε σ τ m τ :=
  lookAhead anyToken

/-- `optionD default p` tries to parse `p`, and returns `default` if `p` fails -/
@[specialize]
def optionD (default : α) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α :=
  try
    withBacktracking p
  catch _ =>
    return default

/-- `option! p` tries to parse `p`, and returns `Inhabited.default` if `p` fails -/
@[inline]
def option! [Inhabited α] (p : ParserT ε σ τ m α) : ParserT ε σ τ m α :=
  optionD default p

/-- `option? p` parses `p` returns `some x` if `p` returns `x`, and returns `none` if `p` fails -/
@[inline]
def option? (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Option α) :=
  optionD none (some <$> p)

/-- `optional p` tries to parse `p`, ignoring the output, never fails -/
@[inline]
def optional (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  option! (p *> return)

/-- `test p` returns `true` if `p` succeeds and `false` otherwise, never fails -/
@[inline]
def test (p : ParserT ε σ τ m α) : ParserT ε σ τ m Bool :=
  optionD false (p *> return true)

/-- `foldl f q p` -/
@[specialize]
partial def foldl (f : β → α → β) (init : β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m β :=
  loop init
where
  loop (y : β) := do
    match ← option? p with
    | some x => loop (f y x)
    | none => return y

/-- `foldr f p q` -/
@[inline]
partial def foldr (f : α → β → β) (p : ParserT ε σ τ m α) (q : ParserT ε σ τ m β) : ParserT ε σ τ m β :=
  try
    let x ← withBacktracking p
    let y ← foldr f p q
    return f x y
  catch _ => q

/-- `take n p` parses exactly `n` occurrences of `p`, and returns an array of the returned values of `p` -/
@[inline]
def take (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  rest n #[]
where
  rest : Nat → Array α → ParserT ε σ τ m (Array α)
    | 0, xs => return xs
    | n+1, xs => do rest n <| xs.push (← p)

/-- `takeUpTo n p` parses up to `n` occurrences of `p`, and returns an array of the returned values of `p` -/
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

/-- `takeMany p` parses zero or more occurrences of `p` until it fails, and returns an array of the returned values of `p` -/
@[inline]
def takeMany (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  foldl Array.push #[] p

/-- `takeMany1 p` parses one or more occurrences of `p` until it fails, and returns an array of the returned values of `p` -/
@[inline]
def takeMany1 (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  foldl Array.push #[(← p)] p

/-- `takeManyN n p` parses `n` or more occurrences of `p` until it fails, and returns an array of the returned values of `p` -/
@[inline]
def takeManyN (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  foldl Array.push (← take n p) p

/-- `takeUntil stop p` parses zero or more occurrences of `p` until `stop` succeeds, and returns an array of the returned values of `p` and the output of `stop` -/
partial def takeUntil (stop : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α × β) :=
  let _ := Inhabited.mk do return ((#[] : Array α), (← stop))
  rest #[]
where
  rest [Inhabited (ParserT ε σ τ m (Array α × β))] (acc : Array α) := do
    match ← option? stop with
    | some s => return (acc, s)
    | none => rest <| acc.push (← p)

/-- `drop n p` parses exactly `n` occurrences of `p`, ignoring all outputs from `p` -/
@[inline]
def drop (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  match n with
  | 0 => return
  | n+1 => p *> drop n p

/-- `dropUpTo n p` parses up to `n` occurrences of `p`, ignoring all outputs from `p` -/
@[inline]
def dropUpTo (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  match n with
  | 0 => return
  | n+1 => do
    match ← option? p with
    | some _ => drop n p
    | none => return

/-- `dropMany p` parses zero or more occurrences of `p` until it fails, ignoring all outputs from `p` -/
@[inline]
def dropMany (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  foldl (Function.const α) () p

/-- `dropMany1 p` parses one or more occurrences of `p` until it fails, ignoring all outputs from `p` -/
@[inline]
def dropMany1 (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  p *> foldl (Function.const α) () p

/-- `dropManyN n p` parses `n` or more occurrences of `p` until it fails, ignoring all outputs from `p` -/
@[inline]
def dropManyN (n : Nat) (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  drop n p *> foldl (Function.const α) () p

/-- `dropUntil stop p` runs `p` until `stop` succeeds, returns the output of `stop` ignoring all outputs from `p` -/
partial def dropUntil (stop : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m β :=
  loop
where
  loop := do
    match ← option? stop with
    | some s => return s
    | none => p *> loop

/-- `count p` parses occurrences of `p` until it fails, and returns the count of successes -/
@[inline]
partial def count (p : ParserT ε σ τ m α) : ParserT ε σ τ m Nat :=
  foldl (fun n _ => n+1) 0 p

/-- `countUpTo n p` parses up to `n` occurrences of `p` until it fails, and returns the count of successes -/
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

/-- `countUntil stop p` counts zero or more occurrences of `p` until `stop` succeeds, and returns an array of the returned values of `p` and the output of `stop` -/
partial def countUntil (stop : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Nat × β) := do
  let _ := Inhabited.mk do return (0, ← stop)
  loop 0
where
  loop [Inhabited (ParserT ε σ τ m (Nat × β))] (ct : Nat) := do
    match ← option? stop with
    | some s => return (ct, s)
    | none => p *> loop (ct+1)

/-- `endBy p sep` parses zero or more occurrences of `p`, separated and ended by `sep`, returns an array of values returned by `p` -/
@[inline]
def endBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  takeMany (p <* sep)

/-- `endBy1 p sep` parses one or more occurrences of `p`, separated and ended by `sep`, returns an array of values returned by `p` -/
@[inline]
def endBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  takeMany1 (p <* sep)

/-- `sepBy1 p sep` parses one or more occurrences of `p`, separated by `sep`, returns an array of values returned by `p` -/
@[inline]
def sepBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  foldl Array.push #[(← p)] (sep *> p)

/-- `sepBy p sep` parses zero or more occurrences of `p`, separated by `sep`, returns an array of values returned by `p` -/
@[inline]
def sepBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  match ← option? p with
  | some x => foldl Array.push #[x] (sep *> p)
  | none => return #[]

/-- `sepEndBy1 p sep` parses one or more occurrences of `p`, separated and optionally ended by `sep`, returns an array of values returned by `p` -/
@[inline]
def sepEndBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy1 sep p <* optional sep

/-- `sepEndBy p sep` parses zero or more occurrences of `p`, separated and optionally ended by `sep`, returns an array of values returned by `p` -/
@[inline]
def sepEndBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy sep p <* optional sep

/-- `sepNoEndBy1 p sep` parses one or more occurrences of `p`, separated `sep` but no trailing `sep`, returns an array of values returned by `p` -/
@[inline]
def sepNoEndBy1 (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy1 sep p <* withErrorMessage "unexpected trailing separator" (notFollowedBy sep)

/-- `sepNoEndBy p sep` parses zero or more occurrences of `p`, separated `sep` but no trailing `sep`, returns an array of values returned by `p` -/
@[inline]
def sepNoEndBy (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy sep p <* withErrorMessage "unexpected trailing separator" (notFollowedBy sep)

end Parser

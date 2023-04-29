/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Error
import Parser.Parser
import Parser.Stream

namespace Parser
variable {ε σ α β γ} [Parser.Stream σ α] [Parser.Error ε σ α] {m} [Monad m] [MonadExceptOf ε m]

/-- `tokenAux next?` reads a token from the stream using `next?` -/
@[inline] def tokenAux (next? : σ → Option (α × σ)) : ParserT ε σ α m α := do
  match next? (← StateT.get).stream with
  | some (tok, stream) =>
    StateT.set {stream := stream, dirty := true}
    return tok
  | none => throwUnexpected

/-- `tokenMap test` accepts token `t` with result `x` if `test t = some x`, otherise fails -/
@[specialize test] def tokenMap (test : α → Option β) : ParserT ε σ α m β := do
  let tok ← tokenAux Stream.next?
  match test tok with
  | some x => return x
  | none => throwUnexpected tok

/-- `tokenFilter test` accepts and returns token `t` if `test t = true`, otherwise fails -/
@[inline] def tokenFilter (test : α → Bool) : ParserT ε σ α m α :=
  tokenMap fun c => if test c then some c else none

/-- `token tk` accepts and returns `tk`, otherwise fails -/
@[inline] def token [BEq α] (tk : α) : ParserT ε σ α m α :=
  tokenFilter (. == tk)

/-- `tokenArray tks` accepts and returns `tks`, otherwise fails -/
def tokenArray [BEq α] (tks : Array α) : ParserT ε σ α m (Array α) :=
  withBacktracking do
    let mut acc : Array α := #[]
    for tk in tks do
      acc := acc.push (← token tk)
    return acc

/-- `tokenList tks` accepts and returns `tks`, otherwise fails -/
def tokenList [BEq α] (tks : List α) : ParserT ε σ α m (List α) :=
  withBacktracking do
    let mut acc : Array α := #[]
    for tk in tks do
      acc := acc.push (← token tk)
    return acc.toList

/-- `lookAhead p` parses `p` without consuming any input -/
def lookAhead (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  let savePos ← getPosition
  try
    let x ← p
    setPosition savePos false
    return x
  catch e =>
    setPosition savePos false
    throw e

/-- `notFollowedBy p` succeeds only if `p` fails -/
@[inline] def notFollowedBy (p : ParserT ε σ α m β) : ParserT ε σ α m Unit := do
  try
    let _ ← lookAhead p
  catch _ =>
    return
  throwUnexpected

/-- `anyToken` accepts any single token and returns that token -/
@[inline] def anyToken : ParserT ε σ α m α :=
  tokenMap some

/-- `endOfInput` succeeds only when there is no input left -/
@[inline] def endOfInput : ParserT ε σ α m Unit :=
  notFollowedBy anyToken

/-- `peek` returns the next token, without consuming any input -/
@[inline] def peek : ParserT ε σ α m α :=
  lookAhead anyToken

/-- `optionD default p` tries to parse `p`, and returns `default` if `p` fails -/
@[inline] def optionD (default : β) (p : ParserT ε σ α m β) : ParserT ε σ α m β :=
  try p catch _ => return default

/-- `option! p` tries to parse `p`, and returns `Inhabited.default` if `p` fails -/
@[inline] def option! [Inhabited β] (p : ParserT ε σ α m β) : ParserT ε σ α m β :=
  optionD default p

/-- `option? p` parses `p` returns `some x` if `p` returns `x`, and returns `none` if `p` fails -/
@[inline] def option? (p : ParserT ε σ α m β) : ParserT ε σ α m (Option β) :=
  optionD none (some <$> p)

/-- `optional p` tries to parse `p`, ignoring the output, never fails -/
@[inline] def optional (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  option! (p *> return)

/-- `test p` returns `true` if `p` succeeds and `false` otherwise, never fails -/
@[inline] def test (p : ParserT ε σ α m β) : ParserT ε σ α m Bool :=
  Option.isSome <$> option? p

@[specialize f]
private partial def foldAux (f : γ → β → γ) (y : γ) (p : ParserT ε σ α m β) : ParserT ε σ α m γ :=
  let rec rest (y : γ) : ParserT ε σ α m γ :=
    try
      let x ← withBacktracking p
      rest (f y x)
    catch _ => return y
  rest y

/-- `foldl f q p` -/
@[inline] def foldl (f : γ → β → γ) (q : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m γ := do
  foldAux f (← q) p

/-- `foldr f p q` -/
@[inline] partial def foldr (f : β → γ → γ) (p : ParserT ε σ α m β) (q : ParserT ε σ α m γ) : ParserT ε σ α m γ :=
  try
    let x ← withBacktracking p
    let y ← foldr f p q
    return f x y
  catch _ => q

/-- `take n p` parses exactly `n` occurrences of `p`, and returns an array of the returned values of `p` -/
@[inline] def take (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) :=
  let rec rest : Nat → Array β → ParserT ε σ α m (Array β)
  | 0, xs => return xs
  | n+1, xs => do
    let x ← p
    rest n (Array.push xs x)
  rest n #[]

/-- `takeUpTo n p` parses up to `n` occurrences of `p`, and returns an array of the returned values of `p` -/
@[inline] def takeUpTo (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) :=
  let rec rest : Nat → Array β → ParserT ε σ α m (Array β)
  | 0, xs => return xs
  | n+1, xs => try
      let x ← withBacktracking p
      rest n (Array.push xs x)
    catch _ => return xs
  rest n #[]

/-- `takeMany p` parses zero or more occurrences of `p` until it fails, and returns an array of the returned values of `p` -/
@[inline] def takeMany (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  foldAux Array.push #[] p

/-- `takeMany1 p` parses one or more occurrences of `p` until it fails, and returns an array of the returned values of `p` -/
@[inline] def takeMany1 (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  foldAux Array.push #[(← p)] p

/-- `takeManyN n p` parses `n` or more occurrences of `p` until it fails, and returns an array of the returned values of `p` -/
@[inline] def takeManyN (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  foldAux Array.push (← take n p) p

/-- `takeUntil stop p` parses zero or more occurrences of `p` until `stop` succeeds, and returns an array of the returned values of `p` and the output of `stop` -/
partial def takeUntil [Inhabited γ] (stop : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β × γ) :=
  -- FIXME: `Inhabited γ` is not necessary here
  let rec loop (acc : Array β) : ParserT ε σ α m (Array β × γ) := do
    try
      return (acc, ← stop)
    catch _ =>
      let _ := inferInstanceAs (Inhabited γ)
      loop <| acc.push (← p)
  loop #[]

/-- `drop n p` parses exactly `n` occurrences of `p`, ignoring all outputs from `p` -/
@[inline] def drop (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  match n with
  | 0 => return
  | n+1 => do
      let _ ← p
      drop n p

/-- `dropUpTo n p` parses up to `n` occurrences of `p`, ignoring all outputs from `p` -/
@[inline] def dropUpTo (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  match n with
  | 0 => return
  | n+1 => try
      let _ ← withBacktracking p
      drop n p
    catch _ => return

/-- `dropMany p` parses zero or more occurrences of `p` until it fails, ignoring all outputs from `p` -/
@[inline] def dropMany (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  foldAux (Function.const β) () p

/-- `dropMany1 p` parses one or more occurrences of `p` until it fails, ignoring all outputs from `p` -/
@[inline] def dropMany1 (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  p *> foldAux (Function.const β) () p

/-- `dropManyN n p` parses `n` or more occurrences of `p` until it fails, ignoring all outputs from `p` -/
@[inline] def dropManyN (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  drop n p *> foldAux (Function.const β) () p

/-- `dropUntil stop p` runs `p` until `stop` succeeds, returns the output of `stop` ignoring all outputs from `p` -/
partial def dropUntil (stop : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m γ :=
  let rec loop := do
    try
      stop
    catch _ =>
      drop 1 p
      loop
  loop

/-- `count p` parses occurrences of `p` until it fails, and returns the count of successes -/
@[inline] def count (p : ParserT ε σ α m β) : ParserT ε σ α m Nat := do
  foldAux (fun n _ => n+1) 0 p

/-- `countUpTo n p` parses up to `n` occurrences of `p` until it fails, and returns the count of successes -/
@[inline] def countUpTo (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m Nat :=
  let rec loop : Nat → Nat → ParserT ε σ α m Nat
  | 0, c => return c
  | n+1, c =>
    try
      let _ ← withBacktracking p
      loop n (c+1)
    catch _ =>
      return c
  loop n 0

/-- `countUntil stop p` counts zero or more occurrences of `p` until `stop` succeeds, and returns an array of the returned values of `p` and the output of `stop` -/
partial def countUntil [Inhabited γ] (stop : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Nat × γ) := do
  -- FIXME: `Inhabited γ` is not necessary here
  let rec loop (ct : Nat) := do
    try
      return (ct, ← stop)
    catch _ =>
      let _ := inferInstanceAs (Inhabited γ)
      drop 1 p
      loop (ct+1)
  loop 0

/-- `endBy p sep` parses zero or more occurrences of `p`, separated and ended by `sep`, returns an array of values returned by `p` -/
@[inline] def endBy (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) :=
  takeMany (p <* sep)

/-- `endBy1 p sep` parses one or more occurrences of `p`, separated and ended by `sep`, returns an array of values returned by `p` -/
@[inline] def endBy1 (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  takeMany1 (p <* sep)

@[specialize]
private partial def sepByAux (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) (acc : Array β) : ParserT ε σ α m (Array β) := do
  try
    drop 1 sep
  catch _ =>
    return acc
  sepByAux sep p (acc.push (← p))

/-- `sepBy1 p sep` parses one or more occurrences of `p`, separated by `sep`, returns an array of values returned by `p` -/
@[inline] def sepBy1 (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  sepByAux sep p #[(← p)]

/-- `sepBy p sep` parses zero or more occurrences of `p`, separated by `sep`, returns an array of values returned by `p` -/
@[inline] def sepBy (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  match ← option? p with
  | some v => sepByAux sep p #[v]
  | none => return #[]

@[specialize]
private partial def sepEndByAux (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) (acc : Array β) : ParserT ε σ α m (Array β) := do
  try
    drop 1 sep
    sepEndByAux sep p (acc.push (← p))
  catch _ =>
    return acc

/-- `sepEndBy1 p sep` parses one or more occurrences of `p`, separated and optionally ended by `sep`, returns an array of values returned by `p` -/
@[inline] def sepEndBy1 (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  sepEndByAux sep p #[(← p)]

/-- `sepEndBy p sep` parses zero or more occurrences of `p`, separated and optionally ended by `sep`, returns an array of values returned by `p` -/
@[inline] def sepEndBy (sep : ParserT ε σ α m γ) (p : ParserT ε σ α m α) : ParserT ε σ α m (Array α) := do
  match ← option? p with
  | some v => sepEndByAux sep p #[v]
  | none => return #[]

end Parser

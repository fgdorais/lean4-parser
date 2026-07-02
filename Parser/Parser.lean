/-
Copyright © 2022-2024 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Parser.Prelude
public import Parser.Error
public import Parser.Stream

public section

/-- Parser result type. -/
protected inductive Parser.Result {τ} (ε σ α : Type u) [Parser.Stream σ τ] : Type u
  /-- Result: success! -/
  | ok : σ → Parser.Stream.Position σ → α → Parser.Result ε σ α
  /-- Result: error! -/
  | error : σ → Parser.Stream.Position σ → ε → Parser.Result ε σ α
deriving Inhabited -- TODO : manually implement Repr

/--
`ParserT ε σ τ` is a monad transformer to parse tokens of type `τ` from the stream type `σ` with
error type `ε`.
-/
@[expose]
def ParserT (ε σ τ : Type _) [Parser.Stream σ τ] [Parser.Error ε σ τ] (m : Type _ → Type _)
  (α : Type _) : Type _ := σ → Parser.Stream.Position σ → m (Parser.Result ε σ α)

/-- Run the monadic parser `p` on input stream `s`. -/
@[inline]
def ParserT.run [stream : Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p : ParserT ε σ τ m α) (s : σ) (pos : optParam stream.Position (stream.start s)):
  m (Parser.Result ε σ α) := p s pos

instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  Monad (ParserT ε σ τ m) where
  pure x s pos := return .ok s pos x
  bind x f s pos := x s pos >>= fun
    | .ok s pos a => f a s pos
    | .error s pos e => return .error s pos e
  map f x s pos := x s pos >>= fun
    | .ok s pos a => return .ok s pos (f a)
    | .error s pos e => return .error s pos e
  seq f x s pos := f s pos >>= fun
    | .ok s pos f => x () s pos >>= fun
      | .ok s pos x => return .ok s pos (f x)
      | .error s pos e => return .error s pos e
    | .error s pos e => return .error s pos e
  seqLeft x y s pos := x s pos >>= fun
    | .ok s pos x => y () s pos >>= fun
      | .ok s pos _ => return .ok s pos x
      | .error s pos e => return .error s pos e
    | .error s pos e => return .error s pos e
  seqRight x y s pos := x s pos >>= fun
    | .ok s pos _ => y () s pos >>= fun
      | .ok s pos y => return .ok s pos y
      | .error s pos e => return .error s pos e
    | .error s pos e => return .error s pos e

instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  MonadExceptOf ε (ParserT ε σ τ m) where
  throw e s pos := return .error s pos e
  tryCatch p c s pos := p s pos >>= fun
    | .ok s pos v => return .ok s pos v
    | .error s pos e => (c e).run s pos

instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  OrElse (ParserT ε σ τ m α) where
  orElse p q s pos :=
    p s pos >>= fun
    | .ok s pos v => return .ok s pos v
    | .error s _ _ => q () s pos
instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  MonadLift m (ParserT ε σ τ m) where
  monadLift x s pos := (.ok s pos ·) <$> x

/--
`Parser ε σ τ` monad to parse tokens of type `τ` from the stream type `σ` with error type `ε`.
-/
abbrev Parser (ε σ τ) [Parser.Stream σ τ] [Parser.Error ε σ τ] := ParserT ε σ τ Id

/-- Run parser `p` on input stream `s`. -/
@[inline]
protected def Parser.run {ε σ τ α} [Parser.Stream σ τ] [Parser.Error ε σ τ] (p : Parser ε σ τ α)
  (s : σ) : Parser.Result ε σ α := p s (Stream.start s)

/--
`TrivialParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with trivial
error handling.
-/
abbrev TrivialParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT Parser.Error.Trivial σ τ m

/--
`TrivialParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with trivial error
handling.
-/
abbrev TrivialParser (σ τ) [Parser.Stream σ τ] := Parser Parser.Error.Trivial σ τ

/--
`BasicParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with basic
error handling.
-/
abbrev BasicParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT (Parser.Error.Basic σ τ) σ τ m

/--
`BasicParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with basic error handling.
-/
abbrev BasicParser (σ τ) [Parser.Stream σ τ] := Parser (Parser.Error.Basic σ τ) σ τ

/--
`SimpleParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with simple
error handling.
-/
abbrev SimpleParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT (Parser.Error.Simple σ τ) σ τ m

/--
`SimpleParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with simple error handling.
-/
abbrev SimpleParser (σ τ) [Parser.Stream σ τ] := Parser (Parser.Error.Simple σ τ) σ τ

namespace Parser
variable {ε σ α β : Type u} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadExceptOf ε m]

/-! # Stream Functions -/

/-- Get parser stream. -/
@[inline]
def getStream : ParserT ε σ τ m σ :=
  fun s pos => return .ok s pos s

/-- Get stream position from parser. -/
@[inline]
def getPosition : ParserT ε σ τ m (Stream.Position σ) :=
  fun s pos => return .ok s pos pos

/-- Set stream position from parser. -/
@[inline]
def setPosition (pos : Stream.Position σ) : ParserT ε σ τ m PUnit := do
  fun s _ => return .ok s pos PUnit.unit

/-- `withBacktracking p` parses `p` but does not consume any input on error. -/
@[inline]
def withBacktracking (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := do
  let savePos ← getPosition
  try p
  catch e =>
    setPosition savePos
    throw e

/--
`withCapture p` parses `p` and returns the output of `p` with the corresponding stream segment.
-/
def withCapture (p : ParserT ε σ τ m α) :
  ParserT ε σ τ m (α × Stream.Segment σ) := do
  let startPos ← getPosition
  let x ← p
  let stopPos ← getPosition
  return (x, startPos, stopPos)

/-! # Error Functions -/

/-- Throw error on unexpected token. -/
@[inline]
def throwUnexpected (input : Option τ := none) : ParserT ε σ τ m α := do
  throw (Error.unexpected (← getPosition) input)

/-- Throw error with additional message. -/
@[inline]
def throwErrorWithMessage (e : ε) (msg : String) : ParserT ε σ τ m α := do
  throw (Error.addMessage e (← getPosition) msg)

/-- Throw error on unexpected token with error message. -/
@[inline]
def throwUnexpectedWithMessage (input : Option τ := none) (msg : String) : ParserT ε σ τ m α := do
  throwErrorWithMessage (Error.unexpected (← getPosition) input) msg

/-- Add message on parser error. -/
@[inline]
def withErrorMessage (msg : String) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := do
  try p catch e => throwErrorWithMessage e msg

/-! # Low-Level Combinators -/

/-! ### `foldl` family -/

@[specialize]
private partial def efoldlPAux [Inhabited ε] [Inhabited σ] [Inhabited β]
    (f : β → α → ParserT ε σ τ m β) (p : ParserT ε σ τ m α) (y : β) (s : σ)
    (pos : Stream.Position σ ) : m (Parser.Result ε σ (β × ε × Bool)) :=
  p s pos >>= fun
    | .ok s pos' x => f y x s pos' >>= fun
      | .ok s pos' y => efoldlPAux f p y s pos'
      | .error s _ e => return .ok s pos (y, e, true)
    | .error s _ e => return .ok s pos (y, e, false)

/--
`foldlP f init p` folds the parser function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as the update
parser function `(p >>= f ⬝)` fails. Then the final folding result is returned along with the pair:

- `(e, true)` if the final `p` succeeds but then `f` fails reporting error `e`.
- `(e, false)` if the final `p` fails reporting error `e`.

In either case, the final `p` is not consumed. This parser never fails.
-/
@[inline]
def efoldlP (f : β → α → ParserT ε σ τ m β) (init : β) (p : ParserT ε σ τ m α) :
  ParserT ε σ τ m (β × ε × Bool) :=
  fun s =>
    have : Inhabited β := ⟨init⟩
    have : Inhabited σ := ⟨s⟩
    have : Inhabited ε := ⟨Error.unexpected (Stream.start s) none⟩
    efoldlPAux f p init s

/--
`foldlM f init p` folds the monadic function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails and
the error reported by `p` is returned along with the result of folding. This parser never fails.
-/
@[inline]
def efoldlM (f : β → α → m β) (init : β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (β × ε) :=
  efoldlP (fun y x => monadLift <| f y x) init p >>= fun (y,e,_) => return (y,e)

/--
`foldl f init p` folds the function `f` from left to right using `init` as an intitial value
and the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails and the
error reported by `p` is returned along with the result of folding. This parser never fails.
-/
@[inline]
def efoldl (f : β → α → β) (init : β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (β × ε) :=
  efoldlM (fun y x => pure <| f y x) init p

/--
`foldlP f init p` folds the parser function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as the update
function `(p >>= f ·)` fails. This parser never fails.
-/
@[inline]
def foldlP (f : β → α → ParserT ε σ τ m β) (init : β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m β :=
  Prod.fst <$> efoldlP f init p

/--
`foldlM f init p` folds the monadic function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails.
This parser never fails.
-/
@[inline]
def foldlM (f : β → α → m β) (init : β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m β :=
  Prod.fst <$> efoldlM f init p

/--
`foldl f init p` folds the function `f` from left to right using `init` as an intitial value and
the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails.
This parser never fails.
-/
@[inline]
def foldl (f : β → α → β) (init : β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m β :=
  Prod.fst <$> efoldl f init p

/-! ### `option` family -/

/--
`eoption p` tries to parse `p` (with backtracking) and returns:

- `Sum.inl x` if `p` returns `x`,
- `Sum.inr e` if `p`fails with error `e`.

This parser never fails.
-/
@[specialize]
def eoption (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Sum α ε) :=
  fun s pos =>
    p s pos >>= fun
    | .ok s pos x => return .ok s pos (.inl x)
    | .error s _ e => return .ok s pos (.inr e)

/--
`optionM p` tries to parse `p` (with backtracking) and returns `x` if `p` returns `x`, returns the
monadic value `default` if `p` fails. This parser never fails.
-/
@[inline]
def optionM (p : ParserT ε σ τ m α) (default : m α) : ParserT ε σ τ m α := do
  match ← eoption p with
  | .inl x => return x
  | .inr _ => default

/--
`optionD p` tries to parse `p` (with backtracking) and returns `x` if `p` returns `x`, returns
`default` if `p` fails. This parser never fails.
-/
@[inline]
def optionD (p : ParserT ε σ τ m α) (default : α) : ParserT ε σ τ m α :=
  optionM p (pure default)

/--
`option! p` tries to parse `p` (with backtracking) and returns `x` if `p` returns `x`, returns
`Inhabited.default` if `p` fails. This parser never fails.
-/
@[inline]
def option! [Inhabited α] (p : ParserT ε σ τ m α) : ParserT ε σ τ m α :=
  optionD p default

/--
`option? p` tries to parse `p` and returns `some x` if `p` returns `x`, returns `none` if `p`
fails. This parser never fails.
-/
@[inline]
def option? (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Option α) :=
  option! (some <$> p)

/--
`optional p` tries to parse `p` (with backtracking) ignoring output or errors. This parser never
fails.
-/
@[inline]
def optional (p : ParserT ε σ τ m α) : ParserT ε σ τ m PUnit :=
  eoption p *> return

/-! ### `first` family -/

/--
`efirst ps` tries parsers from the list `ps` in order (with backtracking) until one succeeds:

- Once a parser `p` succeeds with value `x` then `some x` is returne along with the list of errors
  from all previous parsers.
- If none succeed then `none` is returned along with the list of errors of all parsers.

This parser never fails.
-/
def efirst (ps : List (ParserT ε σ τ m α)) : ParserT ε σ τ m (Option α × List ε) :=
  go ps []
where
  go : List (ParserT ε σ τ m α) → List ε → ParserT ε σ τ m (Option α × List ε)
  | [], es => return (none, es.reverse)
  | p :: ps, es => do
    match ← eoption p with
    | .inl x => return (some x, es.reverse)
    | .inr e => go ps (e :: es)

/--
`first ps` tries parsers from the list `ps` in order (with backtracking) until one succeeds and
returns the result of that parser.

The optional parameter `combine` can be used to control the error reported when all parsers fail.
The default is to only report the error from the last parser.
-/
def first (ps : List (ParserT ε σ τ m α)) (combine : ε → ε → ε := fun _ => id) :
  ParserT ε σ τ m α := do
  go ps (Error.unexpected (← getPosition) none)
where
  go : List (ParserT ε σ τ m α) → ε → ParserT ε σ τ m α
    | [], e, s, pos => return .error s pos e
    | p :: ps, e, s, pos =>
      p s pos >>= fun
      | .ok s pos v => return .ok s pos v
      | .error s _ f => go ps (combine e f) s pos
end Parser

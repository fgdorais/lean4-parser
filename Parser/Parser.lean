/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Error
import Parser.Stream

/-- Parser result type -/
protected inductive Parser.Result (ε σ : Type _) : Type _ → Type _
  /-- Result: success -/
  | ok : σ → α → Parser.Result ε σ α
  /-- Result: error -/
  | error : σ → ε → Parser.Result ε σ α
deriving Repr

/-- `ParserT ε σ τ` is a monad transformer to parse tokens of type `τ` from the stream type `σ` with error type `ε` -/
def ParserT (ε σ τ : Type _) [Parser.Stream σ τ] [Parser.Error ε σ τ] (m : Type _ → Type _)
  (α : Type _) : Type _ := σ → m (Parser.Result ε σ α)

/-- Run the monadic parser `p` on input stream `s` -/
@[inline]
def ParserT.run [Parser.Stream σ τ] [Parser.Error ε σ τ] (p : ParserT ε σ τ m α) (s : σ) : m (Parser.Result ε σ α) := p s

instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  Monad (ParserT ε σ τ m) where
  pure x s := return .ok s x
  bind x f s := x s >>= fun
    | .ok s a => f a s
    | .error s e => return .error s e
  map f x s := x s >>= fun
    | .ok s a => return .ok s (f a)
    | .error s e => return .error s e
  seq f x s := f s >>= fun
    | .ok s f => x () s >>= fun
      | .ok s x => return .ok s (f x)
      | .error s e => return .error s e
    | .error s e => return .error s e
  seqLeft x y s := x s >>= fun
    | .ok s x => y () s >>= fun
      | .ok s _ => return .ok s x
      | .error s e => return .error s e
    | .error s e => return .error s e
  seqRight x y s := x s >>= fun
    | .ok s _ => y () s >>= fun
      | .ok s y => return .ok s y
      | .error s e => return .error s e
    | .error s e => return .error s e

instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  MonadExceptOf ε (ParserT ε σ τ m) where
  throw e s := return .error s e
  tryCatch p c s := p s >>= fun
    | .ok s v => return .ok s v
    | .error s e => (c e).run s

instance (σ ε τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] :
  OrElse (ParserT ε σ τ m α) where
  orElse p q s := p s >>= fun
    | .ok s v => return .ok s v
    | .error _ _ => q () s

/-- `Parser ε σ τ` monad to parse tokens of type `τ` from the stream type `σ` with error type `ε` -/
abbrev Parser (ε σ τ) [Parser.Stream σ τ] [Parser.Error ε σ τ] := ParserT ε σ τ Id

/-- Run parser `p` on input stream `s` -/
@[inline]
protected def Parser.run {ε σ τ α} [Parser.Stream σ τ] [Parser.Error ε σ τ] (p : Parser ε σ τ α)
  (s : σ) : Parser.Result ε σ α := p s

/-- `TrivialParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with trivial error handling -/
abbrev TrivialParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT Parser.Error.Trivial σ τ m

/-- `TrivialParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with trivial error handling -/
abbrev TrivialParser (σ τ) [Parser.Stream σ τ] := Parser Parser.Error.Trivial σ τ

/-- `BasicParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with basic error handling -/
abbrev BasicParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT (Parser.Error.Basic σ τ) σ τ m

/-- `BasicParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with basic error handling -/
abbrev BasicParser (σ τ) [Parser.Stream σ τ] := Parser (Parser.Error.Basic σ τ) σ τ

/-- `SimpleParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with simple error handling -/
abbrev SimpleParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT (Parser.Error.Simple σ τ) σ τ m

/-- `SimpleParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with simple error handling -/
abbrev SimpleParser (σ τ) [Parser.Stream σ τ] := Parser (Parser.Error.Simple σ τ) σ τ

namespace Parser
variable {ε σ τ m α β} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadExceptOf ε m]

/-- Get parser stream -/
@[inline]
def getStream : ParserT ε σ τ m σ :=
  fun s => return .ok s s

/-- Set parser stream -/
@[inline]
def setStream (s : σ) : ParserT ε σ τ m PUnit :=
  fun _ => return .ok s PUnit.unit

/-- Get stream position from parser -/
@[inline]
def getPosition : ParserT ε σ τ m (Stream.Position σ) :=
  Stream.getPosition <$> getStream

/-- Set stream position of parser -/
@[inline]
def setPosition (pos : Stream.Position σ) : ParserT ε σ τ m PUnit := do
  setStream <| Stream.setPosition (← getStream) pos

/-- Throw error on unexpected input -/
@[inline]
def throwUnexpected (input : Option τ := none) : ParserT ε σ τ m α := do
  throw (Error.unexpected (← getPosition) input)

/-- Throw error with additional message -/
@[inline]
def throwErrorWithMessage (e : ε) (msg : String) : ParserT ε σ τ m α := do
  throw (Error.addMessage e (← getPosition) msg)

/-- Add message on parser error -/
@[inline]
def withErrorMessage (msg : String) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := do
  try p catch e => throwErrorWithMessage e msg

@[inline]
def throwUnexpectedWithMessage (input : Option τ := none) (msg : String) : ParserT ε σ τ m α := do
  throwErrorWithMessage (Error.unexpected (← getPosition) input) msg

/-- `withBacktracking p` parses `p` but does not consume any input on error -/
@[inline]
def withBacktracking (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := do
  let savePos ← getPosition
  try p
  catch e =>
    setPosition savePos
    throw e

/-- `withCapture p` parses `p` and returns the output of `p` with the corresponding stream segment -/
def withCapture {ε σ α : Type _} [Parser.Stream σ τ] [Parser.Error ε σ τ] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (α × Stream.Segment σ) := do
  let startPos ← getPosition
  let x ← p
  let stopPos ← getPosition
  return (x, startPos, stopPos)

/-- `first ps` tries parsers from the list `ps` until one succeeds -/
def first (ps : List (ParserT ε σ τ m α)) (combine : ε → ε → ε := fun _ => id) : ParserT ε σ τ m α := do
  go ps (Error.unexpected (← getPosition) none)
where
  go : List (ParserT ε σ τ m α) → ε → ParserT ε σ τ m α
    | [], e, s => return .error s e
    | p :: ps, e, s =>
      p s >>= fun
      | .ok s v => return .ok s v
      | .error _ f => go ps (combine e f) s

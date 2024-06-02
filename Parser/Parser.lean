/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Error
import Parser.Stream

/-- Parser state -/
protected structure Parser.State (σ τ : Type _) [Parser.Stream σ τ] where
  /-- Parser stream -/
  stream : σ
  /-- Whether the parser has consumed any input -/
  dirty : Bool := false

/-- Parser result type -/
inductive Parser.Result (ε σ τ : Type _)
  /-- Result: success -/
  | ok : σ → τ → Result ε σ τ
  /-- Result: error -/
  | error : ε → Result ε σ τ
deriving Repr

/-- `ParserT ε σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with error type `ε` -/
@[nolint unusedArguments]
def ParserT (ε σ τ) (m : Type _ → Type _) [Parser.Stream σ τ] [Parser.Error ε σ τ] :=
  StateT σ m
instance (ε σ τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] : Monad (ParserT ε σ τ m) := inferInstanceAs (Monad (StateT σ m))
instance (ε σ τ m) [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadExceptOf ε m] : MonadExceptOf ε (ParserT ε σ τ m) := inferInstanceAs (MonadExceptOf ε (StateT σ m))

/-- Run parser transformer -/
@[inline]
protected def ParserT.run.{u} {ε σ : Type u} {τ α m} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadExceptOf ε m] (p : ParserT ε σ τ m α) (s : σ) : m (Parser.Result ε σ α) :=
  try
    let (val, s) ← StateT.run p s
    return .ok s val
  catch e =>
    return .error e

/-- `BasicParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with basic error handling -/
abbrev BasicParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT (Parser.Error.Simple σ τ) σ τ m

/-- `SimpleParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with simple error handling -/
abbrev SimpleParserT (σ τ) [Parser.Stream σ τ] (m) := ParserT (Parser.Error.Simple σ τ) σ τ m

/-- `Parser ε σ τ` monad to parse tokens of type `τ` from the stream `σ` with error type `ε` -/
abbrev Parser (ε σ τ) [Parser.Stream σ τ] [Parser.Error ε σ τ] := ParserT ε σ τ (Except ε)

/-- Run parser -/
@[inline]
protected def Parser.run {ε σ τ α} [Parser.Stream σ τ] [Parser.Error ε σ τ] (p : Parser ε σ τ α) (s : σ) : Parser.Result ε σ α :=
  match ParserT.run p s with
  | .ok v => v
  | .error e => .error e

/-- `BasicParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with basic error handling -/
abbrev BasicParser (σ τ) [Parser.Stream σ τ] := Parser (Parser.Error.Simple σ τ) σ τ

/-- `SimpleParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with simple error handling -/
abbrev SimpleParser (σ τ) [Parser.Stream σ τ] := Parser (Parser.Error.Simple σ τ) σ τ

namespace Parser
variable {ε σ τ m α β} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadExceptOf ε m]

/-- Get stream position from parser -/
@[inline]
def getPosition : ParserT ε σ τ m (Stream.Position σ) :=
  Stream.getPosition <$> StateT.get

/-- Set stream position of parser -/
@[inline]
def setPosition (pos : Stream.Position σ) : ParserT ε σ τ m PUnit := do
  StateT.set <| Stream.setPosition (← StateT.get) pos

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
  try p
  catch e => throwErrorWithMessage e msg

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
def withCapture (p : ParserT ε σ τ m α) : ParserT ε σ τ m (α × Stream.Segment σ) := do
  let startPos ← getPosition
  let x ← p
  let stopPos ← getPosition
  return (x, startPos, stopPos)

/- Override default `OrElse` so that the first consumes no input when it fails -/
@[inline]
instance : OrElse (ParserT ε σ τ m α) where
  orElse p q :=
    try withBacktracking p
    catch _ => q ()

/-- `first ps` tries parsers from the list `ps` until one succeeds -/
def first (ps : List (ParserT ε σ τ m α)) (combine : ε → ε → ε := fun _ => id) : ParserT ε σ τ m α := do
  go ps (Error.unexpected (← getPosition) none)
where
  go : List (ParserT ε σ τ m α) → ε → ParserT ε σ τ m α
    | [], e => throw e
    | p :: ps, e =>
      try withBacktracking p
      catch f => go ps (combine e f)

end Parser

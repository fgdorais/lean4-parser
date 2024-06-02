/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Error
import Parser.Stream

/-- Parser state -/
protected structure Parser.State (σ α : Type _) [Parser.Stream σ α] where
  /-- Parser stream -/
  stream : σ
  /-- Whether the parser has consumed any input -/
  dirty : Bool := false

/-- Parser result type -/
inductive Parser.Result (ε σ α : Type _)
  /-- Result: success -/
  | ok : σ → α → Result ε σ α
  /-- Result: error -/
  | error : ε → Result ε σ α
deriving Repr

/-- `ParserT ε σ α` monad transformer to parse tokens of type `α` from the stream `σ` with error type `ε` -/
@[nolint unusedArguments]
def ParserT (ε σ α) (m : Type _ → Type _) [Parser.Stream σ α] [Parser.Error ε σ α] :=
  StateT σ m
instance (ε σ α m) [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] : Monad (ParserT ε σ α m) := inferInstanceAs (Monad (StateT σ m))
instance (ε σ α m) [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] [MonadExceptOf ε m] : MonadExceptOf ε (ParserT ε σ α m) := inferInstanceAs (MonadExceptOf ε (StateT σ m))

/-- Run parser transformer -/
@[inline]
protected def ParserT.run.{u} {ε σ : Type u} {α β m} [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] [MonadExceptOf ε m] (p : ParserT ε σ α m β) (s : σ) : m (Parser.Result ε σ β) :=
  try
    let (val, s) ← StateT.run p s
    return .ok s val
  catch e =>
    return .error e

/-- `BasicParserT σ α` monad transformer to parse tokens of type `α` from the stream `σ` with basic error handling -/
abbrev BasicParserT (σ α) [Parser.Stream σ α] (m) := ParserT (Parser.Error.Simple σ α) σ α m

/-- `SimpleParserT σ α` monad transformer to parse tokens of type `α` from the stream `σ` with simple error handling -/
abbrev SimpleParserT (σ α) [Parser.Stream σ α] (m) := ParserT (Parser.Error.Simple σ α) σ α m

/-- `Parser ε σ α` monad to parse tokens of type `α` from the stream `σ` with error type `ε` -/
abbrev Parser (ε σ α) [Parser.Stream σ α] [Parser.Error ε σ α] := ParserT ε σ α (Except ε)

/-- Run parser -/
@[inline]
protected def Parser.run {ε σ α β} [Parser.Stream σ α] [Parser.Error ε σ α] (p : Parser ε σ α β) (s : σ) : Parser.Result ε σ β :=
  match ParserT.run p s with
  | .ok v => v
  | .error e => .error e

/-- `BasicParser σ α` monad to parse tokens of type `α` from the stream `σ` with basic error handling -/
abbrev BasicParser (σ α) [Parser.Stream σ α] := Parser (Parser.Error.Simple σ α) σ α

/-- `SimpleParser σ α` monad to parse tokens of type `α` from the stream `σ` with simple error handling -/
abbrev SimpleParser (σ α) [Parser.Stream σ α] := Parser (Parser.Error.Simple σ α) σ α

namespace Parser
variable {ε σ α m β γ} [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] [MonadExceptOf ε m]

/-- Get stream position from parser -/
@[inline]
def getPosition : ParserT ε σ α m (Stream.Position σ) :=
  Stream.getPosition <$> StateT.get

/-- Set stream position of parser -/
@[inline]
def setPosition (pos : Stream.Position σ) : ParserT ε σ α m Unit := do
  StateT.set <| Stream.setPosition (← StateT.get) pos

/-- Throw error on unexpected input -/
@[inline]
def throwUnexpected (input : Option α := none) : ParserT ε σ α m β := do
  throw (Error.unexpected (← getPosition) input)

/-- Throw error with additional message -/
@[inline]
def throwErrorWithMessage (e : ε) (msg : String) : ParserT ε σ α m β := do
  throw (Error.addMessage e (← getPosition) msg)

/-- Add message on parser error -/
@[inline]
def withErrorMessage (msg : String) (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  try p
  catch e => throwErrorWithMessage e msg

@[inline]
def throwUnexpectedWithMessage (input : Option α := none) (msg : String) : ParserT ε σ α m β := do
  throwErrorWithMessage (Error.unexpected (← getPosition) input) msg

/-- `withBacktracking p` parses `p` but does not consume any input on error -/
@[inline]
def withBacktracking (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  let savePos ← getPosition
  try p
  catch e =>
    setPosition savePos
    throw e

/-- `withCapture p` parses `p` and returns the output of `p` with the corresponding stream segment -/
def withCapture (p : ParserT ε σ α m β) : ParserT ε σ α m (β × Stream.Segment σ) := do
  let startPos ← getPosition
  let x ← p
  let stopPos ← getPosition
  return (x, startPos, stopPos)

/- Override default `OrElse` so that the first consumes no input when it fails -/
@[inline]
instance : OrElse (ParserT ε σ α m β) where
  orElse p q :=
    try withBacktracking p
    catch _ => q ()

/-- `first ps` tries parsers from the list `ps` until one succeeds -/
def first (ps : List (ParserT ε σ α m β)) (combine : ε → ε → ε := fun _ => id) : ParserT ε σ α m β := do
  go ps (Error.unexpected (← getPosition) none)
where
  go : List (ParserT ε σ α m β) → ε → ParserT ε σ α m β
    | [], e => throw e
    | p :: ps, e =>
      try withBacktracking p
      catch f => go ps (combine e f)

end Parser

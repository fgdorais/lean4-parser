import Parser.Prelude
import Parser.Error
import Parser.Stream

/-- parser state -/
protected structure Parser.State (σ α : Type _) [Parser.Stream σ α] where
  /-- parser stream -/
  stream : σ
  /-- whether the parser has consumed any input -/
  dirty : Bool := false

/-- parser result -/
inductive Parser.Result (ε σ α : Type _)
| ok : σ → α → Result ε σ α
| error : ε → Result ε σ α
deriving Repr

/-- `ParserT ε σ α` monad transformer to parse tokens of type `α` from the stream `σ` with error type `ε` -/
@[nolint unusedArguments]
def ParserT.{u} (ε σ : Type u) (α : Type _) (m : Type _ → Type _) [Parser.Stream σ α] [Parser.Error ε σ α] :=
  StateT (Parser.State σ α) m
instance (ε σ α m) [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] : Monad (ParserT ε σ α m) := inferInstanceAs (Monad (StateT (Parser.State σ α) m))
instance (ε σ α m) [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] [MonadExceptOf ε m] : MonadExceptOf ε (ParserT ε σ α m) := inferInstanceAs (MonadExceptOf ε (StateT (Parser.State σ α) m))

/-- run parser transformer -/
@[inline] protected def ParserT.run.{u} {ε σ : Type u} {α β m} [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] [MonadExceptOf ε m] (p : ParserT ε σ α m β) (s : σ) : m (Parser.Result ε σ β) :=
  try
    let (val, s) ← StateT.run p {stream := s}
    return .ok s.stream val
  catch e =>
    return .error e

/-- `Parser ε σ α` monad to parse tokens of type `α` from the stream `σ` with error type `ε` -/
abbrev Parser (ε σ α) [Parser.Stream σ α] [Parser.Error ε σ α] := ParserT ε σ α (Except ε)

/-- run parser -/
@[inline] protected def Parser.run {ε σ α β} [Parser.Stream σ α] [Parser.Error ε σ α] (p : Parser ε σ α β) (s : σ) : Parser.Result ε σ β :=
  match ParserT.run p s with
  | .ok v => v
  | .error e => .error e

/-- `SimpleParserT σ α` monad transformer to parse tokens of type `α` from the stream `σ` with simple error handling -/
abbrev SimpleParserT (σ α) [Parser.Stream σ α] (m) := ParserT (Parser.Error.Simple σ α) σ α m

/-- `SimpleParser σ α` monad to parse tokens of type `α` from the stream `σ` with simple error handling -/
abbrev SimpleParser (σ α) [Parser.Stream σ α] := Parser (Parser.Error.Simple σ α) σ α

namespace Parser
variable {ε σ α m β γ} [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] [MonadExceptOf ε m]

/-- check whether parser has consumed any input -/
@[inline] def hasConsumed : ParserT ε σ α m Bool := do
  let s ← StateT.get
  return s.dirty

/-- get stream position from parser -/
@[inline] def getPosition : ParserT ε σ α m (Stream.Position σ α) := do
  let s ← StateT.get
  return Stream.getPosition s.stream

/-- set stream position of parser -/
@[inline] def setPosition (pos : Stream.Position σ α) (dirty? : Option Bool := none) : ParserT ε σ α m Unit := do
  let s ← StateT.get
  StateT.set {
    stream := Stream.setPosition s.stream pos
    dirty := dirty?.getD s.dirty
  }

/-- throw error on unexpected input -/
@[inline] def throwUnexpected (input : Option α := none) : ParserT ε σ α m β := do
  throw (Error.unexpected (← getPosition) input)

/-- add message on parser error -/
@[inline] def withErrorMessage (msg : String) (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  try p
  catch e =>
    throw (Error.addMessage e (← getPosition) msg)

/-- `withBacktracking p` parses `p` but does not consume any input on error -/
@[inline] def withBacktracking (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  let savePos ← getPosition
  try p
  catch e =>
    setPosition savePos false
    throw e

/- override default `OrElse` so that the first consumes no input when it fails -/
@[inline] instance : OrElse (ParserT ε σ α m β) where
  orElse p q :=
    try withBacktracking p
    catch _ => q ()

/-- `first ps` tries parsers from the list `ps` until one succeeds -/
def first (ps : List (ParserT ε σ α m β)) (combine : ε → ε → ε := fun _ => id) : ParserT ε σ α m β :=
  let rec go : List (ParserT ε σ α m β) → ε → ParserT ε σ α m β
  | [], e => throw e
  | p :: ps, e =>
    try withBacktracking p
    catch f => go ps (combine e f)
  do go ps (Error.unexpected (← getPosition) none)

end Parser

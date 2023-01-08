import Parser.Prelude
import Parser.Error
import Parser.Stream

/-- parser state -/
protected structure Parser.State (σ α : Type _) [Parser.Stream σ α] where
  /-- parser stream -/
  stream : σ
  /-- whether the parser has consumed any input -/
  dirty : Bool

/-- parser result -/
inductive Parser.Result (ε σ α : Type _)
| ok : σ → α → Result ε σ α
| error : ε → Result ε σ α

/-- `ParserT ε σ α` monad transformer to parse tokens of type `α` from the stream `σ` with error type `ε` -/
@[nolint unusedArguments]
def ParserT.{u} (ε σ : Type u) (α : Type _) [Parser.Stream σ α] [Parser.Error ε σ α] (m : Type _ → Type _) :=
  StateT (Parser.State σ α) (ExceptT ε m)
instance (ε σ α m) [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] : Monad (ParserT ε σ α m) := inferInstanceAs (Monad (StateT (Parser.State σ α) (ExceptT ε m)))
instance (ε σ α m) [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] : MonadExcept ε (ParserT ε σ α m) := inferInstanceAs (MonadExcept ε (StateT (Parser.State σ α) (ExceptT ε m)))

/-- run parser transformer -/
protected def ParserT.run.{u} {ε σ : Type u} {α β m} [Parser.Stream σ α] [Parser.Error ε σ α] [Monad m] (p : ParserT ε σ α m β) (s : σ) : m (Parser.Result ε σ β) := do
  return match (← StateT.run (m := ExceptT ε m) p {stream := s, dirty := false}) with
  | .ok (val, s) => .ok s.stream val
  | .error e => .error e

/-- `Parser ε σ α` monad to parse tokens of type `α` from the stream `σ` with error type `ε` -/
abbrev Parser (ε σ α) [Parser.Stream σ α] [Parser.Error ε σ α] := ParserT ε σ α Id

/-- run parser -/
protected abbrev Parser.run {ε σ α β} [Parser.Stream σ α] [Parser.Error ε σ α] (p : Parser ε σ α β) (s : σ) : Parser.Result ε σ β :=
  ParserT.run p s

/-- `SimpleParserT σ α` monad transformer to parse tokens of type `α` from the stream `σ` with simple error handling -/
abbrev SimpleParserT (σ α) [Parser.Stream σ α] (m) := ParserT (Parser.Error.Simple σ α) σ α m

/-- `SimpleParser σ α` monad to parse tokens of type `α` from the stream `σ` with simple error handling -/
abbrev SimpleParser (σ α) [Parser.Stream σ α] := ParserT (Parser.Error.Simple σ α) σ α Id

namespace Parser
variable {ε σ α β γ} [Parser.Stream σ α] [Parser.Error ε σ α] {m} [Monad m]

/-- check whether parser has consumed any input -/
@[inline] def hasConsumed : ParserT ε σ α m Bool := do
  let s ← StateT.get
  return s.dirty

/- override default `OrElse` so that second is run only when the first has consumed no input -/
@[inline] instance : OrElse (ParserT ε σ α m β) where
  orElse p q := try p catch e => if (← hasConsumed) then throw e else q ()

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
@[inline] def unexpected (input : Option α := none) : ParserT ε σ α m β := do
  throw (Error.unexpected (← getPosition) input)

/-- add message on parser error -/
@[inline] def withErrorMessage (msg : String) (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  try p catch e => throw (Error.addMessage e (← getPosition) msg)

/-- `withBacktracking p` parses `p` but does not consume any input on error -/
@[inline] def withBacktracking (p : ParserT ε σ α m β) : ParserT ε σ α m β := do
  let savePos ← getPosition
  try p
  catch e =>
    setPosition savePos false
    throw e

/-- `tokenMap test` accepts token `t` with result `x` if `test t = some x`, otherise fails -/
@[specialize] def tokenMap (test : α → Option β) : ParserT ε σ α m β := do
  match Stream.next? (← StateT.get).stream with
  | some (x, s) =>
    StateT.set {stream := s, dirty := true}
    match test x with
    | some y => return y
    | none => unexpected x
  | none => unexpected

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
@[inline] def notFollowedBy (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  try
    let _ ← lookAhead p
    unexpected
  catch _ =>
    return

/-- `anyToken` accepts any single token and returns that token -/
@[inline] def anyToken : ParserT ε σ α m α :=
  tokenMap some

/-- `peek` returns the next token, without consuming any input -/
@[inline] def peek : ParserT ε σ α m α :=
  lookAhead anyToken

/-- `endOfInput` succeeds only when there is no input left -/
@[inline] def endOfInput : ParserT ε σ α m Unit :=
  notFollowedBy anyToken

/-- `optionD default p` tries to parse `p`, and returns `default` if `p` fails -/
@[inline] def optionD (default : β) (p : ParserT ε σ α m β) : ParserT ε σ α m β :=
  try p catch _ => return default

/-- `option! p` tries to parse `p`, and returns `Inhabited.default` if `p` fails -/
@[inline] def option! [Inhabited β] (p : ParserT ε σ α m β) : ParserT ε σ α m β :=
  optionD default p

/-- `option? p` parses `p` returns `some x` if `p` returns `x`, and returns `none` if `p` fails -/
@[inline] def option? (p : ParserT ε σ α m β) : ParserT ε σ α m (Option β) :=
  option! (some <$> p)

/-- `optional p` tries to parse `p`, ignoring the output, never fails -/
@[inline] def optional (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  option! (p *> return)

@[specialize]
private partial def foldAux (f : γ → β → γ) (y : γ) (p : ParserT ε σ α m β) : ParserT ε σ α m γ :=
  let rec rest (y : γ) : ParserT ε σ α m γ :=
    try
      let x ← withBacktracking p
      rest (f y x)
    catch _ => return y
  rest y

/-- `foldl f q p` -/
@[inline] partial def foldl (f : γ → β → γ) (q : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m γ := do
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
@[inline] def takeUntil (stop : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β × γ) := do
  return (← takeMany (notFollowedBy stop *> p), ← stop)

/-- `drop n p` parses exactly `n` occurrences of `p`, ignoring all outputs from `p` -/
@[inline] def drop (n : Nat) (p : ParserT ε σ α m β) : ParserT ε σ α m Unit :=
  match n with
  | 0 => return
  | n+1 => do
      let _ ← p
      drop n p

/-- `dropUpto n p` parses up to `n` occurrences of `p`, ignoring all outputs from `p` -/
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
@[inline] def dropUntil (stop : ParserT ε σ α m γ) (p : ParserT ε σ α m β) : ParserT ε σ α m γ :=
  dropMany (notFollowedBy stop *> p) *> stop

/-- `sepBy1 p sep` parses one or more occurrences of `p`, separated by `sep`, returns an array of values returned by `p` -/
@[inline] def sepBy1 (sep : ParserT ε σ α m Unit) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  foldAux Array.push #[← withBacktracking p] (sep *> p)

/-- `sepBy p sep` parses zero or more occurrences of `p`, separated by `sep`, returns an array of values returned by `p` -/
@[inline] def sepBy (sep : ParserT ε σ α m Unit) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) :=
  sepBy1 sep p <|> return #[]

/-- `endBy p sep` parses zero or more occurrences of `p`, separated and ended by `sep`, returns an array of values returned by `p` -/
@[inline] def endBy (sep : ParserT ε σ α m Unit) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) :=
  takeMany (p <* sep)

/-- `endBy1 p sep` parses one or more occurrences of `p`, separated and ended by `sep`, returns an array of values returned by `p` -/
@[inline] def endBy1 (sep : ParserT ε σ α m Unit) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) := do
  takeMany1 (p <* sep)

/-- `sepEndBy1 p sep` parses one or more occurrences of `p`, separated and optionally ended by `sep`, returns an array of values returned by `p` -/
@[inline] def sepEndBy1 (sep : ParserT ε σ α m Unit) (p : ParserT ε σ α m β) : ParserT ε σ α m (Array β) :=
  sepBy1 sep p <* optional sep

/-- `sepEndBy p sep` parses zero or more occurrences of `p`, separated and optionally ended by `sep`, returns an array of values returned by `p` -/
@[inline] def sepEndBy (sep : ParserT ε σ α m Unit) (p : ParserT ε σ α m α) : ParserT ε σ α m (Array α) :=
  sepEndBy1 sep p <|> return #[]

end Parser

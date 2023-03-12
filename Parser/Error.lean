import Parser.Prelude
import Parser.Stream

/-- parser error type -/
protected class Parser.Error (ε σ α : Type _) [Parser.Stream σ α] where
  /-- unexpected input -/
  unexpected : Stream.Position σ α → Option α → ε
  /-- add error message -/
  addMessage : ε → Stream.Position σ α → String → ε

namespace Parser.Error

/-- simple error type -/
inductive Simple (σ α) [Parser.Stream σ α]
| unexpected : Stream.Position σ α → Option α → Simple σ α
| addMessage : Simple σ α → Stream.Position σ α → String → Simple σ α

private def Simple.toString {σ α} [Repr α] [Parser.Stream σ α] [Repr (Parser.Stream.Position σ α)] : Simple σ α → String
| unexpected pos (some input) => s!"unexpected input {repr input} at {repr pos}"
| unexpected pos none => s!"unexpected input at {repr pos}"
| addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {repr pos}"

instance (σ α) [Repr α] [Parser.Stream σ α] [Repr (Parser.Stream.Position σ α)] : ToString (Simple σ α) where
  toString e := Simple.toString e

instance (σ α) [Repr α] [Parser.Stream σ α] [ToString (Simple σ α)] : Repr (Simple σ α) where
  reprPrec result _ := Std.Format.text $ toString result

instance  (σ α) [Parser.Stream σ α] : Parser.Error (Simple σ α) σ α where
  unexpected := Simple.unexpected
  addMessage := Simple.addMessage

end Parser.Error

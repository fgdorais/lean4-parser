
/-
Copyright © 2022-2023 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Basic

namespace Parser

/-- Type of regular expressions -/
inductive RegEx (α : Type _)
| /-- Character set -/
  set : (α → Bool) → RegEx α
| /-- Alternation -/
  alt : RegEx α → RegEx α → RegEx α
| /-- Concatenation -/
  cat : RegEx α → RegEx α → RegEx α
| /-- Unbounded repetition -/
  repMany : RegEx α → RegEx α
| /-- Bounded repetition -/
  repUpTo : Nat → RegEx α → RegEx α
| /-- Grouping (unused) -/
  group : RegEx α → RegEx α

namespace RegEx

/-- Empty character set -/
def fail : RegEx α := set fun _ => false

instance (α) : Inhabited (RegEx α) := ⟨fail⟩

/-- Universal character set -/
def any : RegEx α := set fun _ => true

/-- Nil expression  -/
def nil : RegEx α := repUpTo 0 default

/-- Optional -/
def opt (e : RegEx α) := repUpTo 1 e

/-- Repetition -/
def rep (n : Nat) (e : RegEx α) :=
  match n with
  | 0 => repUpTo 0 e
  | 1 => e
  | n+1 => cat e (rep n e)

/-- Unbounded repetition, at least once -/
def repMany1 (e : RegEx α) := cat e (repMany e)

/-- Unbounded repetition, at least `n` times -/
def repManyN (n : Nat) (e : RegEx α) :=
  match n with
  | 0 => repMany e
  | n+1 => cat e (repManyN n e)

section
variable {ε σ α β} [Parser.Stream σ α] [Parser.Error ε σ α] {m} [Monad m] [MonadExceptOf ε m]

/-- Fold over a regex match from the right -/
protected partial def foldr (f : α → β → β) : RegEx α → ParserT ε σ α m β → ParserT ε σ α m β
| .set s, k => tokenFilter s >>= fun x => f x <$> k
| .alt e₁ e₂, k => RegEx.foldr f e₁ k <|> RegEx.foldr f e₂ k
| .cat e₁ e₂, k => RegEx.foldr f e₁ (RegEx.foldr f e₂ k)
| .repUpTo 0 _, k => k
| .repUpTo (n+1) e, k => RegEx.foldr f e (RegEx.foldr f (.repUpTo n e) k) <|> k
| .repMany e, k => RegEx.foldr f e (RegEx.foldr f (.repMany e) k) <|> k
| .group e, k => RegEx.foldr f e k

/-- Parses tokens matching regex `re` returning the list of tokens, otherwise fails -/
protected def «match» (re : RegEx α) : ParserT ε σ α m (List α) :=
  re.foldr (.::.) (pure [])

end


/-
Copyright © 2022-2023 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Basic

namespace Parser

/-- Type of regular expressions -/
inductive RegEx : Type _ → Type _
  /-- Character set -/
  | set : (α → Bool) → RegEx α
  /-- Alternation -/
  | alt : RegEx α  → RegEx α → RegEx α
  /-- Concatenation -/
  | cat : RegEx α → RegEx α → RegEx α
  /-- Unbounded repetition -/
  | repMany : RegEx α → RegEx α
  /-- Bounded repetition -/
  | repUpTo : Nat → RegEx α → RegEx α
  /-- Grouping -/
  | group : RegEx α → RegEx α

namespace RegEx

/-- Grouping depth -/
def depth : RegEx α → Nat -- TODO: make computed field
  | .set _ => 0
  | .alt e₁ e₂ => depth e₁ + depth e₂
  | .cat e₁ e₂ => depth e₁ + depth e₂
  | .repMany e => depth e
  | .repUpTo _ e => depth e
  | .group e => depth e + 1

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

/-- `take re` parses tokens matching regex `re` returning the list of tokens, otherwise fails -/
protected def take (re : RegEx α) : ParserT ε σ α m (List α) :=
  re.foldr (.::.) (pure [])

/-- `drop re` parses tokens matching regex `re`, otherwise fails -/
protected def drop (re : RegEx α) : ParserT ε σ α m Unit :=
  re.foldr (fun _ => id) (pure ())

/-- `count re` parses tokens matching regex `re` returning the number of tokens, otherwise fails -/
protected def count (re : RegEx α) : ParserT ε σ α m Nat :=
  re.foldr (fun _ => Nat.succ) (pure 0)

/-- Parses tokens matching regex `re` returning all the matching group segments, otherwise fails -/
protected partial def «match» (re : RegEx α) : ParserT ε σ α m (Array (Option (Stream.Segment σ))) := do
  loop re 0 (mkArray re.depth none)
where
  loop : RegEx α → Nat → Array (Option (Stream.Segment σ)) → ParserT ε σ α m (Array (Option (Stream.Segment σ)))
    | .set s, _, ms => tokenFilter s *> return ms
    | .alt e₁ e₂, lvl, ms => loop e₁ lvl ms <|> loop e₂ (lvl + e₁.depth) ms
    | .cat e₁ e₂, lvl, ms => loop e₁ lvl ms >>= loop e₂ (lvl + e₁.depth)
    | .repUpTo 0 _, _, ms => return ms
    | .repUpTo (n+1) e, lvl, ms => loop e lvl ms >>= loop (.repUpTo n e) lvl <|> return ms
    | .repMany e, lvl, ms => loop e lvl ms >>= loop (.repMany e) lvl <|> return ms
    | .group e, lvl, ms => do
      let mut ms := ms
      for i in [lvl:ms.size] do ms := ms.set! i none
      let start ← Parser.getPosition
      ms ← loop e (lvl+1) ms
      let stop ← Parser.getPosition
      return ms.set! lvl (some (start, stop))

end

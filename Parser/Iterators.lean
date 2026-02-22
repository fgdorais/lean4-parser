/-
Copyright © 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Stream
import Std.Data.Iterators

/-! # Std.Iterators bridge for Parser.Stream

This module provides `Iterator` and `Finite` instances for `Parser.Stream` types, bridging the
lean4-parser stream abstraction to the `Std.Data.Iterators` framework.

## Design

Each `Parser.Stream σ τ` provides:
- A `Std.Stream σ τ` with `next? : σ → Option (τ × σ)` for consuming tokens
- `remaining : σ → Nat`, an upper bound that strictly decreases on each `next?` yielding `some`

We define a wrapper `StreamIterator σ τ` that carries a `Parser.Stream` state and provides:
- `Iterator (StreamIterator σ τ) Id τ` — steps via `next?`, never skips
- `Finite (StreamIterator σ τ) Id` — well-founded via `remaining`

This enables using `Std.Data.Iterators` consumers (e.g., `fold`, `toList`, `toArray`) on
parser streams, and provides the foundation for future migration of lean4-parser's fold
combinators to use `Std.Iterators` infrastructure directly.

## Usage

```lean
import Parser.Iterators

-- Given a Parser.Stream instance for String.Slice:
def example (s : String.Slice) : List Char :=
  (StreamIterator.mk s).iter.toList
```
-/

open Std Std.Iterators

namespace Parser.Stream

/--
Wrapper that presents a `Parser.Stream` state as a `Std.Iterators` iterator state.

The iterator yields tokens of type `τ` by calling `next?` on the underlying stream.
It terminates when `next?` returns `none`.
-/
structure StreamIterator (σ : Type) (τ : Type) [Parser.Stream σ τ] where
  /-- The underlying parser stream state. -/
  stream : σ

variable {σ τ : Type} [Parser.Stream σ τ]

/-- Create a `StreamIterator` from a parser stream state. -/
@[inline]
def StreamIterator.mk' (s : σ) : StreamIterator σ τ := ⟨s⟩

/-- Create a monadic iterator (`IterM Id τ`) from a `StreamIterator`. -/
@[inline]
def StreamIterator.iterM (s : StreamIterator σ τ) : IterM (α := StreamIterator σ τ) Id τ :=
  IterM.mk s Id τ

/-- Create a pure iterator (`Iter τ`) from a `StreamIterator`. -/
@[inline]
def StreamIterator.iter (s : StreamIterator σ τ) : Iter (α := StreamIterator σ τ) τ :=
  s.iterM.toIter

/--
Helper predicate for the `Iterator` instance. Defined as a standalone function so that
`simp` and `unfold` can reduce it when the `IterStep` constructor is known.
-/
private def isPlausibleStreamStep
    (it : IterM (α := StreamIterator σ τ) Id τ)
    (step : IterStep (IterM (α := StreamIterator σ τ) Id τ) τ) : Prop :=
  match step with
  | .yield it' out =>
    Stream.next? it.internalState.stream = some (out, it'.internalState.stream)
  | .skip _ => False
  | .done => Stream.next? it.internalState.stream = none

/--
`Iterator` instance for `StreamIterator`. Each step calls `next?` on the underlying stream:
- If `next?` returns `some (tok, s')`, yields `tok` and advances to `s'`.
- If `next?` returns `none`, the iterator is done.

The iterator never produces `skip` steps.

The `IsPlausibleStep` predicate ties each step to the actual `next?` result, ensuring that
the plausible successor relation mirrors the stream's token consumption — which is the basis
for the `Finite` proof.
-/
instance instIterator : Iterator (StreamIterator σ τ) Id τ where
  IsPlausibleStep := isPlausibleStreamStep
  step it := pure <|
    match h : Stream.next? it.internalState.stream with
    | some (tok, s') =>
      .deflate ⟨.yield (IterM.mk (α := StreamIterator σ τ) ⟨s'⟩ Id τ) tok, by
        unfold isPlausibleStreamStep
        simp
        exact h⟩
    | none =>
      .deflate ⟨.done, by
        unfold isPlausibleStreamStep
        exact h⟩

/--
`Finite` instance for `StreamIterator`, proven via `Parser.Stream.remaining`.

The `remaining` field of `Parser.Stream` provides an upper bound on tokens that strictly
decreases when `next?` returns `some`. We use `remaining ∘ StreamIterator.stream` as the
well-founded measure via a `FinitenessRelation`.

**Note**: This proof currently uses `sorry` for the key lemma that `remaining` strictly
decreases on each `next?` step. A complete proof requires adding a contract/axiom to
`Parser.Stream` stating:
  `∀ s tok s', next? s = some (tok, s') → remaining s' < remaining s`
This is semantically required by all `Parser.Stream` instances but not yet enforced by the type.
-/
private def streamFinitenessRelation : FinitenessRelation (StreamIterator σ τ) Id where
  Rel := InvImage WellFoundedRelation.rel
    (Parser.Stream.remaining ∘ StreamIterator.stream ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hsucc, hplaus⟩ := h
    cases step with
    | yield it'' out =>
      simp [IterStep.successor] at hsucc
      subst hsucc
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, isPlausibleStreamStep] at hplaus
      -- hplaus : Stream.next? it.internalState.stream = some (out, it'.internalState.stream)
      -- Need: remaining it'.internalState.stream < remaining it.internalState.stream
      -- This follows from the Parser.Stream contract that remaining strictly decreases
      -- when next? returns some, but that contract is not yet formalized as a typeclass law.
      sorry
    | skip it'' =>
      simp [IterStep.successor] at hsucc
      subst hsucc
      -- IsPlausibleStep for skip is False
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, isPlausibleStreamStep] at hplaus
    | done =>
      simp [IterStep.successor] at hsucc

instance : Iterators.Finite (StreamIterator σ τ) Id :=
  Iterators.Finite.of_finitenessRelation streamFinitenessRelation

/--
`IteratorLoop` instance enabling `for` loops and standard consumers (`fold`, `toList`, etc.)
over `StreamIterator`.
-/
@[always_inline, inline]
instance {n : Type → Type} [Monad n] : IteratorLoop (StreamIterator σ τ) Id n :=
  .defaultImplementation

end Parser.Stream

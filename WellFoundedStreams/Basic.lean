/-
Copyright (c) 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais

Adapted from batteries PR#1331 (https://github.com/leanprover-community/batteries/pull/1331)
for inclusion in lean4-parser as a self-contained component.
-/

import Std.Data.Iterators

/-! # Stream Basics

Basic operations on streams: `drop`, `take`, and `StreamIterator` bridging
streams to `Std.Iterators`.
-/

namespace Stream

/-- Drop up to `n` values from the stream `s`. -/
def drop [Std.Stream σ α] (s : σ) : Nat → σ
  | 0 => s
  | n+1 =>
    match next? s with
    | none => s
    | some (_, s) => drop s n

/-- Read up to `n` values from the stream `s` as a list from first to last. -/
def take [Std.Stream σ α] (s : σ) : Nat → List α × σ
  | 0 => ([], s)
  | n+1 =>
    match next? s with
    | none => ([], s)
    | some (a, s) =>
      match take s n with
      | (as, s) => (a :: as, s)

@[simp] theorem fst_take_zero [Std.Stream σ α] (s : σ) :
    (take s 0).fst = [] := rfl

theorem fst_take_succ [Std.Stream σ α] (s : σ) :
    (take s (n+1)).fst =
      match next? s with
      | none => []
      | some (a, s) => a :: (take s n).fst := by
  simp only [take]; split <;> rfl

@[simp] theorem snd_take_eq_drop [Std.Stream σ α] (s : σ) (n : Nat) :
    (take s n).snd = drop s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [take, drop]
    split <;> simp [ih]

/-- Tail recursive version of `Stream.take`. -/
private def takeTR [Std.Stream σ α] (s : σ) (n : Nat) : List α × σ :=
  loop s [] n
where
  /-- Inner loop for `Stream.takeTR`. -/
  loop (s : σ) (acc : List α)
    | 0 => (acc.reverse, s)
    | n+1 => match next? s with
      | none => (acc.reverse, s)
      | some (a, s) => loop s (a :: acc) n

private theorem fst_takeTR_loop [Std.Stream σ α] (s : σ) (acc : List α) (n : Nat) :
    (takeTR.loop s acc n).fst = acc.reverseAux (take s n).fst := by
  induction n generalizing acc s with
  | zero => rfl
  | succ n ih => simp only [take, takeTR.loop]; split; rfl; simp [ih]

private theorem fst_takeTR [Std.Stream σ α] (s : σ) (n : Nat) : (takeTR s n).fst = (take s n).fst :=
  fst_takeTR_loop ..

private theorem snd_takeTR_loop [Std.Stream σ α] (s : σ) (acc : List α) (n : Nat) :
    (takeTR.loop s acc n).snd = drop s n := by
  induction n generalizing acc s with
  | zero => rfl
  | succ n ih => simp only [takeTR.loop, drop]; split; rfl; simp [ih]

private theorem snd_takeTR [Std.Stream σ α] (s : σ) (n : Nat) :
    (takeTR s n).snd = drop s n := snd_takeTR_loop ..

@[csimp] private theorem take_eq_takeTR : @take = @takeTR := by
  funext; ext : 1; rw [fst_takeTR]; rw [snd_takeTR, snd_take_eq_drop]

end Stream

@[simp]
theorem List.stream_drop_eq_drop (l : List α) : Stream.drop l n = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | _::_ => simp [Stream.drop, List.drop_succ_cons, ih]

@[simp] theorem List.stream_take_eq_take_drop (l : List α) :
    Stream.take l n = (l.take n, l.drop n) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | _::_ => simp [Stream.take, ih]

/-! ## Stream Iterators

The standard library provides iterators that behave much like streams but include many additional
features to support monadic effects, among other things. This added functionality makes the user
interface more complicated. By comparison, the stream interface is quite simple and easy to use.

The standard library provides a stream interface for productive pure iterators.

The following provide the reverse translation. The function `Stream.iter` converts a `Stream σ α`
into a productive pure iterator of type `StreamIterator σ α`. Finiteness properties for streams are
provided in `WellFoundedStreams.Finite`.

In addition to providing a back and forth translation between stream types and productive pure
iterators, this functionality is also useful for existing stream-based libraries to incrementally
convert to iterators.
-/

/-- The underlying type of a stream iterator. -/
structure StreamIterator (σ α) [Std.Stream σ α] where
  /-- Underlying stream of a stream iterator. -/
  stream : σ

section StreamIteratorDefs
open Std.Iterators

/--
Returns a productive pure iterator for the given stream.

**Termination properties:**

* `Finite` instance: maybe available
* `Productive` instance: always
-/
@[always_inline, inline]
def Stream.iter [Std.Stream σ α] (stream : σ) : Std.Iter (α := StreamIterator σ α) α :=
  Std.IterM.mk { stream } Id α |>.toIter

/--
Predicate for the `Iterator` instance. Defined as a standalone function so that
`simp` and `unfold` can reduce it when the `IterStep` constructor is known.
-/
def isPlausibleStreamStep [Std.Stream σ α]
    (it : Std.IterM (α := StreamIterator σ α) Id α)
    (step : Std.IterStep (Std.IterM (α := StreamIterator σ α) Id α) α) : Prop :=
  match step with
  | .yield it' out =>
    Std.Stream.next? it.internalState.stream = some (out, it'.internalState.stream)
  | .skip _ => False
  | .done => Std.Stream.next? it.internalState.stream = none

@[always_inline, inline]
instance (σ α) [Std.Stream σ α] : Std.Iterator (StreamIterator σ α) Id α where
  IsPlausibleStep := isPlausibleStreamStep
  step it := pure <|
    match h : Std.Stream.next? it.internalState.stream with
    | some (out, stream) =>
      .deflate ⟨.yield (Std.IterM.mk (α := StreamIterator σ α) ⟨stream⟩ Id α) out, by
        unfold isPlausibleStreamStep
        simp
        exact h⟩
    | none =>
      .deflate ⟨.done, by
        unfold isPlausibleStreamStep
        exact h⟩

private def StreamIterator.instProductivenessRelation [Std.Stream σ α] :
    ProductivenessRelation (StreamIterator σ α) Id where
  Rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation h := by cases h

instance StreamIterator.instProductive [Std.Stream σ α] :
    Productive (StreamIterator σ α) Id :=
  Productive.of_productivenessRelation
    StreamIterator.instProductivenessRelation

instance StreamIterator.instIteratorLoop [Std.Stream σ α] [Monad n] :
    Std.IteratorLoop (StreamIterator σ α) Id n := .defaultImplementation

end StreamIteratorDefs

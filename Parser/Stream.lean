/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude

/-! # Parser Stream

Parsers read input tokens from a stream. To help with error reporting and backtracking, the
`Parser.Stream` class extends the basic `Stream` class with functionality to save and restore
stream positions.

The simple way to implement backtracking after a parsing error is to first save the stream state
before parsing and, upon encountering an error, restore the saved stream state. The issue with this
strategy is that each backtrack point adds a reference to the entire stream state. This prevents
linear use of the stream state. The `Parser.Stream` class allows users to work around this issue.
The `Parser.Stream.Position` type is intended to store just enough information to *reconstruct* the
stream state at a save point without having to save the entire stream state.
-/

/-- *Parser stream class*

This class extends the basic `Stream` class with position features needed by parsers for
backtracking and error reporting.

* The type `Position` is used to record position data for the stream type.
* `getPosition (s : σ) : Position` returns the current position of stream `s`.
* `setPosition (s : σ) (p : Position) : σ` restores stream `s` to position `p`.
* `remaining (s : σ) : Nat` returns an upper bound on remaining tokens in `s`.

  This value must strictly decrease when a token is consumed (`next?` returns `some`).
  It is used as a termination measure for total fold combinators.

Implementations should try to make the `Position` type as lightweight as possible for `getPosition`
and `setPosition` to work properly. Often `Position` is just a scalar type or another simple type.
This may allow for parsers to use the stream state more efficiently.
-/
protected class Parser.Stream.{u_1} (σ : Type _) (τ : outParam (Type _)) extends Std.Stream σ τ where
  Position : Type u_1
  getPosition : σ → Position
  setPosition : σ → Position → σ
  /-- An upper bound on the number of remaining tokens. Must strictly decrease when `next?`
      returns `some`. Used as a well-founded termination measure for fold combinators. -/
  remaining : σ → Nat
attribute [reducible, inherit_doc Parser.Stream] Parser.Stream.Position
attribute [inherit_doc Parser.Stream] Parser.Stream.getPosition Parser.Stream.setPosition

/-- Lawful parser stream: `remaining` strictly decreases when `next?` consumes a token.

This law formalizes the contract that `Parser.Stream.remaining` provides a well-founded termination
measure. Instances of `LawfulParserStream` are required by the sorry-free `Finite` instance for
`StreamIterator`, enabling provably terminating iteration via `Std.Data.Iterators`.

The `mkDefault` fallback does not satisfy this law (its `remaining` uses a `partial def`),
so there is intentionally no `LawfulParserStream` instance for `mkDefault`.
-/
class LawfulParserStream (σ : Type _) (τ : outParam (Type _)) [Parser.Stream σ τ] : Prop where
  /-- `remaining` strictly decreases when `next?` returns `some`. -/
  remaining_decreases : ∀ (s : σ) (tok : τ) (s' : σ),
    Stream.next? s = some (tok, s') → Parser.Stream.remaining s' < Parser.Stream.remaining s

namespace Parser.Stream

/-- Stream segment type. -/
def Segment (σ) [Parser.Stream σ τ] := Stream.Position σ × Stream.Position σ

/-- Start position of stream segment. -/
abbrev Segment.start [Parser.Stream σ τ] (s : Segment σ) := s.1

/-- Stop position of stream segment. -/
abbrev Segment.stop [Parser.Stream σ τ] (s : Segment σ) := s.2

/-- Default wrapper to make a `Parser.Stream` from a plain `Stream`.

This wrapper uses the entire stream state as position information; this is not efficient. Always
prefer tailored `Parser.Stream` instances to this default.
-/
@[nolint unusedArguments]
def mkDefault (σ τ) [Std.Stream σ τ] := σ

/-- Count remaining tokens by iterating the stream. O(n) — only used by `mkDefault`. -/
private partial def countStreamRemaining (next? : σ → Option (τ × σ)) (s : σ) : Nat :=
  match next? s with
  | none => 0
  | some (_, s') => countStreamRemaining next? s' + 1

@[reducible]
instance (σ τ) [self : Std.Stream σ τ] : Parser.Stream (mkDefault σ τ) τ where
  toStream := self
  Position := σ
  getPosition s := s
  setPosition _ p := p
  remaining s := countStreamRemaining self.next? s

@[reducible]
instance : Parser.Stream String.Slice Char where
  Position := String.Slice
  getPosition s := s
  setPosition _ s := s
  remaining s := s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx

/-- TODO: prove via `Slice.Pos.lt_next` and `Slice.sliceFrom` lemmas once the
right `simp` set for String.Slice byte-index arithmetic is identified. -/
instance : LawfulParserStream String.Slice Char where
  remaining_decreases _ _ _ _ := by
    simp only [Parser.Stream.remaining]
    sorry

@[reducible]
instance : Parser.Stream Substring.Raw Char where
  Position := String.Pos.Raw
  getPosition s := s.startPos
  setPosition s p :=
    if p ≤ s.stopPos then
      { s with startPos := p }
    else
      { s with startPos := s.stopPos }
  remaining s := s.stopPos.byteIdx - s.startPos.byteIdx

/-- TODO: prove via `String.Pos.Raw.lt_next` once the right `simp` set for
Substring.Raw byte-index arithmetic is identified. -/
instance : LawfulParserStream Substring.Raw Char where
  remaining_decreases _ _ _ _ := by
    simp only [Parser.Stream.remaining]
    sorry

@[reducible]
instance (τ) : Parser.Stream (Subarray τ) τ where
  Position := Nat
  getPosition s := s.start
  setPosition s p :=
    if h : p ≤ s.stop then
      ⟨{ s.internalRepresentation with start := p, start_le_stop := h }⟩
    else
      ⟨{ s.internalRepresentation with start := s.stop, start_le_stop := Nat.le_refl s.stop }⟩
  remaining s := s.stop - s.start

instance (τ) : LawfulParserStream (Subarray τ) τ where
  remaining_decreases s tok s' h := by
    simp only [Parser.Stream.remaining]
    dsimp [Stream.next?, Std.Stream.next?] at h
    split at h
    · next hlt =>
      obtain ⟨_, rfl⟩ := Option.some.inj h
      simp only [Subarray.start, Subarray.stop]
      have h1 : s.start = s.internalRepresentation.start := rfl
      have h2 : s.stop = s.internalRepresentation.stop := rfl
      omega
    · nomatch h

@[reducible]
instance : Parser.Stream ByteSlice UInt8 where
  Position := Nat
  getPosition s := s.start
  setPosition s p := s.slice p
  remaining s := s.stop - s.start

instance : LawfulParserStream ByteSlice UInt8 where
  remaining_decreases s tok s' h := by
    simp only [Parser.Stream.remaining]
    -- Stream.next? for ByteSlice: s[0]? >>= (·, s.popFront)
    -- popFront advances start by 1, so s'.stop - s'.start < s.stop - s.start
    sorry

/-- `OfList` is a view of a list stream that keeps track of consumed tokens. -/
structure OfList (τ : Type _) where
  /-- Remaining tokens. -/
  next : List τ
  /-- Consumed tokens. -/
  past : List τ := []

/-- Restore a list stream to a given position. -/
def OfList.setPosition {τ} (s : OfList τ) (p : Nat) : OfList τ :=
  if s.past.length < p then
    fwd (p - s.past.length) s
  else
    rev (s.past.length - p) s
where
  /-- Internal for `OfList.setPosition`. -/
  fwd : Nat → OfList τ → OfList τ
    | k+1, ⟨x :: rest, past⟩ => fwd k ⟨rest, x :: past⟩
    | _, s => s
  /-- Internal for `OfList.setPosition`. -/
  rev : Nat → OfList τ → OfList τ
    | k+1, ⟨rest, x :: past⟩ => rev k ⟨x :: rest, past⟩
    | _, s => s

/-- Make a `Parser.Stream` from a `List`. -/
def mkOfList {τ} (data : List τ) (pos : Nat := 0) : OfList τ :=
  OfList.setPosition { next := data } pos

@[reducible]
instance (τ) : Parser.Stream (OfList τ) τ where
  Position := Nat
  getPosition s := s.past.length
  setPosition := OfList.setPosition
  remaining s := s.next.length
  next? s :=
    match s with
    | ⟨x :: rest, past⟩ => some (x, ⟨rest, x :: past⟩)
    | _ => none

instance (τ) : LawfulParserStream (OfList τ) τ where
  remaining_decreases s tok s' h := by
    simp only [Parser.Stream.remaining]
    match s, h with
    | ⟨_ :: _, _⟩, h =>
      dsimp [Stream.next?, Std.Stream.next?] at h
      obtain ⟨_, rfl⟩ := Option.some.inj h
      simp [List.length_cons]
    | ⟨[], _⟩, h =>
      dsimp [Stream.next?, Std.Stream.next?] at h
      nomatch h

end Parser.Stream

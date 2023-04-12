/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude

/-- `Parser.Stream` class extends `Stream` with position features -/
protected class Parser.Stream (σ : Type _) (α : outParam (Type _)) extends Stream σ α where
  /-- Position type -/
  Position : Type _
  /-- Get current stream position -/
  getPosition : σ → Position
  /-- Set current stream position -/
  setPosition : σ → Position → σ
attribute [reducible] Parser.Stream.Position

namespace Parser.Stream

/-- Wrapper to make a `Parser.Stream` from a core `Stream` -/
@[nolint unusedArguments]
def mkDefault (σ α) [Stream σ α] := σ

@[reducible]
instance (σ α) [self : Stream σ α] : Parser.Stream (mkDefault σ α) α where
  toStream := self
  Position := σ
  getPosition s := s
  setPosition _ p := p

@[reducible]
instance : Parser.Stream Substring Char where
  Position := String.Pos
  getPosition s := s.startPos
  setPosition s p :=
    if p ≤ s.stopPos
    then {s with startPos := p}
    else {s with startPos := s.stopPos}

@[reducible]
instance (α) : Parser.Stream (Subarray α) α where
  Position := Nat
  getPosition s := s.start
  setPosition s p :=
    if h : p ≤ s.stop
    then {s with start := p, h₁ := h}
    else {s with start := s.stop, h₁ := Nat.le_refl s.stop}

@[reducible]
instance : Parser.Stream ByteSubarray UInt8 where
  Position := Nat
  getPosition s := s.start
  setPosition s p :=
    if h : p ≤ s.start + s.size then
      {s with start := p, size := s.start + s.size - p, valid := by rw [Nat.add_sub_cancel' h]; exact s.valid}
    else
      {s with start := s.stop, size := 0, valid := by rw [ByteSubarray.stop]; exact s.valid}

/-- `OfList` is a view of a list along with a position along that list -/
structure OfList (α : Type _) where
  /-- Remaining tokens -/
  next : List α
  /-- Consumed tokens -/
  past : List α := []

/-- Set position -/
def OfList.setPosition {α} (s : OfList α) (p : Nat) : OfList α :=
  let rec fwd : Nat → OfList α → OfList α
  | k+1, ⟨x :: rest, past⟩ => fwd k ⟨rest, x :: past⟩
  | _, s => s
  let rec rev : Nat → OfList α → OfList α
  | k+1, ⟨rest, x :: past⟩ => rev k ⟨x :: rest, past⟩
  | _, s => s
  if s.past.length < p then
    fwd (p - s.past.length) s
  else
    rev (s.past.length - p) s

/-- Make a `Parser.Stream` from a `List` -/
def mkOfList {α} (data : List α) (pos : Nat := 0) : OfList α :=
  OfList.setPosition {next := data} pos

@[reducible]
instance (α) : Parser.Stream (OfList α) α where
  Position := Nat
  getPosition s := s.past.length
  setPosition := OfList.setPosition
  next? s :=
    match s with
    | ⟨x :: rest, past⟩ => some (x, ⟨rest, x :: past⟩)
    | _ => none

end Parser.Stream

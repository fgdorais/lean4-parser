/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude

/-- `Parser.Stream` class extends `Stream` with position features -/
protected class Parser.Stream (σ : Type _) (τ : outParam (Type _)) extends Std.Stream σ τ where
  /-- Position type -/
  Position : Type _
  /-- Get current stream position -/
  getPosition : σ → Position
  /-- Set current stream position -/
  setPosition : σ → Position → σ
attribute [reducible] Parser.Stream.Position

namespace Parser.Stream

/-- Stream segment -/
def Segment (σ) [Parser.Stream σ τ] := Stream.Position σ × Stream.Position σ

/-- Start position of stream segment -/
abbrev Segment.start [Parser.Stream σ τ] (s : Segment σ) := s.1

/-- Stop position of stream segment -/
abbrev Segment.stop [Parser.Stream σ τ] (s : Segment σ) := s.2

/-- Wrapper to make a `Parser.Stream` from a `Std.Stream` -/
@[nolint unusedArguments]
def mkDefault (σ τ) [Std.Stream σ τ] := σ

@[reducible]
instance (σ τ) [self : Std.Stream σ τ] : Parser.Stream (mkDefault σ τ) τ where
  toStream := self
  Position := σ
  getPosition s := s
  setPosition _ p := p

@[reducible]
instance : Parser.Stream String.Slice Char where
  Position := String.Slice
  getPosition s := s
  setPosition _ s := s

@[reducible]
instance : Parser.Stream Substring.Raw Char where
  Position := String.Pos.Raw
  getPosition s := s.startPos
  setPosition s p :=
    if p ≤ s.stopPos
    then {s with startPos := p}
    else {s with startPos := s.stopPos}

@[reducible]
instance (τ) : Parser.Stream (Subarray τ) τ where
  Position := Nat
  getPosition s := s.start
  setPosition s p :=
    if h : p ≤ s.stop
    then ⟨{s.internalRepresentation with start := p, start_le_stop := h}⟩
    else ⟨{s.internalRepresentation with start := s.stop, start_le_stop := Nat.le_refl s.stop}⟩

@[reducible]
instance : Parser.Stream ByteSlice UInt8 where
  Position := Nat
  getPosition s := s.start
  setPosition s p := s.slice p

/-- `OfList` is a view of a list along with a position along that list -/
structure OfList (τ : Type _) where
  /-- Remaining tokens -/
  next : List τ
  /-- Consumed tokens -/
  past : List τ := []

/-- Set position -/
def OfList.setPosition {τ} (s : OfList τ) (p : Nat) : OfList τ :=
  if s.past.length < p then
    fwd (p - s.past.length) s
  else
    rev (s.past.length - p) s
where
  fwd : Nat → OfList τ → OfList τ
    | k+1, ⟨x :: rest, past⟩ => fwd k ⟨rest, x :: past⟩
    | _, s => s
  rev : Nat → OfList τ → OfList τ
    | k+1, ⟨rest, x :: past⟩ => rev k ⟨x :: rest, past⟩
    | _, s => s

/-- Make a `Parser.Stream` from a `List` -/
def mkOfList {τ} (data : List τ) (pos : Nat := 0) : OfList τ :=
  OfList.setPosition {next := data} pos

@[reducible]
instance (τ) : Parser.Stream (OfList τ) τ where
  Position := Nat
  getPosition s := s.past.length
  setPosition := OfList.setPosition
  next? s :=
    match s with
    | ⟨x :: rest, past⟩ => some (x, ⟨rest, x :: past⟩)
    | _ => none

end Parser.Stream

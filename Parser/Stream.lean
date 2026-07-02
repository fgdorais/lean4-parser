/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Parser.Prelude

public section

/-! # Parser Stream

Parsers read input tokens from a stream. In contrast to the `Std.Stream` class, the stream itself
does not change, but instead we keep track of the position inside the stream. This helps with
error reporting and and allows for backtracking.
-/

/-- *Parser stream class*

This class implements streams based on a static stream with a moving position.

* The type `Position` is used to record position data for the stream type.
* `start (s : σ) : Position` returns starting position for the stream `s`
* `next? (s : σ) (pos : Position) : Option (τ × Position)` returns the token at position `pos` in
  `s` together with the next position. It returns `none` if the end of the stream has been reached.

Implementations should try to make the `Position` type as lightweight as possible. Often `Position`
is just a scalar type or another simple type.
This may allow for parsers to use the stream state more efficiently.
-/

protected class Parser.Stream (σ : Type _) (τ : outParam (Type _)) where
  Position : Type u
  start : σ → Position
  next? : σ →  Position → Option (τ × Position)
attribute [reducible, inherit_doc Parser.Stream] Parser.Stream.Position
attribute [inherit_doc Parser.Stream] Parser.Stream.start Parser.Stream.next?

instance {σ τ} [self : Parser.Stream σ τ] [Inhabited σ] : Inhabited self.Position where
  default := Parser.Stream.start default

namespace Parser.Stream

/-- Stream segment type. -/
@[expose]
def Segment σ {τ} [self : Parser.Stream σ τ] := self.Position × self.Position

/-- Default wrapper to make a `Parser.Stream` from a plain `Stream`.

This wrapper uses the entire stream state as position information; this is not efficient. Always
prefer tailored `Parser.Stream` instances to this default.
-/
@[expose]
def mkDefault (σ τ) [Std.Stream σ τ] := σ

@[reducible]
instance (σ τ) [self : Std.Stream σ τ] : Parser.Stream (mkDefault σ τ) τ where
  Position := σ
  start s := s
  next? _ := self.next?

@[reducible]
instance : Parser.Stream String Char where
  Position := String.Pos.Raw
  start s := s.rawStartPos
  next? s p :=
    if h : p.IsValid s ∧ p < s.rawEndPos then
      some (String.Pos.get ⟨p, h.1⟩ (String.Pos.offset_lt_rawEndPos_iff.1 h.2) , p.next s)
    else
      none


@[reducible]
instance : Parser.Stream String.Slice Char where
  Position := String.Pos.Raw
  start s := s.startPos.offset
  next? s p :=
    if h : p.IsValidForSlice s ∧ p < s.rawEndPos then
      have h' : ⟨p, h.1⟩ ≠ s.endPos := String.Slice.Pos.offset_lt_rawEndPos_iff.1 h.2
      some (String.Slice.Pos.get ⟨p, h.1⟩ h' , p.next s.str)
    else
      none

-- Substring.Raw is a legacy function, so maybe this should be removed.
@[reducible]
instance : Parser.Stream Substring.Raw Char where
  Position := String.Pos.Raw
  start s := s.startPos
  next? s p :=  if p < s.stopPos then
      some (s.startPos.get s.str, p.next s.str)
    else
      none

@[reducible]
instance (τ) : Parser.Stream (Subarray τ) τ where
  Position := Nat
  start s := s.start
  next? s p := s[p]? >>= (· , p  + 1)

@[reducible]
instance : Parser.Stream ByteSlice UInt8 where
  Position := Nat
  start s := s.start
  next? s p := s[p]? >>= (· , p  + 1)

@[reducible]
instance (τ) : Parser.Stream (List τ) τ where
  Position := List τ
  start s := s
  next? _ p := p.next?

end Parser.Stream

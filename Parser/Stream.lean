import Parser.Prelude

/-- `Parser.Stream` class extends `Stream` with position features -/
protected class Parser.Stream (σ α : Type _) extends Stream σ α where
  /-- `Parser.Stream` position type -/
  Position : Type _
  /-- get current `Parser.Stream` position -/
  getPosition : σ → Position
  /-- set current `Parser.Stream` position -/
  setPosition (s : σ) : Position → σ

namespace Parser.Stream

/-- wrapper to make a `Parser.Stream` from a plain `Stream` -/
@[nolint unusedArguments] def mkOfStream (σ α : Type _) [Stream σ α] := σ

instance (σ α : Type _) [self : Stream σ α] : Parser.Stream (mkOfStream σ α) α where
  toStream := self
  Position := σ
  getPosition s := s
  setPosition _ p := p

instance : Parser.Stream Substring Char where
  Position := String.Pos
  getPosition s := s.startPos
  setPosition s p :=
    if p ≤ s.stopPos
    then {s with startPos := p}
    else {s with startPos := s.stopPos}

instance (α) : Parser.Stream (Subarray α) α where
  Position := Nat
  getPosition s := s.start
  setPosition s p :=
    if h : p ≤ s.stop
    then {s with start := p, h₁ := h}
    else {s with start := s.stop, h₁ := Nat.le_refl s.stop}

/-- `OfString` is a view of a string along with a position along that string -/
structure OfString where
  /-- token string -/
  data : String
  /-- position -/
  pos : String.Pos := 0

/-- make a `Parser.Stream` from a `String` -/
@[inline] def mkOfString (data : String) (pos : String.Pos := 0) : OfString where
  data := data
  pos := pos

instance : Parser.Stream OfString Char where
  Position := String.Pos
  getPosition s := s.pos
  setPosition s p := {s with pos := p}
  next? s :=
    match s.data.get? s.pos with
    | some x => some (x, {s with pos := s.data.next s.pos})
    | none => none
instance : Repr (Parser.Stream.Position OfString Char) := inferInstanceAs (Repr String.Pos)

/-- `OfByteArray` is a view of a `ByteArray` along with a position along that array -/
structure OfByteArray where
  /-- token array -/
  data : ByteArray
  /-- position -/
  pos : Nat := 0

/-- make a `Parser.Stream` from a `ByteArray` -/
@[inline] def mkOfByteArray (data : ByteArray) (pos : Nat := 0) : OfByteArray where
  data := data
  pos := pos

instance : Parser.Stream OfByteArray UInt8 where
  Position := Nat
  getPosition s := s.pos
  setPosition s p := {s with pos := p}
  next? s :=
    if hpos : s.pos < s.data.size then
      some (s.data.get ⟨s.pos, hpos⟩, {s with pos := s.pos + 1})
    else
      none
instance : Repr (Parser.Stream.Position OfByteArray UInt8) := inferInstanceAs (Repr Nat)

/-- `OfArray` is a view of an `Array` along with a position along that array -/
structure OfArray (α : Type _) where
  /-- token array -/
  data : Array α
  /-- position -/
  pos : Nat := 0

/-- make a `Parser.Stream` from an `Array` -/
@[inline] def mkOfArray {α} (data : Array α) (pos : Nat := 0) : OfArray α where
  data := data
  pos := pos

instance : Parser.Stream (OfArray α) α where
  Position := Nat
  getPosition s := s.pos
  setPosition s p := {s with pos := p}
  next? s :=
    match s.data.get? s.pos with
    | some x => some (x, {s with pos := s.pos + 1})
    | none => none
instance (α) : Repr (Parser.Stream.Position (OfArray α) α) := inferInstanceAs (Repr Nat)

/-- `OfList` is a view of an `List` along with a position along that array -/
structure OfList (α : Type _) where
  /-- remaining tokens -/
  next : List α
  /-- consumed tokens -/
  past : List α := []

/-- set position -/
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

/-- make a `Parser.Stream` from a `List` -/
@[inline] def mkOfList {α} (data : List α) (pos : Nat := 0) : OfList α :=
  OfList.setPosition {next := data} pos

instance (α) : Parser.Stream (OfList α) α where
  Position := Nat
  getPosition s := s.past.length
  setPosition := OfList.setPosition
  next? s :=
    match s with
    | ⟨x :: rest, past⟩ => some (x, ⟨rest, x :: past⟩)
    | _ => none
instance (α) : Repr (Parser.Stream.Position (OfList α) α) := inferInstanceAs (Repr Nat)

end Parser.Stream

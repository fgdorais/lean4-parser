import Parser

open Parser

/-- Byte position of the unexpected input reported by `e`. -/
def Parser.Error.Simple.unexpectedPos : Error.Simple String.Slice Char → Nat
  | .unexpected pos _ => pos.byteIdx
  | .addMessage e _ _ => e.unexpectedPos

/-- Byte position of the error reported by `p` on `s`, if any. -/
def errorPos (p : SimpleParser String.Slice Char Unit) (s : String) : Option Nat :=
  match Parser.run p s.toSlice with
  | .ok _ _ => none
  | .error _ e => some e.unexpectedPos

-- unexpected tokens are reported at their own position, not after them
#guard errorPos (token 'a' *> token 'b' *> pure ()) "ax" == some 1
#guard errorPos (Char.ASCII.digit *> pure ()) "x" == some 0
#guard errorPos (anyToken *> Char.char 'y' *> pure ()) "∀x" == some 3
-- end of input is reported at the end
#guard errorPos (token 'a' *> token 'b' *> pure ()) "a" == some 1

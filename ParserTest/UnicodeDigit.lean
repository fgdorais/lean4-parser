import Parser

open Parser

namespace UnicodeDigit

/-- Run `Char.Unicode.digit` on `s`. -/
def digit? (s : String) : Option Nat :=
  match Parser.run (Char.Unicode.digit : SimpleParser String.Slice Char (Fin 10)) s.toSlice with
  | .ok _ d => some d
  | .error _ _ => none

#guard digit? "7" == some 7
#guard digit? "٣" == some 3
-- superscript digits are not decimal digits
#guard digit? "²" == none

end UnicodeDigit

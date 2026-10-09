import Parser

open Parser

namespace BasicError

/-- Byte position of the error reported by `p` on `s`, if any. -/
def errorPos (p : BasicParser String.Slice Char Unit) (s : String) : Option Nat :=
  match Parser.run p s.toSlice with
  | .ok _ _ => none
  | .error _ (pos, _) => some pos.byteIdx

-- `BasicParser` works on `String.Slice`
#guard errorPos (token 'a' *> token 'b' *> pure ()) "ab" == none
#guard errorPos (token 'a' *> token 'b' *> pure ()) "ax" == some 1

end BasicError

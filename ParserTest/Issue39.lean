import Parser

open Parser

namespace Issue39

def test :=
  match (endOfInput : TrivialParser String.Slice Char Unit).run "abcd" with
  | .ok _ _ => false
  | .error _ _ => true

#guard test

end Issue39

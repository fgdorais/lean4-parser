import Parser.Char

open Parser

namespace Issue35

def test : Bool :=
  match Parser.run (Char.string "abc" : SimpleParser String.Slice Char String.Slice) "abc" with
  | .ok s r => s.isEmpty && r.copy == "abc"
  | .error _ _ => false

#guard test

end Issue35

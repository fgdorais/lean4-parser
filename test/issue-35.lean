import Parser.Char

open Parser

def test : Bool :=
  match Parser.run (Char.string "abc" : SimpleParser String.Slice Char String) "abc" with
  | .ok s pos r => pos == s.rawEndPos && r == "abc"
  | .error _ _ _ => false

#guard test

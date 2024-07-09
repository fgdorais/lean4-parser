import Parser.Char

open Parser

def test : Bool :=
  match Parser.run (Char.string "abc" : SimpleParser Substring Char String) "abc" with
  | .ok s r => s == "" && r == "abc"
  | .error _ _ => false

#guard test

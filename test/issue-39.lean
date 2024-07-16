import Parser

open Parser

def test :=
  match (endOfInput : TrivialParser Substring Char Unit).run "abcd" with
  | .ok _ _ => false
  | .error _ _ => true

#guard test

import Parser

open Parser Char

/--
Parses a list of sign-separated integers (no spaces) from an input string and returns the sum.
-/
def parseSum : SimpleParser String.Slice Char Int := do
  let mut sum : Int := 0
  -- parse until all input is consumed
  while ! (← test endOfInput) do
    -- parse an integer (decimal only) and add to sum
    sum := sum + (← ASCII.parseInt)
  return sum

#guard 42 == match parseSum.run "11-1+2-3+33" with
  | .ok _ sum => sum
  | .error _ e => panic! (toString e)

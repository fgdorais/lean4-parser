import Parser

open Parser

/-- Run `p` on `s` and return the remaining input, if `p` succeeds. -/
def rest (p : SimpleParser String.Slice Char Unit) (s : String) : Option String :=
  match Parser.run p s.toSlice with
  | .ok r _ => some r.copy
  | .error _ _ => none

-- `drop n p` consumes no input on error, like `take n p`
#guard rest (drop 2 (token 'a')) "aab" == some "b"
#guard rest (drop 2 (token 'a')) "ab" == none
#guard rest (try drop 2 (token 'a') catch _ => pure ()) "ab" == some "ab"
-- `dropUpTo n p` stops early when `p` fails
#guard rest (dropUpTo 3 (token 'a')) "aab" == some "b"
#guard rest (dropUpTo 3 (token 'a')) "b" == some "b"
#guard rest (dropUpTo 2 (token 'a')) "aaa" == some "a"

module

import Parser
meta import Parser.Error
meta import Parser.Parser
open Parser

namespace Test126

abbrev TestParser := SimpleParser ByteSlice UInt8

def test (tk : Char) : TestParser UInt8 := tokenFilter (· = tk.val.toUInt8)

def run (p : TestParser UInt8) (input : String) : String :=
  let arr := input.toByteArray.toByteSlice
  match p.run arr with | .ok _ _ x => s!"ok {Char.ofUInt8 x}" | .error _ _ e => s!"error {e}"

/-- info: "ok a" -/
#guard_msgs in #eval run (test 'a' <|> test 'b') "a"

/-- info: "ok b" -/
#guard_msgs in #eval run (test 'a' <|> test 'b') "b"

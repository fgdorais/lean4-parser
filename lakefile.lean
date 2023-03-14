import Lake
open Lake DSL

package Parser

@[default_target]
lean_lib Parser

require Std from git
  "https://github.com/leanprover/std4" @ "main"

require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic" @ "main"

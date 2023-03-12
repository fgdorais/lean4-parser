import Lake
open Lake DSL

package Parser

@[default_target]
lean_lib Parser

require Std from git "https://github.com/leanprover/std4.git"@"main"

require UnicodeData from git "https://github.com/fgdorais/UnicodeData"@"main"

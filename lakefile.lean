import Lake
open Lake DSL

package Parser

@[default_target]
lean_lib Parser

require std from git "https://github.com/leanprover/std4.git"@"main"

require Unicode from git "https://github.com/xubaiw/Unicode.lean"@"main"

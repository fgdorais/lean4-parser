/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lake
open Lake DSL

package Parser

@[default_target]
lean_lib Parser

require std from git
  "https://github.com/leanprover/std4" @ "main"

require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic" @ "main"

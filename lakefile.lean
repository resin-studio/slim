import Lake
open Lake DSL

-- ll -> ≪
-- gg -> ≫

package slim {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- @[default_target]
-- lean_lib Practice {
--   -- add any library configuration options here
-- }

@[default_target]
lean_lib Theory {
  -- add any library configuration options here
}

@[default_target]
lean_exe «greeting»  {
  root := `Main
}
import Lake
open Lake DSL

-- ll -> ≪
-- gg -> ≫

package slim {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


@[default_target]
lean_lib NormalLib {
  -- add any library configuration options here
}

-- @[default_target]
-- lean_lib SurfaceLib {
--   -- add any library configuration options here
-- }

@[default_target]
lean_lib TestLib {
  -- add any library configuration options here
}

@[default_target]
lean_exe «sanity»  {
  root := `SanityScript
}
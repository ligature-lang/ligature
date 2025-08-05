import Lake
open Lake DSL

package ligature_spec {
  -- add package configuration options here
}

@[default_target]
lean_lib Ligature {
  -- add library configuration options here
}

lean_lib TypeSystem {
  -- add library configuration options here
}

lean_lib OperationalSemantics {
  -- add library configuration options here
}

lean_lib ConfigurationLanguage {
  -- add library configuration options here
}

-- Add dependencies on mathlib
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

-- Add test targets
@[default_target]
lean_exe test_spec {
  root := `TestSpec
}

-- Add documentation target
@[default_target]
lean_exe docs {
  root := `Docs
}

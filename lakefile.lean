import Lake
open Lake DSL

package "Peirce" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Peirce» where
  -- add library configuration options here

import Lake
open Lake DSL

package "allegories" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib «Allegories»

import Lake
open Lake DSL

package «fnz-positive-cones» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "dec5b2b780537b6eaf7f5e5f000c12f7387fb24d"

@[default_target]
lean_lib FnZPositiveCones where

-- Comparator builds these separately: Challenge deliberately contains proof holes.
lean_lib Challenge where

lean_lib Solution where

import Lake
open Lake DSL

package schreier_q2 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "141f6b6455959bfeb0b2a6b04118031191d62683"

lean_lib Statement where

@[default_target]
lean_lib SchreierQ2 where
  roots := #[`SchreierQ2.Check]

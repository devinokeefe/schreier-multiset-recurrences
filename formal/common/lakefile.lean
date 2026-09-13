import Lake

open Lake DSL

package schreierUnified where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "141f6b6455959bfeb0b2a6b04118031191d62683"

@[default_target]
lean_lib SchreierUnified where
  roots := #[`SchreierUnified.Audit]

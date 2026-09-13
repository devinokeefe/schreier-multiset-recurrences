import Lake

open Lake DSL

package schreier_q4 where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "141f6b6455959bfeb0b2a6b04118031191d62683"

@[default_target]
lean_lib SchreierQ4 where
  roots := #[`SchreierQ4.Main, `Audit]
  globs := #[.one `Statement, .submodules `SchreierQ4, .one `Audit]

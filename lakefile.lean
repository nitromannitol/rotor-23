import Lake

open Lake DSL

package «rotor23» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «Rotor» where
  globs := #[.submodules `Rotor]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

require PercolationContinuity from git
  "https://github.com/anthropics/formal-math" @ "795efb86f191735c5481675763537cfb4ff37e55" / "percolation"

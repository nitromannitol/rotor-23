import Lake

open Lake DSL

package «rotor23» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "81fad4f28061b5a61ab0d5a190622e8afe95dfe0"

/-- The comparator audit surface (`RotorAudit/*/Challenge.lean`, `RotorAudit/*/SolutionBasic.lean`,
`RotorAudit/*/Solution.lean` and `RotorAudit/Support/`).  Not a default target: it builds only on
demand (`lake build RotorAudit`), so the ordinary build of `Rotor` is unchanged. -/
lean_lib «RotorAudit» where
  globs := #[.submodules `RotorAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «Rotor» where
  globs := #[.andSubmodules `Rotor]
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

import Lake

open Lake DSL

package «rotor23» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "9d44b4d4670df393bb86ac5a4e042f215001cddf"

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

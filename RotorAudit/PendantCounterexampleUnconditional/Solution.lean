import Mathlib
import Rotor.MainTheorems
import RotorAudit.PendantCounterexample.SolutionBasic
import RotorAudit.Support.PendantCounterexampleBridge

/-!
# Unconditional comparator solution: PendantCounterexample

The theorem follows from the main result through the vocabulary bridge.
-/

namespace RotorAudit

open MeasureTheory Filter Topology
open scoped Pointwise

universe u

/-- Proposition 1.3 (`prop:pendant-counterexample`). -/
theorem pendant_counterexample_unconditional :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o := by
  have h := _root_.Rotor.pendant_counterexample
  simp only [Bridge.Recurrent_eq, Bridge.uniformLaw_eq, Bridge.toMech_pendantMech]
  exact h

end RotorAudit

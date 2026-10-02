import Mathlib
import Rotor.MainTheorems
import RotorAudit.PendantCounterexample.SolutionBasic
import RotorAudit.Support.PendantCounterexampleBridge

/-!
# Solution: PendantCounterexample

The challenge module `RotorAudit/PendantCounterexample/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the repository together with
`RotorAudit.PendantCounterexample.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `Rotor.pendant_counterexample` through the bridge in
`RotorAudit/Support/PendantCounterexampleBridge.lean`.
-/

namespace RotorAudit

open MeasureTheory Filter Topology
open scoped Pointwise

universe u

/-- Proposition 1.3 (`prop:pendant-counterexample`). -/
theorem pendant_counterexample :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o := by
  have h := _root_.Rotor.pendant_counterexample
  simp only [Bridge.Recurrent_eq, Bridge.uniformLaw_eq, Bridge.toMech_pendantMech]
  exact h

end RotorAudit

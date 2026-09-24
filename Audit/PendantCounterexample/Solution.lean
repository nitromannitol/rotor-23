import Mathlib
import Rotor.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: PendantCounterexample

The challenge module `Audit/PendantCounterexample/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository
together with `Audit.Support.Vocabulary`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `Rotor.pendant_counterexample` through
the bridges in `Audit/Support/Bridge.lean`.
-/

namespace RotorAudit

open MeasureTheory Filter Topology
open scoped Pointwise

universe u

/-- Proposition 1.3 (`prop:pendant-counterexample`). -/
theorem pendant_counterexample
    (hFLP : ∀ M : ℕ, External.OneCircuit (pendantGraph M))
    (hAH : ∀ M : ℕ, External.RecurrentOfRecurrent (pendantGraph M)) :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o := by
  have h := _root_.Rotor.pendant_counterexample (fun M => Bridge.oneCircuit (hFLP M))
    (fun M => Bridge.recurrentOfRecurrent (hAH M))
  simp only [Bridge.Recurrent_eq, Bridge.uniformLaw_eq, Bridge.toMech_pendantMech]
  exact h

end RotorAudit

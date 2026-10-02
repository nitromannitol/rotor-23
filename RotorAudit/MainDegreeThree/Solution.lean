import Mathlib
import Rotor.MainTheorems
import RotorAudit.MainDegreeThree.SolutionBasic
import RotorAudit.Support.MainDegreeThreeBridge

/-!
# Solution: MainDegreeThree

The challenge module `RotorAudit/MainDegreeThree/Challenge.lean` imports only Mathlib and states the
theorem with one intentional `sorry`.  This solution imports the repository together with
`RotorAudit.MainDegreeThree.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `Rotor.main_degree_three` through the bridge in
`RotorAudit/Support/MainDegreeThreeBridge.lean`.
-/

namespace RotorAudit

open MeasureTheory Filter Topology
open scoped Pointwise

universe u

/-- Theorem 1.1 (`thm:main`), doubly periodic graphs of maximum degree three. -/
theorem main_degree_three {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite]
    (hLSS : External.LSS)
    (P : DoublyPeriodic G) (π : Mechanism G) [Infinite V] (hG : G.Connected)
    (hπ : P.Periodic π) (h3 : ∀ v : V, G.degree v ≤ 3) (o : V) :
    ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(uniformLaw π), Recurrent π ρ o ∧ (∀ n : ℕ, T π ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : V, P.emb x - P.emb o ∈ ((1 - ε) * n) • B → x ∈ A π ρ o n) ∧
          (∀ x ∈ A π ρ o n, P.emb x - P.emb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => P.emb x - P.emb o) '' (R π ρ o t : Set V)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c) := by
  have h := _root_.Rotor.main_degree_three
    (Bridge.lss hLSS)
    (Bridge.toDP P) (Bridge.toMech π) hG ((Bridge.periodic_iff P π).1 hπ) h3 o
  simp only [Bridge.T_eq, Bridge.A_eq, Bridge.R_eq, Bridge.Recurrent_eq, Bridge.uniformLaw_eq]
  exact h

end RotorAudit

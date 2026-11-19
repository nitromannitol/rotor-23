import Rotor.MainTheoremsUnconditional
import Mathlib
import Rotor.MainTheorems
import RotorAudit.MainSquare.SolutionBasic
import RotorAudit.Support.MainSquareBridge

/-!
# Unconditional comparator solution: MainSquare

The theorem follows from the unconditional result through the vocabulary bridge.
-/

namespace RotorAudit

open MeasureTheory Filter Topology
open scoped Pointwise

universe u

/-- Theorem 1.1 (`thm:main`), square lattice. -/
theorem main_square_unconditional
    (o : Site) :
    ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(uniformLaw clockwise), Recurrent clockwise ρ o ∧ (∀ n : ℕ, T clockwise ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) '' (A clockwise ρ o n : Set Site))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => squareEmb x - squareEmb o) '' (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c) := by
  have h := _root_.Rotor.main_square_unconditional
    o
  simp only [Bridge.T_eq, Bridge.A_eq, Bridge.R_eq, Bridge.Recurrent_eq, Bridge.uniformLaw_eq,
    Bridge.toMech_clockwise]
  exact h

end RotorAudit

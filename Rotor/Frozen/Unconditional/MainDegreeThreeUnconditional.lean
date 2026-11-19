import Rotor.MainTheoremsUnconditional

/-! # Unconditional form of the rotor theorem -/

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.main_degree_three_unconditional {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite]
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
        Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)
-- FROZEN-STATEMENT-END
:= Rotor.main_degree_three_unconditional P π hG hπ h3 o

/-
Proposition 1.2 of rotor.tex, the degree-three case, frozen.
`rotor.tex:263-271` (label `prop:small-perturbations`); see
`Rotor/Frozen/Main/PerturbSquare.lean`.
-/
import Rotor.Events
import Rotor.Percolation
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.External.SubcriticalDecay

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.perturbations_degree_three (hFLP : External.OneCircuit G)
    (hAb : External.Abelian G) (hHP : External.VisitsAllOfVisitsOne G)
    (hK : External.Kingman.{u}) (hLSS : External.LSS) (P : DoublyPeriodic G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (hπ : P.Periodic π) (h3 : ∀ v : V, G.degree v ≤ 3) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)],
        (∀ v, tvDist (ν v) (uniformAt π v) < δ) →
        (∀ o : V, ∀ᵐ ρ ∂(productLaw ν), Recurrent π ρ o) ∧
        (P.InvariantMarginals ν → ∀ o : V,
          ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(productLaw ν), (∀ n : ℕ, T π ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : V, P.emb x - P.emb o ∈ ((1 - ε) * n) • B → x ∈ A π ρ o n) ∧
          (∀ x ∈ A π ρ o n, P.emb x - P.emb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => P.emb x - P.emb o) '' (R π ρ o t : Set V)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c))
-- FROZEN-STATEMENT-END
:= by sorry

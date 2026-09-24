import Rotor.Bridge.SubcriticalDecay
import Rotor.Frozen.Square.ConstrainedBonds
import Rotor.Frozen.Square.Passage
import Rotor.Frozen.Main.Square
import Rotor.Frozen.Main.PerturbSquare

/-!
The paper's statements with `External.SubcriticalDecay` discharged by
`Rotor.Bridge.subcriticalDecay_holds`.  The frozen statements themselves keep that hypothesis;
these are corollaries of them.  Lemma 5.3 and Proposition 5.1 become unconditional; Theorem 1.1
and Proposition 1.2 keep the five inputs the percolation library does not provide
(Florescu-Levine-Peres, the abelian property, Holroyd-Propp, Kingman, Liggett-Schonmann-Stacey).
-/

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

namespace Rotor.Bridge


/-- Lemma 5.3 of rotor.tex, with the subcritical decay discharged. -/
theorem square_constrained_bonds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) Rotor.half_le_one (constrainedCrossing x r) ≤
        ENNReal.ofReal (C * Real.exp (-c * r)) :=
  Rotor.Frozen.square_constrained_bonds subcriticalDecay_holds


/-- Proposition 5.1 of rotor.tex, with the subcritical decay discharged. -/
theorem square_passage :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (u v : Site), squareGraph.Adj u v → ∀ R : ℕ, 1 ≤ R →
      uniformLaw clockwise (liveReachEvent clockwise u v R) ≤
        ENNReal.ofReal (C * Real.exp (-c * R)) :=
  Rotor.Frozen.square_passage subcriticalDecay_holds


/-- Theorem 1.1 of rotor.tex for the square lattice, with the subcritical decay discharged. -/
theorem main_square (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS)
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
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c) :=
  Rotor.Frozen.main_square hFLP hAb hHP hK hLSS subcriticalDecay_holds o


/-- Proposition 1.2 of rotor.tex for the square lattice, with the subcritical decay discharged. -/
theorem perturbations_square (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ν : ∀ v : Site, Measure (squareGraph.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)],
        (∀ v, tvDist (ν v) (uniformAt clockwise v) < δ) →
        (∀ o : Site, ∀ᵐ ρ ∂(productLaw ν), Recurrent clockwise ρ o) ∧
        (∀ (Λ : AddSubgroup Site) [Λ.FiniteIndex],
          (∀ z ∈ Λ, ∀ v, Measure.map (squarePeriodic.shiftNbr z) (ν v) = ν (v + z)) →
          ∀ o : Site,
          ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(productLaw ν), (∀ n : ℕ, T clockwise ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) '' (A clockwise ρ o n : Set Site))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => squareEmb x - squareEmb o) '' (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)) :=
  Rotor.Frozen.perturbations_square hFLP hAb hHP hK hLSS subcriticalDecay_holds


end Rotor.Bridge

import Rotor.Support.MainDegreeThree
import Rotor.Support.SquareLattice
import Rotor.Frozen.Square.Passage

/-!
Theorem 1.1 and Proposition 1.2 on the square lattice (`rotor.tex:1490-1508`), from
`prop:square-passage` exactly as the degree-three case follows from
`prop:degree-three-passage`.
-/

open Filter Topology MeasureTheory
open scoped Pointwise ENNReal

namespace Rotor

/-- Theorem 1.1, square-lattice case. -/
theorem main_square_proof (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS) (hSub : External.SubcriticalDecay)
    (o : Site) :
    ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(uniformLaw clockwise), Recurrent clockwise ρ o ∧ (∀ n : ℕ, T clockwise ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) '' (A clockwise ρ o n : Set Site))) B)
          atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) •
            ((fun x => squareEmb x - squareEmb o) '' (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ))
          atTop (𝓝 c) := by
  have hG := squareGraph_connected
  have hπ := squarePeriodic_periodic
  have hdeg : ∀ v : Site, squareGraph.degree v ≤ 4 := fun v => (squareGraph_degree v).le
  obtain ⟨ε, hε, L₀, hL₀, hblock⟩ :=
    Rotor.Frozen.block_live_paths hLSS squarePeriodic clockwise hG
  obtain ⟨c₀, C₀, hc₀, hC₀, hpass⟩ := Rotor.Frozen.square_passage hSub
  obtain ⟨L, hLL₀, hLpos, hsmall⟩ :=
    exists_block_small clockwise squarePeriodic hG hdeg hc₀ hC₀ hpass hε L₀
  obtain ⟨η, hη, hcrit, -⟩ := hblock (uniformAt clockwise) L hLL₀ hsmall
  obtain ⟨hrec, -, -⟩ := Rotor.Frozen.path_reduction hFLP hAb hHP hK clockwise hG ⟨4, hdeg⟩
    (uniformLaw clockwise) η hη hcrit
  obtain ⟨B, hBc, hBconv, hB0, κ, c, hκ, hc, hae⟩ := shape_sandwich_proof clockwise squarePeriodic
    hFLP hAb hHP hK hG ⟨4, hdeg⟩ (uniformLaw clockwise) η hη hcrit hπ
    (squarePeriodic.uniformLaw_invariant clockwise) (squarePeriodic.uniformLaw_ergodic clockwise) o
  refine ⟨B, hBc, hBconv, hB0, κ, c, hκ, hc, ?_⟩
  filter_upwards [hrec, hae] with ρ h1 h2
  exact ⟨h1.2 o, h2⟩

/-- Proposition 1.2, square-lattice case. -/
theorem perturbations_square_proof (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS) (hSub : External.SubcriticalDecay) :
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
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) '' (A clockwise ρ o n : Set Site))) B)
          atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) •
            ((fun x => squareEmb x - squareEmb o) '' (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ))
          atTop (𝓝 c)) := by
  have hG := squareGraph_connected
  have hdeg : ∀ v : Site, squareGraph.degree v ≤ 4 := fun v => (squareGraph_degree v).le
  obtain ⟨ε, hε, L₀, hL₀, hblock⟩ :=
    Rotor.Frozen.block_live_paths hLSS squarePeriodic clockwise hG
  obtain ⟨c₀, C₀, hc₀, hC₀, hpass⟩ := Rotor.Frozen.square_passage hSub
  obtain ⟨L, hLL₀, hLpos, hsmall⟩ :=
    exists_block_small clockwise squarePeriodic hG hdeg hc₀ hC₀ hpass hε L₀
  obtain ⟨η, hη, -, δ, hδ, hpert⟩ := hblock (uniformAt clockwise) L hLL₀ hsmall
  refine ⟨δ, hδ, fun ν _ hν => ?_⟩
  have hcrit : Criterion clockwise (productLaw ν) η := hpert ν (fun v => (hν v).le)
  obtain ⟨hrec, -, -⟩ := Rotor.Frozen.path_reduction hFLP hAb hHP hK clockwise hG ⟨4, hdeg⟩
    (productLaw ν) η hη hcrit
  refine ⟨fun o => by filter_upwards [hrec] with ρ h; exact h.2 o, fun Λ _ hinv o => ?_⟩
  exact shape_sandwich_proof clockwise (squareLatticePeriodic Λ) hFLP hAb hHP hK hG ⟨4, hdeg⟩ (productLaw ν)
    η hη hcrit (squareLatticePeriodic_periodic Λ)
    ((squareLatticePeriodic Λ).productLaw_invariant ν
      (squareLatticePeriodic_invariantMarginals Λ ν hinv))
    ((squareLatticePeriodic Λ).productLaw_ergodic
      ((squareLatticePeriodic Λ).productLaw_invariant ν
        (squareLatticePeriodic_invariantMarginals Λ ν hinv))) o

end Rotor

/-
Proposition 1.2 of rotor.tex, the square-lattice case, frozen.
`rotor.tex:263-271` (label `prop:small-perturbations`):

  "Fix a graph and rotor mechanism satisfying the hypotheses of Theorem 1.1.
   There is $\delta>0$ with the following property.  Suppose that the initial
   rotors are independent and that the law at every vertex has total variation
   distance less than $\delta$ from the uniform law.  Then conclusion (i) of
   Theorem 1.1 holds, and if these laws are invariant under the translation
   lattice, then conclusions (ii) and (iii) hold as well."

Split into two nodes like Theorem 1.1.  Conclusion (i) is asserted for every
start; (ii) and (iii) are the conjunction frozen in `thm-main-square` minus
recurrence, under invariance of the one-vertex laws.
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
theorem Rotor.Frozen.perturbations_square (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS) (hSub : External.SubcriticalDecay) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ν : ∀ v : Site, Measure (squareGraph.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)],
        (∀ v, tvDist (ν v) (uniformAt clockwise v) < δ) →
        (∀ o : Site, ∀ᵐ ρ ∂(productLaw ν), Recurrent clockwise ρ o) ∧
        (squarePeriodic.InvariantMarginals ν → ∀ o : Site,
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
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c))
-- FROZEN-STATEMENT-END
:= by sorry

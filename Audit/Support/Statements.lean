import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace RotorAudit.Statements

open RotorAudit MeasureTheory Filter Topology
open scoped Pointwise

universe u

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/MainSquare/Challenge.lean`. -/
def mainSquare : Prop :=
  ∀ (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS)
    (o : Site),
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
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)

/-- The statement of `Audit/MainDegreeThree/Challenge.lean`. -/
def mainDegreeThree : Prop :=
  ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite] (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) (hLSS : External.LSS)
    (P : DoublyPeriodic G) (π : Mechanism G) [Infinite V] (hG : G.Connected)
    (hπ : P.Periodic π) (h3 : ∀ v : V, G.degree v ≤ 3) (o : V),
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

/-- The statement of `Audit/PerturbationsSquare/Challenge.lean`. -/
def perturbationsSquare : Prop :=
  ∀ (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS),
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
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c))

/-- The statement of `Audit/PerturbationsDegreeThree/Challenge.lean`. -/
def perturbationsDegreeThree : Prop :=
  ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite] (hFLP : External.OneCircuit G)
    (hAb : External.Abelian G) (hHP : External.VisitsAllOfVisitsOne G)
    (hK : External.Kingman.{u}) (hLSS : External.LSS) (P : DoublyPeriodic G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (hπ : P.Periodic π) (h3 : ∀ v : V, G.degree v ≤ 3),
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

/-- The statement of `Audit/PendantCounterexample/Challenge.lean`. -/
def pendantCounterexample : Prop :=
  ∀
    (hFLP : ∀ M : ℕ, External.OneCircuit (pendantGraph M))
    (hAH : ∀ M : ℕ, External.RecurrentOfRecurrent (pendantGraph M)),
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o

end RotorAudit.Statements

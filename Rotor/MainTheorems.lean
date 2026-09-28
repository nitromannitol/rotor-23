import Rotor.Frozen.Main.Square
import Rotor.Frozen.Main.DegreeThree
import Rotor.Frozen.Main.PerturbSquare
import Rotor.Frozen.Main.PerturbDegreeThree
import Rotor.Frozen.Main.Pendant

/-!
# Main results

The main theorems of the formalization of *Eulerian walkers on `ℤ²` have range
exponent `2/3`* (Bou-Rabee and Peres, arXiv:2608.23545), stated here in full:
Theorem 1.1 (`thm:main`) for the square lattice and for doubly periodic graphs
of maximum degree three, Proposition 1.2 (`prop:small-perturbations`) in the
same two cases, and Proposition 1.3 (`prop:pendant-counterexample`).

Each theorem below restates its certified counterpart in `Rotor/Frozen/Main/`
and is proved by direct application of it, so the statements displayed in this
file are byte-faithful to the certified ones.  None of the five carries
Florescu–Levine–Peres' one-circuit property (Lemmas 2.1 and 2.4) as a
hypothesis any longer: it is proved in this repository,
`Rotor.Bridge.oneCircuit_holds`, by an injectivity argument on the walk's
traversed edges together with incoming/outgoing degree counts at circuit
times.  Nor do the four theorems below that used to carry
Holroyd–Propp's Lemma 6 (a rotor walk that visits one vertex infinitely often
visits every vertex infinitely often) any longer: it is proved in this
repository, `Rotor.Bridge.visitsAllOfVisitsOne_holds`, by propagating
infinitely-many-visits along a walk between any two vertices of the graph.
Nor does any of the four square/degree-three theorems carry the
abelian property of rotor-routing (HLMPPW Lemma 3.9) as a hypothesis any
longer: it is proved in this repository, `Rotor.Bridge.abelian_holds`, by
induction on legal routings.  Nor does `Rotor.pendant_counterexample` carry
Angel–Holroyd's independence-of-start property for recurrence
(`External.RecurrentOfRecurrent`) as a hypothesis any longer: it is proved in
this repository, `Rotor.Bridge.recurrentOfRecurrent_holds`, by propagating
recurrence along adjacency and then along a connecting walk between any two
vertices.  On the square lattice, the certified statements
`Rotor.Frozen.main_square` and `Rotor.Frozen.perturbations_square` likewise no
longer carry Kingman's subadditive ergodic theorem or subcritical exponential
decay for Bernoulli bond percolation as hypotheses: both are proved in this
repository, `Rotor.Bridge.kingman_holds` from the shared library
`Lattice-Probability` and `Rotor.Bridge.subcriticalDecay_holds` from the
percolation library `PercolationContinuity`.  Each is discharged by
instantiating the corresponding bridge theorem directly.  The remaining
hypotheses named `External.*` are results the paper cites without proof; they
are assumed, not proved, and are listed with their statements in
`ASSUMPTIONS.md`.

* `Rotor.main_square`: Theorem 1.1 on `ℤ²` with the clockwise mechanism and
  independent uniform initial rotors.  Almost surely the walk is recurrent,
  `n⁻¹ A_n → B` and `t^{-1/3} R_t → κ B` in Hausdorff distance for a
  deterministic compact convex `B` with the origin in its interior and a
  deterministic `κ > 0`, and `|R_t| t^{-2/3} → c` for a deterministic
  `c ∈ (0, ∞)`.
* `Rotor.main_degree_three`: the same conclusions on a doubly periodic plane
  graph of maximum degree three with a doubly periodic mechanism.
* `Rotor.perturbations_square`, `Rotor.perturbations_degree_three`:
  Proposition 1.2, the same conclusions for independent rotor laws within
  total variation `δ` of uniform.
* `Rotor.pendant_counterexample`: Proposition 1.3, on the square lattice with
  `M ≥ 50331645` leaves attached to each vertex the walk is almost surely
  transient.

All five reduce to the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); see `Rotor/Meta/AxiomsAudit.lean`.
-/

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

/-- **Theorem 1.1, square lattice** (`thm:main`).  The certified statement is
`Rotor.Frozen.main_square`. -/
theorem Rotor.main_square
    (hLSS : External.LSS)
    (o : Site) :
    ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(uniformLaw clockwise), Recurrent clockwise ρ o ∧ (∀ n : ℕ, T clockwise ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) ''
            (A clockwise ρ o n : Set Site))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => squareEmb x - squareEmb o) ''
            (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ))
          atTop (𝓝 c) := by
  exact Rotor.Frozen.main_square hLSS o

/-- **Theorem 1.1, doubly periodic graphs of maximum degree three** (`thm:main`).
The certified statement is `Rotor.Frozen.main_degree_three`. -/
theorem Rotor.main_degree_three {V : Type u} [DecidableEq V] {G : SimpleGraph V}
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
  exact Rotor.Frozen.main_degree_three hLSS P π hG hπ h3 o

/-- **Proposition 1.2, square lattice** (`prop:small-perturbations`).  The
certified statement is `Rotor.Frozen.perturbations_square`. -/
theorem Rotor.perturbations_square
    (hLSS : External.LSS) :
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
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) ''
            (A clockwise ρ o n : Set Site))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => squareEmb x - squareEmb o) ''
            (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ))
          atTop (𝓝 c)) := by
  exact Rotor.Frozen.perturbations_square hLSS

/-- **Proposition 1.2, doubly periodic graphs of maximum degree three**
(`prop:small-perturbations`).  The certified statement is
`Rotor.Frozen.perturbations_degree_three`. -/
theorem Rotor.perturbations_degree_three {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite]
    (hLSS : External.LSS) (P : DoublyPeriodic G) (π : Mechanism G)
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
        Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)) := by
  exact Rotor.Frozen.perturbations_degree_three hLSS P π hG hπ h3

/-- **Proposition 1.3** (`prop:pendant-counterexample`).  The certified
statement is `Rotor.Frozen.pendant_counterexample`. -/
theorem Rotor.pendant_counterexample :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o := by
  exact Rotor.Frozen.pendant_counterexample

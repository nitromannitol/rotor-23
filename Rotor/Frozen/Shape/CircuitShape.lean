/-
Proposition 3.3 of rotor.tex, frozen.  `rotor.tex:1115-1133` (label `prop:circuit-shape`):

  "Let $\mu$ be the passage function from Proposition 3.2.  Suppose that the
   passage-ball identity holds almost surely for every $n\geq0$ and that
   $\min_{|u|=1}\mu(u)>0$.  Define $B:=\{x\in\R^2:\mu(x)\leq1\}$.  Then $B$
   is compact and convex and contains the origin in its interior.  Almost
   surely, $n^{-1}A_n\to B$ in Hausdorff distance.  Almost surely, for every
   $\varepsilon\in(0,1)$, $(1-\varepsilon)nB\cap V\subseteq A_n\subseteq
   (1+\varepsilon)nB\cap V$ for every sufficiently large $n$."

The passage function is a parameter `f` carrying the conclusion of
`prop:passage-limit` as hypotheses; the passage-ball identity is
`prop:passage`'s third conjunct almost surely; `min_{|u|=1} μ(u) > 0` is a
positive lower bound on the unit sphere.  Sets are drawn through `P.emb`
relative to `o`.  Two set limits and three properties of `B`.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
-/
import Rotor.Events
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.circuit_shape (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) (P : DoublyPeriodic G) (hπ : P.Periodic π)
    (hinv : P.Invariant μ) (herg : P.Ergodic μ) (o : V) (f : Plane → ℝ)
    (hf : Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x y, f (x + y) ≤ f x + f y) ∧
      (∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x) ∧
      ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : V, R₀ ≤ ‖P.emb x - P.emb o‖ →
        |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ ε * ‖P.emb x - P.emb o‖)
    (hball : ∀ᵐ ρ ∂μ, ∀ n : ℕ, T π ρ o n < ⊤ ∧ ∀ x : V, x ∈ A π ρ o n ↔ τ π ρ o x ≤ n)
    (hmin : ∃ l : ℝ, 0 < l ∧ ∀ u : Plane, ‖u‖ = 1 → l ≤ f u) :
    IsCompact {x : Plane | f x ≤ 1} ∧ Convex ℝ {x : Plane | f x ≤ 1} ∧
      (0 : Plane) ∈ interior {x : Plane | f x ≤ 1} ∧
    (∀ᵐ ρ ∂μ, Tendsto (fun n : ℕ => Metric.hausdorffDist
        ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V)))
        {x : Plane | f x ≤ 1}) atTop (𝓝 0)) ∧
    (∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n))
-- FROZEN-STATEMENT-END
:= by sorry

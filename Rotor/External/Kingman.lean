/-
External input: Kingman's subadditive ergodic theorem, *The ergodic theory of
subadditive stochastic processes* (1968), Theorems 3 and 5, as used in the
proof of `prop:passage-limit` (`rotor.tex:1096-1113`):

  "The stationary subadditive array `{τ(o+mz, o+nz) : 0 ≤ m < n}` has an
   integrable linear bound ... The subadditive ergodic theorem gives, almost
   surely and in `L¹`, ... a limit `μ(z) := lim τ(o, o+nz)/n`", deterministic
   by ergodicity of the law under the lattice.

Assumed in the form used (Kingman's Theorem 3): for a measure-preserving map
`θ` and a nonnegative stationary subadditive array `X m n` with a linear bound
on its expectations, `X 0 n / n` converges almost surely to a measurable
`θ`-invariant limit.  The paper calls this limit "a priori random" and makes it
deterministic through ergodicity of the whole lattice action, not of the single
map `θ`; version 1 of this file assumed ergodicity of `θ` and a constant limit,
which the paper's hypotheses cannot supply (an ergodic `ℤ²`-action need not
have ergodic generators).  Kingman's theorem also gives convergence in `L¹`;
the paper's proof uses only the almost-sure limit, so the `L¹` clause is
deliberately not assumed.
-/
import Mathlib

open MeasureTheory Filter Topology

universe u

-- FROZEN-STATEMENT-BEGIN
/-- Kingman's subadditive ergodic theorem (Theorem 3 of Kingman 1968),
assumed: a measurable `θ`-invariant almost-sure limit. -/
def Rotor.External.Kingman : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ θ : Ω → Ω, MeasurePreserving θ μ μ →
      ∀ X : ℕ → ℕ → Ω → ℝ,
        (∀ m n, Measurable (X m n)) →
        (∀ m n ω, 0 ≤ X m n ω) →
        (∀ m n ω, X m n (θ ω) = X (m + 1) (n + 1) ω) →
        (∀ l m n ω, l ≤ m → m ≤ n → X l n ω ≤ X l m ω + X m n ω) →
        (∃ c : ℝ, ∀ n, ∫ ω, X 0 n ω ∂μ ≤ c * n) →
        ∃ γ : Ω → ℝ, Measurable γ ∧ (∀ᵐ ω ∂μ, γ (θ ω) = γ ω) ∧
          ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (γ ω))
-- FROZEN-STATEMENT-END

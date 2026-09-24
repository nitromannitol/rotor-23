/-
External input: Kingman's subadditive ergodic theorem, *The ergodic theory of
subadditive stochastic processes* (1968), Theorems 3 and 5, as used in the
proof of `prop:passage-limit` (`rotor.tex:1116-1125`).

On a probability space, a measure-preserving map `θ` and a measurable,
nonnegative, integrable, stationary subadditive array `X m n` with linearly
bounded expectations admit a measurable, almost surely `θ`-invariant limit
of `X 0 n / n`.  Theorem 3 gives invariance of the limit, and Theorem 5 gives
almost-sure convergence.  The paper makes this limit deterministic through
ergodicity of the whole lattice action.  The almost-sure conclusion is the
form used here.
-/
import Mathlib

open MeasureTheory Filter Topology

universe u

-- FROZEN-STATEMENT-BEGIN
/-- Kingman's subadditive ergodic theorem (Kingman 1968, Theorems 3 and 5):
a measurable, nonnegative, integrable stationary subadditive array with linearly
bounded expectations has a measurable, almost surely `θ`-invariant limit. -/
def Rotor.External.Kingman : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ θ : Ω → Ω, MeasurePreserving θ μ μ →
      ∀ X : ℕ → ℕ → Ω → ℝ,
        (∀ m n, Measurable (X m n)) →
        (∀ m n, Integrable (X m n) μ) →
        (∀ m n ω, 0 ≤ X m n ω) →
        (∀ m n ω, X m n (θ ω) = X (m + 1) (n + 1) ω) →
        (∀ l m n ω, l ≤ m → m ≤ n → X l n ω ≤ X l m ω + X m n ω) →
        (∃ c : ℝ, ∀ n, ∫ ω, X 0 n ω ∂μ ≤ c * n) →
        ∃ γ : Ω → ℝ, Measurable γ ∧ (∀ᵐ ω ∂μ, γ (θ ω) = γ ω) ∧
          ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (γ ω))
-- FROZEN-STATEMENT-END

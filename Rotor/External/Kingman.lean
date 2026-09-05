/-
External input: Kingman's subadditive ergodic theorem, *The ergodic theory of
subadditive stochastic processes* (1968), Theorems 3 and 5, as used in the
proof of `prop:passage-limit` (`rotor.tex:1096-1113`):

  "The stationary subadditive array `{τ(o+mz, o+nz) : 0 ≤ m < n}` has an
   integrable linear bound ... The subadditive ergodic theorem gives, almost
   surely and in `L¹`, ... a limit `μ(z) := lim τ(o, o+nz)/n`", deterministic
   by ergodicity of the law under the lattice.

Assumed in the form used: for an ergodic measure-preserving map `θ` and a
nonnegative stationary subadditive array `X m n` with a linear bound on its
expectations, `X 0 n / n` converges almost surely to a constant.  Kingman's
theorem also gives convergence in `L¹`; the paper's proof uses only the
almost-sure limit (through convergence in probability), so the `L¹` clause is
deliberately not assumed.  Ruling X-001.
-/
import Mathlib

open MeasureTheory Filter Topology

universe u

-- FROZEN-STATEMENT-BEGIN
/-- Kingman's subadditive ergodic theorem, ergodic case, assumed. -/
def Rotor.External.Kingman : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ θ : Ω → Ω, MeasurePreserving θ μ μ →
      (∀ s : Set Ω, MeasurableSet s → θ ⁻¹' s = s → μ s = 0 ∨ μ s = 1) →
      ∀ X : ℕ → ℕ → Ω → ℝ,
        (∀ m n, Measurable (X m n)) →
        (∀ m n ω, 0 ≤ X m n ω) →
        (∀ m n ω, X m n (θ ω) = X (m + 1) (n + 1) ω) →
        (∀ l m n ω, l ≤ m → m ≤ n → X l n ω ≤ X l m ω + X m n ω) →
        (∃ c : ℝ, ∀ n, ∫ ω, X 0 n ω ∂μ ≤ c * n) →
        ∃ γ : ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 γ)
-- FROZEN-STATEMENT-END

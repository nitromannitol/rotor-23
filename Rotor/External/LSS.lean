/-
External input: Liggett--Schonmann--Stacey, *Domination by product measures*
(1997), Theorem 0.0(ii), in the instance the paper uses in the proof of
`lem:block-live-paths` (`rotor.tex:1243-1247`):

  "Choose `ε > 0` so that every `2`-dependent `{0,1}`-field with one-site
   probabilities at most `2ε` is dominated by independent Bernoulli variables
   of parameter `1/8`; this is possible by [LSS, Theorem 0.0(ii)]."

Domination is stated through increasing events: every increasing measurable
event has no larger probability under the field than under the product of
Bernoulli(1/8) laws.  Ruling X-001.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace Rotor.External

/-- The Bernoulli law on `Bool` with success probability `p`. -/
noncomputable def bernoulli (p : NNReal) (hp : p ≤ 1) : Measure Bool := (PMF.bernoulli p hp).toMeasure

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (bernoulli p hp) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Independent Bernoulli(`p`) variables indexed by `ℤ²`. -/
noncomputable def bernoulliField (p : NNReal) (hp : p ≤ 1) : Measure (ℤ × ℤ → Bool) :=
  Measure.infinitePi (fun _ : ℤ × ℤ => bernoulli p hp)

/-- A set of `{0,1}`-fields is increasing. -/
def IsIncreasing (A : Set (ℤ × ℤ → Bool)) : Prop :=
  ∀ ω ω' : ℤ × ℤ → Bool, ω ∈ A → (∀ z, ω z = true → ω' z = true) → ω' ∈ A

/-- The field with law `μ` is `k`-dependent: its restrictions to two finite
index sets at `ℓ^∞`-distance more than `k` are independent. -/
def KDependent (k : ℕ) (μ : Measure (ℤ × ℤ → Bool)) : Prop :=
  ∀ I J : Finset (ℤ × ℤ), (∀ i ∈ I, ∀ j ∈ J, (k : ℤ) < max |i.1 - j.1| |i.2 - j.2|) →
    IndepFun (fun ω : ℤ × ℤ → Bool => (fun i : I => ω i)) (fun ω => (fun j : J => ω j)) μ

theorem eighth_le_one : (1 / 8 : NNReal) ≤ 1 := by
  rw [div_le_one (by norm_num)]; norm_num

end Rotor.External

open Rotor.External

-- FROZEN-STATEMENT-BEGIN
/-- LSS Theorem 0.0(ii), in the instance used: some `ε > 0` makes every
`2`-dependent field with one-site probabilities at most `2ε` dominated by
independent Bernoulli(`1/8`) variables.  Assumed. -/
def Rotor.External.LSS : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ μ : Measure (ℤ × ℤ → Bool), IsProbabilityMeasure μ →
    KDependent 2 μ → (∀ z, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
    ∀ A : Set (ℤ × ℤ → Bool), MeasurableSet A → IsIncreasing A →
      μ A ≤ bernoulliField (1 / 8) eighth_le_one A
-- FROZEN-STATEMENT-END

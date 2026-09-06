/-
Analytic constants for the block estimate: the criterion follows from an eventual bound
uniform in the directed edge; the choice of `η` with `s^{-η} (7/8)^{c₁} < 1`
(`rotor.tex:1274`: "Choosing `η log(1/s) < γ`"); and the geometric decay of the bound.
-/
import Rotor.Events

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

omit [G.LocallyFinite] in
/-- The criterion follows from a bound that is uniform in the directed edge and tends to zero. -/
theorem criterion_of_bound (μ : Measure (Config G)) (η : ℝ) (b : ℕ → ℝ≥0∞)
    (hb : ∀ᶠ R in atTop, ∀ e : G.Dart, μ (almostLiveEvent π η e.fst e.snd R) ≤ b R)
    (hlim : Tendsto b atTop (𝓝 0)) : Criterion π μ η := by
  unfold Criterion
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun R => zero_le _)) ?_
  filter_upwards [hb] with R hR
  exact iSup_le hR

/-- The choice of `η`: `η := c₁ log(8/7) / (2 log(1/s))`. -/
theorem exists_eta {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ η : ℝ, 0 < η ∧ (7 / 8 : ℝ) ^ c₁ * (1 / s) ^ η < 1 := by
  have hs' : 1 < 1 / s := by rw [one_div, one_lt_inv₀ hs0]; exact hs1
  have hlog : 0 < Real.log (1 / s) := Real.log_pos hs'
  have hlog87 : 0 < Real.log (8 / 7) := Real.log_pos (by norm_num)
  refine ⟨c₁ * Real.log (8 / 7) / (2 * Real.log (1 / s)), by positivity, ?_⟩
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 7 / 8),
    Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 1 / s), ← Real.exp_add]
  apply Real.exp_lt_one_iff.2
  have h78 : Real.log (7 / 8) = - Real.log (8 / 7) := by
    rw [← Real.log_inv]; norm_num
  have h2 : Real.log (1 / s) * (c₁ * Real.log (8 / 7) / (2 * Real.log (1 / s))) =
      c₁ * Real.log (8 / 7) / 2 := by
    field_simp
  rw [h78, h2]
  nlinarith [mul_pos hc₁ hlog87]

/-- Geometric decay of the bound `(7/8)^{⌊c₁R - c₂⌋₊ - 10} (1/s)^{⌈ηR⌉₊}`. -/
theorem tendsto_geom_bound {s c₁ c₂ η : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hc₁ : 0 < c₁)
    (hη : 0 ≤ η) (hq : (7 / 8 : ℝ) ^ c₁ * (1 / s) ^ η < 1) :
    Tendsto (fun R : ℕ => (7 / 8 : ℝ) ^ (⌊c₁ * R - c₂⌋₊ - 10) * (1 / s) ^ ⌈η * R⌉₊) atTop
      (𝓝 0) := by
  have hq0 : 0 ≤ (7 / 8 : ℝ) ^ c₁ * (1 / s) ^ η := by positivity
  have hs' : 1 ≤ 1 / s := by rw [one_div, one_le_inv₀ hs0]; exact hs1
  have hlim : Tendsto (fun R : ℕ => (7 / 8 : ℝ) ^ (-(c₂ + 11)) * (1 / s) *
      ((7 / 8 : ℝ) ^ c₁ * (1 / s) ^ η) ^ R) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul
      ((7 / 8 : ℝ) ^ (-(c₂ + 11)) * (1 / s))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun R => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop ⌈(c₂ + 11) / c₁⌉₊] with R hR
  have hR' : (c₂ + 11) / c₁ ≤ R := (Nat.le_ceil _).trans (by exact_mod_cast hR)
  rw [div_le_iff₀ hc₁] at hR'
  have hfl : 10 ≤ ⌊c₁ * R - c₂⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hfl' : c₁ * R - c₂ - 11 ≤ ((⌊c₁ * R - c₂⌋₊ - 10 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfl]
    push_cast
    have := Nat.lt_floor_add_one (c₁ * R - c₂)
    linarith
  have hce : (⌈η * R⌉₊ : ℝ) ≤ η * R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h1 : (7 / 8 : ℝ) ^ (⌊c₁ * R - c₂⌋₊ - 10) ≤ (7 / 8 : ℝ) ^ (c₁ * R - c₂ - 11) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hfl'
  have h2 : (1 / s : ℝ) ^ ⌈η * R⌉₊ ≤ (1 / s : ℝ) ^ (η * R + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hs' hce
  calc (7 / 8 : ℝ) ^ (⌊c₁ * R - c₂⌋₊ - 10) * (1 / s) ^ ⌈η * R⌉₊
      ≤ (7 / 8 : ℝ) ^ (c₁ * R - c₂ - 11) * (1 / s) ^ (η * R + 1) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (7 / 8 : ℝ) ^ (-(c₂ + 11)) * (1 / s) * ((7 / 8 : ℝ) ^ c₁ * (1 / s) ^ η) ^ R := by
        rw [show c₁ * R - c₂ - 11 = c₁ * R + (-(c₂ + 11)) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 7 / 8), Real.rpow_add (by positivity : (0 : ℝ) < 1 / s),
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7 / 8), Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / s),
          Real.rpow_natCast, Real.rpow_natCast, Real.rpow_one, mul_pow]
        ring

end Rotor

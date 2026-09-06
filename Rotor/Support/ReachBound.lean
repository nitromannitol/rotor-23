import Rotor.Support.RootPotential
import Rotor.Frozen.Square.ForcedTests

/-!
Proposition 5.1 (`prop:square-passage`), part 7: the constants.  With `a = e^{c/2}` the layer
cake constant is finite, and the choice `n₀ = ⌊εR⌋ + 1` with `ε` small makes every term of the
reach bound exponentially small in `R`.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-! ### Real-analysis bookkeeping -/

theorem exp_decay_poly {α β γ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (R : ℕ) :
    (β * R + γ) * Real.exp (-α * R) ≤ (2 * β / α + γ) * Real.exp (-(α / 2) * R) := by
  have hx : 0 ≤ (α / 2) * R := by positivity
  have h1 : (α / 2) * R ≤ Real.exp ((α / 2) * R) := by
    have := Real.add_one_le_exp ((α / 2) * R); linarith
  have hexp : Real.exp (-α * R) = Real.exp (-(α / 2) * R) * Real.exp (-(α / 2) * R) := by
    rw [← Real.exp_add]; congr 1; ring
  have hβR : β * R * Real.exp (-(α / 2) * R) ≤ 2 * β / α := by
    have h2 : Real.exp (-(α / 2) * R) * Real.exp ((α / 2) * R) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos : 0 < Real.exp (-(α / 2) * R) := Real.exp_pos _
    calc β * R * Real.exp (-(α / 2) * R)
        = (2 * β / α) * ((α / 2) * R * Real.exp (-(α / 2) * R)) := by field_simp; try ring
      _ ≤ (2 * β / α) * (Real.exp ((α / 2) * R) * Real.exp (-(α / 2) * R)) := by
          gcongr
      _ = 2 * β / α := by rw [mul_comm (Real.exp _), h2, mul_one]
  rw [hexp]
  have hγ' : γ * Real.exp (-(α / 2) * R) ≤ γ := by
    have := Real.exp_le_one_iff.2 (show -(α / 2) * R ≤ 0 by nlinarith)
    nlinarith [Real.exp_pos (-(α / 2) * R)]
  nlinarith [Real.exp_pos (-(α / 2) * R)]

/-- Three exponentially decaying terms with polynomial prefactors are one. -/
theorem exists_exp_decay_three {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃ : ℝ} (h1 : 0 < α₁) (h2 : 0 < α₂)
    (h3 : 0 < α₃) (hb1 : 0 ≤ β₁) (hb2 : 0 ≤ β₂) (hb3 : 0 ≤ β₃) (hg1 : 0 ≤ γ₁) (hg2 : 0 ≤ γ₂)
    (hg3 : 0 ≤ γ₃) :
    ∃ C' c' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ R : ℕ,
      (β₁ * R + γ₁) * Real.exp (-α₁ * R) + (β₂ * R + γ₂) * Real.exp (-α₂ * R) +
        (β₃ * R + γ₃) * Real.exp (-α₃ * R) ≤ C' * Real.exp (-c' * R) := by
  refine ⟨(2 * β₁ / α₁ + γ₁) + (2 * β₂ / α₂ + γ₂) + (2 * β₃ / α₃ + γ₃) + 1,
    min (α₁ / 2) (min (α₂ / 2) (α₃ / 2)), by positivity, by positivity, fun R => ?_⟩
  have e1 := exp_decay_poly h1 hb1 hg1 R
  have e2 := exp_decay_poly h2 hb2 hg2 R
  have e3 := exp_decay_poly h3 hb3 hg3 R
  have hm1 : Real.exp (-(α₁ / 2) * R) ≤ Real.exp (-min (α₁ / 2) (min (α₂ / 2) (α₃ / 2)) * R) := by
    apply Real.exp_le_exp.2
    have := min_le_left (α₁ / 2) (min (α₂ / 2) (α₃ / 2))
    nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hm2 : Real.exp (-(α₂ / 2) * R) ≤ Real.exp (-min (α₁ / 2) (min (α₂ / 2) (α₃ / 2)) * R) := by
    apply Real.exp_le_exp.2
    have := (min_le_right (α₁ / 2) (min (α₂ / 2) (α₃ / 2))).trans (min_le_left _ _)
    nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hm3 : Real.exp (-(α₃ / 2) * R) ≤ Real.exp (-min (α₁ / 2) (min (α₂ / 2) (α₃ / 2)) * R) := by
    apply Real.exp_le_exp.2
    have := (min_le_right (α₁ / 2) (min (α₂ / 2) (α₃ / 2))).trans (min_le_right _ _)
    nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hc1 : 0 ≤ 2 * β₁ / α₁ + γ₁ := by positivity
  have hc2 : 0 ≤ 2 * β₂ / α₂ + γ₂ := by positivity
  have hc3 : 0 ≤ 2 * β₃ / α₃ + γ₃ := by positivity
  have hE : 0 ≤ Real.exp (-min (α₁ / 2) (min (α₂ / 2) (α₃ / 2)) * R) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hm1 hc1, mul_le_mul_of_nonneg_left hm2 hc2,
    mul_le_mul_of_nonneg_left hm3 hc3]

/-! ### The layer-cake constant is finite -/

theorem Mconst_le_ofReal {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    Mconst (ENNReal.ofReal (Real.exp (c / 2))) c C ≤
      ENNReal.ofReal (1 + C * Real.exp (-c / 2) / (1 - Real.exp (-c / 2))) := by
  unfold Mconst
  set a := ENNReal.ofReal (Real.exp (c / 2)) with ha
  have hr : Real.exp (-c / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hr0 : 0 ≤ Real.exp (-c / 2) := (Real.exp_pos _).le
  have hterm : ∀ s : ℕ, (a ^ (s + 1) - a ^ s) * ENNReal.ofReal (C * Real.exp (-c * (s + 1))) ≤
      ENNReal.ofReal (C * Real.exp (-c / 2) ^ (s + 1)) := by
    intro s
    calc (a ^ (s + 1) - a ^ s) * ENNReal.ofReal (C * Real.exp (-c * (s + 1)))
        ≤ a ^ (s + 1) * ENNReal.ofReal (C * Real.exp (-c * (s + 1))) := by
          gcongr; exact tsub_le_self
      _ = ENNReal.ofReal (Real.exp (c / 2) ^ (s + 1) * (C * Real.exp (-c * (s + 1)))) := by
          rw [ha, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C * Real.exp (-c / 2) ^ (s + 1)) := by
          congr 1
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
          congr 2
          push_cast; ring
  have hsum : Summable (fun s : ℕ => C * Real.exp (-c / 2) ^ (s + 1)) := by
    simp_rw [pow_succ]
    exact ((summable_geometric_of_lt_one hr0 hr).mul_right _).mul_left C
  calc 1 + ∑' s : ℕ, (a ^ (s + 1) - a ^ s) * ENNReal.ofReal (C * Real.exp (-c * (s + 1)))
      ≤ 1 + ∑' s : ℕ, ENNReal.ofReal (C * Real.exp (-c / 2) ^ (s + 1)) := by
        gcongr; exact hterm _
    _ = 1 + ENNReal.ofReal (∑' s : ℕ, C * Real.exp (-c / 2) ^ (s + 1)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun s => by positivity) hsum]
    _ = ENNReal.ofReal (1 + C * Real.exp (-c / 2) / (1 - Real.exp (-c / 2))) := by
        have htsum : ∑' s : ℕ, C * Real.exp (-c / 2) ^ (s + 1) =
            C * Real.exp (-c / 2) / (1 - Real.exp (-c / 2)) := by
          simp_rw [pow_succ]
          rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
          field_simp
        rw [htsum, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (div_nonneg (by positivity) (by linarith))]

/-! ### The three terms -/

theorem term1_bound {ε : ℝ} {n₀ R : ℕ} (hn₀ge : ε * R ≤ n₀) :
    (4 / 3 : ℝ) * (3 / 4) ^ ((n₀ : ℝ) / 3) ≤
      (0 * R + 4 / 3) * Real.exp (-(ε * Real.log (4 / 3) / 3) * R) := by
  rw [zero_mul, zero_add]
  gcongr
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  have hl : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3) := by
    rw [← Real.log_inv]; norm_num
  rw [hl]
  have hpos := Real.log_pos (show (1 : ℝ) < 4 / 3 by norm_num)
  have := mul_le_mul_of_nonneg_left hn₀ge hpos.le
  nlinarith

theorem half_floor_ge (R : ℕ) : ((R / 2 : ℕ) : ℝ) ≥ ((R : ℝ) - 1) / 2 := by
  have := Nat.div_add_mod R 2
  have h2 : R % 2 ≤ 1 := by omega
  have h3 : (R : ℝ) = 2 * ((R / 2 : ℕ) : ℝ) + ((R % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
  have h4 : ((R % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h2
  linarith

theorem term2_bound {c Q ε : ℝ} (hc : 0 < c) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hεlog : ε * Real.log Q ≤ c / 8) {n₀ R : ℕ} (hn₀le : (n₀ : ℝ) ≤ ε * R + 1) :
    (n₀ : ℝ) * (Q ^ n₀ / Real.exp (c / 2) ^ (R / 2)) ≤
      (ε * Q * Real.exp (c / 4) * R + Q * Real.exp (c / 4)) * Real.exp (-(c / 8) * R) := by
  have hQpos : 0 < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hQn : Q ^ n₀ ≤ Q * Real.exp (c / 8 * R) := by
    calc Q ^ n₀ = Real.exp (n₀ * Real.log Q) := by
          rw [Real.exp_nat_mul, Real.exp_log hQpos]
      _ ≤ Real.exp ((ε * R + 1) * Real.log Q) := by
          apply Real.exp_le_exp.2; exact mul_le_mul_of_nonneg_right hn₀le hlogQ
      _ = Q * Real.exp (ε * R * Real.log Q) := by
          rw [add_mul, one_mul, Real.exp_add, Real.exp_log hQpos, mul_comm]
      _ ≤ Q * Real.exp (c / 8 * R) := by
          apply mul_le_mul_of_nonneg_left _ hQpos.le
          apply Real.exp_le_exp.2
          have key : ε * R * Real.log Q = (ε * Real.log Q) * R := by ring
          rw [key]
          exact mul_le_mul_of_nonneg_right hεlog hR0
  have hden : 1 / Real.exp (c / 2) ^ (R / 2) ≤ Real.exp (c / 4) * Real.exp (-(c / 4) * R) := by
    rw [one_div, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := half_floor_ge R
    have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ c / 2 by linarith)
    nlinarith
  have hE : Real.exp (c / 8 * R) * (Real.exp (c / 4) * Real.exp (-(c / 4) * R)) =
      Real.exp (c / 4) * Real.exp (-(c / 8) * R) := by
    rw [mul_left_comm, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hn₀0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  have hεR : (0 : ℝ) ≤ ε * R + 1 := add_nonneg (mul_nonneg hε hR0) zero_le_one
  have hinv0 : (0 : ℝ) ≤ 1 / Real.exp (c / 2) ^ (R / 2) := by positivity
  calc (n₀ : ℝ) * (Q ^ n₀ / Real.exp (c / 2) ^ (R / 2))
      ≤ (ε * R + 1) * ((Q * Real.exp (c / 8 * R)) * (1 / Real.exp (c / 2) ^ (R / 2))) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul hn₀le (mul_le_mul_of_nonneg_right hQn hinv0)
          (mul_nonneg (pow_nonneg hQpos.le _) hinv0) hεR
    _ ≤ (ε * R + 1) * ((Q * Real.exp (c / 8 * R)) * (Real.exp (c / 4) * Real.exp (-(c / 4) * R))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden
          (mul_nonneg hQpos.le (Real.exp_pos _).le)) hεR
    _ = (ε * Q * Real.exp (c / 4) * R + Q * Real.exp (c / 4)) * Real.exp (-(c / 8) * R) := by
        rw [mul_assoc Q, hE]; ring

theorem term3_bound {c C ε : ℝ} (hc : 0 < c) (hC : 0 < C) (hε : 0 ≤ ε) {n₀ R : ℕ}
    (hn₀le : (n₀ : ℝ) ≤ ε * R + 1) :
    (n₀ : ℝ) * (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) ≤
      (ε * C * R + C) * Real.exp (-(c / 2) * R) := by
  have h1 : ((R - R / 2 : ℕ) : ℝ) ≥ (R : ℝ) / 2 := by
    have h3 : ((R - R / 2 : ℕ) : ℝ) = (R : ℝ) - ((R / 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.div_le_self _ _)]
    have := Nat.div_add_mod R 2
    have h4 : (R : ℝ) = 2 * ((R / 2 : ℕ) : ℝ) + ((R % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
    have h5 : (0 : ℝ) ≤ ((R % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hexp : Real.exp (-c * ((R - R / 2 : ℕ) : ℝ)) ≤ Real.exp (-(c / 2) * R) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left h1 hc.le
    nlinarith
  have hn₀0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  calc (n₀ : ℝ) * (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ)))
      ≤ (ε * R + 1) * (C * Real.exp (-(c / 2) * R)) := by gcongr
    _ = _ := by ring

/-! ### The exponential bound for the reach event -/

theorem reach_le_ofReal (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {c C : ℝ}
    (hC : 0 < C)
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r)))
    {E : ℝ} (hE1 : 1 ≤ E) {Q : ℝ} (hQ1 : 1 ≤ Q)
    (hq : ENNReal.ofReal E * Mconst (ENNReal.ofReal E) c C ≤ ENNReal.ofReal Q)
    (R n₀ : ℕ) (hR : 1 ≤ R) (hn₀ : 1 ≤ n₀) :
    uniformLaw clockwise (ReachEvent f d R) ≤
      ENNReal.ofReal ((4 / 3) * (3 / 4) ^ ((n₀ : ℝ) / 3) +
        n₀ * (Q ^ n₀ / E ^ (R / 2) + C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ)))) := by
  have hEpos : 0 < E := by linarith
  have hQpos : 0 < Q := by linarith
  have ha1 : 1 ≤ ENNReal.ofReal E := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hE1
  have hmain := reachEvent_measure_le f hd hCB ha1 ENNReal.ofReal_ne_top R n₀ hR
  have hK := Rotor.Frozen.square_forced_tests f d hd n₀ hn₀
  have hapow : ENNReal.ofReal E ^ (R / 2) = ENNReal.ofReal (E ^ (R / 2)) :=
    (ENNReal.ofReal_pow hEpos.le _).symm
  have hterm : ∀ j ∈ Finset.range n₀,
      (ENNReal.ofReal E * Mconst (ENNReal.ofReal E) c C) ^ j / ENNReal.ofReal E ^ (R / 2) +
        ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) * uniformLaw clockwise (KEvent f d j) ≤
      ENNReal.ofReal (Q ^ n₀ / E ^ (R / 2) + C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hnn1 : 0 ≤ Q ^ n₀ / E ^ (R / 2) := div_nonneg (pow_nonneg hQpos.le _) (pow_nonneg hEpos.le _)
    have hnn2 : 0 ≤ C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ)) := mul_nonneg hC.le (Real.exp_pos _).le
    rw [ENNReal.ofReal_add hnn1 hnn2]
    gcongr
    · rw [hapow]
      calc (ENNReal.ofReal E * Mconst (ENNReal.ofReal E) c C) ^ j / ENNReal.ofReal (E ^ (R / 2))
          ≤ ENNReal.ofReal Q ^ j / ENNReal.ofReal (E ^ (R / 2)) := by gcongr
        _ = ENNReal.ofReal (Q ^ j / E ^ (R / 2)) := by
            rw [← ENNReal.ofReal_pow hQpos.le, ← ENNReal.ofReal_div_of_pos (pow_pos hEpos _)]
        _ ≤ ENNReal.ofReal (Q ^ n₀ / E ^ (R / 2)) := by
            apply ENNReal.ofReal_le_ofReal
            exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hQ1 hj.le) (pow_nonneg hEpos.le _)
    · calc ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) * uniformLaw clockwise (KEvent f d j)
          ≤ ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) * 1 := by
            gcongr; exact prob_le_one
        _ = _ := mul_one _
  have hsum : ∑ j ∈ Finset.range n₀, ((ENNReal.ofReal E * Mconst (ENNReal.ofReal E) c C) ^ j /
      ENNReal.ofReal E ^ (R / 2) +
      ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) * uniformLaw clockwise (KEvent f d j)) ≤
      ENNReal.ofReal (n₀ * (Q ^ n₀ / E ^ (R / 2) + C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ)))) := by
    calc _ ≤ ∑ j ∈ Finset.range n₀, ENNReal.ofReal (Q ^ n₀ / E ^ (R / 2) +
          C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) := Finset.sum_le_sum hterm
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  refine (hmain.trans (add_le_add hK hsum)).trans ?_
  have hnn1 : 0 ≤ Q ^ n₀ / E ^ (R / 2) := div_nonneg (pow_nonneg hQpos.le _) (pow_nonneg hEpos.le _)
  have hnn2 : 0 ≤ C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ)) := mul_nonneg hC.le (Real.exp_pos _).le
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hnn1 hnn2))]

/-- The reach bound, with constants depending only on those of Lemma 5.3. -/
theorem reach_exp_bound {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r))) :
    ∃ C' c' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ (f d : Site), squareGraph.Adj f (f + d) → ∀ R : ℕ, 1 ≤ R →
      uniformLaw clockwise (ReachEvent f d R) ≤ ENNReal.ofReal (C' * Real.exp (-c' * R)) := by
  have hE1 : 1 ≤ Real.exp (c / 2) := Real.one_le_exp_iff.2 (by linarith)
  have hr : Real.exp (-c / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hMr1 : 1 ≤ 1 + C * Real.exp (-c / 2) / (1 - Real.exp (-c / 2)) := by
    have : 0 ≤ C * Real.exp (-c / 2) / (1 - Real.exp (-c / 2)) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hM := Mconst_le_ofReal hc hC
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Real.exp (c / 2) * (1 + C * Real.exp (-c / 2) / (1 - Real.exp (-c / 2))) :=
    ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; nlinarith
  have hQpos : 0 < Q := by linarith
  have hq : ENNReal.ofReal (Real.exp (c / 2)) * Mconst (ENNReal.ofReal (Real.exp (c / 2))) c C ≤
      ENNReal.ofReal Q := by
    rw [hQdef, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left hM (zero_le _)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = c / (8 * (Real.log Q + 1)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεlog : ε * Real.log Q ≤ c / 8 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨C', c', hc', hC', hbound⟩ := exists_exp_decay_three
    (α₁ := ε * Real.log (4 / 3) / 3) (α₂ := c / 8) (α₃ := c / 2)
    (β₁ := 0) (β₂ := ε * Q * Real.exp (c / 4)) (β₃ := ε * C)
    (γ₁ := 4 / 3) (γ₂ := Q * Real.exp (c / 4)) (γ₃ := C)
    (by have := Real.log_pos (show (1 : ℝ) < 4 / 3 by norm_num); positivity)
    (by positivity) (by positivity) le_rfl (by positivity) (by positivity) (by norm_num)
    (by positivity) hC.le
  refine ⟨C', c', hc', hC', fun f d hd R hR => ?_⟩
  obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : ℕ, n₀ = ⌊ε * R⌋₊ + 1 := ⟨_, rfl⟩
  have hn₀1 : 1 ≤ n₀ := by omega
  have hn₀le : (n₀ : ℝ) ≤ ε * R + 1 := by
    rw [hn₀def]; push_cast
    have := Nat.floor_le (show 0 ≤ ε * R by positivity)
    linarith
  have hn₀ge : ε * R ≤ n₀ := by
    rw [hn₀def]; push_cast
    have := Nat.lt_floor_add_one (ε * R)
    linarith
  refine (reach_le_ofReal f hd hC hCB hE1 hQ1 hq R n₀ hR hn₀1).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have ht1 := term1_bound hn₀ge
  have ht2 := term2_bound hc hQ1 hεpos.le hεlog hn₀le
  have ht3 := term3_bound hc hC hεpos.le hn₀le
  have hb := hbound R
  have hsplit : (n₀ : ℝ) * (Q ^ n₀ / Real.exp (c / 2) ^ (R / 2) + C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) =
      (n₀ : ℝ) * (Q ^ n₀ / Real.exp (c / 2) ^ (R / 2)) +
        (n₀ : ℝ) * (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) := by ring
  rw [hsplit]
  linarith [ht1, ht2, ht3, hb]

end Rotor

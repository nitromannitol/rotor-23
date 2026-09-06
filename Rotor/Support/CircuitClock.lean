/-
Proposition 3.4 (`prop:circuit-clock`, `rotor.tex:1148-1176`): converting circuit number
into time.  Part one, the squeeze `eq:universal-clock-squeeze` and the cubic growth of
`T(n)`.  The paper: "By Lemma 2.1, between times `T(n)` and `T(n+1)` the walk departs
exactly `deg(x)` times from each `x ∈ A_n` and every departure leaves a vertex of
`A_{n+1}`, which is the squeeze; with the second assumed asymptotic, summing gives
`T(n) = βn³/3 + o(n³)`."
-/
import Rotor.Support.Passage
import Rotor.Periodic

open Rotor Filter Topology
open scoped Pointwise

universe u

namespace Rotor

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (ρ : Config G) (o : V)

/-! ### The squeeze -/

/-- Each `x ∈ A_n` departs `deg x` times during the `(n+1)`-st circuit, at distinct times. -/
theorem clock_lower (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (hn1 : T π ρ o (n + 1) < ⊤) :
    ∑ x ∈ A π ρ o n, G.degree x ≤ (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat := by
  classical
  have hdep := (hFLP π hG ρ o n hn).2 hn1
  calc ∑ x ∈ A π ρ o n, G.degree x
      = ∑ x ∈ A π ρ o n, departures π ρ o x (T π ρ o n).toNat (T π ρ o (n + 1)).toNat :=
        Finset.sum_congr rfl (fun x hx => (hdep x hx).symm)
    _ = ((Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).filter
          (fun t => X π ρ o t ∈ A π ρ o n)).card := by
        have H : Set.MapsTo (X π ρ o) (↑((Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).filter
            (fun t => X π ρ o t ∈ A π ρ o n))) (↑(A π ρ o n)) :=
          fun t ht => Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
        rw [Finset.card_eq_sum_card_fiberwise H]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        unfold departures
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hx⟩, h2⟩
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    _ ≤ (Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).card := Finset.card_filter_le _ _
    _ = (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat := Nat.card_Ico _ _

/-- Every step of the `(n+1)`-st circuit traverses a distinct directed edge out of `A_{n+1}`. -/
theorem clock_upper (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (hn1 : T π ρ o (n + 1) < ⊤) :
    (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat ≤ ∑ x ∈ A π ρ o (n + 1), G.degree x := by
  classical
  have hmem : ∀ s ∈ Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat,
      X π ρ o s ∈ A π ρ o (n + 1) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    exact X_mem_R π ρ o s _ hs.2.le
  calc (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat
      = (Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).card := (Nat.card_Ico _ _).symm
    _ ≤ ((A π ρ o (n + 1)).biUnion (fun v => (G.neighborFinset v).image (fun w => (v, w)))).card := by
        refine Finset.card_le_card_of_injOn (fun s => traversal π ρ o s) ?_ ?_
        · intro s hs
          have hs' := hmem s hs
          simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image,
            SimpleGraph.mem_neighborFinset, exists_prop]
          exact ⟨X π ρ o s, hs', X π ρ o (s + 1), adj_X_succ π ρ o s, rfl⟩
        · intro s hs s' hs' heq
          simp only [Finset.coe_Ico, Set.mem_Ico] at hs hs'
          by_contra hne
          have key : ∀ a b : ℕ, a < b → (T π ρ o n).toNat ≤ a → b < (T π ρ o (n + 1)).toNat →
              traversal π ρ o a = traversal π ρ o b → False := by
            intro a b hab ha hb hX
            have h1 : T π ρ o n ≤ (a : ℕ∞) := by
              rw [← coe_toNat_T π ρ o n hn]; exact_mod_cast ha
            have h2 : (b : ℕ∞) < T π ρ o (n + 1) := by
              rw [← coe_toNat_T π ρ o (n + 1) hn1]; exact_mod_cast hb
            exact (hFLP π hG ρ o n hn).1 a b h1 hab h2 hX
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · exact key s s' h hs.1 hs'.2 heq
          · exact key s' s h hs'.1 hs.2 heq.symm
    _ ≤ ∑ v ∈ A π ρ o (n + 1), ((G.neighborFinset v).image (fun w => (v, w))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ A π ρ o (n + 1), G.degree v := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_image_le

/-! ### Cesàro for cubic sums -/

theorem sum_range_sq (n : ℕ) :
    6 * ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sum_range_sq_le (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 / 3 := by
  have h := sum_range_sq n
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    nlinarith

theorem abs_sum_range_sq_sub (n : ℕ) :
    |∑ k ∈ Finset.range n, (k : ℝ) ^ 2 - (n : ℝ) ^ 3 / 3| ≤ (n : ℝ) ^ 2 := by
  have h := sum_range_sq n
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    rw [abs_le]
    constructor <;> nlinarith

/-- Cesàro: if `u k / k² → L` then `(∑_{k<n} u k) / n³ → L / 3`. -/
theorem tendsto_sum_div_cube {u : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun k : ℕ => u k / (k : ℝ) ^ 2) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, u k) / (n : ℝ) ^ 3) atTop (𝓝 (L / 3)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 h (ε / 2) (by positivity)
  obtain ⟨K, hK1, hK⟩ : ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k → |u k - L * (k : ℝ) ^ 2| ≤ ε / 2 * (k : ℝ) ^ 2 := by
    refine ⟨max K₀ 1, le_max_right _ _, fun k hk => ?_⟩
    have hk0 : K₀ ≤ k := le_trans (le_max_left _ _) hk
    have hk1 : (1 : ℕ) ≤ k := le_trans (le_max_right _ _) hk
    have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by
      have : (0 : ℝ) < k := by exact_mod_cast hk1
      positivity
    have := hK₀ k hk0
    rw [Real.dist_eq, div_sub' hkpos.ne', abs_div, abs_of_pos hkpos, div_lt_iff₀ hkpos,
      mul_comm ((k : ℝ) ^ 2) L] at this
    linarith
  -- the contribution of the first `K` terms
  obtain ⟨C₀, hC₀0, hC₀⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ n, K ≤ n → |∑ k ∈ Finset.range n, (u k - L * (k : ℝ) ^ 2)| ≤ C₀ + ε / 2 * (n : ℝ) ^ 3 / 3 := by
    refine ⟨∑ k ∈ Finset.range K, |u k - L * (k : ℝ) ^ 2|, Finset.sum_nonneg (fun _ _ => abs_nonneg _),
      fun n hn => ?_⟩
    rw [← Finset.sum_range_add_sum_Ico _ hn]
    refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
    calc |∑ k ∈ Finset.Ico K n, (u k - L * (k : ℝ) ^ 2)|
        ≤ ∑ k ∈ Finset.Ico K n, |u k - L * (k : ℝ) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico K n, ε / 2 * (k : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun k hk => hK k (Finset.mem_Ico.1 hk).1)
      _ ≤ ∑ k ∈ Finset.range n, ε / 2 * (k : ℝ) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          rw [Finset.mem_Ico] at hk
          exact Finset.mem_range.2 hk.2
      _ = ε / 2 * ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ε / 2 * ((n : ℝ) ^ 3 / 3) := by gcongr; exact sum_range_sq_le n
      _ = ε / 2 * (n : ℝ) ^ 3 / 3 := by ring
  -- the threshold
  obtain ⟨N, hN1, hNK, hN⟩ : ∃ N : ℕ, 1 ≤ N ∧ K ≤ N ∧ C₀ + |L| ≤ ε / 3 * N := by
    refine ⟨max K ⌈(C₀ + |L|) / (ε / 3)⌉₊, le_trans hK1 (le_max_left _ _), le_max_left _ _, ?_⟩
    have h1 : (C₀ + |L|) / (ε / 3) ≤ (max K ⌈(C₀ + |L|) / (ε / 3)⌉₊ : ℕ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hN1 hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.dist_eq]
  -- decompose
  have hdec : (∑ k ∈ Finset.range n, u k) / (n : ℝ) ^ 3 - L / 3 =
      (∑ k ∈ Finset.range n, (u k - L * (k : ℝ) ^ 2)) / (n : ℝ) ^ 3 +
        L * (∑ k ∈ Finset.range n, (k : ℝ) ^ 2 - (n : ℝ) ^ 3 / 3) / (n : ℝ) ^ 3 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp
    ring
  rw [hdec]
  have e1 : |(∑ k ∈ Finset.range n, (u k - L * (k : ℝ) ^ 2)) / (n : ℝ) ^ 3| ≤
      C₀ / (n : ℝ) ^ 3 + ε / 6 := by
    rw [abs_div, abs_of_pos hn3, div_le_iff₀ hn3]
    have := hC₀ n (le_trans hNK hn)
    calc |∑ k ∈ Finset.range n, (u k - L * (k : ℝ) ^ 2)| ≤ C₀ + ε / 2 * (n : ℝ) ^ 3 / 3 := this
      _ = (C₀ / (n : ℝ) ^ 3 + ε / 6) * (n : ℝ) ^ 3 := by field_simp; ring
  have e2 : |L * (∑ k ∈ Finset.range n, (k : ℝ) ^ 2 - (n : ℝ) ^ 3 / 3) / (n : ℝ) ^ 3| ≤
      |L| / n := by
    rw [abs_div, abs_of_pos hn3, abs_mul, div_le_div_iff₀ hn3 hnpos]
    have := abs_sum_range_sq_sub n
    calc |L| * |∑ k ∈ Finset.range n, (k : ℝ) ^ 2 - (n : ℝ) ^ 3 / 3| * n
        ≤ |L| * (n : ℝ) ^ 2 * n := by gcongr
      _ = |L| * (n : ℝ) ^ 3 := by ring
  have e3 : C₀ / (n : ℝ) ^ 3 ≤ C₀ / n := by
    apply div_le_div_of_nonneg_left hC₀0 hnpos
    calc (n : ℝ) = n * 1 * 1 := by ring
      _ ≤ n * n * n := by gcongr
      _ = (n : ℝ) ^ 3 := by ring
  have e4 : C₀ / n + |L| / n ≤ ε / 3 := by
    rw [← add_div, div_le_iff₀ hnpos]
    calc C₀ + |L| ≤ ε / 3 * N := hN
      _ ≤ ε / 3 * n := by gcongr
  calc |(∑ k ∈ Finset.range n, (u k - L * (k : ℝ) ^ 2)) / (n : ℝ) ^ 3 +
        L * (∑ k ∈ Finset.range n, (k : ℝ) ^ 2 - (n : ℝ) ^ 3 / 3) / (n : ℝ) ^ 3|
      ≤ |(∑ k ∈ Finset.range n, (u k - L * (k : ℝ) ^ 2)) / (n : ℝ) ^ 3| +
        |L * (∑ k ∈ Finset.range n, (k : ℝ) ^ 2 - (n : ℝ) ^ 3 / 3) / (n : ℝ) ^ 3| := abs_add_le _ _
    _ ≤ (C₀ / (n : ℝ) ^ 3 + ε / 6) + |L| / n := add_le_add e1 e2
    _ ≤ (C₀ / n + ε / 6) + |L| / n := by linarith
    _ < ε := by linarith

/-! ### Cubic growth of the circuit times -/

/-- `T(n) = Σ_{k<n} (T(k+1) - T(k))`. -/
theorem toNat_T_eq_sum (hT : ∀ n, T π ρ o n < ⊤) (n : ℕ) :
    (T π ρ o n).toNat = ∑ k ∈ Finset.range n, ((T π ρ o (k + 1)).toNat - (T π ρ o k).toNat) := by
  induction n with
  | zero => simp [T_zero']
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have := toNat_T_le π ρ o n (hT (n + 1))
    omega

/-- `T(n)/n³ → β/3` when the degree sums grow like `β n²`. -/
theorem tendsto_T_div_cube (hFLP : External.OneCircuit G) (hG : G.Connected)
    (hT : ∀ n, T π ρ o n < ⊤) {β : ℝ}
    (hβ : Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 β)) :
    Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)) := by
  -- the lower and upper sums
  have hlow : ∀ n, (∑ k ∈ Finset.range n, ((∑ x ∈ A π ρ o k, G.degree x : ℕ) : ℝ)) / (n : ℝ) ^ 3 ≤
      (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3 := by
    intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [toNat_T_eq_sum π ρ o hT n]
    push_cast
    exact Finset.sum_le_sum (fun k _ => by
      exact_mod_cast clock_lower π ρ o hFLP hG k (hT k) (hT (k + 1)))
  have hup : ∀ n, (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤
      (∑ k ∈ Finset.range n, ((∑ x ∈ A π ρ o (k + 1), G.degree x : ℕ) : ℝ)) / (n : ℝ) ^ 3 := by
    intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [toNat_T_eq_sum π ρ o hT n]
    push_cast
    exact Finset.sum_le_sum (fun k _ => by
      exact_mod_cast clock_upper π ρ o hFLP hG k (hT k) (hT (k + 1)))
  have h1 : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, ((∑ x ∈ A π ρ o k, G.degree x : ℕ) : ℝ)) / (n : ℝ) ^ 3) atTop
      (𝓝 (β / 3)) := tendsto_sum_div_cube hβ
  -- the upper sum: shift the index
  have h2 : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, ((∑ x ∈ A π ρ o (k + 1), G.degree x : ℕ) : ℝ)) / (n : ℝ) ^ 3) atTop
      (𝓝 (β / 3)) := by
    have ha : Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range (n + 1), ((∑ x ∈ A π ρ o k, G.degree x : ℕ) : ℝ)) / ((n : ℝ) + 1) ^ 3)
        atTop (𝓝 (β / 3)) := by
      have := h1.comp (tendsto_add_atTop_nat 1)
      refine this.congr (fun n => ?_)
      simp only [Function.comp]
      push_cast
      rfl
    have hb : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / n) ^ 3) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / n) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      have := this.pow 3
      rw [one_pow] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hc : Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o 0, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop
        (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
    have := (ha.mul hb).sub hc
    rw [mul_one, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [Finset.sum_range_succ']
    field_simp
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 hlow hup

/-! ### The circuit index at time `t` -/

theorem T_mono_le (m n : ℕ) (h : m ≤ n) : T π ρ o m ≤ T π ρ o n :=
  monotone_nat_of_le_succ (fun k => T_mono π ρ o k) h

theorem toNat_T_mono (hT : ∀ n, T π ρ o n < ⊤) {m n : ℕ} (h : m ≤ n) :
    (T π ρ o m).toNat ≤ (T π ρ o n).toNat :=
  ENat.toNat_le_toNat (T_mono_le π ρ o m n h) (hT n).ne

/-- `T(n) → ∞` when `T(n)/n³` has a positive limit. -/
theorem tendsto_T_atTop {β : ℝ} (hβ : 0 < β)
    (hTn : Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3))) :
    Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ)) atTop atTop := by
  have hev : ∀ᶠ n : ℕ in atTop, β / 6 * (n : ℝ) ^ 3 ≤ (((T π ρ o n).toNat : ℕ) : ℝ) := by
    filter_upwards [hTn.eventually (eventually_gt_nhds (show β / 6 < β / 3 by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    rw [lt_div_iff₀ this] at hn
    linarith
  exact tendsto_atTop_mono' atTop hev
    (((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity))

theorem exists_idx {β : ℝ} (hβ : 0 < β)
    (hTn : Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)))
    (t : ℕ) : ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat := by
  obtain ⟨n, hn⟩ := ((tendsto_T_atTop π ρ o hβ hTn).eventually (eventually_gt_atTop (t : ℝ))).exists
  have hn' : t < (T π ρ o n).toNat := by exact_mod_cast hn
  rcases n with _ | m
  · rw [T_zero'] at hn'
    simp at hn'
  · exact ⟨m, hn'⟩

/-- The number of circuits completed by time `t`. -/
noncomputable def idx (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) (t : ℕ) : ℕ :=
  Nat.find (hex t)

theorem lt_T_idx_succ (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) (t : ℕ) :
    t < (T π ρ o (idx π ρ o hex t + 1)).toNat := Nat.find_spec (hex t)

theorem T_idx_le (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) (t : ℕ) :
    (T π ρ o (idx π ρ o hex t)).toNat ≤ t := by
  unfold idx
  rcases h : Nat.find (hex t) with _ | m
  · rw [T_zero']; exact Nat.zero_le _
  · have := Nat.find_min (hex t) (show m < Nat.find (hex t) by omega)
    exact not_lt.1 this

theorem idx_tendsto (hT : ∀ n, T π ρ o n < ⊤)
    (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) :
    Tendsto (idx π ρ o hex) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨(T π ρ o N).toNat, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 := lt_T_idx_succ π ρ o hex t
  have h2 : (T π ρ o (idx π ρ o hex t + 1)).toNat ≤ (T π ρ o N).toNat :=
    toNat_T_mono π ρ o hT (by omega)
  omega

theorem A_idx_subset (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) (t : ℕ) :
    A π ρ o (idx π ρ o hex t) ⊆ R π ρ o t :=
  R_mono π ρ o (T_idx_le π ρ o hex t)

theorem subset_A_idx_succ (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) (t : ℕ) :
    R π ρ o t ⊆ A π ρ o (idx π ρ o hex t + 1) :=
  R_mono π ρ o (lt_T_idx_succ π ρ o hex t).le

/-! ### The scaling `n(t) t^{-1/3} → (3/β)^{1/3}` -/

theorem tendsto_idx_div_cbrt (hT : ∀ n, T π ρ o n < ⊤) {β : ℝ} (hβ : 0 < β)
    (hTn : Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)))
    (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) :
    Tendsto (fun t : ℕ => (idx π ρ o hex t : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) atTop
      (𝓝 ((3 / β) ^ (1 / 3 : ℝ))) := by
  have hidx := idx_tendsto π ρ o hT hex
  -- `t / n(t)³ → β / 3`
  have hlow : ∀ᶠ t : ℕ in atTop, (((T π ρ o (idx π ρ o hex t)).toNat : ℕ) : ℝ) / (idx π ρ o hex t : ℝ) ^ 3 ≤
      (t : ℝ) / (idx π ρ o hex t : ℝ) ^ 3 := by
    refine Eventually.of_forall (fun t => ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast T_idx_le π ρ o hex t
  have hup : ∀ᶠ t : ℕ in atTop, (t : ℝ) / (idx π ρ o hex t : ℝ) ^ 3 ≤
      (((T π ρ o (idx π ρ o hex t + 1)).toNat : ℕ) : ℝ) / ((idx π ρ o hex t : ℝ) + 1) ^ 3 *
        (((idx π ρ o hex t : ℝ) + 1) / (idx π ρ o hex t : ℝ)) ^ 3 := by
    filter_upwards [hidx.eventually (eventually_gt_atTop 0)] with t ht
    have hn : (0 : ℝ) < idx π ρ o hex t := by exact_mod_cast ht
    have h1 : (t : ℝ) ≤ ((T π ρ o (idx π ρ o hex t + 1)).toNat : ℕ) := by
      exact_mod_cast (lt_T_idx_succ π ρ o hex t).le
    rw [div_pow, div_mul_div_comm, mul_comm (((idx π ρ o hex t : ℝ) + 1) ^ 3),
      mul_div_mul_right _ _ (by positivity)]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hA : Tendsto (fun t : ℕ => (((T π ρ o (idx π ρ o hex t)).toNat : ℕ) : ℝ) /
      (idx π ρ o hex t : ℝ) ^ 3) atTop (𝓝 (β / 3)) := hTn.comp hidx
  have hB : Tendsto (fun t : ℕ => (((T π ρ o (idx π ρ o hex t + 1)).toNat : ℕ) : ℝ) /
      ((idx π ρ o hex t : ℝ) + 1) ^ 3 * (((idx π ρ o hex t : ℝ) + 1) / (idx π ρ o hex t : ℝ)) ^ 3)
      atTop (𝓝 (β / 3)) := by
    have h1 : Tendsto (fun n : ℕ => (((T π ρ o (n + 1)).toNat : ℕ) : ℝ) / ((n : ℝ) + 1) ^ 3) atTop
        (𝓝 (β / 3)) := by
      have := hTn.comp (tendsto_add_atTop_nat 1)
      refine this.congr (fun n => ?_)
      simp only [Function.comp]
      push_cast
      rfl
    have h2 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / n) ^ 3) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / n) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      have := this.pow 3
      rw [one_pow] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have := (h1.mul h2).comp hidx
    rw [mul_one] at this
    exact this
  have ht3 : Tendsto (fun t : ℕ => (t : ℝ) / (idx π ρ o hex t : ℝ) ^ 3) atTop (𝓝 (β / 3)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hA hB hlow hup
  -- take cube roots and invert
  have hβ3 : (0 : ℝ) < β / 3 := by positivity
  have hroot := ht3.rpow_const (p := (1 / 3 : ℝ)) (Or.inr (by norm_num))
  have hroot' : Tendsto (fun t : ℕ => (t : ℝ) ^ (1 / 3 : ℝ) / (idx π ρ o hex t : ℝ)) atTop
      (𝓝 ((β / 3) ^ (1 / 3 : ℝ))) := by
    refine hroot.congr' ?_
    filter_upwards [hidx.eventually (eventually_gt_atTop 0)] with t ht
    have hn : (0 : ℝ) ≤ idx π ρ o hex t := Nat.cast_nonneg _
    rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity)]
    congr 1
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hn (by norm_num)]
  have hinv := hroot'.inv₀ (by positivity)
  rw [← Real.inv_rpow hβ3.le, inv_div] at hinv
  refine hinv.congr' ?_
  filter_upwards [hidx.eventually (eventually_gt_atTop 0)] with t ht
  rw [inv_div]

/-! ### The range asymptotics -/

theorem tendsto_card_R_div (hT : ∀ n, T π ρ o n < ⊤) {α β : ℝ} (hβ : 0 < β)
    (hαn : Tendsto (fun n : ℕ => ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 α))
    (hTn : Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)))
    (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat) :
    Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop
      (𝓝 (α * (3 / β) ^ (2 / 3 : ℝ))) := by
  have hidx := idx_tendsto π ρ o hT hex
  have hκ := tendsto_idx_div_cbrt π ρ o hT hβ hTn hex
  have hκ' : Tendsto (fun t : ℕ => ((idx π ρ o hex t : ℝ) + 1) / (t : ℝ) ^ (1 / 3 : ℝ)) atTop
      (𝓝 ((3 / β) ^ (1 / 3 : ℝ))) := by
    have h0 : Tendsto (fun t : ℕ => (1 : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop this
    have := hκ.add h0
    rw [add_zero] at this
    refine this.congr (fun t => ?_)
    rw [add_div]
  have hsq : ∀ t : ℕ, (t : ℝ) ^ (2 / 3 : ℝ) = ((t : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := fun t => by
    rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hκ2 : (3 / β) ^ (2 / 3 : ℝ) = ((3 / β) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hκ2]
  -- the two bounds
  have hlow : ∀ᶠ t : ℕ in atTop, ((A π ρ o (idx π ρ o hex t)).card : ℝ) / (idx π ρ o hex t : ℝ) ^ 2 *
      ((idx π ρ o hex t : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) ^ 2 ≤
      ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ) := by
    filter_upwards [hidx.eventually (eventually_gt_atTop 0), eventually_gt_atTop 0] with t ht ht0
    have hn : (0 : ℝ) < idx π ρ o hex t := by exact_mod_cast ht
    have ht' : (0 : ℝ) < (t : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast ht0) _
    rw [hsq, div_pow, div_mul_div_comm, mul_comm ((idx π ρ o hex t : ℝ) ^ 2),
      mul_div_mul_right _ _ (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (A_idx_subset π ρ o hex t)
  have hup : ∀ᶠ t : ℕ in atTop, ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ) ≤
      ((A π ρ o (idx π ρ o hex t + 1)).card : ℝ) / ((idx π ρ o hex t : ℝ) + 1) ^ 2 *
      (((idx π ρ o hex t : ℝ) + 1) / (t : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    filter_upwards [eventually_gt_atTop 0] with t ht0
    have ht' : (0 : ℝ) < (t : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast ht0) _
    rw [hsq, div_pow, div_mul_div_comm, mul_comm (((idx π ρ o hex t : ℝ) + 1) ^ 2),
      mul_div_mul_right _ _ (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (subset_A_idx_succ π ρ o hex t)
  have hA : Tendsto (fun t : ℕ => ((A π ρ o (idx π ρ o hex t)).card : ℝ) / (idx π ρ o hex t : ℝ) ^ 2 *
      ((idx π ρ o hex t : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) ^ 2) atTop (𝓝 (α * ((3 / β) ^ (1 / 3 : ℝ)) ^ 2)) :=
    (hαn.comp hidx).mul (hκ.pow 2)
  have hB : Tendsto (fun t : ℕ => ((A π ρ o (idx π ρ o hex t + 1)).card : ℝ) /
      ((idx π ρ o hex t : ℝ) + 1) ^ 2 * (((idx π ρ o hex t : ℝ) + 1) / (t : ℝ) ^ (1 / 3 : ℝ)) ^ 2) atTop
      (𝓝 (α * ((3 / β) ^ (1 / 3 : ℝ)) ^ 2)) := by
    have h1 : Tendsto (fun n : ℕ => ((A π ρ o (n + 1)).card : ℝ) / ((n : ℝ) + 1) ^ 2) atTop (𝓝 α) := by
      have := hαn.comp (tendsto_add_atTop_nat 1)
      refine this.congr (fun n => ?_)
      simp only [Function.comp]
      push_cast
      rfl
    exact (h1.comp hidx).mul (hκ'.pow 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hA hB hlow hup

/-! ### The Hausdorff limit of the scaled range -/

theorem dist_smul_smul_le (a b : ℝ) (u v : Plane) :
    dist (a • u) (b • v) ≤ |a| * dist u v + |a - b| * ‖v‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖a • u - b • v‖ = ‖a • (u - v) + (a - b) • v‖ := by
        congr 1; rw [smul_sub, sub_smul]; abel
    _ ≤ ‖a • (u - v)‖ + ‖(a - b) • v‖ := norm_add_le _ _
    _ = |a| * ‖u - v‖ + |a - b| * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

theorem tendsto_hausdorff_R (hT : ∀ n, T π ρ o n < ⊤) {β : ℝ} (hβ : 0 < β)
    (hTn : Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)))
    (hex : ∀ t : ℕ, ∃ n : ℕ, t < (T π ρ o (n + 1)).toNat)
    (emb : V → Plane) (B : Set Plane) (hBc : IsCompact B)
    (hB : Tendsto (fun n : ℕ => Metric.hausdorffDist ((n : ℝ)⁻¹ • (emb '' (A π ρ o n : Set V))) B)
      atTop (𝓝 0)) :
    Tendsto (fun t : ℕ => Metric.hausdorffDist
      (((t : ℝ) ^ (-(1 / 3 : ℝ))) • (emb '' (R π ρ o t : Set V))) (((3 / β) ^ (1 / 3 : ℝ)) • B))
      atTop (𝓝 0) := by
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simp only [Set.smul_set_empty, Metric.hausdorffDist_empty]
    exact tendsto_const_nhds
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = (3 / β) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hκ_def]
  have hκ0 : 0 < κ := by rw [hκ_def]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨RB, hRB⟩ := hBc.isBounded.exists_norm_le
  have hRB0 : 0 ≤ RB := le_trans (norm_nonneg _) (hRB _ hBne.some_mem)
  have hidx := idx_tendsto π ρ o hT hex
  have hc := tendsto_idx_div_cbrt π ρ o hT hβ hTn hex
  rw [← hκ_def] at hc
  have hc' : Tendsto (fun t : ℕ => ((idx π ρ o hex t : ℝ) + 1) / (t : ℝ) ^ (1 / 3 : ℝ)) atTop
      (𝓝 κ) := by
    have h0 : Tendsto (fun t : ℕ => (1 : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop this
    have := hc.add h0
    rw [add_zero] at this
    refine this.congr (fun t => ?_)
    rw [add_div]
  have hfin : ∀ n : ℕ, Metric.hausdorffEDist ((n : ℝ)⁻¹ • (emb '' (A π ρ o n : Set V))) B ≠ ⊤ :=
    fun n => Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      ⟨(n : ℝ)⁻¹ • emb o, Set.smul_mem_smul_set (Set.mem_image_of_mem emb (o_mem_A π ρ o n))⟩
      hBne (((A π ρ o n).finite_toSet.image emb).smul_set.isBounded) hBc.isBounded
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨δ', hδ'0, hδ'1, hδ'⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ 1 ∧ δ' * (2 * κ + 2 + RB) < δ := by
    refine ⟨min 1 (δ / (2 * κ + 3 + RB)), by positivity, min_le_left _ _, ?_⟩
    calc min 1 (δ / (2 * κ + 3 + RB)) * (2 * κ + 2 + RB)
        ≤ (δ / (2 * κ + 3 + RB)) * (2 * κ + 2 + RB) := by
          gcongr; exact min_le_right _ _
      _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have hbound : ∀ (a : ℝ) (u v : Plane), |a - κ| < δ' → dist u v < δ' → ‖v‖ ≤ RB →
      dist (a • u) (κ • v) ≤ δ' * (2 * κ + 2 + RB) := by
    intro a u v ha huv hv
    have h1 : |a| ≤ κ + δ' := by
      have := abs_sub_abs_le_abs_sub a κ
      rw [abs_of_pos hκ0] at this
      linarith
    calc dist (a • u) (κ • v) ≤ |a| * dist u v + |a - κ| * ‖v‖ := dist_smul_smul_le _ _ _ _
      _ ≤ (κ + δ') * δ' + δ' * RB := by
          gcongr
      _ ≤ δ' * (2 * κ + 2 + RB) := by nlinarith
  have e1 := (hB.comp hidx).eventually (eventually_lt_nhds hδ'0)
  have e2 := ((hB.comp (tendsto_add_atTop_nat 1)).comp hidx).eventually (eventually_lt_nhds hδ'0)
  have e3 := hc.eventually (Metric.ball_mem_nhds κ hδ'0)
  have e4 := hc'.eventually (Metric.ball_mem_nhds κ hδ'0)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (e1.and (e2.and (e3.and (e4.and (hidx.eventually (eventually_gt_atTop 0))))))
  refine ⟨N + 1, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN t (by omega)
  simp only [Function.comp] at h1 h2
  rw [Real.dist_eq] at h3 h4
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht' : (0 : ℝ) < (t : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hn0 : (0 : ℝ) < idx π ρ o hex t := by exact_mod_cast h5
  have hneg : (t : ℝ) ^ (-(1 / 3 : ℝ)) = ((t : ℝ) ^ (1 / 3 : ℝ))⁻¹ := Real.rpow_neg ht0.le _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
  refine lt_of_le_of_lt (Metric.hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_) hδ'
  · rintro y ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    have hxA : x ∈ A π ρ o (idx π ρ o hex t + 1) := subset_A_idx_succ π ρ o hex t hx
    have hq : ((idx π ρ o hex t : ℝ) + 1)⁻¹ • emb x ∈
        (((idx π ρ o hex t + 1 : ℕ) : ℝ))⁻¹ • (emb '' (A π ρ o (idx π ρ o hex t + 1) : Set V)) := by
      push_cast
      exact Set.smul_mem_smul_set (Set.mem_image_of_mem emb hxA)
    obtain ⟨b, hb, hqb⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hq h2 (hfin _)
    refine ⟨κ • b, Set.smul_mem_smul_set hb, ?_⟩
    have hy : (t : ℝ) ^ (-(1 / 3 : ℝ)) • emb x =
        (((idx π ρ o hex t : ℝ) + 1) / (t : ℝ) ^ (1 / 3 : ℝ)) • (((idx π ρ o hex t : ℝ) + 1)⁻¹ • emb x) := by
      rw [smul_smul, hneg]
      congr 1
      field_simp
    beta_reduce
    rw [hy]
    exact hbound _ _ _ h4 hqb (hRB b hb)
  · rintro z ⟨b, hb, rfl⟩
    obtain ⟨q, hq, hqb⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hb h1 (hfin _)
    obtain ⟨p, ⟨x, hx, rfl⟩, rfl⟩ := hq
    have hqb' : dist ((idx π ρ o hex t : ℝ)⁻¹ • emb x) b < δ' := hqb
    have hxR : x ∈ R π ρ o t := A_idx_subset π ρ o hex t hx
    refine ⟨(t : ℝ) ^ (-(1 / 3 : ℝ)) • emb x,
      Set.smul_mem_smul_set (Set.mem_image_of_mem emb hxR), ?_⟩
    have hy : (t : ℝ) ^ (-(1 / 3 : ℝ)) • emb x =
        ((idx π ρ o hex t : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) • ((idx π ρ o hex t : ℝ)⁻¹ • emb x) := by
      rw [smul_smul, hneg]
      congr 1
      field_simp
    beta_reduce
    rw [dist_comm, hy]
    exact hbound ((idx π ρ o hex t : ℝ) / (t : ℝ) ^ (1 / 3 : ℝ)) ((idx π ρ o hex t : ℝ)⁻¹ • emb x) b
      h3 hqb' (hRB b hb)

/-- Proof of `prop:circuit-clock`. -/
theorem circuit_clock_proof (hFLP : External.OneCircuit G) (hG : G.Connected)
    (hT : ∀ n : ℕ, T π ρ o n < ⊤) :
    (∀ n : ℕ, ∑ x ∈ A π ρ o n, G.degree x ≤ (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat ∧
      (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat ≤ ∑ x ∈ A π ρ o (n + 1), G.degree x) ∧
    (∀ α β : ℝ, 0 < α → 0 < β →
      Tendsto (fun n : ℕ => ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 α) →
      Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 β) →
      Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)) ∧
      Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop
        (𝓝 (α * (3 / β) ^ (2 / 3 : ℝ)))) ∧
    (∀ α β : ℝ, 0 < α → 0 < β →
      Tendsto (fun n : ℕ => ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 α) →
      Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 β) →
      ∀ (emb : V → Plane) (B : Set Plane), IsCompact B →
      Tendsto (fun n : ℕ => Metric.hausdorffDist ((n : ℝ)⁻¹ • (emb '' (A π ρ o n : Set V))) B)
        atTop (𝓝 0) →
      Tendsto (fun t : ℕ => Metric.hausdorffDist
        (((t : ℝ) ^ (-(1 / 3 : ℝ))) • (emb '' (R π ρ o t : Set V))) (((3 / β) ^ (1 / 3 : ℝ)) • B))
        atTop (𝓝 0)) := by
  refine ⟨fun n => ⟨clock_lower π ρ o hFLP hG n (hT n) (hT (n + 1)),
    clock_upper π ρ o hFLP hG n (hT n) (hT (n + 1))⟩, ?_, ?_⟩
  · intro α β _ hβ hαn hβn
    have hTn := tendsto_T_div_cube π ρ o hFLP hG hT hβn
    exact ⟨hTn, tendsto_card_R_div π ρ o hT hβ hαn hTn (exists_idx π ρ o hβ hTn)⟩
  · intro α β _ hβ _ hβn emb B hBc hB
    have hTn := tendsto_T_div_cube π ρ o hFLP hG hT hβn
    exact tendsto_hausdorff_R π ρ o hT hβ hTn (exists_idx π ρ o hβ hTn) emb B hBc hB

end Rotor


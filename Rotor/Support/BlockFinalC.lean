/-
The block estimate, `lem:block-live-paths` (`rotor.tex:1227-1275`), assembled from the
marked block field, its domination, the coarse king paths, and the constants.
-/
import Rotor.Support.BlockAssembly
import Rotor.Support.BlockFinalA
import Rotor.Support.BlockFinalB

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

theorem tvDist_self {α : Type*} [MeasurableSpace α] (μ : Measure α) : tvDist μ μ = 0 := by
  unfold tvDist
  simp

/-- The block event under a perturbed product law, by total variation. -/
theorem blockEvent_tv_bound (ν ν' : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] [∀ v, IsProbabilityMeasure (ν' v)] (L : ℕ) (z : ℤ × ℤ)
    {δ : ℝ} (hδ : ∀ v, tvDist (ν' v) (ν v) ≤ δ) :
    (productLaw ν' (blockEvent π P L z)).toReal ≤
      (productLaw ν (blockEvent π P L z)).toReal + (blockPlusFin P L z).card * δ := by
  have hdet := blockEvent_determined π P L z
  rw [← coe_blockPlusFin P L z] at hdet
  have hB : MeasurableSet ((blockPlusFin P L z).restrict '' blockEvent π P L z) :=
    (Set.toFinite _).measurableSet
  have h := infinitePi_restrict_tv_le ν ν' (blockPlusFin P L z) hB
  rw [hdet.preimage_image] at h
  have h1 := (abs_sub_le_iff.1 h).1
  have h2 : ∑ v ∈ blockPlusFin P L z, tvDist (ν' v) (ν v) ≤ (blockPlusFin P L z).card * δ := by
    have := Finset.sum_le_card_nsmul (blockPlusFin P L z) (fun v => tvDist (ν' v) (ν v)) δ
      (fun v _ => hδ v)
    rwa [nsmul_eq_mul] at this
  unfold productLaw
  linarith

/-- Proof of `lem:block-live-paths`. -/
theorem block_live_paths_proof (hLSS : External.LSS) [Infinite V] (hG : G.Connected) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℕ, 1 ≤ L₀ ∧
      ∀ (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)],
      ∀ L : ℕ, L₀ ≤ L →
        (⨆ z : ℤ × ℤ, productLaw ν (blockEvent π P L z)) < ENNReal.ofReal ε →
        ∃ η : ℝ, 0 < η ∧ Criterion π (productLaw ν) η ∧
          ∃ δ : ℝ, 0 < δ ∧
            ∀ (ν' : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν' v)],
              (∀ v, tvDist (ν' v) (ν v) ≤ δ) → Criterion π (productLaw ν') η := by
  classical
  haveI : Countable V := countable_of_connected hG
  obtain ⟨ε₀, hε₀, hLSS'⟩ := hLSS
  obtain ⟨K, hK0, hK⟩ := P.exists_coord_adj_bound
  refine ⟨ε₀, hε₀, K.toNat + 1, by omega, ?_⟩
  intro ν _ L hL hsup
  have hKL : K < L := by
    have h1 : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK0
    have h2 : (K.toNat : ℤ) + 1 ≤ L := by exact_mod_cast hL
    omega
  have hL0 : 0 < L := by omega
  obtain ⟨c₁, c₂, hc₁, hc₂, hcdist⟩ := exists_blockDist_bound P hG hL0
  -- the block size, independent of the index
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ z, (blockPlusFin P L z).card = M := by
    refine ⟨(blockPlusFin P L 0).card, fun z => ?_⟩
    simp only [blockPlusFin]
    rw [← Set.ncard_eq_toFinset_card _ (P.blockPlus_finite L z),
      ← Set.ncard_eq_toFinset_card _ (P.blockPlus_finite L 0)]
    exact P.ncard_blockPlus hL0 z
  -- the margin below `ε₀`
  have ha_ne : (⨆ z : ℤ × ℤ, productLaw ν (blockEvent π P L z)) ≠ ⊤ := ne_top_of_lt hsup
  have ha_lt : (⨆ z : ℤ × ℤ, productLaw ν (blockEvent π P L z)).toReal < ε₀ :=
    ENNReal.toReal_lt_of_lt_ofReal hsup
  obtain ⟨ε₁, hε₁0, hε₁, hPz⟩ : ∃ ε₁ : ℝ, 0 ≤ ε₁ ∧ ε₁ < ε₀ ∧
      ∀ z, (productLaw ν (blockEvent π P L z)).toReal ≤ ε₁ :=
    ⟨_, ENNReal.toReal_nonneg, ha_lt, fun z => ENNReal.toReal_mono ha_ne
      (le_iSup (fun z => productLaw ν (blockEvent π P L z)) z)⟩
  -- the marking probability and the perturbation size
  obtain ⟨d, hd0, hd1, hdM⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ 2 * M * d ≤ (ε₀ - ε₁) / 2 := by
    refine ⟨min (1 / 2) ((ε₀ - ε₁) / (4 * M + 4)), lt_min (by norm_num) (by
      apply div_pos <;> [linarith; positivity]), min_le_left _ _, ?_⟩
    have h1 : min (1 / 2) ((ε₀ - ε₁) / (4 * M + 4)) ≤ (ε₀ - ε₁) / (4 * M + 4) := min_le_right _ _
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    calc 2 * M * min (1 / 2) ((ε₀ - ε₁) / (4 * M + 4))
        ≤ 2 * M * ((ε₀ - ε₁) / (4 * M + 4)) := by gcongr
      _ ≤ (ε₀ - ε₁) / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  let s : NNReal := ⟨d, hd0.le⟩
  have hs : s ≤ 1 := by
    show d ≤ 1
    linarith
  have hs0 : (0 : ℝ) < s := hd0
  have hs1 : (s : ℝ) < 1 := by
    show d < 1
    linarith
  have hsne : (s : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 hd0.ne')
  have hsd : (s : ℝ≥0∞) = ENNReal.ofReal d := (ENNReal.ofReal_coe_nnreal).symm
  obtain ⟨η, hη, hq⟩ := exists_eta hs0 hs1 hc₁
  -- the one-site bound for every product law within `d`
  have hsite : ∀ (ν' : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν' v)],
      (∀ v, tvDist (ν' v) (ν v) ≤ d) →
      ∀ z, mLaw ν' s hs (markedBlockEvent π P L z) ≤ ENNReal.ofReal (2 * ε₀) := by
    intro ν' _ hν' z
    have h1 := mLaw_markedBlockEvent_le π P L ν' s hs z
    have h2 := blockEvent_tv_bound π P ν ν' L z hν'
    rw [hM] at h1 h2
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h3 : productLaw ν' (blockEvent π P L z) ≤ ENNReal.ofReal (ε₁ + M * d) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (productLaw ν') _)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hPz z])
    have h4 : ((M : ℕ) : ℝ≥0∞) * (s : ℝ≥0∞) = ENNReal.ofReal (M * d) := by
      rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_natCast, ← hsd]
    calc mLaw ν' s hs (markedBlockEvent π P L z)
        ≤ productLaw ν' (blockEvent π P L z) + (M : ℝ≥0∞) * (s : ℝ≥0∞) := h1
      _ ≤ ENNReal.ofReal (ε₁ + M * d) + ENNReal.ofReal (M * d) := by
          rw [h4]; exact add_le_add h3 le_rfl
      _ = ENNReal.ofReal (ε₁ + M * d + M * d) := by
          rw [ENNReal.ofReal_add (p := ε₁ + M * d) (q := M * d) (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (2 * ε₀) := ENNReal.ofReal_le_ofReal (by linarith)
  -- the criterion for every product law within `d`
  have key : ∀ (ν' : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν' v)],
      (∀ v, tvDist (ν' v) (ν v) ≤ d) → Criterion π (productLaw ν') η := by
    intro ν' _ hν'
    have hsite' := hsite ν' hν'
    refine criterion_of_bound π (productLaw ν') η
      (fun R => ENNReal.ofReal ((7 / 8 : ℝ) ^ (⌊c₁ * R - c₂⌋₊ - 10) * (1 / (s : ℝ)) ^ ⌈η * R⌉₊))
      ?_ ?_
    · filter_upwards [eventually_ge_atTop ⌈(c₂ + 11) / c₁⌉₊] with R hR
      intro e
      have hR' : (c₂ + 11) / c₁ ≤ R := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      rw [div_le_iff₀ hc₁] at hR'
      have hfl : 10 ≤ ⌊c₁ * R - c₂⌋₊ := Nat.le_floor (by push_cast; linarith)
      have hm₀ : ∀ w : V, G.dist e.fst w = R →
          ((⌊c₁ * R - c₂⌋₊ - 10 : ℕ) : ℤ) + 10 ≤
            linf (P.blockIndex L w - P.blockIndex L e.fst) + 1 := by
        intro w hw
        have h1 := hcdist e.fst w
        rw [hw] at h1
        have h2 : (⌊c₁ * R - c₂⌋₊ : ℝ) ≤ linf (P.blockIndex L w - P.blockIndex L e.fst) :=
          (Nat.floor_le (by linarith)).trans h1
        have h3 : (⌊c₁ * R - c₂⌋₊ : ℤ) ≤ linf (P.blockIndex L w - P.blockIndex L e.fst) := by
          exact_mod_cast h2
        rw [Nat.cast_sub hfl]
        push_cast
        omega
      have hge := mLaw_coverEvent_ge π ν' s hs η e.fst e.snd R
      have hle := mLaw_coverEvent_le π P hK hKL hL0 ν' s hs hLSS' hsite' η e.fst e.snd R
        (⌊c₁ * R - c₂⌋₊ - 10) hm₀
      have hs_ne : ((s : ℝ≥0∞) ^ ⌈η * R⌉₊) ≠ 0 := pow_ne_zero _ hsne
      have hs_top : ((s : ℝ≥0∞) ^ ⌈η * R⌉₊) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
      have hdiv : productLaw ν' (almostLiveEvent π η e.fst e.snd R) ≤
          (7 / 8 : ℝ≥0∞) ^ (⌊c₁ * R - c₂⌋₊ - 10) / (s : ℝ≥0∞) ^ ⌈η * R⌉₊ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hs_ne) (Or.inl hs_top), mul_comm]
        exact hge.trans hle
      refine hdiv.trans (le_of_eq ?_)
      have h78 : (7 / 8 : ℝ≥0∞) = ENNReal.ofReal (7 / 8) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by positivity), one_div, ENNReal.ofReal_inv_of_pos hs0,
        ENNReal.ofReal_coe_nnreal, ← ENNReal.inv_pow, div_eq_mul_inv, h78]
    · have := tendsto_geom_bound (c₂ := c₂) hs0 hs1.le hc₁ hη.le hq
      simpa using ENNReal.tendsto_ofReal this
  exact ⟨η, hη, key ν (fun v => by rw [tvDist_self]; exact hd0.le), d, hd0, key⟩

end Rotor

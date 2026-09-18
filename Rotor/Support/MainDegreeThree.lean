import Rotor.Support.BlockReach
import Rotor.Support.MainShape
import Rotor.Support.ProductErgodic
import Rotor.Frozen.Shape.BlockLivePaths
import Rotor.Frozen.Shape.PathReduction
import Rotor.Frozen.DegreeThree.Passage

/-!
Theorem 1.1 and Proposition 1.2 in the degree-three case (`rotor.tex:1490-1508`):
`prop:degree-three-passage` verifies `eq:block-crossing-hypothesis` for large `L`,
`lem:block-live-paths` gives `eq:criterion-path-hypothesis`, the uniform product law is
invariant and ergodic, and `prop:path-reduction` gives the conclusions.
-/

open Filter Topology MeasureTheory
open scoped Pointwise ENNReal

universe u

namespace Rotor

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

/-- `(3x+1)² e^{-ax} → 0` along the integers. -/
theorem tendsto_sq_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℕ => ((3 * (L : ℝ) + 1) ^ 2) * Real.exp (-(a * L))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℕ => a * (L : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h1
  have h3 : Tendsto (fun L : ℕ => (16 / a ^ 2) * ((a * (L : ℝ)) ^ 2 * Real.exp (-(a * L))))
      atTop (𝓝 0) := by
    simpa using h2.const_mul (16 / a ^ 2)
  refine squeeze_zero' (Eventually.of_forall (fun L => by positivity)) ?_ h3
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hexp : 0 < Real.exp (-(a * L)) := Real.exp_pos _
  have hsq : (3 * (L : ℝ) + 1) ^ 2 ≤ 16 * (L : ℝ) ^ 2 := by nlinarith
  calc (3 * (L : ℝ) + 1) ^ 2 * Real.exp (-(a * L))
      ≤ 16 * (L : ℝ) ^ 2 * Real.exp (-(a * L)) := by gcongr
    _ = (16 / a ^ 2) * ((a * (L : ℝ)) ^ 2 * Real.exp (-(a * L))) := by
        field_simp

/-- For large `L`, the block events are uniformly small (`eq:block-crossing-hypothesis`). -/
theorem exists_block_small (hG : G.Connected) {D : ℕ} (hD : ∀ v : V, G.degree v ≤ D)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hpass : ∀ (u v : V), G.Adj u v → ∀ R : ℕ, 1 ≤ R →
      uniformLaw π (liveReachEvent π u v R) ≤ ENNReal.ofReal (C * Real.exp (-c * R)))
    {ε : ℝ} (hε : 0 < ε) (L₀ : ℕ) :
    ∃ L : ℕ, L₀ ≤ L ∧ 0 < L ∧
      (⨆ z : ℤ × ℤ, uniformLaw π (blockEvent π P L z)) < ENNReal.ofReal ε := by
  obtain ⟨K, hK0, hK⟩ := P.exists_coord_adj_bound
  obtain ⟨Q, hQ⟩ := P.finite_orbits.exists_finset_coe
  set k : ℕ := K.toNat + 1 with hk
  have hkK : (k : ℤ) = K + 1 := by rw [hk]; push_cast; rw [Int.toNat_of_nonneg hK0]
  have hkpos : (0 : ℝ) < k := by positivity
  set a : ℝ := c / k with ha
  have ha0 : 0 < a := by positivity
  -- the real bound
  set M : ℝ := D * Q.card * C * Real.exp c with hM
  have hlim := (tendsto_sq_mul_exp_neg ha0).const_mul M
  rw [mul_zero] at hlim
  obtain ⟨L₁, hL₁⟩ := (Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε)))
  refine ⟨max (max L₀ L₁) k, le_trans (le_max_left _ _) (le_max_left _ _), by
    have := le_max_right (max L₀ L₁) k; omega, ?_⟩
  set L := max (max L₀ L₁) k with hLdef
  have hLk : k ≤ L := le_max_right _ _
  have hLpos : 0 < L := by omega
  have hL₁' : L₁ ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  set R : ℕ := L / k with hR
  have hR1 : 1 ≤ R := Nat.div_pos hLk (by omega)
  have hRK : (R : ℤ) * (K + 1) ≤ L := by
    rw [← hkK]; exact_mod_cast Nat.div_mul_le_self L k
  -- R ≥ L/k - 1 as reals
  have hRreal : (L : ℝ) / k - 1 ≤ R := by
    have h1 := Nat.div_add_mod L k
    have h2 := Nat.mod_lt L (by omega : 0 < k)
    rw [← hR] at h1
    have h3 : (L : ℝ) < k * R + k := by
      have : L < k * R + k := by omega
      exact_mod_cast this
    rw [div_sub_one hkpos.ne', div_le_iff₀ hkpos]
    linarith
  have hexp : Real.exp (-c * R) ≤ Real.exp c * Real.exp (-(a * L)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [ha]
    have : c * ((L : ℝ) / k - 1) ≤ c * R := mul_le_mul_of_nonneg_left hRreal hc.le
    have e : c * ((L : ℝ) / k - 1) = c / k * L - c := by ring
    linarith
  refine lt_of_le_of_lt (iSup_le (fun z => ?_)) (ENNReal.ofReal_lt_ofReal_iff hε |>.2 (hL₁ L hL₁'))
  calc uniformLaw π (blockEvent π P L z)
      ≤ ((P.blockPlus L 0).ncard * D : ENNReal) * ENNReal.ofReal (C * Real.exp (-c * R)) :=
        uniformLaw_blockEvent_le P π hG hK0 hK hLpos z hRK hD _ (fun u v huv => hpass u v huv R hR1)
    _ ≤ (((3 * L + 1) ^ 2 * Q.card : ℕ) * D : ENNReal) *
          ENNReal.ofReal (C * Real.exp (-c * R)) := by
        gcongr
        exact_mod_cast ncard_blockPlus_zero_le P hLpos hQ
    _ = ENNReal.ofReal ((((3 * L + 1) ^ 2 * Q.card * D : ℕ) : ℝ) * (C * Real.exp (-c * R))) := by
        rw [← Nat.cast_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (M * ((3 * (L : ℝ) + 1) ^ 2 * Real.exp (-(a * L)))) := by
        apply ENNReal.ofReal_le_ofReal
        push_cast
        rw [hM]
        have hq : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
        have hsq : (0 : ℝ) ≤ (3 * (L : ℝ) + 1) ^ 2 := by positivity
        calc (3 * (L : ℝ) + 1) ^ 2 * Q.card * D * (C * Real.exp (-c * R))
            ≤ (3 * (L : ℝ) + 1) ^ 2 * Q.card * D * (C * (Real.exp c * Real.exp (-(a * L)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC.le) (by positivity)
          _ = D * Q.card * C * Real.exp c * ((3 * (L : ℝ) + 1) ^ 2 * Real.exp (-(a * L))) := by
              ring

/-- Theorem 1.1, degree-three case. -/
theorem main_degree_three_proof (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) (hLSS : External.LSS)
    [Infinite V] (hG : G.Connected) (hπ : P.Periodic π) (h3 : ∀ v : V, G.degree v ≤ 3) (o : V) :
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
  obtain ⟨ε, hε, L₀, hL₀, hblock⟩ := Rotor.Frozen.block_live_paths hLSS P π hG
  obtain ⟨c₀, C₀, hc₀, hC₀, hpass⟩ := Rotor.Frozen.degree_three_passage P π hG h3
  obtain ⟨L, hLL₀, hLpos, hsmall⟩ := exists_block_small π P hG h3 hc₀ hC₀ hpass hε L₀
  obtain ⟨η, hη, hcrit, -⟩ := hblock (uniformAt π) L hLL₀ hsmall
  obtain ⟨hrec, -, -⟩ := Rotor.Frozen.path_reduction hFLP hAb hHP hK π hG ⟨3, h3⟩
    (uniformLaw π) η hη hcrit
  obtain ⟨B, hBc, hBconv, hB0, κ, c, hκ, hc, hae⟩ := shape_sandwich_proof π P hFLP hAb hHP hK hG
    ⟨3, h3⟩ (uniformLaw π) η hη hcrit hπ (P.uniformLaw_invariant π) (P.uniformLaw_ergodic π) o
  refine ⟨B, hBc, hBconv, hB0, κ, c, hκ, hc, ?_⟩
  filter_upwards [hrec, hae] with ρ h1 h2
  exact ⟨h1.2 o, h2⟩

/-- Proposition 1.2, degree-three case. -/
theorem perturbations_degree_three_proof (hFLP : External.OneCircuit G)
    (hAb : External.Abelian G) (hHP : External.VisitsAllOfVisitsOne G)
    (hK : External.Kingman.{u}) (hLSS : External.LSS) [Infinite V] (hG : G.Connected)
    (hπ : P.Periodic π) (h3 : ∀ v : V, G.degree v ≤ 3) :
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
  obtain ⟨ε, hε, L₀, hL₀, hblock⟩ := Rotor.Frozen.block_live_paths hLSS P π hG
  obtain ⟨c₀, C₀, hc₀, hC₀, hpass⟩ := Rotor.Frozen.degree_three_passage P π hG h3
  obtain ⟨L, hLL₀, hLpos, hsmall⟩ := exists_block_small π P hG h3 hc₀ hC₀ hpass hε L₀
  obtain ⟨η, hη, -, δ, hδ, hpert⟩ := hblock (uniformAt π) L hLL₀ hsmall
  refine ⟨δ, hδ, fun ν _ hν => ?_⟩
  have hcrit : Criterion π (productLaw ν) η := hpert ν (fun v => (hν v).le)
  obtain ⟨hrec, -, -⟩ := Rotor.Frozen.path_reduction hFLP hAb hHP hK π hG ⟨3, h3⟩
    (productLaw ν) η hη hcrit
  refine ⟨fun o => by filter_upwards [hrec] with ρ h; exact h.2 o, fun hinv o => ?_⟩
  exact shape_sandwich_proof π P hFLP hAb hHP hK hG ⟨3, h3⟩ (productLaw ν) η hη hcrit hπ
    (P.productLaw_invariant ν hinv) (P.productLaw_ergodic (P.productLaw_invariant ν hinv)) o

end Rotor

import Rotor.Support.GridModel
import Rotor.Support.Assembly53
import Rotor.External.SubcriticalDecay

open Finset Classical MeasureTheory ENNReal

namespace Rotor

section Final

variable (x y : Site) (r : ℕ)

/-- Pattern-free configurations belong to the marked event, whatever the marks. -/
theorem pf_subset_gEvent :
    {ω : GIdx x y r → Bool | (fun b => ω (Sum.inl b)) ∈
      {ξ | extF (Fset x y r) ξ ∈ PFEvent x y r}} ⊆ GEvent x y r := by
  rintro ω ⟨l, hl, hh, hlast, hD, hp⟩
  exact ⟨l, hl, hh, hlast, hD, fun z hz hT => absurd (containsPattern_of_traverses hT) hp⟩

/-- The marked event is contained in the connection event. -/
theorem gEvent_subset_conn :
    GEvent x y r ⊆ {ω : GIdx x y r → Bool | (fun b => ω (Sum.inl b)) ∈
      {ξ | extF (Fset x y r) ξ ∈ ConnEvent x y r}} := by
  rintro ω ⟨l, hl, hh, hlast, hD, -⟩
  exact ⟨l, hl, hh, hlast, hD⟩

/-- Pattern-free connection at `1/2` is dominated by connection at `1/2 - ε`. -/
theorem pf_le_conn {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hεK : ε * 2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100 ≤ 1)
    (p : NNReal) (hp : p ≤ 1) (hpε : (p : ℝ) = 1 / 2 - ε) :
    (bondLaw (1 / 2) half_le_one (PFEvent x y r)).toReal ≤
      (bondLaw p hp (ConnEvent x y r)).toReal := by
  rw [bondLaw_toReal_eq_fpr _ _ _ (pfEvent_determined x y r),
    bondLaw_toReal_eq_fpr _ _ _ (connEvent_determined x y r)]
  have hc : (fun _ : ↥(Fset x y r) => ((1 / 2 : NNReal) : ℝ)) = fun _ => (1 / 2 : ℝ) := by
    funext _; push_cast; ring
  have hp' : (fun _ : ↥(Fset x y r) => (p : ℝ)) = fun _ => (1 / 2 - ε : ℝ) := by
    funext _; rw [hpε]
  rw [hc, hp']
  have h1 := fpr_mono (gridPar_isParam x y r hε.le hε' ∅) (pf_subset_gEvent x y r)
  rw [fpr_inl, gridPar_empty] at h1
  simp only [Sum.elim_inl] at h1
  have h2 := fpr_mono (gridPar_isParam x y r hε.le hε' (Zset r)) (gEvent_subset_conn x y r)
  rw [fpr_inl, gridPar_full] at h2
  simp only [Sum.elim_inl] at h2
  have h3 := gridPar_mono x y r hε hε' hεK (Zset r) subset_rfl
  rw [gridPar_empty, gridPar_full] at h3
  exact h1.trans (h3.trans h2)

theorem bondLaw_pf_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hεK : ε * 2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100 ≤ 1)
    (p : NNReal) (hp : p ≤ 1) (hpε : (p : ℝ) = 1 / 2 - ε) {B : ℝ} (hB : 0 ≤ B)
    (hbox : bondLaw p hp (boxCrossing x r) ≤ ENNReal.ofReal B) (hy : linfDist y x = r) :
    bondLaw (1 / 2) half_le_one (PFEvent x y r) ≤ ENNReal.ofReal B := by
  have h1 := pf_le_conn x y r hε hε' hεK p hp hpε
  have h2 : (bondLaw p hp (ConnEvent x y r)).toReal ≤ (bondLaw p hp (boxCrossing x r)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (connEvent_subset_boxCrossing hy))
  have h3 : (bondLaw p hp (boxCrossing x r)).toReal ≤ B := ENNReal.toReal_le_of_le_ofReal hB hbox
  rw [← ENNReal.ofReal_toReal (measure_ne_top (bondLaw (1 / 2) half_le_one) (PFEvent x y r))]
  exact ENNReal.ofReal_le_ofReal (h1.trans (h2.trans h3))

end Final

/-- Lemma 5.3 (`lem:square-constrained-bonds`), modulo the assumed subcritical decay
`External.SubcriticalDecay` at `1/2 - ε` (ruling X-001). -/
theorem square_constrained_bonds_proof (hSub : External.SubcriticalDecay) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) Rotor.half_le_one (constrainedCrossing x r) ≤
        ENNReal.ofReal (C * Real.exp (-c * r)) := by
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = 1 / (2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hε' : ε ≤ 1 / 4 := by rw [hε_def]; norm_num
  have hεK : ε * 2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100 ≤ 1 := by rw [hε_def]; norm_num
  obtain ⟨p, hpε⟩ : ∃ p : NNReal, (p : ℝ) = 1 / 2 - ε := ⟨⟨1 / 2 - ε, by linarith⟩, rfl⟩
  have hp : p ≤ 1 := by rw [← NNReal.coe_le_coe, hpε, NNReal.coe_one]; linarith
  have hplt : p < 1 / 2 := by
    rw [← NNReal.coe_lt_coe, hpε]; push_cast; linarith
  obtain ⟨c, C, hc, hC, hbox⟩ := hSub p hp hplt
  refine ⟨c / 2, 144 * C / c ^ 2, by positivity, by positivity, ?_⟩
  intro x r hr
  calc bondLaw (1 / 2) half_le_one (constrainedCrossing x r)
      ≤ bondLaw (1 / 2) half_le_one (⋃ y ∈ sphere x r, PFEvent x y r) :=
        measure_mono (constrainedCrossing_subset x r)
    _ ≤ ∑ y ∈ sphere x r, bondLaw (1 / 2) half_le_one (PFEvent x y r) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ y ∈ sphere x r, ENNReal.ofReal (C * Real.exp (-c * r)) := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        exact bondLaw_pf_le x y r hε hε' hεK p hp hpε (by positivity) (hbox x r hr)
          (mem_sphere.1 hy)
    _ = (sphere x r).card * ENNReal.ofReal (C * Real.exp (-c * r)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((2 * r + 1) ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * r)) := by
        gcongr
        exact_mod_cast card_sphere_le x r
    _ = ENNReal.ofReal ((((2 * r + 1) ^ 2 : ℕ) : ℝ) * (C * Real.exp (-c * r))) := by
        rw [ENNReal.ofReal_mul (p := (((2 * r + 1) ^ 2 : ℕ) : ℝ)) (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (144 * C / c ^ 2 * Real.exp (-(c / 2) * r)) :=
        ENNReal.ofReal_le_ofReal (poly_exp_bound hc hC r hr)

end Rotor

import Rotor.Support.ExplProb
import Rotor.Dual

/-!
Proposition 5.1 (`prop:square-passage`), part 2: Bernoulli(1/2) bond percolation on finitely
many bonds.  Events determined by a finite set of bonds are counted uniformly over the
configurations of those bonds; flipping a bond open does not decrease the probability of an
increasing event.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-- The configurations agreeing with `ξ` on the bonds `F`. -/
def cylBonds (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) : Set BondConfig :=
  {ω | ∀ b ∈ F, ω b = ξ b}

theorem measurableSet_cylBonds (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) :
    MeasurableSet (cylBonds F ξ) := by
  have : cylBonds F ξ = ⋂ b ∈ F, (fun ω : BondConfig => ω b) ⁻¹' {ξ b} := by
    ext ω; simp [cylBonds]
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet F)
    (fun b _ => measurable_pi_apply b MeasurableSet.of_discrete)

set_option linter.deprecated false in
theorem bondLaw_half_cyl (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) :
    bondLaw (1 / 2) half_le_one (cylBonds F ξ) = (1 / 2 : ℝ≥0∞) ^ F.card := by
  have hset : cylBonds F ξ = Set.pi (↑F) (fun b => {ξ b}) := by
    ext ω; simp [cylBonds, Set.pi]
  rw [hset]
  unfold bondLaw
  have key := Measure.infinitePi_pi (μ := fun _ : Sym2 Site => External.bernoulli (1 / 2) half_le_one)
    (s := F) (t := fun b => {ξ b}) (fun _ _ => MeasurableSet.of_discrete)
  refine key.trans ?_
  have hb : ∀ b, External.bernoulli (1 / 2) half_le_one {ξ b} = 1 / 2 := by
    intro b
    unfold External.bernoulli
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete), PMF.bernoulli_apply]
    rcases ξ b with _ | _ <;> simp
  simp only [hb, Finset.prod_const]

/-- `E` depends only on the bonds in `F`. -/
def BondDetermined (F : Finset (Sym2 Site)) (E : Set BondConfig) : Prop :=
  ∀ ω ω' : BondConfig, (∀ b ∈ F, ω b = ω' b) → (ω ∈ E ↔ ω' ∈ E)

/-- The configuration on `F` given by `ξ`, closed elsewhere. -/
def extF (F : Finset (Sym2 Site)) (ξ : ↥F → Bool) : BondConfig :=
  fun b => if h : b ∈ F then ξ ⟨b, h⟩ else false

/-- The restriction of `ω` to `F`. -/
def resF (F : Finset (Sym2 Site)) (ω : BondConfig) : ↥F → Bool := fun b => ω b.1

theorem mem_cylBonds_extF (F : Finset (Sym2 Site)) (ξ : ↥F → Bool) (ω : BondConfig) :
    ω ∈ cylBonds F (extF F ξ) ↔ resF F ω = ξ := by
  constructor
  · intro h
    funext b
    have := h b.1 b.2
    simp only [extF, b.2, dite_true] at this
    exact this
  · intro h b hb
    rw [← h]
    simp [extF, hb, resF]

theorem cylBonds_extF_disjoint (F : Finset (Sym2 Site)) {ξ ξ' : ↥F → Bool} (h : ξ ≠ ξ') :
    Disjoint (cylBonds F (extF F ξ)) (cylBonds F (extF F ξ')) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  rw [mem_cylBonds_extF] at h1 h2
  exact h (h1.symm.trans h2)

theorem determined_inter_cyl (F : Finset (Sym2 Site)) {E : Set BondConfig} (hE : BondDetermined F E)
    (ξ : ↥F → Bool) :
    E ∩ cylBonds F (extF F ξ) = if extF F ξ ∈ E then cylBonds F (extF F ξ) else ∅ := by
  ext ω
  split_ifs with hξ
  · simp only [Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hω
    exact (hE _ _ (fun b hb => (hω b hb).symm)).1 hξ
  · simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hω hcyl
    exact hξ ((hE _ _ (fun b hb => hcyl b hb)).1 hω)

theorem iUnion_cylBonds_extF (F : Finset (Sym2 Site)) :
    ⋃ ξ : ↥F → Bool, cylBonds F (extF F ξ) = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨resF F ω, by rw [mem_cylBonds_extF]⟩

theorem measurableSet_of_determined (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) : MeasurableSet E := by
  have : E = ⋃ ξ : ↥F → Bool, (E ∩ cylBonds F (extF F ξ)) := by
    rw [← Set.inter_iUnion, iUnion_cylBonds_extF, Set.inter_univ]
  rw [this]
  refine MeasurableSet.iUnion (fun ξ => ?_)
  rw [determined_inter_cyl F hE]
  split_ifs
  · exact measurableSet_cylBonds F _
  · exact MeasurableSet.empty

/-- Bernoulli(1/2) of an `F`-determined event counts its configurations on `F`. -/
theorem bondLaw_half_eq_sum (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) :
    bondLaw (1 / 2) half_le_one E =
      ∑ ξ : ↥F → Bool, if extF F ξ ∈ E then (1 / 2 : ℝ≥0∞) ^ F.card else 0 := by
  classical
  have hunion : E = ⋃ ξ : ↥F → Bool, (E ∩ cylBonds F (extF F ξ)) := by
    rw [← Set.inter_iUnion, iUnion_cylBonds_extF, Set.inter_univ]
  conv_lhs => rw [hunion]
  rw [measure_iUnion (fun ξ ξ' hne => Set.disjoint_of_subset Set.inter_subset_right
      Set.inter_subset_right (cylBonds_extF_disjoint F hne))
    (fun ξ => (measurableSet_of_determined F hE).inter (measurableSet_cylBonds F _))]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [determined_inter_cyl F hE]
  split_ifs
  · exact bondLaw_half_cyl F _
  · exact measure_empty

/-- Flipping the bond `b` open: if it maps `E₁ ⊆ {b closed}` into `E₂`, then
`μ E₁ ≤ μ E₂` (both determined by `F ∋ b`). -/
theorem bondLaw_half_le_of_flip (F : Finset (Sym2 Site)) {E₁ E₂ : Set BondConfig}
    (h₁ : BondDetermined F E₁) (h₂ : BondDetermined F E₂) {b : Sym2 Site} (hb : b ∈ F)
    (hclosed : ∀ ω ∈ E₁, ω b = false) (hflip : ∀ ω ∈ E₁, Function.update ω b true ∈ E₂) :
    bondLaw (1 / 2) half_le_one E₁ ≤ bondLaw (1 / 2) half_le_one E₂ := by
  classical
  rw [bondLaw_half_eq_sum F h₁, bondLaw_half_eq_sum F h₂]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  refine (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))).2
    (Nat.cast_le.2 ?_)
  -- the injection `ξ ↦ ξ[b := true]`
  refine Finset.card_le_card_of_injOn (fun ξ : ↥F → Bool => Function.update ξ (⟨b, hb⟩ : ↥F) true) ?_ ?_
  · intro ξ hξ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hξ ⊢
    have := hflip _ hξ
    have hext : extF F (Function.update ξ ⟨b, hb⟩ true) = Function.update (extF F ξ) b true := by
      funext c
      by_cases hcb : c = b
      · subst hcb
        simp [extF, hb]
      · have hne : ∀ (hc : c ∈ F), (⟨c, hc⟩ : ↥F) ≠ ⟨b, hb⟩ := fun hc h => hcb (congrArg Subtype.val h)
        by_cases hc : c ∈ F
        · simp [extF, hc, Function.update_of_ne (hne hc), Function.update_of_ne hcb]
        · simp [extF, hc, Function.update_of_ne hcb]
    rw [hext]; exact this
  · intro ξ hξ ξ' hξ' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hξ hξ'
    have hξb : ξ ⟨b, hb⟩ = false := by
      have := hclosed _ hξ; simpa [extF, hb] using this
    have hξ'b : ξ' ⟨b, hb⟩ = false := by
      have := hclosed _ hξ'; simpa [extF, hb] using this
    funext c
    by_cases hc : c = ⟨b, hb⟩
    · subst hc; rw [hξb, hξ'b]
    · have := congrFun heq c
      simpa [Function.update, hc] using this

end Rotor

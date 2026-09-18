import Rotor.Support.PendantInduced
import Rotor.Support.Excursion

/-!
The counting estimate of the pendant counterexample (`rotor.tex:2240-2247`): for the uniform
law on `G_M`, the probability that some king-connected set `U ∋ o` has at least `|U|/3`
sites whose induced rotor does not point west is at most `1/64` once `M + 4 ≥ 3 · 2^24`.
The induced rotor at `v` does not point west exactly when the neighbour index of `ρ(v)` is
`0, 1, 2` (the directions `N, E, S`), an event of probability `3/(M+4)` at each site,
independently over sites.
-/

open Finset MeasureTheory ENNReal

namespace Rotor

variable (M : ℕ)

theorem dir0_induce (ρ : Config (pendantGraph M)) (v : Site) :
    dir0 (induce M ρ) v = latDir M (nbrIdx M (ρ (.inl v))) := by
  unfold dir0 induce
  exact Equiv.symm_apply_apply _ _

theorem latDir_ne_three_iff (k : Fin (M + 4)) : latDir M k ≠ 3 ↔ (k : ℕ) ≤ 2 := by
  unfold latDir
  split_ifs with h
  · rw [Ne, Fin.ext_iff]
    show ¬ (k : ℕ) = 3 ↔ _
    omega
  · simp only [ne_eq, not_true_eq_false, false_iff, not_le]
    omega

/-- The event that the rotors at all sites of `A` do not point west. -/
def nonWestOn (A : Finset Site) : Set (Config (pendantGraph M)) :=
  {ρ | ∀ v ∈ A, (nbrIdx M (ρ (.inl v)) : ℕ) ≤ 2}

/-- The non-west rotors at a vertex: at a lattice vertex the neighbour indices `0, 1, 2`, at
a leaf everything. -/
def nonWestSet : ∀ w : PVertex M, Set ((pendantGraph M).neighborSet w)
  | .inl _ => {a | (nbrIdx M a : ℕ) ≤ 2}
  | .inr _ => Set.univ

theorem nonWestOn_eq (A : Finset Site) :
    nonWestOn M A = Set.pi ↑(A.image (Sum.inl : Site → PVertex M)) (nonWestSet M) := by
  ext ρ
  simp only [nonWestOn, Set.mem_setOf_eq, Set.mem_pi, coe_image, Set.mem_image, mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

theorem card_filter_nbrIdx_le_two (v : Site) :
    (Finset.univ.filter (fun a : (pendantGraph M).neighborSet (.inl v) =>
      (nbrIdx M a : ℕ) ≤ 2)).card = 3 := by
  rw [Finset.card_equiv (pendantNbrLattice M v).symm (t := Finset.univ.filter
      (fun k : Fin (M + 4) => (k : ℕ) ≤ 2))]
  · have : Finset.univ.filter (fun k : Fin (M + 4) => (k : ℕ) ≤ 2) =
        {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      omega
    rw [this]
    rfl
  · intro a
    simp [nbrIdx]

theorem uniformAt_nonWestSet_inl (v : Site) :
    uniformAt (pendantMech M) (.inl v) (nonWestSet M (.inl v)) = 3 / ((M : ℝ≥0∞) + 4) := by
  have hset : nonWestSet M (.inl v) = ↑(Finset.univ.filter
      (fun a : (pendantGraph M).neighborSet (.inl v) => (nbrIdx M a : ℕ) ≤ 2)) := by
    ext a; simp [nonWestSet]
  unfold uniformAt
  rw [hset, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul, card_filter_nbrIdx_le_two,
    SimpleGraph.card_neighborSet_eq_degree, pendantGraph_degree_inl]
  rw [div_eq_mul_inv]
  push_cast
  rfl

theorem uniformLaw_nonWestOn (A : Finset Site) :
    uniformLaw (pendantMech M) (nonWestOn M A) = (3 / ((M : ℝ≥0∞) + 4)) ^ A.card := by
  have key := Measure.infinitePi_pi (μ := uniformAt (pendantMech M))
    (s := A.image (Sum.inl : Site → PVertex M)) (t := nonWestSet M)
    (fun _ _ => MeasurableSet.of_discrete)
  rw [nonWestOn_eq, uniformLaw, productLaw]
  refine key.trans ?_
  rw [prod_image (fun _ _ _ _ h => Sum.inl_injective h)]
  simp only [uniformAt_nonWestSet_inl, prod_const]

/-- The bad event: some king-connected set containing `o` has at least a third of its sites
with a non-west induced rotor. -/
def badEvent (o : Site) : Set (Config (pendantGraph M)) :=
  {ρ | ∃ U : Finset Site, KConn o U ∧
    U.card ≤ 3 * (U.filter (fun v => dir0 (induce M ρ) v ≠ 3)).card}

/-- The bad event at size `n + 1`. -/
def badN (o : Site) (n : ℕ) : Set (Config (pendantGraph M)) :=
  {ρ | ∃ U : Finset Site, KConn o U ∧ U.card = n + 1 ∧
    n + 1 ≤ 3 * (U.filter (fun v => (nbrIdx M (ρ (.inl v)) : ℕ) ≤ 2)).card}

theorem badEvent_subset (o : Site) : badEvent M o ⊆ ⋃ n : ℕ, badN M o n := by
  intro ρ hρ
  obtain ⟨U, hK, hU⟩ := hρ
  have hpos : 0 < U.card := card_pos.2 ⟨o, hK.1⟩
  refine Set.mem_iUnion.2 ⟨U.card - 1, U, hK, by omega, ?_⟩
  have : U.filter (fun v => dir0 (induce M ρ) v ≠ 3) =
      U.filter (fun v => (nbrIdx M (ρ (.inl v)) : ℕ) ≤ 2) :=
    filter_congr (fun v _ => by rw [dir0_induce, latDir_ne_three_iff])
  rw [← this]
  omega

theorem badN_subset (o : Site) (n : ℕ) (𝒰 : Finset (Finset Site))
    (h𝒰 : ∀ U, KConn o U → U.card = n + 1 → U ∈ 𝒰) :
    badN M o n ⊆ ⋃ U ∈ 𝒰, ⋃ A ∈ U.powersetCard ((n + 3) / 3), nonWestOn M A := by
  intro ρ hρ
  obtain ⟨U, hK, hU, hcard⟩ := hρ
  obtain ⟨A, hAsub, hAcard⟩ := exists_subset_card_eq (s := U.filter
    (fun v => (nbrIdx M (ρ (.inl v)) : ℕ) ≤ 2)) (n := (n + 3) / 3) (by omega)
  refine Set.mem_iUnion₂.2 ⟨U, h𝒰 U hK hU, Set.mem_iUnion₂.2 ⟨A, ?_, ?_⟩⟩
  · exact mem_powersetCard.2 ⟨hAsub.trans (filter_subset _ _), hAcard⟩
  · exact fun v hv => (mem_filter.1 (hAsub hv)).2

theorem measure_badN_le (o : Site) (n : ℕ) :
    uniformLaw (pendantMech M) (badN M o n) ≤
      (64 : ℝ≥0∞) ^ n * 2 ^ (n + 1) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) := by
  obtain ⟨𝒰₀, h𝒰₀card, h𝒰₀⟩ := exists_animal_family o n
  set 𝒰 := 𝒰₀.filter (fun U => U.card = n + 1) with h𝒰def
  have h𝒰card : 𝒰.card ≤ 64 ^ n := (card_filter_le _ _).trans h𝒰₀card
  have h𝒰 : ∀ U, KConn o U → U.card = n + 1 → U ∈ 𝒰 :=
    fun U hK hU => mem_filter.2 ⟨h𝒰₀ U hK hU, hU⟩
  have hcard : ∀ U ∈ 𝒰, U.card = n + 1 := fun U hU => (mem_filter.1 hU).2
  calc uniformLaw (pendantMech M) (badN M o n)
      ≤ uniformLaw (pendantMech M) (⋃ U ∈ 𝒰, ⋃ A ∈ U.powersetCard ((n + 3) / 3), nonWestOn M A) :=
        measure_mono (badN_subset M o n 𝒰 h𝒰)
    _ ≤ ∑ U ∈ 𝒰, uniformLaw (pendantMech M) (⋃ A ∈ U.powersetCard ((n + 3) / 3), nonWestOn M A) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ U ∈ 𝒰, ∑ A ∈ U.powersetCard ((n + 3) / 3), uniformLaw (pendantMech M) (nonWestOn M A) :=
        sum_le_sum (fun U _ => measure_biUnion_finset_le _ _)
    _ = ∑ U ∈ 𝒰, ∑ A ∈ U.powersetCard ((n + 3) / 3), (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) := by
        refine sum_congr rfl (fun U _ => sum_congr rfl (fun A hA => ?_))
        rw [uniformLaw_nonWestOn, (mem_powersetCard.1 hA).2]
    _ = ∑ U ∈ 𝒰, ((n + 1).choose ((n + 3) / 3) : ℝ≥0∞) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) := by
        refine sum_congr rfl (fun U hU => ?_)
        rw [sum_const, card_powersetCard, nsmul_eq_mul, hcard U hU]
    _ ≤ ∑ U ∈ 𝒰, (2 : ℝ≥0∞) ^ (n + 1) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) := by
        refine sum_le_sum (fun U hU => mul_le_mul' ?_ le_rfl)
        calc ((n + 1).choose ((n + 3) / 3) : ℝ≥0∞) ≤ ((2 ^ (n + 1) : ℕ) : ℝ≥0∞) :=
              Nat.cast_le.2 (Nat.choose_le_two_pow _ _)
          _ = (2 : ℝ≥0∞) ^ (n + 1) := by push_cast; rfl
    _ = 𝒰.card * ((2 : ℝ≥0∞) ^ (n + 1) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (64 : ℝ≥0∞) ^ n * (2 ^ (n + 1) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3)) := by
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast h𝒰card
    _ = _ := by ring

/-! ### The numerical bound -/

theorem three_div_le (hM : 50331645 ≤ M) :
    (3 : ℝ≥0∞) / ((M : ℝ≥0∞) + 4) ≤ (2⁻¹ : ℝ≥0∞) ^ 24 := by
  have h1 : (3 : ℝ≥0∞) / ((M : ℝ≥0∞) + 4) ≤ 3 / (3 * 2 ^ 24) := by
    refine ENNReal.div_le_div_left ?_ 3
    have : ((3 * 2 ^ 24 : ℕ) : ℝ≥0∞) ≤ ((M + 4 : ℕ) : ℝ≥0∞) := Nat.cast_le.2 (by omega)
    push_cast at this
    norm_num
    exact this
  refine h1.trans (le_of_eq ?_)
  rw [← ENNReal.inv_pow, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem term_le (hM : 50331645 ≤ M) (n : ℕ) :
    (64 : ℝ≥0∞) ^ n * 2 ^ (n + 1) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) ≤
      (2⁻¹ : ℝ≥0∞) ^ (n + 7) := by
  have hq : (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) ≤ (2⁻¹ : ℝ≥0∞) ^ (8 * n + 8) := by
    calc (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3) ≤ ((2⁻¹ : ℝ≥0∞) ^ 24) ^ ((n + 3) / 3) :=
          pow_le_pow_left' (three_div_le M hM) _
      _ = (2⁻¹ : ℝ≥0∞) ^ (24 * ((n + 3) / 3)) := by rw [← pow_mul]
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ (8 * n + 8) :=
          pow_le_pow_of_le_one (zero_le) (ENNReal.inv_le_one.2 one_le_two) (by omega)
  calc (64 : ℝ≥0∞) ^ n * 2 ^ (n + 1) * (3 / ((M : ℝ≥0∞) + 4)) ^ ((n + 3) / 3)
      ≤ (64 : ℝ≥0∞) ^ n * 2 ^ (n + 1) * (2⁻¹ : ℝ≥0∞) ^ (8 * n + 8) := mul_le_mul' le_rfl hq
    _ = (2 : ℝ≥0∞) ^ (7 * n + 1) * ((2⁻¹ : ℝ≥0∞) ^ (7 * n + 1) * (2⁻¹ : ℝ≥0∞) ^ (n + 7)) := by
        rw [show (64 : ℝ≥0∞) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
        congr 2 <;> ring
    _ = (2⁻¹ : ℝ≥0∞) ^ (n + 7) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top, one_pow,
          one_mul]

theorem tsum_half_pow : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 7) = (2⁻¹ : ℝ≥0∞) ^ 6 := by
  simp_rw [pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    pow_succ, mul_left_comm, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top, mul_one]

/-- The counting bound: the bad event has probability at most `1/64`. -/
theorem measure_badEvent_le (hM : 50331645 ≤ M) (o : Site) :
    uniformLaw (pendantMech M) (badEvent M o) ≤ (2⁻¹ : ℝ≥0∞) ^ 6 := by
  calc uniformLaw (pendantMech M) (badEvent M o)
      ≤ uniformLaw (pendantMech M) (⋃ n : ℕ, badN M o n) := measure_mono (badEvent_subset M o)
    _ ≤ ∑' n : ℕ, uniformLaw (pendantMech M) (badN M o n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 7) :=
        ENNReal.tsum_le_tsum (fun n => (measure_badN_le M o n).trans (term_le M hM n))
    _ = (2⁻¹ : ℝ≥0∞) ^ 6 := tsum_half_pow

theorem measure_badEvent_lt_one (hM : 50331645 ≤ M) (o : Site) :
    uniformLaw (pendantMech M) (badEvent M o) < 1 :=
  (measure_badEvent_le M hM o).trans_lt
    (pow_lt_one₀ (zero_le) (ENNReal.inv_lt_one.2 one_lt_two) (by norm_num))


end Rotor

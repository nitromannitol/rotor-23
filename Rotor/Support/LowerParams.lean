import Rotor.Support.FiniteProduct

open Finset Classical

namespace Rotor

section Lower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lowering the parameters on `E` by `ε` loses at most `ε 2^|E|` times the sum of the pivotal
masses. -/
theorem fpr_lower_set {par : ι → ℝ} (hpar : IsParam par) {A : Set (ι → Bool)} (hA : IncrEvent A)
    {ε : ℝ} (hε : 0 ≤ ε) (E : Finset ι) (hE : ∀ j ∈ E, ε ≤ par j ∧ par j + ε ≤ 1) :
    fpr par A - fpr (fun j => if j ∈ E then par j - ε else par j) A ≤
      ε * 2 ^ E.card * ∑ j ∈ E, fpr par (Pivot j A) := by
  induction E using Finset.induction_on with
  | empty => simp
  | insert i E hi ih =>
    have hE' : ∀ j ∈ E, ε ≤ par j ∧ par j + ε ≤ 1 := fun j hj => hE j (mem_insert_of_mem hj)
    have ih := ih hE'
    have hparE_param : IsParam (fun j => if j ∈ E then par j - ε else par j) := by
      intro j; simp only; split_ifs with hj
      · have := hE' j hj; have := hpar j; constructor <;> linarith
      · exact hpar j
    have hagree : ∀ j, j ≠ i →
        (fun j => if j ∈ insert i E then par j - ε else par j) j =
        (fun j => if j ∈ E then par j - ε else par j) j := by
      intro j hj; simp only [mem_insert, hj, false_or]
    have hchange := fpr_change (par := fun j => if j ∈ E then par j - ε else par j)
      (par' := fun j => if j ∈ insert i E then par j - ε else par j) i hagree hA
    have hi' : (fun j => if j ∈ E then par j - ε else par j) i -
        (fun j => if j ∈ insert i E then par j - ε else par j) i = ε := by simp [hi]
    rw [hi'] at hchange
    have hpiv : fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot i A) ≤
        2 ^ E.card * fpr par (Pivot i A) := by
      refine fpr_le_of_par hpar (by positivity) (fun ω => ?_) _
      refine fpw_le_of_par hparE_param hpar E (by norm_num) (fun j hj => by simp [hj])
        (fun j hj => ?_) ω
      have := hE' j hj; have := hpar j
      simp only [hj, if_true]
      constructor <;> linarith
    have hpiv0 : 0 ≤ fpr par (Pivot i A) := fpr_nonneg hpar _
    have hsum0 : 0 ≤ ∑ j ∈ E, fpr par (Pivot j A) := sum_nonneg (fun j _ => fpr_nonneg hpar _)
    have h2 : (0:ℝ) ≤ 2 ^ E.card := by positivity
    rw [sum_insert hi, card_insert_of_notMem hi, pow_succ]
    have hε2 : 0 ≤ ε * 2 ^ E.card := mul_nonneg hε h2
    calc fpr par A - fpr (fun j => if j ∈ insert i E then par j - ε else par j) A
        = (fpr par A - fpr (fun j => if j ∈ E then par j - ε else par j) A) +
          (fpr (fun j => if j ∈ E then par j - ε else par j) A -
            fpr (fun j => if j ∈ insert i E then par j - ε else par j) A) := by ring
      _ ≤ ε * 2 ^ E.card * ∑ j ∈ E, fpr par (Pivot j A) +
          ε * (2 ^ E.card * fpr par (Pivot i A)) := by
          rw [hchange]; exact add_le_add ih (mul_le_mul_of_nonneg_left hpiv hε)
      _ ≤ ε * (2 ^ E.card * 2) * (fpr par (Pivot i A) + ∑ j ∈ E, fpr par (Pivot j A)) := by
          nlinarith [mul_nonneg hε2 hpiv0, mul_nonneg hε2 hsum0]

/-- One block step: lower the block's coordinates `E` by `ε`, then raise the mark `m` to `1`.
The probability of the increasing event `A` does not decrease when `ε` is small. -/
theorem fpr_block_step {par : ι → ℝ} (hpar : IsParam par) {A : Set (ι → Bool)} (hA : IncrEvent A)
    {ε : ℝ} (hε : 0 ≤ ε) (E : Finset ι) (hE : ∀ j ∈ E, 2 * ε ≤ par j ∧ par j + ε ≤ 1)
    (m : ι) (hm : m ∉ E) (hm0 : par m = 0) {K : ℝ} (hK : 0 ≤ K)
    (hcomp : ∀ j ∈ E, fpr par (Pivot j A) ≤ K * fpr par (Pivot m A))
    (hεK : ε * 2 ^ E.card * E.card * K * 2 ^ E.card ≤ 1) :
    fpr par A ≤ fpr (fun j => if j = m then 1 else if j ∈ E then par j - ε else par j) A := by
  have hE' : ∀ j ∈ E, ε ≤ par j ∧ par j + ε ≤ 1 :=
    fun j hj => ⟨by linarith [(hE j hj).1], (hE j hj).2⟩
  have hlow := fpr_lower_set hpar hA hε E hE'
  have hparE_param : IsParam (fun j => if j ∈ E then par j - ε else par j) := by
    intro j; simp only; split_ifs with hj
    · have := hE' j hj; have := hpar j; constructor <;> linarith
    · exact hpar j
  have hagree : ∀ j, j ≠ m →
      (fun j => if j = m then 1 else if j ∈ E then par j - ε else par j) j =
      (fun j => if j ∈ E then par j - ε else par j) j := by
    intro j hj; simp only [hj, if_false]
  have hchange := fpr_change (par := fun j => if j ∈ E then par j - ε else par j)
    (par' := fun j => if j = m then 1 else if j ∈ E then par j - ε else par j) m hagree hA
  have hm' : (fun j => if j ∈ E then par j - ε else par j) m -
      (fun j => if j = m then 1 else if j ∈ E then par j - ε else par j) m = -1 := by
    simp [hm, hm0]
  rw [hm'] at hchange
  have hpiv : fpr par (Pivot m A) ≤
      2 ^ E.card * fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A) := by
    refine fpr_le_of_par hparE_param (by positivity) (fun ω => ?_) _
    refine fpw_le_of_par hpar hparE_param E (by norm_num) (fun j hj => by simp [hj])
      (fun j hj => ?_) ω
    have := hE j hj; have := hpar j
    simp only [hj, if_true]
    constructor <;> linarith
  have hsum : ∑ j ∈ E, fpr par (Pivot j A) ≤ E.card * (K * fpr par (Pivot m A)) := by
    calc ∑ j ∈ E, fpr par (Pivot j A) ≤ ∑ j ∈ E, K * fpr par (Pivot m A) := sum_le_sum hcomp
      _ = E.card * (K * fpr par (Pivot m A)) := by rw [sum_const, nsmul_eq_mul]
  have hpivE0 : 0 ≤ fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A) :=
    fpr_nonneg hparE_param _
  have h2 : (0:ℝ) ≤ 2 ^ E.card := by positivity
  have hε2 : 0 ≤ ε * 2 ^ E.card := mul_nonneg hε h2
  have step2 : ε * 2 ^ E.card * ∑ j ∈ E, fpr par (Pivot j A) ≤
      ε * 2 ^ E.card * (E.card * (K * fpr par (Pivot m A))) :=
    mul_le_mul_of_nonneg_left hsum hε2
  have step3 : ε * 2 ^ E.card * (E.card * (K * fpr par (Pivot m A))) ≤
      ε * 2 ^ E.card * (E.card * (K * (2 ^ E.card *
        fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A)))) := by
    gcongr
  have step4 : ε * 2 ^ E.card * (E.card * (K * (2 ^ E.card *
      fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A)))) ≤
      fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A) := by
    have : ε * 2 ^ E.card * (E.card * (K * (2 ^ E.card *
        fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A)))) =
        (ε * 2 ^ E.card * E.card * K * 2 ^ E.card) *
          fpr (fun j => if j ∈ E then par j - ε else par j) (Pivot m A) := by ring
    rw [this]; exact mul_le_of_le_one_left hpivE0 hεK
  linarith

end Lower

/-! ### Projecting a product model on the first factor -/

theorem fpr_inl {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (par : ι₁ ⊕ ι₂ → ℝ) (E : Set (ι₁ → Bool)) :
    fpr par {ω | (fun i => ω (Sum.inl i)) ∈ E} = fpr (fun i => par (Sum.inl i)) E := by
  unfold fpr
  rw [← (Equiv.sumArrowEquivProdArrow ι₁ ι₂ Bool).symm.sum_comp, Fintype.sum_prod_type]
  have hw : ∀ (f : ι₁ → Bool) (g : ι₂ → Bool),
      fpw par ((Equiv.sumArrowEquivProdArrow ι₁ ι₂ Bool).symm (f, g)) =
        fpw (fun i => par (Sum.inl i)) f * fpw (fun i => par (Sum.inr i)) g := by
    intro f g
    unfold fpw
    rw [Fintype.prod_sum_type]
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr]
    rfl
  simp only [hw]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  have hmem : ∀ g : ι₂ → Bool,
      ((Equiv.sumArrowEquivProdArrow ι₁ ι₂ Bool).symm (f, g) ∈
        {ω : ι₁ ⊕ ι₂ → Bool | (fun i => ω (Sum.inl i)) ∈ E}) ↔ f ∈ E := by
    intro g; simp [Equiv.sumArrowEquivProdArrow]
  by_cases hf : f ∈ E
  · simp only [hmem, hf, if_true]
    rw [← Finset.mul_sum, sum_fpw, mul_one]
  · simp only [hmem, hf, if_false, Finset.sum_const_zero]

end Rotor

import Rotor.Support.BondFinite

/-!
Lemma 5.3 (`lem:square-constrained-bonds`), part 1: finite product models with a parameter for
every coordinate.  The probability of an event is affine in each parameter, the slope being the
probability that the coordinate is pivotal (for increasing events); a map that changes at most
`B` coordinates, with parameters in `[1/4, 3/4]`, changes weights by at most `3^B` and has at
most `2^B` preimages.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

section FiniteProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of a configuration under the parameters `par`. -/
noncomputable def fpw (par : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then par i else 1 - par i

/-- Parameters are probabilities. -/
def IsParam (par : ι → ℝ) : Prop := ∀ i, 0 ≤ par i ∧ par i ≤ 1

omit [DecidableEq ι] in
theorem fpw_nonneg {par : ι → ℝ} (hpar : IsParam par) (ω : ι → Bool) : 0 ≤ fpw par ω :=
  Finset.prod_nonneg (fun i _ => by
    split_ifs
    · exact (hpar i).1
    · linarith [(hpar i).2])

/-- The probability of `A`. -/
noncomputable def fpr (par : ι → ℝ) (A : Set (ι → Bool)) : ℝ :=
  ∑ ω, if ω ∈ A then fpw par ω else 0

theorem fpr_nonneg {par : ι → ℝ} (hpar : IsParam par) (A : Set (ι → Bool)) : 0 ≤ fpr par A :=
  Finset.sum_nonneg (fun ω _ => by split_ifs; exacts [fpw_nonneg hpar ω, le_rfl])

theorem fpr_mono {par : ι → ℝ} (hpar : IsParam par) {A B : Set (ι → Bool)} (h : A ⊆ B) :
    fpr par A ≤ fpr par B := by
  refine Finset.sum_le_sum (fun ω _ => ?_)
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h h1) h2
  · exact fpw_nonneg hpar ω
  · exact le_rfl

theorem sum_fpw {par : ι → ℝ} : ∑ ω, fpw par ω = 1 := by
  have h := Finset.prod_univ_sum (t := fun _ : ι => (Finset.univ : Finset Bool))
    (f := fun i b => if b = true then par i else 1 - par i)
  rw [Fintype.piFinset_univ] at h
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_sub_cancel,
    Finset.prod_const_one] at h
  unfold fpw
  exact h.symm

theorem fpr_univ {par : ι → ℝ} : fpr par Set.univ = 1 := by
  unfold fpr; simp [sum_fpw]

theorem fpr_le_one {par : ι → ℝ} (hpar : IsParam par) (A : Set (ι → Bool)) : fpr par A ≤ 1 := by
  rw [← fpr_univ (par := par)]
  exact fpr_mono hpar (Set.subset_univ A)

/-! ### Splitting at one coordinate -/

/-- The weight without the coordinate `i`, on the other coordinates. -/
noncomputable def fpwE (par : ι → ℝ) (i : ι) (τ : {j // j ≠ i} → Bool) : ℝ :=
  ∏ j : {j // j ≠ i}, if τ j then par j.1 else 1 - par j.1

theorem fpw_symm (par : ι → ℝ) (i : ι) (b : Bool) (τ : {j // j ≠ i} → Bool) :
    fpw par ((Equiv.piSplitAt i (fun _ => Bool)).symm (b, τ)) =
      (if b then par i else 1 - par i) * fpwE par i τ := by
  unfold fpw fpwE
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · rw [Finset.prod_subtype (Finset.univ.erase i) (p := fun j => j ≠ i) (fun j => by simp)]
    refine Fintype.prod_congr _ _ (fun j => ?_)
    have hj : j.1 ≠ i := j.2
    simp [Equiv.piSplitAt_symm_apply, hj]

omit [Fintype ι] in
theorem update_symm (i : ι) (b b' : Bool) (τ : {j // j ≠ i} → Bool) :
    Function.update ((Equiv.piSplitAt i (fun _ => Bool)).symm (b, τ)) i b' =
      (Equiv.piSplitAt i (fun _ => Bool)).symm (b', τ) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.piSplitAt_symm_apply]
  · simp [Equiv.piSplitAt_symm_apply, hj]

/-- The probability of `A` as an affine function of the parameter at `i`. -/
theorem fpr_affine (par : ι → ℝ) (i : ι) (A : Set (ι → Bool)) :
    fpr par A = par i * (∑ τ, if (Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A
        then fpwE par i τ else 0) +
      (1 - par i) * (∑ τ, if (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∈ A
        then fpwE par i τ else 0) := by
  unfold fpr
  rw [← (Equiv.piSplitAt i (fun _ => Bool)).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [fpw_symm, if_true, Bool.false_eq_true, if_false, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl (fun τ _ => ?_) <;> split_ifs <;> ring

/-- `i` is pivotal for `A`. -/
def Pivot (i : ι) (A : Set (ι → Bool)) : Set (ι → Bool) :=
  {ω | Function.update ω i true ∈ A ∧ Function.update ω i false ∉ A}

/-- Increasing events. -/
def IncrEvent (A : Set (ι → Bool)) : Prop :=
  ∀ ω ω' : ι → Bool, (∀ j, ω j = true → ω' j = true) → ω ∈ A → ω' ∈ A

theorem fpr_piv (par : ι → ℝ) (i : ι) {A : Set (ι → Bool)} (hA : IncrEvent A) :
    fpr par (Pivot i A) = (∑ τ, if (Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A
        then fpwE par i τ else 0) -
      (∑ τ, if (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∈ A
        then fpwE par i τ else 0) := by
  rw [fpr_affine par i (Pivot i A), ← Finset.sum_sub_distrib]
  have hmem : ∀ (b : Bool) τ, (Equiv.piSplitAt i (fun _ => Bool)).symm (b, τ) ∈ Pivot i A ↔
      ((Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A ∧
        (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∉ A) := by
    intro b τ
    simp only [Pivot, Set.mem_setOf_eq, update_symm]
  have hincr : ∀ τ, (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∈ A →
      (Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A := by
    intro τ h
    refine hA _ _ (fun j hj => ?_) h
    by_cases hji : j = i
    · subst hji; simp [Equiv.piSplitAt_symm_apply]
    · simpa [Equiv.piSplitAt_symm_apply, hji] using hj
  simp only [hmem]
  have : ∀ τ, (if (Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A ∧
        (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∉ A then fpwE par i τ else 0) =
      (if (Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A then fpwE par i τ else 0) -
        (if (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∈ A then fpwE par i τ else 0) := by
    intro τ
    by_cases h1 : (Equiv.piSplitAt i (fun _ => Bool)).symm (true, τ) ∈ A <;>
      by_cases h0 : (Equiv.piSplitAt i (fun _ => Bool)).symm (false, τ) ∈ A
    · simp [h1, h0]
    · simp [h1, h0]
    · exact absurd (hincr τ h0) h1
    · simp [h1, h0]
  have hx : ∀ x : ℝ, par i * x + (1 - par i) * x = x := fun x => by ring
  rw [hx]
  exact Finset.sum_congr rfl (fun τ _ => this τ)

/-! ### Changing one parameter -/

theorem fpwE_congr {par par' : ι → ℝ} (i : ι) (h : ∀ j, j ≠ i → par' j = par j)
    (τ : {j // j ≠ i} → Bool) : fpwE par' i τ = fpwE par i τ := by
  unfold fpwE
  exact Fintype.prod_congr _ _ (fun j => by rw [h j.1 j.2])

/-- The probability of an increasing event changes by the parameter change times the pivotal
probability. -/
theorem fpr_change {par par' : ι → ℝ} (i : ι) (h : ∀ j, j ≠ i → par' j = par j)
    {A : Set (ι → Bool)} (hA : IncrEvent A) :
    fpr par A - fpr par' A = (par i - par' i) * fpr par (Pivot i A) := by
  rw [fpr_affine par i A, fpr_affine par' i A, fpr_piv par i hA]
  simp only [fpwE_congr i h]
  ring

theorem fpr_pivot_congr {par par' : ι → ℝ} (i : ι) (h : ∀ j, j ≠ i → par' j = par j)
    {A : Set (ι → Bool)} (hA : IncrEvent A) :
    fpr par' (Pivot i A) = fpr par (Pivot i A) := by
  rw [fpr_piv par i hA, fpr_piv par' i hA]
  simp only [fpwE_congr i h]

theorem fpr_pivot_nonneg {par : ι → ℝ} (hpar : IsParam par) (i : ι) (A : Set (ι → Bool)) :
    0 ≤ fpr par (Pivot i A) := fpr_nonneg hpar _

/-! ### Comparison through a map -/

/-- If `φ` maps `S` into `T`, increases weights by at most `K`, and has at most `M` preimages,
then `P(S) ≤ K M P(T)`. -/
theorem fpr_le_of_map {par : ι → ℝ} (hpar : IsParam par) {S T : Set (ι → Bool)}
    (φ : (ι → Bool) → (ι → Bool)) (hφ : ∀ ω ∈ S, φ ω ∈ T) {K : ℝ} (hK : 0 ≤ K)
    (hwt : ∀ ω ∈ S, fpw par ω ≤ K * fpw par (φ ω)) {M : ℕ}
    (hM : ∀ ω', (Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω')).card ≤ M) :
    fpr par S ≤ K * M * fpr par T := by
  unfold fpr
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  calc ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ S), fpw par ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ S), K * fpw par (φ ω) :=
        Finset.sum_le_sum (fun ω hω => hwt ω (Finset.mem_filter.1 hω).2)
    _ = K * ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ S), fpw par (φ ω) := by rw [Finset.mul_sum]
    _ = K * ∑ ω' ∈ Finset.univ, ∑ ω ∈ (Finset.univ.filter (fun ω => ω ∈ S)).filter (fun ω => φ ω = ω'),
          fpw par (φ ω) := by
        rw [Finset.sum_fiberwise_of_maps_to (fun ω _ => Finset.mem_univ (φ ω))]
    _ = K * ∑ ω' ∈ Finset.univ, ((Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω')).card : ℝ) *
          fpw par ω' := by
        congr 1
        refine Finset.sum_congr rfl (fun ω' _ => ?_)
        rw [Finset.filter_filter]
        rw [Finset.sum_congr rfl (fun ω hω => by
          rw [(Finset.mem_filter.1 hω).2.2] : ∀ ω ∈ Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω'),
            fpw par (φ ω) = fpw par ω')]
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * ∑ ω' ∈ Finset.univ.filter (fun ω' => ω' ∈ T), (M : ℝ) * fpw par ω' := by
        gcongr
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω' => ω' ∈ T)]
        have hzero : ∑ ω' ∈ Finset.univ.filter (fun ω' => ¬ ω' ∈ T),
            ((Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω')).card : ℝ) * fpw par ω' = 0 := by
          refine Finset.sum_eq_zero (fun ω' hω' => ?_)
          have hT := (Finset.mem_filter.1 hω').2
          have : (Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω')).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            rintro ω - ⟨hS, hφω⟩
            exact hT (hφω ▸ hφ ω hS)
          rw [this]; simp
        rw [hzero, add_zero]
        refine Finset.sum_le_sum (fun ω' _ => ?_)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM ω') (fpw_nonneg hpar ω')
    _ = K * M * ∑ ω' ∈ Finset.univ.filter (fun ω' => ω' ∈ T), fpw par ω' := by
        rw [← Finset.mul_sum, mul_assoc]

/-- Configurations agreeing outside `J` have at most `2^|J|` variants. -/
theorem card_agree_le (J : Finset ι) (S : Set (ι → Bool)) (φ : (ι → Bool) → (ι → Bool))
    (hφ : ∀ ω ∈ S, ∀ j, j ∉ J → φ ω j = ω j) (ω' : ι → Bool) :
    (Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω')).card ≤ 2 ^ J.card := by
  have hinj : Set.InjOn (fun ω : ι → Bool => fun j : ↥J => ω j.1)
      ↑(Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω')) := by
    intro ω hω ω₂ hω₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω hω₂
    funext j
    by_cases hj : j ∈ J
    · exact congrFun heq ⟨j, hj⟩
    · rw [← hφ ω hω.1 j hj, ← hφ ω₂ hω₂.1 j hj, hω.2, hω₂.2]
  have := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
  calc _ ≤ (Finset.univ : Finset (↥J → Bool)).card := this
    _ = 2 ^ J.card := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- The weight ratio of two configurations agreeing outside `J`. -/
theorem fpw_le_of_agree {par : ι → ℝ} (hpar : IsParam par) (J : Finset ι) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hlow : ∀ j ∈ J, 1 / ρ ≤ par j ∧ par j ≤ 1 - 1 / ρ) {ω ω' : ι → Bool}
    (hJ : ∀ j, j ∉ J → ω j = ω' j) : fpw par ω ≤ ρ ^ J.card * fpw par ω' := by
  unfold fpw
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j ∈ J),
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j ∈ J)]
  have hJ' : Finset.univ.filter (fun j => j ∈ J) = J := by ext j; simp
  rw [hJ']
  have hout : ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω j then par j else 1 - par j) =
      ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω' j then par j else 1 - par j) :=
    Finset.prod_congr rfl (fun j hj => by rw [hJ j (Finset.mem_filter.1 hj).2])
  rw [hout]
  have hρ0 : 0 < ρ := by linarith
  have hin : ∏ j ∈ J, (if ω j then par j else 1 - par j) ≤
      ρ ^ J.card * ∏ j ∈ J, (if ω' j then par j else 1 - par j) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun j _ => by split_ifs; exacts [(hpar j).1, by linarith [(hpar j).2]])
      (fun j hj => ?_)
    obtain ⟨h1, h2⟩ := hlow j hj
    have hp0 : 0 < par j := by
      have : 0 < 1 / ρ := by positivity
      linarith
    have hp1 : 0 < 1 - par j := by
      have : 0 < 1 / ρ := by positivity
      linarith
    -- every factor is at most 1 and at least 1/ρ
    have hle1 : (if ω j then par j else 1 - par j) ≤ 1 := by
      split_ifs; exacts [(hpar j).2, by linarith [(hpar j).1]]
    have hge : 1 / ρ ≤ (if ω' j then par j else 1 - par j) := by
      split_ifs; exacts [h1, by linarith]
    calc (if ω j then par j else 1 - par j) ≤ 1 := hle1
      _ = ρ * (1 / ρ) := by field_simp
      _ ≤ ρ * (if ω' j then par j else 1 - par j) := by gcongr
  have hout0 : 0 ≤ ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω' j then par j else 1 - par j) :=
    Finset.prod_nonneg (fun j _ => by split_ifs; exacts [(hpar j).1, by linarith [(hpar j).2]])
  calc (∏ j ∈ J, (if ω j then par j else 1 - par j)) *
        ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω' j then par j else 1 - par j)
      ≤ (ρ ^ J.card * ∏ j ∈ J, (if ω' j then par j else 1 - par j)) *
        ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω' j then par j else 1 - par j) := by
        gcongr
    _ = _ := by ring

/-- The weight ratio under two parameter families agreeing outside `J`. -/
theorem fpw_le_of_par {par par' : ι → ℝ} (hpar : IsParam par) (hpar' : IsParam par') (J : Finset ι)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) (hJ : ∀ j, j ∉ J → par j = par' j)
    (hrat : ∀ j ∈ J, par j ≤ ρ * par' j ∧ 1 - par j ≤ ρ * (1 - par' j)) (ω : ι → Bool) :
    fpw par ω ≤ ρ ^ J.card * fpw par' ω := by
  unfold fpw
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j ∈ J),
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j ∈ J)]
  have hJ' : Finset.univ.filter (fun j => j ∈ J) = J := by ext j; simp
  rw [hJ']
  have hout : ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω j then par j else 1 - par j) =
      ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω j then par' j else 1 - par' j) :=
    Finset.prod_congr rfl (fun j hj => by rw [hJ j (Finset.mem_filter.1 hj).2])
  rw [hout]
  have hin : ∏ j ∈ J, (if ω j then par j else 1 - par j) ≤
      ρ ^ J.card * ∏ j ∈ J, (if ω j then par' j else 1 - par' j) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun j _ => by split_ifs; exacts [(hpar j).1, by linarith [(hpar j).2]])
      (fun j hj => ?_)
    obtain ⟨h1, h2⟩ := hrat j hj
    split_ifs; exacts [h1, h2]
  have hout0 : 0 ≤ ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω j then par' j else 1 - par' j) :=
    Finset.prod_nonneg (fun j _ => by split_ifs; exacts [(hpar' j).1, by linarith [(hpar' j).2]])
  calc (∏ j ∈ J, (if ω j then par j else 1 - par j)) *
        ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω j then par' j else 1 - par' j)
      ≤ (ρ ^ J.card * ∏ j ∈ J, (if ω j then par' j else 1 - par' j)) *
        ∏ j ∈ Finset.univ.filter (fun j => ¬ j ∈ J), (if ω j then par' j else 1 - par' j) := by
        gcongr
    _ = _ := by ring

theorem fpr_le_of_par {par par' : ι → ℝ} (_hpar' : IsParam par') {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (h : ∀ ω, fpw par ω ≤ ρ * fpw par' ω) (A : Set (ι → Bool)) : fpr par A ≤ ρ * fpr par' A := by
  unfold fpr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  split_ifs
  · exact h ω
  · simp

end FiniteProduct

/-! ### Bernoulli(p) on finitely many bonds -/

set_option linter.deprecated false in
theorem bondLaw_cyl (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 Site)) (ξ : Sym2 Site → Bool) :
    bondLaw p hp (cylBonds F ξ) = ∏ b ∈ F, (if ξ b then (p : ℝ≥0∞) else 1 - p) := by
  have hset : cylBonds F ξ = Set.pi (↑F) (fun b => {ξ b}) := by
    ext ω; simp [cylBonds, Set.pi]
  rw [hset]
  unfold bondLaw
  have key := MeasureTheory.Measure.infinitePi_pi (μ := fun _ : Sym2 Site => External.bernoulli p hp)
    (s := F) (t := fun b => {ξ b}) (fun _ _ => MeasurableSet.of_discrete)
  refine key.trans ?_
  refine Finset.prod_congr rfl (fun b _ => ?_)
  unfold External.bernoulli
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete), PMF.bernoulli_apply]
  rcases ξ b with _ | _ <;> simp

theorem bondLaw_eq_sum (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) :
    bondLaw p hp E = ∑ ξ : ↥F → Bool,
      if extF F ξ ∈ E then ∏ b : ↥F, (if ξ b then (p : ℝ≥0∞) else 1 - p) else 0 := by
  have hunion : E = ⋃ ξ : ↥F → Bool, (E ∩ cylBonds F (extF F ξ)) := by
    rw [← Set.inter_iUnion, iUnion_cylBonds_extF, Set.inter_univ]
  conv_lhs => rw [hunion]
  rw [MeasureTheory.measure_iUnion (fun ξ ξ' hne => Set.disjoint_of_subset Set.inter_subset_right
      Set.inter_subset_right (cylBonds_extF_disjoint F hne))
    (fun ξ => (measurableSet_of_determined F hE).inter (measurableSet_cylBonds F _))]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [determined_inter_cyl F hE]
  split_ifs
  · rw [bondLaw_cyl, ← Finset.prod_coe_sort F]
    refine Fintype.prod_congr _ _ (fun b => ?_)
    simp [extF, b.2]
  · exact MeasureTheory.measure_empty

/-- The finite model of `bondLaw p` on the bonds `F`. -/
theorem bondLaw_toReal_eq_fpr (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 Site)) {E : Set BondConfig}
    (hE : BondDetermined F E) :
    (bondLaw p hp E).toReal = fpr (fun _ : ↥F => (p : ℝ)) {ξ | extF F ξ ∈ E} := by
  rw [bondLaw_eq_sum p hp F hE, ENNReal.toReal_sum (fun ξ _ => by
    split_ifs
    · exact ENNReal.prod_ne_top (fun b _ => by split_ifs <;> simp)
    · simp)]
  unfold fpr fpw
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  simp only [Set.mem_setOf_eq]
  split_ifs with h
  · rw [ENNReal.toReal_prod]
    refine Fintype.prod_congr _ _ (fun b => ?_)
    split_ifs
    · simp
    · rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp) ENNReal.one_ne_top]; simp
  · simp

end Rotor

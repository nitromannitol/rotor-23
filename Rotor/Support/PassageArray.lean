/-
The directional limits of the passage time, from Kingman's theorem
(`rotor.tex:1096-1113`, first half of the proof of `prop:passage-limit`):

  "Fix nonzero `z ∈ Λ`.  The stationary subadditive array
   `{τ(o+mz, o+nz) : 0 ≤ m < n}` has an integrable linear bound by
   `τ ≤ d_G` and the distance comparison.  The subadditive ergodic theorem
   gives, almost surely and in `L¹`, simultaneously for every base point and
   every `z ∈ Λ`, an a priori random limit `μ(z) := lim τ(o, o+nz)/n`."

The limit is made deterministic by the invariance of the law under the whole
lattice (`rotor.tex:1036-1040`).
-/
import Rotor.Support.Measurability
import Rotor.External.Kingman

open Finset MeasureTheory Filter Topology

namespace Rotor

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
variable (π : Mechanism G) (P : DoublyPeriodic G)

/-! ### The shift action on configurations -/

namespace DoublyPeriodic

omit [DecidableEq V] [G.LocallyFinite] in
theorem shiftConfig_val (z : ℤ × ℤ) (ρ : Config G) (v : V) :
    (P.shiftConfig z ρ v).1 = P.shift z (ρ (P.shift (-z) v)).1 := rfl

omit [DecidableEq V] [G.LocallyFinite] in
theorem shiftConfig_add (z w : ℤ × ℤ) (ρ : Config G) :
    P.shiftConfig z (P.shiftConfig w ρ) = P.shiftConfig (z + w) ρ := by
  funext v
  apply Subtype.ext
  simp only [shiftConfig_val]
  rw [← P.shift_add, neg_add, ← P.shift_add, add_comm (-w) (-z)]

omit [DecidableEq V] [G.LocallyFinite] in
theorem shiftConfig_zero (ρ : Config G) : P.shiftConfig 0 ρ = ρ := by
  funext v
  apply Subtype.ext
  simp only [shiftConfig_val]
  rw [neg_zero, P.shift_zero, P.shift_zero]

omit [DecidableEq V] in
theorem measurable_shiftConfig (z : ℤ × ℤ) : Measurable (P.shiftConfig z) := by
  refine measurable_pi_lambda _ (fun v => ?_)
  -- the coordinate at `v` is a function of the coordinate at `shift (-z) v`
  have : (fun ρ : Config G => P.shiftConfig z ρ v) =
      (fun a : G.neighborSet (P.shift (-z) v) =>
        (⟨P.shift z a.1, by
          have := (P.adj_shift z _ _).2 a.2
          rwa [P.shift_neg_shift] at this⟩ : G.neighborSet v)) ∘
      (fun ρ : Config G => ρ (P.shift (-z) v)) := by
    funext ρ; rfl
  rw [this]
  exact (measurable_of_finite _).comp (measurable_pi_apply _)

end DoublyPeriodic

/-! ### The passage-time array -/

/-- The array `τ(o + m z, o + n z)`. -/
noncomputable def arr (ρ : Config G) (o : V) (z : ℤ × ℤ) (m n : ℕ) : ℝ :=
  τ π ρ (P.shift (m • z) o) (P.shift (n • z) o)

/-- Stationarity: shifting the rotors by `-z` shifts the array. -/
theorem arr_shift (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (o : V) (z : ℤ × ℤ) (m n : ℕ) (ρ : Config G) :
    arr π P (P.shiftConfig (-z) ρ) o z m n = arr π P ρ o z (m + 1) (n + 1) := by
  unfold arr
  rw [← P.mechAut_act π hπ (-z)]
  have hs (k : ℕ) :
      P.shift (k • z) o =
        (P.mechAut π hπ (-z)).σ (P.shift ((k + 1) • z) o) := by
    rw [P.mechAut_σ, ← P.shift_add, succ_nsmul]
    congr 1
    abel
  rw [hs m, hs n, (P.mechAut π hπ (-z)).τ_act hAb hG]
theorem arr_subadd (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (o : V) (z : ℤ × ℤ) (l m n : ℕ) (ρ : Config G) :
    arr π P ρ o z l n ≤ arr π P ρ o z l m + arr π P ρ o z m n := by
  unfold arr
  exact_mod_cast τ_triangle π hAb hG ρ _ _ _

omit [G.LocallyFinite] in
theorem arr_nonneg (o : V) (z : ℤ × ℤ) (m n : ℕ) (ρ : Config G) : 0 ≤ arr π P ρ o z m n := by
  unfold arr; positivity

omit [DecidableEq V] [G.LocallyFinite] in
/-- Distances between lattice translates grow at most linearly. -/
theorem dist_shift_nsmul_le (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) (n : ℕ) :
    G.dist o (P.shift (n • z) o) ≤ n * G.dist o (P.shift z o) := by
  induction n with
  | zero => simp [P.shift_zero]
  | succ n ih =>
    have htri := hG.dist_triangle (u := o) (v := P.shift (n • z) o) (w := P.shift ((n + 1) • z) o)
    have h2 : G.dist (P.shift (n • z) o) (P.shift ((n + 1) • z) o) = G.dist o (P.shift z o) := by
      have := (P.mechAut π hπ (n • z)).dist_act hG o (P.shift z o)
      rw [P.mechAut_σ, P.mechAut_σ, ← P.shift_add] at this
      rw [← this]; congr 2; exact succ_nsmul z n
    rw [h2] at htri
    nlinarith

omit [G.LocallyFinite] in
theorem arr_le (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) (n : ℕ) (ρ : Config G) :
    arr π P ρ o z 0 n ≤ n * G.dist o (P.shift z o) := by
  unfold arr
  rw [zero_smul, P.shift_zero]
  have h1 := τ_le_dist π hG ρ o (P.shift (n • z) o)
  have h2 := dist_shift_nsmul_le π P hπ hG o z n
  exact_mod_cast h1.trans h2

theorem measurable_arr (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (o : V) (z : ℤ × ℤ) (m n : ℕ) :
    Measurable (fun ρ => arr π P ρ o z m n) := by
  haveI := countable_of_connected hG
  exact measurable_from_nat.comp (measurable_τ π hAb hG _ _)

/-- Each passage-array entry is integrable under a finite measure, since it is
measurable and bounded by the graph distance between its endpoints. -/
theorem integrable_arr (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (μ : Measure (Config G)) [IsFiniteMeasure μ] (o : V) (z : ℤ × ℤ) (m n : ℕ) :
    Integrable (fun ρ => arr π P ρ o z m n) μ := by
  refine (integrable_const
    (G.dist (P.shift (m • z) o) (P.shift (n • z) o) : ℝ)).mono'
      (measurable_arr π P hAb hG o z m n).aestronglyMeasurable ?_
  refine ae_of_all _ fun ρ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (arr_nonneg π P o z m n ρ)]
  unfold arr
  exact_mod_cast τ_le_dist π hG ρ (P.shift (m • z) o) (P.shift (n • z) o)

/-! ### Kingman's theorem in direction `z` -/

/-- The directional limit from Kingman's theorem: an a priori random,
`θ`-invariant limit. -/
theorem exists_dirLimit (hK : External.Kingman.{u}) (hπ : P.Periodic π) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (hinv : P.Invariant μ) (o : V) (z : ℤ × ℤ) :
    ∃ γ : Config G → ℝ, Measurable γ ∧ (∀ᵐ ρ ∂μ, γ (P.shiftConfig (-z) ρ) = γ ρ) ∧
      ∀ᵐ ρ ∂μ, Tendsto (fun n : ℕ => arr π P ρ o z 0 n / n) atTop (𝓝 (γ ρ)) := by
  refine hK μ inferInstance (P.shiftConfig (-z)) (hinv (-z)) (fun m n ρ => arr π P ρ o z m n)
    (fun m n => measurable_arr π P hAb hG o z m n)
    (fun m n => integrable_arr π P hAb hG μ o z m n)
    (fun m n ρ => arr_nonneg π P o z m n ρ)
    (fun m n ρ => arr_shift π P hπ hAb hG o z m n ρ)
    (fun l m n ρ _ _ => arr_subadd π P hAb hG o z l m n ρ)
    ⟨G.dist o (P.shift z o), fun n => ?_⟩
  have hb : ∀ᵐ ρ ∂μ, ‖arr π P ρ o z 0 n‖ ≤ n * G.dist o (P.shift z o) :=
    ae_of_all _ (fun ρ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (arr_nonneg π P o z 0 n ρ)]
      exact arr_le π P hπ hG o z n ρ)
  have := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one] at this
  calc ∫ ρ, arr π P ρ o z 0 n ∂μ ≤ ‖∫ ρ, arr π P ρ o z 0 n ∂μ‖ := Real.le_norm_self _
    _ ≤ n * G.dist o (P.shift z o) := this
    _ = G.dist o (P.shift z o) * n := by ring

/-! ### The limit is invariant under every lattice shift -/

/-- `eq:passage-four-endpoints`. -/
theorem τ_four (hAb : External.Abelian G) [Infinite V] (hG : G.Connected) (ρ : Config G)
    (x₁ x₂ y₁ y₂ : V) :
    |(τ π ρ x₁ y₁ : ℝ) - τ π ρ x₂ y₂| ≤ G.dist x₁ x₂ + G.dist y₁ y₂ := by
  have key (x x' y y' : V) :
      (τ π ρ x y : ℝ) ≤ τ π ρ x' y' + G.dist x x' + G.dist y y' := by
    have ht := (τ_triangle π hAb hG ρ x x' y).trans
      (add_le_add le_rfl (τ_triangle π hAb hG ρ x' y' y))
    have hd := add_le_add (τ_le_dist π hG ρ x x')
      (add_le_add (le_refl (τ π ρ x' y')) (τ_le_dist π hG ρ y' y))
    have hb := ht.trans hd
    rw [G.dist_comm (u := y') (v := y)] at hb
    exact_mod_cast (by
      simpa only [add_assoc, add_comm, add_left_comm] using hb :
      τ π ρ x y ≤ τ π ρ x' y' + G.dist x x' + G.dist y y')
  rw [abs_le]
  have h₁ := key x₁ x₂ y₁ y₂
  have h₂ := key x₂ x₁ y₂ y₁
  rw [G.dist_comm (u := x₂), G.dist_comm (u := y₂)] at h₂
  constructor <;> linarith only [h₁, h₂]
/-- The array from `o` at the shifted rotors is the array from `shift (-w) o`. -/
theorem arr_shiftConfig (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o : V) (z w : ℤ × ℤ) (n : ℕ) :
    arr π P (P.shiftConfig w ρ) o z 0 n = arr π P ρ (P.shift (-w) o) z 0 n := by
  unfold arr
  rw [← P.mechAut_act π hπ w]
  have hs (u : ℤ × ℤ) :
      P.shift u o = (P.mechAut π hπ w).σ (P.shift u (P.shift (-w) o)) := by
    rw [P.mechAut_σ, ← P.shift_add, ← P.shift_add]
    congr 1
    abel
  rw [hs (0 • z), hs (n • z), (P.mechAut π hπ w).τ_act hAb hG]
/-- The arrays from two base points differ by a bounded amount. -/
theorem arr_base_diff (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o o' : V) (z : ℤ × ℤ) (n : ℕ) :
    |arr π P ρ o z 0 n - arr π P ρ o' z 0 n| ≤ 2 * G.dist o o' := by
  simpa only [arr, zero_smul, P.shift_zero,
    ← P.mechAut_σ π hπ (n • z),
    (P.mechAut π hπ (n • z)).dist_act hG, two_mul] using
    τ_four π hAb hG ρ o o'
      (P.shift (n • z) o) (P.shift (n • z) o')
/-- The limit of the array from any base point is the same. -/
theorem tendsto_arr_of_base (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o o' : V) (z : ℤ × ℤ) (c : ℝ)
    (h : Tendsto (fun n : ℕ => (arr π P ρ o z 0 n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (arr π P ρ o' z 0 n : ℝ) / n) atTop (𝓝 c) := by
  have hdiff : Tendsto
      (fun n : ℕ => (arr π P ρ o' z 0 n - arr π P ρ o z 0 n) / n)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (2 * (G.dist o o' : ℝ)))
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    simpa only [abs_sub_comm] using
      arr_base_diff π P hπ hAb hG ρ o o' z n
  simpa only [sub_div, add_sub_cancel, add_zero] using h.add hdiff
theorem dirLimit_shift_invariant (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (μ : Measure (Config G)) (hinv : P.Invariant μ) (o : V) (z w : ℤ × ℤ)
    (γ : Config G → ℝ)
    (hγ : ∀ᵐ ρ ∂μ, Tendsto (fun n : ℕ => (arr π P ρ o z 0 n : ℝ) / n) atTop (𝓝 (γ ρ))) :
    ∀ᵐ ρ ∂μ, γ (P.shiftConfig w ρ) = γ ρ := by
  have h3 : ∀ᵐ ρ ∂μ, Tendsto (fun n : ℕ => (arr π P (P.shiftConfig w ρ) o z 0 n : ℝ) / n) atTop
      (𝓝 (γ (P.shiftConfig w ρ))) := (hinv w).quasiMeasurePreserving.ae hγ
  filter_upwards [hγ, h3] with ρ hρ hρ'
  simp only [arr_shiftConfig π P hπ hAb hG ρ o z w] at hρ'
  exact tendsto_nhds_unique hρ' (tendsto_arr_of_base π P hπ hAb hG ρ o _ z _ hρ)

/-! ### An invariant function is almost surely constant -/

omit [DecidableEq V] in
/-- Under an ergodic lattice action, a measurable real function that is
almost surely invariant under every shift is almost surely constant. -/
theorem ae_const_of_shift_invariant (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (herg : P.Ergodic μ) (γ : Config G → ℝ) (hγ : Measurable γ)
    (hinvγ : ∀ w : ℤ × ℤ, ∀ᵐ ρ ∂μ, γ (P.shiftConfig w ρ) = γ ρ) :
    ∃ c : ℝ, ∀ᵐ ρ ∂μ, γ ρ = c := by
  refine Filter.exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_
  intro U hU
  let A : Set (Config G) := ⋂ w : ℤ × ℤ, (γ ∘ P.shiftConfig w) ⁻¹' U
  have hAm : MeasurableSet A :=
    MeasurableSet.iInter fun w => (hγ.comp (P.measurable_shiftConfig w)) hU
  have hAi : ∀ u, P.shiftConfig u ⁻¹' A = A := by
    intro u
    ext ρ
    simp only [A, Set.mem_preimage, Set.mem_iInter, Function.comp_apply]
    constructor
    · intro h w
      simpa only [P.shiftConfig_add, sub_add_cancel] using h (w - u)
    · intro h w
      simpa only [P.shiftConfig_add] using h (w + u)
  rcases herg A hAm hAi with h0 | h1
  · right
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0,
      ae_all_iff.2 hinvγ] with ρ hn hρ
    intro hmem
    apply hn
    exact Set.mem_iInter.2 fun w => by
      simpa only [Set.mem_preimage, Function.comp_apply, hρ w] using hmem
  · left
    filter_upwards [(mem_ae_iff_prob_eq_one hAm).2 h1] with ρ hρ
    simpa only [Set.mem_preimage, Function.comp_apply, P.shiftConfig_zero] using
      Set.mem_iInter.1 hρ (0 : ℤ × ℤ)
/-! ### The directional constants -/

/-- `c` is the almost sure directional limit of the passage time in the lattice direction `z`,
simultaneously from every base point. -/
def IsDirLimit (μ : Measure (Config G)) (z : ℤ × ℤ) (c : ℝ) : Prop :=
  ∀ᵐ ρ ∂μ, ∀ o : V, Tendsto (fun n : ℕ => (arr π P ρ o z 0 n : ℝ) / n) atTop (𝓝 c)

/-- Existence of the deterministic directional limit (Kingman plus ergodicity). -/
theorem exists_isDirLimit (hK : External.Kingman.{u}) (hπ : P.Periodic π) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (hinv : P.Invariant μ) (herg : P.Ergodic μ) (z : ℤ × ℤ) : ∃ c : ℝ, IsDirLimit π P μ z c := by
  obtain ⟨o₀⟩ : Nonempty V := inferInstance
  obtain ⟨γ, hγm, -, hγlim⟩ :=
    exists_dirLimit π P hK hπ hAb hG μ hinv o₀ z
  obtain ⟨c, hc⟩ := ae_const_of_shift_invariant P μ herg γ hγm
    (fun w => dirLimit_shift_invariant π P hπ hAb hG μ hinv o₀ z w γ hγlim)
  refine ⟨c, ?_⟩
  filter_upwards [hγlim, hc] with ρ hρ hρc
  rw [hρc] at hρ
  exact fun o => tendsto_arr_of_base π P hπ hAb hG ρ o₀ o z c hρ
omit [DecidableEq V] [G.LocallyFinite] in
/-- A property holding almost surely holds at some point. -/
theorem exists_of_ae (μ : Measure (Config G)) [IsProbabilityMeasure μ] {p : Config G → Prop}
    (h : ∀ᵐ ρ ∂μ, p ρ) : ∃ ρ, p ρ := by
  exact h.exists
omit [G.LocallyFinite] in
theorem IsDirLimit.unique [Infinite V] (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    {z : ℤ × ℤ} {c c' : ℝ} (h : IsDirLimit π P μ z c) (h' : IsDirLimit π P μ z c') : c = c' := by
  obtain ⟨o⟩ : Nonempty V := inferInstance
  obtain ⟨ρ, hρ, hρ'⟩ := exists_of_ae μ (h.and h')
  exact tendsto_nhds_unique (hρ o) (hρ' o)

omit [G.LocallyFinite] in
theorem IsDirLimit.nonneg [Infinite V] (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    {z : ℤ × ℤ} {c : ℝ} (h : IsDirLimit π P μ z c) : 0 ≤ c := by
  obtain ⟨o⟩ : Nonempty V := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_of_ae μ h
  exact ge_of_tendsto' (hρ o) (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [G.LocallyFinite] in
/-- The array divided by `n` is at most the distance to the unit translate. -/
theorem arr_div_le (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) (n : ℕ)
    (ρ : Config G) : (arr π P ρ o z 0 n : ℝ) / n ≤ G.dist o (P.shift z o) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_iff₀ (by exact_mod_cast hn)]
    have := arr_le π P hπ hG o z n ρ
    exact_mod_cast (this.trans (le_of_eq (mul_comm _ _)))

omit [G.LocallyFinite] in
theorem IsDirLimit.le_dist [Infinite V] (hπ : P.Periodic π) (hG : G.Connected)
    (μ : Measure (Config G)) [IsProbabilityMeasure μ] {z : ℤ × ℤ} {c : ℝ}
    (h : IsDirLimit π P μ z c) (o : V) : c ≤ G.dist o (P.shift z o) := by
  obtain ⟨ρ, hρ⟩ := exists_of_ae μ h
  exact le_of_tendsto' (hρ o) (fun n => arr_div_le π P hπ hG o z n ρ)

omit [G.LocallyFinite] in
theorem τ_self (hG : G.Connected) (ρ : Config G) (x : V) : τ π ρ x x = 0 := by
  have := τ_le_dist π hG ρ x x
  rwa [SimpleGraph.dist_self, Nat.le_zero] at this

omit [G.LocallyFinite] in
theorem isDirLimit_zero (hG : G.Connected) (μ : Measure (Config G)) : IsDirLimit π P μ 0 0 := by
  refine ae_of_all _ fun ρ o => ?_
  simpa only [arr, smul_zero, P.shift_zero, τ_self π hG,
    Nat.cast_zero, zero_div] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
omit [G.LocallyFinite] in
theorem arr_nsmul (o : V) (z : ℤ × ℤ) (k n : ℕ) (ρ : Config G) :
    arr π P ρ o (k • z) 0 n = arr π P ρ o z 0 (k * n) := by
  simp only [arr, zero_smul, mul_nsmul]

omit [G.LocallyFinite] in
theorem IsDirLimit.nsmul (hG : G.Connected) (μ : Measure (Config G)) {z : ℤ × ℤ} {c : ℝ}
    (h : IsDirLimit π P μ z c) (k : ℕ) : IsDirLimit π P μ (k • z) (k * c) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using isDirLimit_zero π P hG μ
  filter_upwards [h] with ρ hρ
  intro o
  have hmul : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => hn.trans (Nat.le_mul_of_pos_left n hk)⟩)
  have := ((hρ o).comp hmul).const_mul (k : ℝ)
  refine this.congr (fun n => ?_)
  simp only [Function.comp, arr_nsmul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · push_cast
    field_simp

/-- The lattice shift as a measurable equivalence of configurations. -/
def shiftEquiv (z : ℤ × ℤ) : Config G ≃ᵐ Config G where
  toFun := P.shiftConfig z
  invFun := P.shiftConfig (-z)
  left_inv ρ := by rw [P.shiftConfig_add, neg_add_cancel, P.shiftConfig_zero]
  right_inv ρ := by rw [P.shiftConfig_add, add_neg_cancel, P.shiftConfig_zero]
  measurable_toFun := P.measurable_shiftConfig z
  measurable_invFun := P.measurable_shiftConfig (-z)

omit [DecidableEq V] in
/-- The expectation of a function of the shifted rotors. -/
theorem integral_shiftConfig (μ : Measure (Config G)) (hinv : P.Invariant μ) (z : ℤ × ℤ)
    (g : Config G → ℝ) : ∫ ρ, g (P.shiftConfig z ρ) ∂μ = ∫ ρ, g ρ ∂μ :=
  MeasurePreserving.integral_comp' (f := shiftEquiv P z) (hinv z) g

/-- The passage time between translates of the base point, as seen from the base point. -/
theorem τ_shift_shift (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o : V) (u w : ℤ × ℤ) :
    τ π ρ (P.shift u o) (P.shift u (P.shift w o)) = τ π (P.shiftConfig (-u) ρ) o (P.shift w o) := by
  have := (P.mechAut π hπ u).τ_act hAb hG (P.shiftConfig (-u) ρ) o (P.shift w o)
  rw [P.mechAut_act, P.mechAut_σ, P.mechAut_σ, P.shiftConfig_add, add_neg_cancel,
    P.shiftConfig_zero] at this
  exact this

theorem integrable_arr_div (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ] (o : V) (z : ℤ × ℤ)
    (n : ℕ) : Integrable (fun ρ => (arr π P ρ o z 0 n : ℝ) / n) μ := by
  refine (integrable_const (G.dist o (P.shift z o) : ℝ)).mono' ?_ (ae_of_all _ (fun ρ => ?_))
  · exact ((measurable_arr π P hAb hG o z 0 n).div_const _).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact arr_div_le π P hπ hG o z n ρ

/-- The expectations converge to the directional constant. -/
theorem IsDirLimit.tendsto_integral [Infinite V] (hπ : P.Periodic π) (hAb : External.Abelian G)
    (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ] {z : ℤ × ℤ} {c : ℝ}
    (h : IsDirLimit π P μ z c) (o : V) :
    Tendsto (fun n : ℕ => ∫ ρ, (arr π P ρ o z 0 n : ℝ) / n ∂μ) atTop (𝓝 c) := by
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ρ => (arr π P ρ o z 0 n : ℝ) / n) (f := fun _ => c)
    (fun _ => (G.dist o (P.shift z o) : ℝ))
    (fun n => ((measurable_arr π P hAb hG o z 0 n).div_const _).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ (fun ρ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      exact arr_div_le π P hπ hG o z n ρ))
    (by filter_upwards [h] with ρ hρ using hρ o)
  simpa using this

/-- Subadditivity of the directional constants. -/
theorem IsDirLimit.add_le [Infinite V] (hπ : P.Periodic π) (hAb : External.Abelian G)
    (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ] (hinv : P.Invariant μ)
    {z w : ℤ × ℤ} {c d e : ℝ} (hz : IsDirLimit π P μ z c) (hw : IsDirLimit π P μ w d)
    (hzw : IsDirLimit π P μ (z + w) e) : e ≤ c + d := by
  obtain ⟨o⟩ : Nonempty V := inferInstance
  refine le_of_tendsto_of_tendsto' (hzw.tendsto_integral π P hπ hAb hG μ o)
    ((hz.tendsto_integral π P hπ hAb hG μ o).add
      (hw.tendsto_integral π P hπ hAb hG μ o)) fun n => ?_
  have iz := integrable_arr_div π P hπ hAb hG μ o z n
  have iw : Integrable
      (fun ρ => arr π P (P.shiftConfig (-(n • z)) ρ) o w 0 n / n) μ :=
    (hinv (-(n • z))).integrable_comp_of_integrable
      (integrable_arr_div π P hπ hAb hG μ o w n)
  calc
    ∫ ρ, arr π P ρ o (z + w) 0 n / n ∂μ
        ≤ ∫ ρ, arr π P ρ o z 0 n / n +
          arr π P (P.shiftConfig (-(n • z)) ρ) o w 0 n / n ∂μ := by
      refine integral_mono
        (integrable_arr_div π P hπ hAb hG μ o (z + w) n)
        (iz.add iw) fun ρ => ?_
      simp only [arr, zero_smul, P.shift_zero, ← add_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [← τ_shift_shift π P hπ hAb hG ρ o (n • z) (n • w),
        smul_add, P.shift_add]
      exact_mod_cast τ_triangle π hAb hG ρ o (P.shift (n • z) o)
        (P.shift (n • z) (P.shift (n • w) o))
    _ = _ := by
      rw [integral_add iz iw,
        integral_shiftConfig P μ hinv (-(n • z))
          (fun ρ => arr π P ρ o w 0 n / n)]
end Rotor


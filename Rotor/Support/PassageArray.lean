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
  have h1 : P.shift (m • z) o = (P.mechAut π hπ (-z)).σ (P.shift ((m + 1) • z) o) := by
    rw [P.mechAut_σ, ← P.shift_add]; congr 1
    rw [succ_nsmul]; abel
  have h2 : P.shift (n • z) o = (P.mechAut π hπ (-z)).σ (P.shift ((n + 1) • z) o) := by
    rw [P.mechAut_σ, ← P.shift_add]; congr 1
    rw [succ_nsmul]; abel
  rw [h1, h2, (P.mechAut π hπ (-z)).τ_act hAb hG]

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

/-! ### Kingman's theorem in direction `z` -/

/-- The directional limit from Kingman's theorem: an a priori random,
`θ`-invariant limit. -/
theorem exists_dirLimit (hK : External.Kingman.{u}) (hπ : P.Periodic π) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (hinv : P.Invariant μ) (o : V) (z : ℤ × ℤ) :
    ∃ γ : Config G → ℝ, Measurable γ ∧ (∀ᵐ ρ ∂μ, γ (P.shiftConfig (-z) ρ) = γ ρ) ∧
      ∀ᵐ ρ ∂μ, Tendsto (fun n : ℕ => arr π P ρ o z 0 n / n) atTop (𝓝 (γ ρ)) := by
  refine hK μ inferInstance (P.shiftConfig (-z)) (hinv (-z)) (fun m n ρ => arr π P ρ o z m n)
    (fun m n => measurable_arr π P hAb hG o z m n) (fun m n ρ => arr_nonneg π P o z m n ρ)
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
  have h1 := τ_triangle π hAb hG ρ x₁ x₂ y₁
  have h2 := τ_triangle π hAb hG ρ x₂ y₂ y₁
  have h3 := τ_triangle π hAb hG ρ x₂ x₁ y₂
  have h4 := τ_triangle π hAb hG ρ x₁ y₁ y₂
  have d1 := τ_le_dist π hG ρ x₁ x₂
  have d2 := τ_le_dist π hG ρ y₂ y₁
  have d3 := τ_le_dist π hG ρ x₂ x₁
  have d4 := τ_le_dist π hG ρ y₁ y₂
  have s1 := G.dist_comm (u := x₁) (v := x₂)
  have s2 := G.dist_comm (u := y₁) (v := y₂)
  have h1' : (τ π ρ x₁ y₁ : ℝ) ≤ τ π ρ x₁ x₂ + τ π ρ x₂ y₁ := by exact_mod_cast h1
  have h2' : (τ π ρ x₂ y₁ : ℝ) ≤ τ π ρ x₂ y₂ + τ π ρ y₂ y₁ := by exact_mod_cast h2
  have h3' : (τ π ρ x₂ y₂ : ℝ) ≤ τ π ρ x₂ x₁ + τ π ρ x₁ y₂ := by exact_mod_cast h3
  have h4' : (τ π ρ x₁ y₂ : ℝ) ≤ τ π ρ x₁ y₁ + τ π ρ y₁ y₂ := by exact_mod_cast h4
  have d1' : (τ π ρ x₁ x₂ : ℝ) ≤ G.dist x₁ x₂ := by exact_mod_cast d1
  have d2' : (τ π ρ y₂ y₁ : ℝ) ≤ G.dist y₂ y₁ := by exact_mod_cast d2
  have d3' : (τ π ρ x₂ x₁ : ℝ) ≤ G.dist x₂ x₁ := by exact_mod_cast d3
  have d4' : (τ π ρ y₁ y₂ : ℝ) ≤ G.dist y₁ y₂ := by exact_mod_cast d4
  have s1' : (G.dist x₁ x₂ : ℝ) = G.dist x₂ x₁ := by exact_mod_cast s1
  have s2' : (G.dist y₁ y₂ : ℝ) = G.dist y₂ y₁ := by exact_mod_cast s2
  rw [abs_le]
  constructor <;> linarith

/-- The array from `o` at the shifted rotors is the array from `shift (-w) o`. -/
theorem arr_shiftConfig (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o : V) (z w : ℤ × ℤ) (n : ℕ) :
    arr π P (P.shiftConfig w ρ) o z 0 n = arr π P ρ (P.shift (-w) o) z 0 n := by
  unfold arr
  rw [← P.mechAut_act π hπ w]
  have e1 : P.shift (0 • z) o = (P.mechAut π hπ w).σ (P.shift (0 • z) (P.shift (-w) o)) := by
    rw [P.mechAut_σ, ← P.shift_add, ← P.shift_add]; congr 1; abel
  have e2 : P.shift (n • z) o = (P.mechAut π hπ w).σ (P.shift (n • z) (P.shift (-w) o)) := by
    rw [P.mechAut_σ, ← P.shift_add, ← P.shift_add]; congr 1; abel
  rw [e1, e2, (P.mechAut π hπ w).τ_act hAb hG]

/-- The arrays from two base points differ by a bounded amount. -/
theorem arr_base_diff (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o o' : V) (z : ℤ × ℤ) (n : ℕ) :
    |arr π P ρ o z 0 n - arr π P ρ o' z 0 n| ≤ 2 * G.dist o o' := by
  unfold arr
  have := τ_four π hAb hG ρ (P.shift (0 • z) o) (P.shift (0 • z) o') (P.shift (n • z) o)
    (P.shift (n • z) o')
  have h0 : G.dist (P.shift (0 • z) o) (P.shift (0 • z) o') = G.dist o o' := by
    simp [P.shift_zero]
  have hn : G.dist (P.shift (n • z) o) (P.shift (n • z) o') = G.dist o o' := by
    have := (P.mechAut π hπ (n • z)).dist_act hG o o'
    simpa [P.mechAut_σ] using this
  rw [h0, hn] at this
  linarith

/-- The limit of the array from any base point is the same. -/
theorem tendsto_arr_of_base (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o o' : V) (z : ℤ × ℤ) (c : ℝ)
    (h : Tendsto (fun n : ℕ => (arr π P ρ o z 0 n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (arr π P ρ o' z 0 n : ℝ) / n) atTop (𝓝 c) := by
  have hdiff : Tendsto (fun n : ℕ => ((arr π P ρ o' z 0 n : ℝ) - arr π P ρ o z 0 n) / n) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 * (G.dist o o' : ℝ)))
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
      have := arr_base_diff π P hπ hAb hG ρ o' o z n
      rwa [G.dist_comm] at this
  have := h.add hdiff
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  rw [← add_div]; ring_nf

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
  -- the exactly invariant version of `{γ ≤ q}`
  let A : ℚ → Set (Config G) := fun q => ⋂ w : ℤ × ℤ, (γ ∘ P.shiftConfig w) ⁻¹' Set.Iic (q : ℝ)
  have hAmem : ∀ q ρ, ρ ∈ A q ↔ ∀ w : ℤ × ℤ, γ (P.shiftConfig w ρ) ≤ q := fun q ρ => by
    simp only [A, Set.mem_iInter, Set.mem_preimage, Function.comp, Set.mem_Iic]
  have hAmeas : ∀ q, MeasurableSet (A q) := fun q =>
    MeasurableSet.iInter (fun w => (hγ.comp (P.measurable_shiftConfig w)) measurableSet_Iic)
  have hAinv : ∀ q u, P.shiftConfig u ⁻¹' A q = A q := by
    intro q u
    ext ρ
    simp only [Set.mem_preimage, hAmem]
    constructor
    · intro h w
      have := h (w - u)
      rwa [P.shiftConfig_add, sub_add_cancel] at this
    · intro h w
      rw [P.shiftConfig_add]
      exact h _
  have hall : ∀ᵐ ρ ∂μ, ∀ w : ℤ × ℤ, γ (P.shiftConfig w ρ) = γ ρ := ae_all_iff.2 hinvγ
  have hAeq : ∀ q : ℚ, μ {ρ | γ ρ ≤ q} = μ (A q) := by
    intro q
    apply measure_congr
    filter_upwards [hall] with ρ hρ
    show (γ ρ ≤ q) = (ρ ∈ A q)
    rw [hAmem]
    apply propext
    exact ⟨fun h w => by rw [hρ w]; exact h, fun h => by have := h 0; rwa [hρ 0] at this⟩
  have F01 : ∀ q : ℚ, μ {ρ | γ ρ ≤ q} = 0 ∨ μ {ρ | γ ρ ≤ q} = 1 := fun q => by
    rw [hAeq]; exact herg (A q) (hAmeas q) (hAinv q)
  have Fmono : ∀ q q' : ℚ, q ≤ q' → μ {ρ | γ ρ ≤ q} ≤ μ {ρ | γ ρ ≤ q'} := fun q q' h =>
    measure_mono (fun ρ (hρ : γ ρ ≤ q) => show γ ρ ≤ q' from le_trans hρ (by exact_mod_cast h))
  -- some threshold has full measure, some has measure zero
  have hex1 : ∃ q : ℚ, μ {ρ | γ ρ ≤ q} = 1 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∀ q : ℚ, μ {ρ | γ ρ ≤ q} = 0 := fun q => (F01 q).resolve_right (hcon q)
    have : μ (⋃ q : ℚ, {ρ | γ ρ ≤ q}) = 0 := measure_iUnion_null h0
    have huniv : (⋃ q : ℚ, {ρ | γ ρ ≤ q}) = Set.univ := by
      ext ρ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      obtain ⟨q, hq⟩ := exists_rat_gt (γ ρ)
      exact ⟨q, hq.le⟩
    rw [huniv, measure_univ] at this
    exact one_ne_zero this
  have hex0 : ∃ q : ℚ, μ {ρ | γ ρ ≤ q} = 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∀ q : ℚ, μ {ρ | γ ρ ≤ q} = 1 := fun q => (F01 q).resolve_left (hcon q)
    -- the sets `{γ ≤ -n}` decrease to `∅`
    have hanti : Antitone (fun n : ℕ => {ρ : Config G | γ ρ ≤ ((-(n : ℚ) : ℚ) : ℝ)}) := by
      intro m n hmn ρ hρ
      simp only [Set.mem_setOf_eq] at hρ ⊢
      have : ((-(n : ℚ) : ℚ) : ℝ) ≤ ((-(m : ℚ) : ℚ) : ℝ) := by push_cast; linarith [(Nat.cast_le (α := ℝ)).2 hmn]
      linarith
    have hinter : (⋂ n : ℕ, {ρ : Config G | γ ρ ≤ ((-(n : ℚ) : ℚ) : ℝ)}) = ∅ := by
      ext ρ
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(γ ρ))
      exact ⟨n, by push_cast; linarith⟩
    have := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ => {ρ : Config G | γ ρ ≤ ((-(n : ℚ) : ℚ) : ℝ)})
      (fun n => (measurableSet_le hγ measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at this
    have hconst : (⇑μ ∘ fun n : ℕ => {ρ : Config G | γ ρ ≤ ((-(n : ℚ) : ℚ) : ℝ)}) = fun _ => 1 :=
      funext (fun n => h1 _)
    rw [hconst] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)
  obtain ⟨q₁, hq₁⟩ := hex1
  obtain ⟨q₀, hq₀⟩ := hex0
  -- the threshold
  set Q : Set ℝ := {x | ∃ q : ℚ, x = q ∧ μ {ρ | γ ρ ≤ q} = 1} with hQ
  have hQne : Q.Nonempty := ⟨q₁, q₁, rfl, hq₁⟩
  have hQbdd : BddBelow Q := by
    refine ⟨q₀, ?_⟩
    rintro x ⟨q, rfl, hq⟩
    by_contra hlt
    push_neg at hlt
    have hle : q ≤ q₀ := by exact_mod_cast hlt.le
    have := Fmono q q₀ hle
    rw [hq, hq₀] at this
    exact absurd this (by simp)
  refine ⟨sInf Q, ?_⟩
  -- a.s. `γ ≤ sInf Q`: for every rational `q > sInf Q`, a.s. `γ ≤ q`
  have hup : ∀ q : ℚ, sInf Q < q → μ {ρ | γ ρ ≤ q} = 1 := by
    intro q hq
    obtain ⟨x, ⟨q', rfl, hq'⟩, hlt⟩ := exists_lt_of_csInf_lt hQne hq
    have hle : q' ≤ q := by exact_mod_cast hlt.le
    have := Fmono q' q hle
    rw [hq'] at this
    exact le_antisymm prob_le_one this
  have hdown : ∀ q : ℚ, (q : ℝ) < sInf Q → μ {ρ | γ ρ ≤ q} = 0 := by
    intro q hq
    rcases F01 q with h | h
    · exact h
    · exfalso
      have : sInf Q ≤ q := csInf_le hQbdd ⟨q, rfl, h⟩
      linarith
  have hae1 : ∀ᵐ ρ ∂μ, ∀ q : ℚ, sInf Q < q → γ ρ ≤ q := by
    rw [ae_all_iff]
    intro q
    by_cases hq : sInf Q < q
    · have := hup q hq
      have h0 : μ {ρ | γ ρ ≤ q}ᶜ = 0 :=
        (prob_compl_eq_zero_iff (measurableSet_le hγ measurable_const)).2 this
      rw [ae_iff]
      refine measure_mono_null ?_ h0
      intro ρ hρ
      simp only [Set.mem_setOf_eq, Classical.not_imp, not_le] at hρ
      exact fun h => absurd h (not_le.2 hρ.2)
    · exact ae_of_all _ (fun ρ h => absurd h hq)
  have hae0 : ∀ᵐ ρ ∂μ, ∀ q : ℚ, (q : ℝ) < sInf Q → (q : ℝ) < γ ρ := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) < sInf Q
    · have := hdown q hq
      rw [ae_iff]
      refine measure_mono_null ?_ this
      intro ρ hρ
      simp only [Set.mem_setOf_eq, Classical.not_imp, not_lt] at hρ
      exact hρ.2
    · exact ae_of_all _ (fun ρ h => absurd h hq)
  filter_upwards [hae1, hae0] with ρ h1 h0
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact absurd (h1 q hq1) (not_le.2 hq2)
  · by_contra hlt
    push_neg at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact absurd (h0 q hq2) (not_lt.2 hq1.le)

/-! ### The directional constants -/

/-- `c` is the almost sure directional limit of the passage time in the lattice direction `z`,
simultaneously from every base point. -/
def IsDirLimit (μ : Measure (Config G)) (z : ℤ × ℤ) (c : ℝ) : Prop :=
  ∀ᵐ ρ ∂μ, ∀ o : V, Tendsto (fun n : ℕ => (arr π P ρ o z 0 n : ℝ) / n) atTop (𝓝 c)

/-- Existence of the deterministic directional limit (Kingman plus ergodicity). -/
theorem exists_isDirLimit (hK : External.Kingman.{u}) (hπ : P.Periodic π) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (hinv : P.Invariant μ) (herg : P.Ergodic μ) (z : ℤ × ℤ) : ∃ c : ℝ, IsDirLimit π P μ z c := by
  haveI : Countable V := countable_of_connected hG
  obtain ⟨o₀⟩ : Nonempty V := inferInstance
  obtain ⟨γ, hγm, -, hγlim⟩ := exists_dirLimit π P hK hπ hAb hG μ hinv o₀ z
  have hinvw : ∀ w, ∀ᵐ ρ ∂μ, γ (P.shiftConfig w ρ) = γ ρ := fun w =>
    dirLimit_shift_invariant π P hπ hAb hG μ hinv o₀ z w γ hγlim
  obtain ⟨c, hc⟩ := ae_const_of_shift_invariant P μ herg γ hγm hinvw
  refine ⟨c, ?_⟩
  rw [IsDirLimit, ae_all_iff]
  intro o
  filter_upwards [hγlim, hc] with ρ hρ hρc
  rw [hρc] at hρ
  exact tendsto_arr_of_base π P hπ hAb hG ρ o₀ o z c hρ

omit [DecidableEq V] [G.LocallyFinite] in
/-- A property holding almost surely holds at some point. -/
theorem exists_of_ae (μ : Measure (Config G)) [IsProbabilityMeasure μ] {p : Config G → Prop}
    (h : ∀ᵐ ρ ∂μ, p ρ) : ∃ ρ, p ρ := by
  haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
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
  refine ae_of_all _ (fun ρ o => ?_)
  have : (fun n : ℕ => (arr π P ρ o 0 0 n : ℝ) / n) = fun _ => 0 := by
    funext n
    simp [arr, P.shift_zero, τ_self π hG]
  rw [this]
  exact tendsto_const_nhds

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
    ((hz.tendsto_integral π P hπ hAb hG μ o).add (hw.tendsto_integral π P hπ hAb hG μ o))
    (fun n => ?_)
  -- the `w`-part from the translated base point has the same expectation
  have hw' : ∫ ρ, (arr π P ρ o w 0 n : ℝ) / n ∂μ =
      ∫ ρ, (τ π ρ (P.shift (n • z) o) (P.shift (n • z) (P.shift (n • w) o)) : ℝ) / n ∂μ := by
    rw [← integral_shiftConfig P μ hinv (-(n • z))]
    congr 1
    funext ρ
    rw [τ_shift_shift π P hπ hAb hG ρ o (n • z) (n • w)]
    simp only [arr, zero_smul, P.shift_zero]
  have hint : Integrable
      (fun ρ => (τ π ρ (P.shift (n • z) o) (P.shift (n • z) (P.shift (n • w) o)) : ℝ) / n) μ := by
    have := integrable_arr_div π P hπ hAb hG μ o w n
    rw [← integral_shiftConfig P μ hinv (-(n • z))] at hw'
    have h2 : (fun ρ => (τ π ρ (P.shift (n • z) o) (P.shift (n • z) (P.shift (n • w) o)) : ℝ) / n) =
        (fun ρ => (arr π P ρ o w 0 n : ℝ) / n) ∘ P.shiftConfig (-(n • z)) := by
      funext ρ
      simp only [Function.comp, arr, zero_smul, P.shift_zero]
      rw [τ_shift_shift π P hπ hAb hG ρ o (n • z) (n • w)]
    rw [h2]
    exact ((hinv _).integrable_comp this.aestronglyMeasurable).2 this
  rw [hw', ← integral_add (integrable_arr_div π P hπ hAb hG μ o z n) hint]
  refine integral_mono (integrable_arr_div π P hπ hAb hG μ o (z + w) n)
    ((integrable_arr_div π P hπ hAb hG μ o z n).add hint) (fun ρ => ?_)
  simp only [arr, zero_smul, P.shift_zero, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have := τ_triangle π hAb hG ρ o (P.shift (n • z) o) (P.shift (n • (z + w)) o)
  rw [smul_add, P.shift_add]
  rw [smul_add, P.shift_add] at this
  exact_mod_cast this

end Rotor


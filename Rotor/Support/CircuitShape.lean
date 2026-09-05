/-
Proposition 3.3 (`prop:circuit-shape`, `rotor.tex:1115-1135`): the shape of the passage
balls.  The paper's proof: "Homogeneity and continuity give `λ|x| ≤ μ(x) ≤ C|x|` with
`λ := min_{|u|=1} μ(u) > 0`, so `B` is compact and contains a neighborhood of the origin,
and subadditivity makes it convex.  Comparing `τ(o,·)` with `μ` through the uniform limit
and applying the passage-ball identity gives the sandwich for all large `n`, from which the
Hausdorff convergence follows."
-/
import Rotor.Support.PassageUniform

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

namespace Rotor

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

/-! ### Two facts about the periodic placement -/

omit [DecidableEq V] [G.LocallyFinite] in
/-- Graph distance from the base point is at most linear in the Euclidean distance
(the upper half of `eq:distance-comparison`). -/
theorem exists_dist_le_norm (hπ : P.Periodic π) (hG : G.Connected) (o : V) :
    ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
      ∀ x : V, (G.dist o x : ℝ) ≤ K * ‖P.emb x - P.emb o‖ + K' := by
  obtain ⟨D, hD0, hD⟩ := P.exists_rep_bound π hπ hG o
  obtain ⟨K₀, hK₀0, hK₀⟩ : ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ z, (G.dist o (P.shift z o) : ℝ) ≤ K₀ * supNorm z :=
    ⟨_, add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), dist_shift_le_supNorm π P hπ hG o⟩
  have hC0 : 0 ≤ ‖P.coords‖ := norm_nonneg _
  refine ⟨K₀ * ‖P.coords‖, K₀ * ‖P.coords‖ * D + D, by positivity, by positivity, fun x => ?_⟩
  obtain ⟨hd, he⟩ := hD x
  have h1 : (G.dist o x : ℝ) ≤
      G.dist o (P.shift (P.coord x) o) + G.dist (P.shift (P.coord x) o) x := by
    exact_mod_cast hG.dist_triangle
  have h2 := hK₀ (P.coord x)
  have h3 := P.supNorm_le_norm_latVec (P.coord x)
  have h4 : ‖P.latVec (P.coord x)‖ ≤ ‖P.emb x - P.emb o‖ + D := by
    rw [← P.emb_shift_sub]
    calc ‖P.emb (P.shift (P.coord x) o) - P.emb o‖
        = ‖(P.emb x - P.emb o) - (P.emb x - P.emb (P.shift (P.coord x) o))‖ := by
          congr 1; abel
      _ ≤ ‖P.emb x - P.emb o‖ + ‖P.emb x - P.emb (P.shift (P.coord x) o)‖ := norm_sub_le _ _
      _ ≤ ‖P.emb x - P.emb o‖ + D := by linarith
  have hd' : (G.dist (P.shift (P.coord x) o) x : ℝ) ≤ D := by rw [G.dist_comm]; exact hd
  calc (G.dist o x : ℝ) ≤ K₀ * supNorm (P.coord x) + D := by linarith
    _ ≤ K₀ * (‖P.coords‖ * ‖P.latVec (P.coord x)‖) + D := by gcongr
    _ ≤ K₀ * (‖P.coords‖ * (‖P.emb x - P.emb o‖ + D)) + D := by gcongr
    _ = K₀ * ‖P.coords‖ * ‖P.emb x - P.emb o‖ + (K₀ * ‖P.coords‖ * D + D) := by ring

omit [DecidableEq V] [G.LocallyFinite] in
/-- Every point of the plane is within a bounded distance of a vertex, drawn relative to `o`. -/
theorem exists_vertex_near (o : V) :
    ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ p : Plane, ∃ x : V, ‖(P.emb x - P.emb o) - p‖ ≤ D₀ := by
  refine ⟨‖P.b 0‖ + ‖P.b 1‖, by positivity, fun p => ?_⟩
  refine ⟨P.shift (⌊P.coords p 0⌋, ⌊P.coords p 1⌋) o, ?_⟩
  rw [P.emb_shift_sub]
  have hp : p = P.coords p 0 • P.b 0 + P.coords p 1 • P.b 1 := by
    have := P.basis.sum_equivFun p
    rw [Fin.sum_univ_two] at this
    simp only [P.basis_apply] at this
    rw [P.coords_apply]
    exact this.symm
  have hsub : P.latVec (⌊P.coords p 0⌋, ⌊P.coords p 1⌋) -
      (P.coords p 0 • P.b 0 + P.coords p 1 • P.b 1) =
      -(Int.fract (P.coords p 0) • P.b 0 + Int.fract (P.coords p 1) • P.b 1) := by
    simp only [DoublyPeriodic.latVec, Int.fract, sub_smul]
    abel
  rw [← hp] at hsub
  rw [hsub, norm_neg]
  calc ‖Int.fract (P.coords p 0) • P.b 0 + Int.fract (P.coords p 1) • P.b 1‖
      ≤ ‖Int.fract (P.coords p 0) • P.b 0‖ + ‖Int.fract (P.coords p 1) • P.b 1‖ := norm_add_le _ _
    _ = Int.fract (P.coords p 0) * ‖P.b 0‖ + Int.fract (P.coords p 1) * ‖P.b 1‖ := by
        rw [norm_smul_of_nonneg (Int.fract_nonneg _), norm_smul_of_nonneg (Int.fract_nonneg _)]
    _ ≤ 1 * ‖P.b 0‖ + 1 * ‖P.b 1‖ := by
        gcongr
        · exact (Int.fract_lt_one _).le
        · exact (Int.fract_lt_one _).le
    _ = ‖P.b 0‖ + ‖P.b 1‖ := by ring

/-! ### The passage function and its unit ball -/

section PassageFun

variable {f : Plane → ℝ} (hfc : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
  (hfadd : ∀ x y, f (x + y) ≤ f x + f y) (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
  {l : ℝ} (hl : 0 < l) (hmin : ∀ u : Plane, ‖u‖ = 1 → l ≤ f u)

include hfsmul in
theorem pf_zero : f 0 = 0 := by
  have := hfsmul 0 le_rfl 0
  simpa using this

include hfsmul in
theorem pf_eq_norm_mul (x : Plane) (hx : x ≠ 0) : f x = ‖x‖ * f (‖x‖⁻¹ • x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [← hfsmul _ hn.le, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

include hfsmul hmin in
theorem pf_lower (x : Plane) : l * ‖x‖ ≤ f x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [pf_zero hfsmul]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.2 hn.le), inv_mul_cancel₀ hn.ne']
    rw [pf_eq_norm_mul hfsmul x hx, mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin _ hu) hn.le

include hfc hfsmul in
theorem pf_exists_upper : ∃ C : ℝ, 0 < C ∧ ∀ x, f x ≤ C * ‖x‖ := by
  obtain ⟨u, -, hu⟩ := (isCompact_sphere (0 : Plane) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hfc.continuousOn
  refine ⟨max (f u) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [pf_zero hfsmul]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Plane) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul_of_nonneg (inv_nonneg.2 hn.le),
        inv_mul_cancel₀ hn.ne']
    have h1 : f (‖x‖⁻¹ • x) ≤ f u := hu hmem
    rw [pf_eq_norm_mul hfsmul x hx, mul_comm]
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) hn.le

include hfadd in
theorem pf_lip {C : ℝ} (hC : ∀ x, f x ≤ C * ‖x‖) (x y : Plane) : f x ≤ f y + C * ‖x - y‖ := by
  have := hfadd y (x - y)
  rw [add_sub_cancel] at this
  linarith [hC (x - y)]

include hfc hfsmul hl hmin in
theorem pf_isCompact : IsCompact {x : Plane | f x ≤ 1} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_Iic.preimage hfc) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨l⁻¹, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : l * ‖x‖ ≤ 1 := (pf_lower hfsmul hmin x).trans hx
  calc ‖x‖ = l⁻¹ * (l * ‖x‖) := by field_simp
    _ ≤ l⁻¹ * 1 := by gcongr
    _ = l⁻¹ := mul_one _

include hfadd hfsmul in
theorem pf_convex : Convex ℝ {x : Plane | f x ≤ 1} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  calc f (a • x + b • y) ≤ f (a • x) + f (b • y) := hfadd _ _
    _ = a * f x + b * f y := by rw [hfsmul a ha.le, hfsmul b hb.le]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

theorem pf_zero_mem_interior {C : ℝ} (hC0 : 0 < C) (hC : ∀ x, f x ≤ C * ‖x‖) :
    (0 : Plane) ∈ interior {x : Plane | f x ≤ 1} := by
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Plane) (inv_pos.2 hC0))
    (fun x hx => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hx
  show f x ≤ 1
  calc f x ≤ C * ‖x‖ := hC x
    _ ≤ C * C⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hC0.ne'

end PassageFun

/-! ### The sandwich and the Hausdorff limit -/

/-- The sandwich `eq:shape-sandwich` for one configuration in the good event. -/
theorem sandwich_of (hπ : P.Periodic π) (hG : G.Connected) (o : V) {f : Plane → ℝ}
    (hfc : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
    {l : ℝ} (hl : 0 < l) (hmin : ∀ u : Plane, ‖u‖ = 1 → l ≤ f u) (ρ : Config G)
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : V, R₀ ≤ ‖P.emb x - P.emb o‖ →
      |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ ε * ‖P.emb x - P.emb o‖)
    (hball : ∀ n : ℕ, ∀ x : V, x ∈ A π ρ o n ↔ τ π ρ o x ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n) := by
  obtain ⟨C, hC0, hC⟩ := pf_exists_upper hfc hfsmul
  obtain ⟨K, K', hK0, hK'0, hK⟩ := exists_dist_le_norm π P hπ hG o
  obtain ⟨R₀, hR₀⟩ := hunif (l * ε / 4) (by positivity)
  obtain ⟨R, hR0, hRR⟩ : ∃ R : ℝ, 0 ≤ R ∧ R₀ ≤ R := ⟨max R₀ 0, le_max_right _ _, le_max_left _ _⟩
  filter_upwards [eventually_ge_atTop ⌈K * R + K'⌉₊, eventually_ge_atTop ⌈C * R⌉₊] with n hn1 hn2
  have hn1' : K * R + K' ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn1)
  have hn2' : C * R ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  have hεn : 0 ≤ ε * n := by positivity
  have hεεn : 0 ≤ ε * ε * n := by positivity
  constructor
  · intro x hx
    rw [hball]
    have hf := hf0 (P.emb x - P.emb o)
    have hτ : (τ π ρ o x : ℝ) ≤ n := by
      by_cases hsmall : ‖P.emb x - P.emb o‖ < R₀
      · have h1 : (τ π ρ o x : ℝ) ≤ G.dist o x := by exact_mod_cast τ_le_dist π hG ρ o x
        have h2 := hK x
        have h3 : ‖P.emb x - P.emb o‖ ≤ R := hsmall.le.trans hRR
        have h4 : K * ‖P.emb x - P.emb o‖ ≤ K * R := mul_le_mul_of_nonneg_left h3 hK0
        linarith
      · push_neg at hsmall
        have h1 := (abs_le.1 (hR₀ x hsmall)).2
        have h2 := pf_lower hfsmul hmin (P.emb x - P.emb o)
        have h3 : (ε / 4) * (l * ‖P.emb x - P.emb o‖) ≤ (ε / 4) * f (P.emb x - P.emb o) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : (ε / 4) * f (P.emb x - P.emb o) ≤ (ε / 4) * ((1 - ε) * n) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        nlinarith
    exact_mod_cast hτ
  · intro x hx
    rw [hball] at hx
    have hτ : (τ π ρ o x : ℝ) ≤ n := by exact_mod_cast hx
    have hf := hf0 (P.emb x - P.emb o)
    by_cases hsmall : ‖P.emb x - P.emb o‖ < R₀
    · have h1 := hC (P.emb x - P.emb o)
      have h3 : ‖P.emb x - P.emb o‖ ≤ R := hsmall.le.trans hRR
      have h4 : C * ‖P.emb x - P.emb o‖ ≤ C * R := mul_le_mul_of_nonneg_left h3 hC0.le
      linarith
    · push_neg at hsmall
      have h1 := (abs_le.1 (hR₀ x hsmall)).1
      have h2 := pf_lower hfsmul hmin (P.emb x - P.emb o)
      have h3 : (ε / 4) * (l * ‖P.emb x - P.emb o‖) ≤ (ε / 4) * f (P.emb x - P.emb o) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      -- `(1 - ε/4) f ≤ n`, and `(1 + ε)(1 - ε/4) ≥ 1`
      have h5 : (1 - ε / 4) * f (P.emb x - P.emb o) ≤ n := by nlinarith
      have h6 : (1 + ε) * ((1 - ε / 4) * f (P.emb x - P.emb o)) ≤ (1 + ε) * n :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h7 : 0 ≤ (ε / 4) * (3 - ε) * f (P.emb x - P.emb o) :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) hf
      nlinarith

/-- The Hausdorff convergence `eq:circuit-shape` from the sandwich. -/
theorem hausdorff_of (o : V) {f : Plane → ℝ}
    (hfc : Continuous f) (hfadd : ∀ x y, f (x + y) ≤ f x + f y)
    (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
    {l : ℝ} (hl : 0 < l) (hmin : ∀ u : Plane, ‖u‖ = 1 → l ≤ f u) (ρ : Config G)
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n)) :
    Tendsto (fun n : ℕ => Metric.hausdorffDist
      ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V)))
      {x : Plane | f x ≤ 1}) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := pf_exists_upper hfc hfsmul
  obtain ⟨D₀, hD₀0, hD₀⟩ := exists_vertex_near P o
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨ε, hε0, hε1, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε ≤ l * δ / 4 :=
    ⟨min (l * δ / 4) (1 / 2), lt_min (by positivity) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num), min_le_left _ _⟩
  have hε2 : ε / 2 < 1 := by linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hsand ε hε0 hε1)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hsand (ε / 2) (by positivity) hε2)
  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ n : ℕ, N₃ ≤ n → C * D₀ ≤ ε / 2 * n ∧ D₀ ≤ δ / 4 * n := by
    refine ⟨⌈max (C * D₀ / (ε / 2)) (D₀ / (δ / 4))⌉₊, fun n hn => ?_⟩
    have h : max (C * D₀ / (ε / 2)) (D₀ / (δ / 4)) ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    constructor
    · have := (le_max_left _ _).trans h
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    · have := (le_max_right _ _).trans h
      rw [div_le_iff₀ (by positivity)] at this
      linarith
  refine ⟨max N₁ (max N₂ N₃) + 1, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hn3 : N₃ ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨-, hup⟩ := hN₁ n hn1
  obtain ⟨hlow2, -⟩ := hN₂ n hn2
  obtain ⟨hCD, hDn⟩ := hN₃ n hn3
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
  refine lt_of_le_of_lt (Metric.hausdorffDist_le_of_mem_dist (r := δ / 2) (by positivity) ?_ ?_)
    (by linarith)
  · -- points of the scaled range are within `δ/2` of `B`
    rintro y ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    have hfx := hup x hx
    have h1ε : 0 < 1 + ε := by linarith
    refine ⟨(1 + ε)⁻¹ • ((n : ℝ)⁻¹ • (P.emb x - P.emb o)), ?_, ?_⟩
    · show f _ ≤ 1
      rw [hfsmul _ (inv_nonneg.2 h1ε.le), hfsmul _ (inv_nonneg.2 hn'.le), ← mul_assoc,
        ← mul_inv, inv_mul_le_iff₀ (by positivity), mul_one]
      exact hfx
    · rw [dist_eq_norm]
      have hy : f ((n : ℝ)⁻¹ • (P.emb x - P.emb o)) ≤ 1 + ε := by
        rw [hfsmul _ (inv_nonneg.2 hn'.le), inv_mul_le_iff₀ hn']
        linarith
      have hyn : ‖(n : ℝ)⁻¹ • (P.emb x - P.emb o)‖ ≤ (1 + ε) / l := by
        have := pf_lower hfsmul hmin ((n : ℝ)⁻¹ • (P.emb x - P.emb o))
        rw [le_div_iff₀ hl]
        linarith
      have hinv : (1 + ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hsplit : (n : ℝ)⁻¹ • (P.emb x - P.emb o) - (1 + ε)⁻¹ • ((n : ℝ)⁻¹ • (P.emb x - P.emb o))
          = (1 - (1 + ε)⁻¹) • ((n : ℝ)⁻¹ • (P.emb x - P.emb o)) := by
        rw [sub_smul, one_smul]
      have h1 : 1 - (1 + ε)⁻¹ ≤ ε := by
        have : 1 - (1 + ε)⁻¹ = ε * (1 + ε)⁻¹ := by
          field_simp
          ring
        rw [this]
        exact mul_le_of_le_one_right hε0.le hinv
      rw [hsplit, norm_smul_of_nonneg (by linarith)]
      calc (1 - (1 + ε)⁻¹) * ‖(n : ℝ)⁻¹ • (P.emb x - P.emb o)‖ ≤ ε * ((1 + ε) / l) :=
            mul_le_mul h1 hyn (norm_nonneg _) hε0.le
        _ ≤ (l * δ / 4) * (2 / l) := by
            gcongr
            linarith
        _ = δ / 2 := by field_simp; ring
  · -- points of `B` are within `δ/2` of the scaled range
    intro b hb
    have hb' : f b ≤ 1 := hb
    have h1ε : 0 ≤ (1 - ε) * n := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    obtain ⟨x, hx⟩ := hD₀ (((1 - ε) * n) • b)
    have hxA : x ∈ A π ρ o n := by
      apply hlow2
      have h1 := pf_lip hfadd hC (P.emb x - P.emb o) (((1 - ε) * n) • b)
      rw [hfsmul _ h1ε] at h1
      have h2 : (1 - ε) * n * f b ≤ (1 - ε) * n := mul_le_of_le_one_right h1ε hb'
      have h3 : C * ‖P.emb x - P.emb o - ((1 - ε) * n) • b‖ ≤ C * D₀ :=
        mul_le_mul_of_nonneg_left hx hC0.le
      linarith
    refine ⟨(n : ℝ)⁻¹ • (P.emb x - P.emb o), ⟨_, ⟨x, hxA, rfl⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have hbn : ‖b‖ ≤ l⁻¹ := by
      have h2 : l * ‖b‖ ≤ 1 := (pf_lower hfsmul hmin b).trans hb'
      calc ‖b‖ = l⁻¹ * (l * ‖b‖) := by field_simp
        _ ≤ l⁻¹ * 1 := by gcongr
        _ = l⁻¹ := mul_one _
    have e1 : ε * l⁻¹ ≤ δ / 4 := by
      calc ε * l⁻¹ ≤ (l * δ / 4) * l⁻¹ := by gcongr
        _ = δ / 4 := by field_simp
    have e2 : (n : ℝ)⁻¹ * D₀ ≤ δ / 4 := by
      calc (n : ℝ)⁻¹ * D₀ ≤ (n : ℝ)⁻¹ * (δ / 4 * n) := by gcongr
        _ = δ / 4 := by field_simp
    calc ‖b - (n : ℝ)⁻¹ • (P.emb x - P.emb o)‖
        = ‖ε • b + (n : ℝ)⁻¹ • (((1 - ε) * n) • b - (P.emb x - P.emb o))‖ := by
          congr 1
          rw [smul_sub (n : ℝ)⁻¹ (((1 - ε) * n) • b), smul_smul,
            show (n : ℝ)⁻¹ * ((1 - ε) * n) = 1 - ε by
              rw [mul_comm, mul_assoc, mul_inv_cancel₀ hn'.ne', mul_one],
            sub_smul, one_smul]
          abel
      _ ≤ ‖ε • b‖ + ‖(n : ℝ)⁻¹ • (((1 - ε) * n) • b - (P.emb x - P.emb o))‖ := norm_add_le _ _
      _ = ε * ‖b‖ + (n : ℝ)⁻¹ * ‖((1 - ε) * n) • b - (P.emb x - P.emb o)‖ := by
          rw [norm_smul_of_nonneg hε0.le, norm_smul_of_nonneg (inv_nonneg.2 hn'.le)]
      _ ≤ ε * l⁻¹ + (n : ℝ)⁻¹ * D₀ :=
          add_le_add (mul_le_mul_of_nonneg_left hbn hε0.le)
            (mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hx) (inv_nonneg.2 hn'.le))
      _ ≤ δ / 4 + δ / 4 := add_le_add e1 e2
      _ = δ / 2 := by ring

/-- Proof of `prop:circuit-shape`. -/
theorem circuit_shape_proof (hπ : P.Periodic π) (hG : G.Connected) (μ : Measure (Config G))
    (o : V) (f : Plane → ℝ)
    (hf : Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x y, f (x + y) ≤ f x + f y) ∧
      (∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x) ∧
      ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : V, R₀ ≤ ‖P.emb x - P.emb o‖ →
        |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ ε * ‖P.emb x - P.emb o‖)
    (hball : ∀ᵐ ρ ∂μ, ∀ n : ℕ, T π ρ o n < ⊤ ∧ ∀ x : V, x ∈ A π ρ o n ↔ τ π ρ o x ≤ n)
    (hmin : ∃ l : ℝ, 0 < l ∧ ∀ u : Plane, ‖u‖ = 1 → l ≤ f u) :
    IsCompact {x : Plane | f x ≤ 1} ∧ Convex ℝ {x : Plane | f x ≤ 1} ∧
      (0 : Plane) ∈ interior {x : Plane | f x ≤ 1} ∧
    (∀ᵐ ρ ∂μ, Tendsto (fun n : ℕ => Metric.hausdorffDist
        ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V)))
        {x : Plane | f x ≤ 1}) atTop (𝓝 0)) ∧
    (∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n)) := by
  obtain ⟨hfc, hf0, hfadd, hfsmul, hunif⟩ := hf
  obtain ⟨l, hl, hmin⟩ := hmin
  obtain ⟨C, hC0, hC⟩ := pf_exists_upper hfc hfsmul
  have hsand : ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n) := by
    filter_upwards [hunif, hball] with ρ hρ hρb
    exact fun ε hε hε1 => sandwich_of π P hπ hG o hfc hf0 hfsmul hl hmin ρ hρ
      (fun n x => (hρb n).2 x) ε hε hε1
  refine ⟨pf_isCompact hfc hfsmul hl hmin, pf_convex hfadd hfsmul, pf_zero_mem_interior hC0 hC,
    ?_, hsand⟩
  filter_upwards [hsand] with ρ hρ
  exact hausdorff_of π P o hfc hfadd hfsmul hl hmin ρ hρ

end Rotor

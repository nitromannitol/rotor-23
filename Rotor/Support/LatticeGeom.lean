/-
Geometry of a doubly periodic graph: the graph distance between lattice
translates grows at most linearly in the sup norm of the lattice vector, the
lattice vectors embed with comparable Euclidean norm, and the orbit
representatives lie at bounded distance from any base point.  Support for
`prop:passage-limit`.
-/
import Rotor.Support.Equivariance

open Rotor MeasureTheory Filter Topology

universe u

namespace Rotor

/-- The sup norm of a lattice vector, as a real number. -/
def supNorm (z : ℤ × ℤ) : ℝ := max |(z.1 : ℝ)| |(z.2 : ℝ)|

theorem supNorm_nonneg (z : ℤ × ℤ) : 0 ≤ supNorm z := le_max_of_le_left (abs_nonneg _)

theorem abs_fst_le_supNorm (z : ℤ × ℤ) : |(z.1 : ℝ)| ≤ supNorm z := le_max_left _ _

theorem abs_snd_le_supNorm (z : ℤ × ℤ) : |(z.2 : ℝ)| ≤ supNorm z := le_max_right _ _

theorem supNorm_le_iff {z : ℤ × ℤ} {r : ℝ} : supNorm z ≤ r ↔ |(z.1 : ℝ)| ≤ r ∧ |(z.2 : ℝ)| ≤ r :=
  max_le_iff

theorem supNorm_neg (z : ℤ × ℤ) : supNorm (-z) = supNorm z := by
  simp [supNorm]

theorem supNorm_sub_comm (z w : ℤ × ℤ) : supNorm (z - w) = supNorm (w - z) := by
  rw [← supNorm_neg, neg_sub]

theorem supNorm_add_le (z w : ℤ × ℤ) : supNorm (z + w) ≤ supNorm z + supNorm w := by
  rw [supNorm_le_iff]
  constructor
  · calc |((z + w).1 : ℝ)| = |(z.1 : ℝ) + w.1| := by simp
      _ ≤ |(z.1 : ℝ)| + |(w.1 : ℝ)| := abs_add_le _ _
      _ ≤ supNorm z + supNorm w := add_le_add (abs_fst_le_supNorm z) (abs_fst_le_supNorm w)
  · calc |((z + w).2 : ℝ)| = |(z.2 : ℝ) + w.2| := by simp
      _ ≤ |(z.2 : ℝ)| + |(w.2 : ℝ)| := abs_add_le _ _
      _ ≤ supNorm z + supNorm w := add_le_add (abs_snd_le_supNorm z) (abs_snd_le_supNorm w)

theorem supNorm_nsmul (n : ℕ) (z : ℤ × ℤ) : supNorm (n • z) = n * supNorm z := by
  unfold supNorm
  rw [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  rw [abs_mul, abs_mul, Nat.abs_cast, mul_max_of_nonneg _ _ (Nat.cast_nonneg n)]

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

omit [DecidableEq V] [G.LocallyFinite] in
/-- Translations preserve the graph distance. -/
theorem dist_shift_shift (hπ : P.Periodic π) (hG : G.Connected) (z : ℤ × ℤ) (x y : V) :
    G.dist (P.shift z x) (P.shift z y) = G.dist x y := by
  have := (P.mechAut π hπ z).dist_act hG x y
  simpa [P.mechAut_σ] using this

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_nsmul_le' (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) (n : ℕ) :
    G.dist o (P.shift (n • z) o) ≤ n * G.dist o (P.shift z o) := by
  induction n with
  | zero => simp [P.shift_zero]
  | succ n ih =>
    have htri := hG.dist_triangle (u := o) (v := P.shift (n • z) o) (w := P.shift ((n + 1) • z) o)
    have h2 : G.dist (P.shift (n • z) o) (P.shift ((n + 1) • z) o) = G.dist o (P.shift z o) := by
      rw [succ_nsmul, P.shift_add, dist_shift_shift π P hπ hG]
    rw [h2] at htri
    nlinarith

omit [DecidableEq V] [G.LocallyFinite] in
/-- Distance to the translate by `-z` equals the distance to the translate by `z`. -/
theorem dist_shift_neg (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) :
    G.dist o (P.shift (-z) o) = G.dist o (P.shift z o) := by
  have := dist_shift_shift π P hπ hG z o (P.shift (-z) o)
  rw [P.shift_neg_shift] at this
  rw [← this, G.dist_comm]

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_zsmul_le (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) (k : ℤ) :
    (G.dist o (P.shift (k • z) o) : ℝ) ≤ |(k : ℝ)| * G.dist o (P.shift z o) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [natCast_zsmul, Int.cast_natCast, Nat.abs_cast]
    have := dist_shift_nsmul_le' π P hπ hG o z n
    exact_mod_cast this
  · rw [neg_zsmul, natCast_zsmul, dist_shift_neg π P hπ hG, Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.abs_cast]
    have := dist_shift_nsmul_le' π P hπ hG o z n
    exact_mod_cast this

omit [DecidableEq V] [G.LocallyFinite] in
/-- The distance to a lattice translate is at most `K₀` times the sup norm of the lattice vector,
with `K₀` the sum of the distances to the two unit translates. -/
theorem dist_shift_le_supNorm (hπ : P.Periodic π) (hG : G.Connected) (o : V) (z : ℤ × ℤ) :
    (G.dist o (P.shift z o) : ℝ) ≤
      (G.dist o (P.shift (1, 0) o) + G.dist o (P.shift (0, 1) o)) * supNorm z := by
  have hz : z = z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  have htri := hG.dist_triangle (u := o) (v := P.shift (z.1 • ((1, 0) : ℤ × ℤ)) o)
    (w := P.shift z o)
  have hz' : P.shift z o = P.shift (z.1 • ((1, 0) : ℤ × ℤ)) (P.shift (z.2 • ((0, 1) : ℤ × ℤ)) o) := by
    rw [← P.shift_add, ← hz]
  have h2 : G.dist (P.shift (z.1 • ((1, 0) : ℤ × ℤ)) o) (P.shift z o) =
      G.dist o (P.shift (z.2 • ((0, 1) : ℤ × ℤ)) o) := by
    rw [hz']
    exact dist_shift_shift π P hπ hG _ _ _
  rw [h2] at htri
  have e1 := dist_shift_zsmul_le π P hπ hG o (1, 0) z.1
  have e2 := dist_shift_zsmul_le π P hπ hG o (0, 1) z.2
  have b1 := abs_fst_le_supNorm z
  have b2 := abs_snd_le_supNorm z
  have d1 : (0 : ℝ) ≤ G.dist o (P.shift (1, 0) o) := Nat.cast_nonneg _
  have d2 : (0 : ℝ) ≤ G.dist o (P.shift (0, 1) o) := Nat.cast_nonneg _
  have htri' : (G.dist o (P.shift z o) : ℝ) ≤
      G.dist o (P.shift (z.1 • ((1, 0) : ℤ × ℤ)) o) + G.dist o (P.shift (z.2 • ((0, 1) : ℤ × ℤ)) o) := by
    exact_mod_cast htri
  nlinarith [mul_le_mul_of_nonneg_left b1 d1, mul_le_mul_of_nonneg_left b2 d2]

/-! ### The lattice in the plane -/

namespace DoublyPeriodic

/-- The lattice vector `z₁ b₀ + z₂ b₁`. -/
noncomputable def latVec (z : ℤ × ℤ) : Plane := (z.1 : ℝ) • P.b 0 + (z.2 : ℝ) • P.b 1

omit [DecidableEq V] [G.LocallyFinite] in
theorem emb_shift_sub (z : ℤ × ℤ) (v : V) : P.emb (P.shift z v) - P.emb v = P.latVec z := by
  rw [P.emb_shift, latVec]; abel

omit [DecidableEq V] [G.LocallyFinite] in
theorem norm_latVec_le (z : ℤ × ℤ) : ‖P.latVec z‖ ≤ (‖P.b 0‖ + ‖P.b 1‖) * supNorm z := by
  have b1 := abs_fst_le_supNorm z
  have b2 := abs_snd_le_supNorm z
  calc ‖P.latVec z‖ ≤ ‖(z.1 : ℝ) • P.b 0‖ + ‖(z.2 : ℝ) • P.b 1‖ := norm_add_le _ _
    _ = |(z.1 : ℝ)| * ‖P.b 0‖ + |(z.2 : ℝ)| * ‖P.b 1‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ supNorm z * ‖P.b 0‖ + supNorm z * ‖P.b 1‖ :=
        add_le_add (mul_le_mul_of_nonneg_right b1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right b2 (norm_nonneg _))
    _ = (‖P.b 0‖ + ‖P.b 1‖) * supNorm z := by ring

/-- The basis of the plane formed by the lattice generators. -/
noncomputable def basis : Module.Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank P.b_indep (by simp)

omit [DecidableEq V] [G.LocallyFinite] in
@[simp] theorem basis_apply (i : Fin 2) : P.basis i = P.b i := by
  simp [basis]

/-- The coordinates of a point of the plane in the lattice basis, as a continuous linear map. -/
noncomputable def coords : Plane →L[ℝ] (Fin 2 → ℝ) :=
  (P.basis.equivFun.toContinuousLinearEquiv : Plane ≃L[ℝ] (Fin 2 → ℝ))

omit [DecidableEq V] [G.LocallyFinite] in
theorem coords_apply (x : Plane) : P.coords x = P.basis.equivFun x := rfl

omit [DecidableEq V] [G.LocallyFinite] in
theorem coords_latVec (z : ℤ × ℤ) : P.coords (P.latVec z) = ![(z.1 : ℝ), (z.2 : ℝ)] := by
  rw [coords_apply]
  have : P.latVec z = P.basis.equivFun.symm ![(z.1 : ℝ), (z.2 : ℝ)] := by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp [latVec]
  rw [this, LinearEquiv.apply_symm_apply]

omit [DecidableEq V] [G.LocallyFinite] in
/-- The sup norm of a lattice vector is controlled by the Euclidean norm of its image. -/
theorem supNorm_le_norm_latVec (z : ℤ × ℤ) : supNorm z ≤ ‖P.coords‖ * ‖P.latVec z‖ := by
  have h := P.coords.le_opNorm (P.latVec z)
  rw [coords_latVec] at h
  refine le_trans ?_ h
  rw [supNorm_le_iff]
  constructor
  · have := norm_le_pi_norm ![(z.1 : ℝ), (z.2 : ℝ)] 0
    simpa using this
  · have := norm_le_pi_norm ![(z.1 : ℝ), (z.2 : ℝ)] 1
    simpa using this

/-! ### Orbit representatives are at bounded distance -/

omit [DecidableEq V] [G.LocallyFinite] in
/-- Every vertex is at bounded graph distance and bounded Euclidean offset from the translate of
the base point with the same coordinates. -/
theorem exists_rep_bound (π : Mechanism G) (hπ : P.Periodic π) (hG : G.Connected) (o : V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v : V, (G.dist v (P.shift (P.coord v) o) : ℝ) ≤ D ∧
      ‖P.emb v - P.emb (P.shift (P.coord v) o)‖ ≤ D := by
  obtain ⟨D₁, hD₁⟩ := (P.finite_orbits.image (fun r => (G.dist r o : ℝ))).bddAbove
  obtain ⟨D₂, hD₂⟩ := (P.finite_orbits.image (fun r => ‖P.emb r - P.emb o‖)).bddAbove
  refine ⟨max 0 (max D₁ D₂), le_max_left _ _, fun v => ?_⟩
  have hmem : P.rep v ∈ Set.range P.rep := ⟨v, rfl⟩
  constructor
  · have h1 : G.dist v (P.shift (P.coord v) o) = G.dist (P.rep v) o := by
      rw [← dist_shift_shift π P hπ hG (P.coord v) (P.rep v) o, P.shift_coord_rep]
    rw [h1]
    have := hD₁ (Set.mem_image_of_mem (fun r => (G.dist r o : ℝ)) hmem)
    exact this.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · have h2 : ∀ w, P.emb (P.shift (P.coord v) w) - P.emb (P.shift (P.coord v) o) =
        P.emb w - P.emb o := fun w => by
      rw [P.emb_shift, P.emb_shift]; abel
    have := h2 (P.rep v)
    rw [P.shift_coord_rep] at this
    rw [this]
    have := hD₂ (Set.mem_image_of_mem (fun r => ‖P.emb r - P.emb o‖) hmem)
    exact this.trans (le_trans (le_max_right _ _) (le_max_right _ _))

end DoublyPeriodic

end Rotor

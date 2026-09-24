/-
The distance lemmas of `LatticeGeom` without the periodicity of the mechanism: the lattice
translations are graph automorphisms by definition, which is all that graph distances need.
Used by `lem:block-live-paths`, whose statement has an arbitrary mechanism.
-/
import Rotor.Support.BlockGeom

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)

namespace DoublyPeriodic

/-- A lattice translation as a graph isomorphism. -/
def shiftIso (z : ℤ × ℤ) : G ≃g G where
  toEquiv := ⟨P.shift z, P.shift (-z), P.shift_shift_neg z, P.shift_neg_shift z⟩
  map_rel_iff' := fun {u v} => P.adj_shift z u v

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_shift₀ (hG : G.Connected) (z : ℤ × ℤ) (x y : V) :
    G.dist (P.shift z x) (P.shift z y) = G.dist x y := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := (hG.preconnected x y).exists_walk_length_eq_dist
    have := G.dist_le (p.map (P.shiftIso z).toHom)
    rwa [SimpleGraph.Walk.length_map, hp] at this
  · obtain ⟨p, hp⟩ := (hG.preconnected (P.shift z x) (P.shift z y)).exists_walk_length_eq_dist
    have := G.dist_le (p.map (P.shiftIso z).symm.toHom)
    rw [SimpleGraph.Walk.length_map, hp] at this
    have e1 : (P.shiftIso z).symm (P.shift z x) = x := P.shift_shift_neg z x
    have e2 : (P.shiftIso z).symm (P.shift z y) = y := P.shift_shift_neg z y
    simpa [e1, e2] using this

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_nsmul_le₀ (hG : G.Connected) (o : V) (z : ℤ × ℤ) (n : ℕ) :
    G.dist o (P.shift (n • z) o) ≤ n * G.dist o (P.shift z o) := by
  induction n with
  | zero => simp [P.shift_zero]
  | succ n ih =>
    have htri := hG.dist_triangle (u := o) (v := P.shift (n • z) o) (w := P.shift ((n + 1) • z) o)
    have h2 : G.dist (P.shift (n • z) o) (P.shift ((n + 1) • z) o) = G.dist o (P.shift z o) := by
      rw [succ_nsmul, P.shift_add, P.dist_shift_shift₀ hG]
    rw [h2] at htri
    nlinarith

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_neg₀ (hG : G.Connected) (o : V) (z : ℤ × ℤ) :
    G.dist o (P.shift (-z) o) = G.dist o (P.shift z o) := by
  have := P.dist_shift_shift₀ hG z o (P.shift (-z) o)
  rw [P.shift_neg_shift] at this
  rw [← this, G.dist_comm]

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_zsmul_le₀ (hG : G.Connected) (o : V) (z : ℤ × ℤ) (k : ℤ) :
    (G.dist o (P.shift (k • z) o) : ℝ) ≤ |(k : ℝ)| * G.dist o (P.shift z o) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [natCast_zsmul, Int.cast_natCast, Nat.abs_cast]
    have := P.dist_shift_nsmul_le₀ hG o z n
    exact_mod_cast this
  · rw [neg_zsmul, natCast_zsmul, P.dist_shift_neg₀ hG, Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.abs_cast]
    have := P.dist_shift_nsmul_le₀ hG o z n
    exact_mod_cast this

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_shift_le_supNorm₀ (hG : G.Connected) (o : V) (z : ℤ × ℤ) :
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
    exact P.dist_shift_shift₀ hG _ _ _
  rw [h2] at htri
  have e1 := P.dist_shift_zsmul_le₀ hG o (1, 0) z.1
  have e2 := P.dist_shift_zsmul_le₀ hG o (0, 1) z.2
  have b1 := abs_fst_le_supNorm z
  have b2 := abs_snd_le_supNorm z
  have d1 : (0 : ℝ) ≤ G.dist o (P.shift (1, 0) o) := Nat.cast_nonneg _
  have d2 : (0 : ℝ) ≤ G.dist o (P.shift (0, 1) o) := Nat.cast_nonneg _
  have htri' : (G.dist o (P.shift z o) : ℝ) ≤
      G.dist o (P.shift (z.1 • ((1, 0) : ℤ × ℤ)) o) + G.dist o (P.shift (z.2 • ((0, 1) : ℤ × ℤ)) o) := by
    exact_mod_cast htri
  nlinarith [mul_le_mul_of_nonneg_left b1 d1, mul_le_mul_of_nonneg_left b2 d2]

omit [DecidableEq V] [G.LocallyFinite] in
theorem exists_rep_bound₀ (hG : G.Connected) (o : V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v : V, (G.dist v (P.shift (P.coord v) o) : ℝ) ≤ D ∧
      ‖P.emb v - P.emb (P.shift (P.coord v) o)‖ ≤ D := by
  obtain ⟨D₁, hD₁⟩ := (P.finite_orbits.image (fun r => (G.dist r o : ℝ))).bddAbove
  obtain ⟨D₂, hD₂⟩ := (P.finite_orbits.image (fun r => ‖P.emb r - P.emb o‖)).bddAbove
  refine ⟨max 0 (max D₁ D₂), le_max_left _ _, fun v => ?_⟩
  have hmem : P.rep v ∈ Set.range P.rep := ⟨v, rfl⟩
  constructor
  · have h1 : G.dist v (P.shift (P.coord v) o) = G.dist (P.rep v) o := by
      rw [← P.dist_shift_shift₀ hG (P.coord v) (P.rep v) o, P.shift_coord_rep]
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

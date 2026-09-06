import Rotor.Support.BlockGeom
import Rotor.Support.PathReductionIII

/-!
Balls in a doubly periodic graph have at most `C r²` vertices, `rotor.tex:1408-1409`:
"By assumption, balls of radius `r` in the graph metric have at most `C r²` vertices."
-/

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

theorem exists_ball_bound (P : DoublyPeriodic G) (hG : G.Connected) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : V) (r : ℕ), ∃ s : Finset V,
      (∀ y : V, G.dist x y ≤ r → y ∈ s) ∧ (s.card : ℝ) ≤ C * (r + 1) ^ 2 := by
  classical
  obtain ⟨v₀⟩ := hG.nonempty
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_edge_bound P
  obtain ⟨Q, hQ⟩ := P.finite_orbits.exists_finset_coe
  obtain ⟨D, hD⟩ := (P.finite_orbits.image (fun r => ‖P.emb r‖)).bddAbove
  have hD' : ∀ v, ‖P.emb (P.rep v)‖ ≤ D := fun v => hD (Set.mem_image_of_mem _ ⟨v, rfl⟩)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD' v₀)
  set N : ℝ := ‖P.coords‖ with hNdef
  have hN : 0 ≤ N := norm_nonneg _
  set A : ℝ := 2 * N * ℓ + 4 * N * D + 1 with hAdef
  have hA : 0 < A := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hN) hℓ0.le
    have h2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hN) hD0
    rw [hAdef]
    linarith
  refine ⟨A ^ 2 * (Q.card + 1), mul_pos (pow_pos hA 2) (by positivity), fun x r => ?_⟩
  set K : ℤ := ⌊N * (ℓ * r + 2 * D)⌋ with hKdef
  have hK0 : 0 ≤ K := Int.floor_nonneg.2 (by positivity)
  set B : Finset (ℤ × ℤ) :=
    Icc ((P.coord x).1 - K) ((P.coord x).1 + K) ×ˢ Icc ((P.coord x).2 - K) ((P.coord x).2 + K)
    with hBdef
  refine ⟨(B ×ˢ Q).image (fun p => P.shift p.1 p.2), fun y hy => ?_, ?_⟩
  · rw [mem_image]
    refine ⟨(P.coord y, P.rep y), ?_, P.shift_coord_rep y⟩
    rw [mem_product]
    refine ⟨?_, by rw [← Finset.mem_coe, hQ]; exact ⟨y, rfl⟩⟩
    have h1 : ‖P.emb x - P.emb y‖ ≤ ℓ * r := by
      calc ‖P.emb x - P.emb y‖ ≤ ℓ * G.dist x y := norm_sub_le_dist P hG hℓ x y
        _ ≤ ℓ * r := by
            apply mul_le_mul_of_nonneg_left _ hℓ0.le
            exact_mod_cast hy
    have h2 : ‖P.latVec (P.coord y - P.coord x)‖ ≤ ℓ * r + 2 * D := by
      rw [P.latVec_sub]
      have e1 := P.emb_eq_rep_add y
      have e2 := P.emb_eq_rep_add x
      have : P.latVec (P.coord y) - P.latVec (P.coord x)
          = (P.emb y - P.emb x) - P.emb (P.rep y) + P.emb (P.rep x) := by
        rw [e1, e2]; abel
      rw [this]
      calc ‖(P.emb y - P.emb x) - P.emb (P.rep y) + P.emb (P.rep x)‖
          ≤ ‖P.emb y - P.emb x‖ + ‖P.emb (P.rep y)‖ + ‖P.emb (P.rep x)‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ ≤ ℓ * r + D + D := by
            rw [norm_sub_rev]
            gcongr
            · exact hD' y
            · exact hD' x
        _ = ℓ * r + 2 * D := by ring
    have h3 : supNorm (P.coord y - P.coord x) ≤ N * (ℓ * r + 2 * D) :=
      (P.supNorm_le_norm_latVec _).trans (mul_le_mul_of_nonneg_left h2 hN)
    rw [supNorm_eq_linf] at h3
    have h4 : linf (P.coord y - P.coord x) ≤ K := Int.le_floor.2 h3
    rw [linf_le_iff] at h4
    simp only [Prod.fst_sub, Prod.snd_sub, abs_le] at h4
    rw [hBdef, mem_product, mem_Icc, mem_Icc]
    dsimp only
    omega
  · have hcast : ∀ c : ℤ, (((c + K + 1 - (c - K)).toNat : ℕ) : ℝ) = 2 * (K : ℝ) + 1 := by
      intro c
      have h1 : c + K + 1 - (c - K) = 2 * K + 1 := by ring
      have h2 : (((2 * K + 1).toNat : ℕ) : ℤ) = 2 * K + 1 := Int.toNat_of_nonneg (by omega)
      rw [h1, ← Int.cast_natCast, h2]
      push_cast
      ring
    calc (((B ×ˢ Q).image (fun p => P.shift p.1 p.2)).card : ℝ)
        ≤ ((B ×ˢ Q).card : ℝ) := by exact_mod_cast card_image_le
      _ = (2 * (K : ℝ) + 1) ^ 2 * Q.card := by
          rw [card_product, hBdef, card_product, Int.card_Icc, Int.card_Icc]
          push_cast
          rw [hcast, hcast]
          ring
      _ ≤ (A * (r + 1)) ^ 2 * Q.card := by
          gcongr
          have hKle : (K : ℝ) ≤ N * (ℓ * r + 2 * D) := Int.floor_le _
          have hr : (0:ℝ) ≤ r := Nat.cast_nonneg r
          have h5 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hN) hD0) hr
          rw [hAdef]
          nlinarith
      _ = A ^ 2 * (r + 1) ^ 2 * Q.card := by ring
      _ ≤ A ^ 2 * (r + 1) ^ 2 * (Q.card + 1) := by
          gcongr
          linarith
      _ = A ^ 2 * (Q.card + 1) * (r + 1) ^ 2 := by ring

end Rotor

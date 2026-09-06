/-
Geometric constants for the block estimate: graph distance is at most linear in Euclidean
distance uniformly in the endpoints, and the sup-distance between the block indices of two
vertices is at least a positive multiple of their graph distance, minus a constant.
-/
import Rotor.Support.PathReductionIII
import Rotor.Support.LatticeGeom0

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)

omit [DecidableEq V] [G.LocallyFinite] in
/-- Uniform distance comparison (the upper half of `eq:distance-comparison`). -/
theorem exists_dist_le_norm_uniform (hG : G.Connected) :
    ∃ K K' : ℝ, 0 < K ∧ 0 ≤ K' ∧ ∀ u w : V, (G.dist u w : ℝ) ≤ K * ‖P.emb u - P.emb w‖ + K' := by
  obtain ⟨o⟩ := hG.nonempty
  obtain ⟨D, hD0, hD⟩ := P.exists_rep_bound₀ hG o
  obtain ⟨K₀, hK₀0, hK₀⟩ : ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ z, (G.dist o (P.shift z o) : ℝ) ≤ K₀ * supNorm z :=
    ⟨_, add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), P.dist_shift_le_supNorm₀ hG o⟩
  obtain ⟨D₂, hD₂⟩ := (P.finite_orbits.image (fun r => ‖P.emb r‖)).bddAbove
  have hD₂' : ∀ v, ‖P.emb (P.rep v)‖ ≤ D₂ := fun v => hD₂ (Set.mem_image_of_mem _ ⟨v, rfl⟩)
  have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂' o)
  have hC0 : 0 ≤ ‖P.coords‖ := norm_nonneg _
  refine ⟨K₀ * ‖P.coords‖ + 1, K₀ * ‖P.coords‖ * (2 * D₂) + 2 * D, by positivity, by positivity,
    fun u w => ?_⟩
  have h1 : (G.dist u w : ℝ) ≤ G.dist u (P.shift (P.coord u) o) +
      G.dist (P.shift (P.coord u) o) (P.shift (P.coord w) o) + G.dist (P.shift (P.coord w) o) w := by
    have hN : G.dist u w ≤ G.dist u (P.shift (P.coord u) o) +
        G.dist (P.shift (P.coord u) o) (P.shift (P.coord w) o) + G.dist (P.shift (P.coord w) o) w := by
      have := hG.dist_triangle (u := u) (v := P.shift (P.coord w) o) (w := w)
      have := hG.dist_triangle (u := u) (v := P.shift (P.coord u) o) (w := P.shift (P.coord w) o)
      omega
    exact_mod_cast hN
  have h2 : (G.dist u (P.shift (P.coord u) o) : ℝ) ≤ D := (hD u).1
  have h3 : (G.dist (P.shift (P.coord w) o) w : ℝ) ≤ D := by rw [G.dist_comm]; exact (hD w).1
  have h4 : G.dist (P.shift (P.coord u) o) (P.shift (P.coord w) o) =
      G.dist o (P.shift (P.coord w - P.coord u) o) := by
    have : P.shift (P.coord w) o = P.shift (P.coord u) (P.shift (P.coord w - P.coord u) o) := by
      rw [← P.shift_add, add_sub_cancel]
    rw [this]
    exact P.dist_shift_shift₀ hG _ _ _
  have h5 := hK₀ (P.coord w - P.coord u)
  have h6 := P.supNorm_le_norm_latVec (P.coord w - P.coord u)
  have h7 : ‖P.latVec (P.coord w - P.coord u)‖ ≤ ‖P.emb u - P.emb w‖ + 2 * D₂ := by
    rw [P.latVec_sub]
    have e1 := P.emb_eq_rep_add w
    have e2 := P.emb_eq_rep_add u
    have : P.latVec (P.coord w) - P.latVec (P.coord u) =
        -(P.emb u - P.emb w) + (P.emb (P.rep u) - P.emb (P.rep w)) := by
      rw [e1, e2]; abel
    rw [this]
    calc ‖-(P.emb u - P.emb w) + (P.emb (P.rep u) - P.emb (P.rep w))‖
        ≤ ‖-(P.emb u - P.emb w)‖ + ‖P.emb (P.rep u) - P.emb (P.rep w)‖ := norm_add_le _ _
      _ ≤ ‖P.emb u - P.emb w‖ + (‖P.emb (P.rep u)‖ + ‖P.emb (P.rep w)‖) := by
          rw [norm_neg]; gcongr; exact norm_sub_le _ _
      _ ≤ ‖P.emb u - P.emb w‖ + 2 * D₂ := by linarith [hD₂' u, hD₂' w]
  have h8 : (G.dist (P.shift (P.coord u) o) (P.shift (P.coord w) o) : ℝ) ≤
      K₀ * (‖P.coords‖ * (‖P.emb u - P.emb w‖ + 2 * D₂)) := by
    rw [h4]
    refine h5.trans (mul_le_mul_of_nonneg_left (h6.trans ?_) hK₀0)
    exact mul_le_mul_of_nonneg_left h7 hC0
  have hn : 0 ≤ ‖P.emb u - P.emb w‖ := norm_nonneg _
  nlinarith [mul_nonneg hK₀0 hC0]

omit [DecidableEq V] [G.LocallyFinite] in
/-- The coordinate displacement is at least linear in the Euclidean displacement. -/
theorem exists_norm_le_linf_coord : ∃ Cb D₂ : ℝ, 0 < Cb ∧ 0 ≤ D₂ ∧
    ∀ u w : V, ‖P.emb u - P.emb w‖ - 2 * D₂ ≤ Cb * (linf (P.coord w - P.coord u) : ℝ) := by
  obtain ⟨D₂, hD₂⟩ := (P.finite_orbits.image (fun r => ‖P.emb r‖)).bddAbove
  have hD₂' : ∀ v, ‖P.emb (P.rep v)‖ ≤ D₂ := fun v => hD₂ (Set.mem_image_of_mem _ ⟨v, rfl⟩)
  refine ⟨‖P.b 0‖ + ‖P.b 1‖, max D₂ 0, add_pos_of_pos_of_nonneg (norm_pos_iff.2 (P.b_indep.ne_zero 0))
    (norm_nonneg _), le_max_right _ _, fun u w => ?_⟩
  have h1 := P.norm_latVec_le (P.coord w - P.coord u)
  rw [supNorm_eq_linf] at h1
  have h2 : ‖P.emb u - P.emb w‖ - 2 * max D₂ 0 ≤ ‖P.latVec (P.coord w - P.coord u)‖ := by
    rw [P.latVec_sub]
    have e1 := P.emb_eq_rep_add w
    have e2 := P.emb_eq_rep_add u
    have : P.emb u - P.emb w = -(P.latVec (P.coord w) - P.latVec (P.coord u)) +
        (P.emb (P.rep u) - P.emb (P.rep w)) := by
      rw [e1, e2]; abel
    have h3 : ‖P.emb u - P.emb w‖ ≤ ‖P.latVec (P.coord w) - P.latVec (P.coord u)‖ + 2 * max D₂ 0 := by
      rw [this]
      calc ‖-(P.latVec (P.coord w) - P.latVec (P.coord u)) + (P.emb (P.rep u) - P.emb (P.rep w))‖
          ≤ ‖-(P.latVec (P.coord w) - P.latVec (P.coord u))‖ +
            ‖P.emb (P.rep u) - P.emb (P.rep w)‖ := norm_add_le _ _
        _ ≤ ‖P.latVec (P.coord w) - P.latVec (P.coord u)‖ +
            (‖P.emb (P.rep u)‖ + ‖P.emb (P.rep w)‖) := by
            rw [norm_neg]; gcongr; exact norm_sub_le _ _
        _ ≤ ‖P.latVec (P.coord w) - P.latVec (P.coord u)‖ + 2 * max D₂ 0 := by
            linarith [hD₂' u, hD₂' w, le_max_left D₂ 0]
    linarith
  linarith

/-- Floor division contracts differences by at most `L - 1`. -/
theorem abs_sub_le_mul_abs_ediv_sub {L : ℤ} (hL : 0 < L) (a b : ℤ) :
    |a - b| - (L - 1) ≤ L * |a / L - b / L| := by
  have ha := Int.mul_ediv_add_emod a L
  have hb := Int.mul_ediv_add_emod b L
  have hra := Int.emod_nonneg a hL.ne'
  have hra' := Int.emod_lt_of_pos a hL
  have hrb := Int.emod_nonneg b hL.ne'
  have hrb' := Int.emod_lt_of_pos b hL
  have e : a - b = L * (a / L - b / L) + (a % L - b % L) := by linarith
  have h1 : |a - b| ≤ |L * (a / L - b / L)| + |a % L - b % L| := by rw [e]; exact abs_add_le _ _
  rw [abs_mul, abs_of_pos hL] at h1
  have h2 : |a % L - b % L| ≤ L - 1 := by rw [abs_le]; constructor <;> linarith
  linarith

omit [DecidableEq V] [G.LocallyFinite] in
theorem linf_coord_sub_le_blockIndex {L : ℕ} (hL : 0 < L) (u w : V) :
    linf (P.coord w - P.coord u) - (L - 1) ≤ L * linf (P.blockIndex L w - P.blockIndex L u) := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h1 := abs_sub_le_mul_abs_ediv_sub hL' (P.coord w).1 (P.coord u).1
  have h2 := abs_sub_le_mul_abs_ediv_sub hL' (P.coord w).2 (P.coord u).2
  simp only [linf, DoublyPeriodic.blockIndex, Prod.fst_sub, Prod.snd_sub]
  have m1 := mul_le_mul_of_nonneg_left (le_max_left |(P.coord w).1 / L - (P.coord u).1 / L|
    |(P.coord w).2 / L - (P.coord u).2 / L|) hL'.le
  have m2 := mul_le_mul_of_nonneg_left (le_max_right |(P.coord w).1 / L - (P.coord u).1 / L|
    |(P.coord w).2 / L - (P.coord u).2 / L|) hL'.le
  rw [sub_le_iff_le_add, max_le_iff]
  constructor <;> linarith

omit [DecidableEq V] [G.LocallyFinite] in
/-- The block-index displacement grows linearly with the graph distance. -/
theorem exists_blockDist_bound (hG : G.Connected) {L : ℕ} (hL : 0 < L) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 ≤ c₂ ∧ ∀ u w : V,
      c₁ * G.dist u w - c₂ ≤ (linf (P.blockIndex L w - P.blockIndex L u) : ℝ) := by
  obtain ⟨K, K', hK0, hK'0, hK⟩ := exists_dist_le_norm_uniform P hG
  obtain ⟨Cb, D₂, hCb, hD₂, hCbD⟩ := exists_norm_le_linf_coord P
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨1 / (K * Cb * L), (K' + 2 * K * D₂ + K * Cb * (L - 1)) / (K * Cb * L), by positivity,
    by apply div_nonneg <;> nlinarith [mul_pos hK0 hCb, (by exact_mod_cast hL : (1 : ℝ) ≤ L)],
    fun u w => ?_⟩
  have h1 := hK u w
  have h2 := hCbD u w
  have h3 := linf_coord_sub_le_blockIndex P hL u w
  have h3' : (linf (P.coord w - P.coord u) : ℝ) - (L - 1) ≤
      L * (linf (P.blockIndex L w - P.blockIndex L u) : ℝ) := by exact_mod_cast h3
  have hlinf0 : (0 : ℝ) ≤ linf (P.blockIndex L w - P.blockIndex L u) := by
    exact_mod_cast linf_nonneg _
  rw [div_mul_eq_mul_div, one_mul, div_sub_div_same, div_le_iff₀ (by positivity)]
  -- d ≤ K * (Cb * (L * linfb + (L - 1)) + 2 D₂) + K'
  have h4 : ‖P.emb u - P.emb w‖ ≤ Cb * (L * (linf (P.blockIndex L w - P.blockIndex L u) : ℝ) + (L - 1)) + 2 * D₂ := by
    nlinarith
  have h5 : K * ‖P.emb u - P.emb w‖ ≤
      K * (Cb * (L * (linf (P.blockIndex L w - P.blockIndex L u) : ℝ) + (L - 1)) + 2 * D₂) :=
    mul_le_mul_of_nonneg_left h4 hK0.le
  nlinarith

end Rotor

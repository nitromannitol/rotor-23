/-
Geometry of the blocks `Q_z` and `Q_z⁺` (`rotor.tex:1216-1222`, `eq:block-definitions`):
every vertex lies in exactly one block; adjacent vertices lie in blocks whose indices are at
`ℓ^∞`-distance at most one once `L` is large; blocks are finite with a bound on their size
uniform in `z`; the enlarged blocks of indices at distance at least three are disjoint.
Support for `lem:block-live-paths`.
-/
import Rotor.Support.PathReductionIII

open Rotor Filter Topology

universe u

namespace Rotor

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)

/-- The `ℓ^∞` norm on `ℤ²` as an integer. -/
def linf (z : ℤ × ℤ) : ℤ := max |z.1| |z.2|

theorem linf_le_iff {z : ℤ × ℤ} {k : ℤ} : linf z ≤ k ↔ |z.1| ≤ k ∧ |z.2| ≤ k := max_le_iff

theorem linf_nonneg (z : ℤ × ℤ) : 0 ≤ linf z := le_max_of_le_left (abs_nonneg _)

theorem linf_sub_comm (z w : ℤ × ℤ) : linf (z - w) = linf (w - z) := by
  simp [linf, abs_sub_comm]

theorem linf_triangle (z w u : ℤ × ℤ) : linf (z - u) ≤ linf (z - w) + linf (w - u) := by
  rw [linf_le_iff]
  constructor
  · calc |(z - u).1| = |(z - w).1 + (w - u).1| := by congr 1; simp
      _ ≤ |(z - w).1| + |(w - u).1| := abs_add_le _ _
      _ ≤ linf (z - w) + linf (w - u) := add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc |(z - u).2| = |(z - w).2 + (w - u).2| := by congr 1; simp
      _ ≤ |(z - w).2| + |(w - u).2| := abs_add_le _ _
      _ ≤ linf (z - w) + linf (w - u) := add_le_add (le_max_right _ _) (le_max_right _ _)

omit [DecidableEq V] [G.LocallyFinite] in
theorem supNorm_eq_linf (z : ℤ × ℤ) : supNorm z = (linf z : ℝ) := by
  simp only [supNorm, linf, Int.cast_max, Int.cast_abs]

/-! ### Block indices -/

namespace DoublyPeriodic

/-- The index of the block of side `L` containing `v`. -/
def blockIndex (L : ℕ) (v : V) : ℤ × ℤ := ((P.coord v).1 / L, (P.coord v).2 / L)

omit [DecidableEq V] [G.LocallyFinite] in
theorem mem_block_iff {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) (v : V) :
    v ∈ P.block L z ↔ P.blockIndex L v = z := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have key : ∀ a b : ℤ, (a - L * b ∈ Set.Ico (0 : ℤ) L) ↔ a / L = b := by
    intro a b
    rw [Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · have : a / (L : ℤ) < b + 1 := (Int.ediv_lt_iff_lt_mul hL').2 (by linarith)
        omega
      · exact (Int.le_ediv_iff_mul_le hL').2 (by linarith)
    · intro h
      have h1 : b * L ≤ a := (Int.le_ediv_iff_mul_le hL').1 h.ge
      have h2 : a < (b + 1) * L := (Int.ediv_lt_iff_lt_mul hL').1 (by omega)
      constructor <;> linarith
  simp only [DoublyPeriodic.block, blockIndex, Set.mem_setOf_eq, Prod.ext_iff]
  rw [key, key]

omit [DecidableEq V] [G.LocallyFinite] in
theorem mem_blockPlus_iff {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) (v : V) :
    v ∈ P.blockPlus L z ↔ linf (P.blockIndex L v - z) ≤ 1 := by
  simp only [DoublyPeriodic.blockPlus, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨w, hw, hv⟩
    rw [P.mem_block_iff hL] at hv
    rw [hv]
    exact hw
  · intro h
    exact ⟨P.blockIndex L v, h, (P.mem_block_iff hL _ _).2 rfl⟩

omit [DecidableEq V] [G.LocallyFinite] in
theorem mem_block_blockIndex {L : ℕ} (hL : 0 < L) (v : V) : v ∈ P.block L (P.blockIndex L v) :=
  (P.mem_block_iff hL _ _).2 rfl

omit [DecidableEq V] [G.LocallyFinite] in
/-- Enlarged blocks with indices at distance at least three are disjoint. -/
theorem blockPlus_disjoint {L : ℕ} (hL : 0 < L) {z w : ℤ × ℤ} (h : 3 ≤ linf (z - w)) :
    Disjoint (P.blockPlus L z) (P.blockPlus L w) := by
  rw [Set.disjoint_left]
  intro v hz hw
  rw [P.mem_blockPlus_iff hL] at hz hw
  have := linf_triangle z (P.blockIndex L v) w
  rw [linf_sub_comm z (P.blockIndex L v)] at this
  omega

/-! ### Coordinates of adjacent vertices -/

omit [DecidableEq V] [G.LocallyFinite] in
theorem latVec_sub (z w : ℤ × ℤ) : P.latVec (z - w) = P.latVec z - P.latVec w := by
  simp only [DoublyPeriodic.latVec, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, sub_smul]
  abel

omit [DecidableEq V] [G.LocallyFinite] in
theorem emb_eq_rep_add (v : V) : P.emb v = P.emb (P.rep v) + P.latVec (P.coord v) := by
  have := P.emb_shift_sub (P.coord v) (P.rep v)
  rw [P.shift_coord_rep] at this
  rw [← this]
  abel

omit [DecidableEq V] in
/-- The coordinates of adjacent vertices differ by a bounded amount. -/
theorem exists_coord_adj_bound : ∃ K : ℤ, 0 ≤ K ∧
    ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K := by
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_edge_bound P
  obtain ⟨D, hD⟩ := (P.finite_orbits.image (fun r => ‖P.emb r‖)).bddAbove
  have hD' : ∀ v, ‖P.emb (P.rep v)‖ ≤ D := fun v =>
    hD (Set.mem_image_of_mem _ ⟨v, rfl⟩)
  refine ⟨⌈‖P.coords‖ * (ℓ + 2 * D)⌉₊, Int.natCast_nonneg _, fun u v huv => ?_⟩
  have h1 : ‖P.latVec (P.coord v - P.coord u)‖ ≤ ℓ + 2 * D := by
    rw [P.latVec_sub]
    have e1 := P.emb_eq_rep_add v
    have e2 := P.emb_eq_rep_add u
    have : P.latVec (P.coord v) - P.latVec (P.coord u) =
        (P.emb v - P.emb u) + (P.emb (P.rep u) - P.emb (P.rep v)) := by
      rw [e1, e2]; abel
    rw [this]
    calc ‖(P.emb v - P.emb u) + (P.emb (P.rep u) - P.emb (P.rep v))‖
        ≤ ‖P.emb v - P.emb u‖ + ‖P.emb (P.rep u) - P.emb (P.rep v)‖ := norm_add_le _ _
      _ ≤ ℓ + (‖P.emb (P.rep u)‖ + ‖P.emb (P.rep v)‖) := by
          gcongr
          · rw [norm_sub_rev]; exact hℓ _ _ huv
          · exact norm_sub_le _ _
      _ ≤ ℓ + 2 * D := by linarith [hD' u, hD' v]
  have h2 := P.supNorm_le_norm_latVec (P.coord v - P.coord u)
  have h3 : supNorm (P.coord v - P.coord u) ≤ ‖P.coords‖ * (ℓ + 2 * D) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have h4 := h3.trans (Nat.le_ceil _)
  rw [supNorm_eq_linf] at h4
  exact_mod_cast h4

omit [DecidableEq V] [G.LocallyFinite] in
/-- Adjacent vertices lie in blocks whose indices are at `ℓ^∞`-distance at most one, once the
side `L` exceeds the coordinate bound `K`. -/
theorem linf_blockIndex_adj {K : ℤ} (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K)
    {L : ℕ} (hL : K < L) (u v : V) (huv : G.Adj u v) :
    linf (P.blockIndex L v - P.blockIndex L u) ≤ 1 := by
  have hL' : (0 : ℤ) < L := by
    have := linf_nonneg (P.coord v - P.coord u)
    have := hK u v huv
    omega
  have key : ∀ a b : ℤ, |b - a| ≤ K → |b / L - a / L| ≤ 1 := by
    intro a b hab
    rw [abs_le] at hab ⊢
    have ha1 := Int.lt_ediv_add_one_mul_self a hL'
    have hb1 := Int.lt_ediv_add_one_mul_self b hL'
    have ha2 : a / L * L ≤ a := Int.ediv_mul_le a hL'.ne'
    have hb2 : b / L * L ≤ b := Int.ediv_mul_le b hL'.ne'
    constructor
    · -- a / L ≤ b / L + 1: a < (b/L + 2) L
      have : a / (L : ℤ) < b / L + 2 := (Int.ediv_lt_iff_lt_mul hL').2 (by nlinarith)
      omega
    · have : b / (L : ℤ) < a / L + 2 := (Int.ediv_lt_iff_lt_mul hL').2 (by nlinarith)
      omega
  have := hK u v huv
  rw [linf_le_iff] at this ⊢
  simp only [blockIndex, Prod.fst_sub, Prod.snd_sub] at this ⊢
  exact ⟨key _ _ this.1, key _ _ this.2⟩

/-! ### Blocks are finite, with a size independent of the index -/

omit [DecidableEq V] [G.LocallyFinite] in
theorem coord_shift (w : ℤ × ℤ) (v : V) : P.coord (P.shift w v) = w + P.coord v := by
  have hinj : Function.Injective (fun z : ℤ × ℤ => P.shift z (P.rep v)) := by
    intro z z' h
    have h' : P.shift z (P.rep v) = P.shift z' (P.rep v) := h
    have : P.latVec z = P.latVec z' := by
      rw [← P.emb_shift_sub z (P.rep v), ← P.emb_shift_sub z' (P.rep v), h']
    exact P.latVec_injective this
  apply hinj
  show P.shift (P.coord (P.shift w v)) (P.rep v) = P.shift (w + P.coord v) (P.rep v)
  conv_lhs => rw [← P.rep_shift w v, P.shift_coord_rep]
  rw [P.shift_add, P.shift_coord_rep]

omit [DecidableEq V] [G.LocallyFinite] in
theorem blockIndex_shift {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) (v : V) :
    P.blockIndex L (P.shift (L • z) v) = z + P.blockIndex L v := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h1 : (L • z).1 = L * z.1 := by simp
  have h2 : (L • z).2 = L * z.2 := by simp
  simp only [blockIndex, P.coord_shift, Prod.fst_add, Prod.snd_add, h1, h2, Prod.ext_iff]
  constructor
  · rw [add_comm ((L : ℤ) * z.1), Int.add_mul_ediv_left _ _ hL'.ne', add_comm]
  · rw [add_comm ((L : ℤ) * z.2), Int.add_mul_ediv_left _ _ hL'.ne', add_comm]

omit [DecidableEq V] [G.LocallyFinite] in
theorem block_finite (L : ℕ) (z : ℤ × ℤ) : (P.block L z).Finite := by
  have hsub : P.block L z ⊆ (fun p : (ℤ × ℤ) × V => P.shift p.1 p.2) ''
      (Set.Icc (L * z.1, L * z.2) (L * z.1 + L, L * z.2 + L) ×ˢ Set.range P.rep) := by
    intro v hv
    simp only [DoublyPeriodic.block, Set.mem_setOf_eq, Set.mem_Ico] at hv
    refine ⟨(P.coord v, P.rep v), ?_, P.shift_coord_rep v⟩
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_range]
    exact ⟨⟨⟨by linarith [hv.1.1], by linarith [hv.2.1]⟩, ⟨by linarith [hv.1.2], by linarith [hv.2.2]⟩⟩, ⟨v, rfl⟩⟩
  exact ((Set.finite_Icc _ _).prod P.finite_orbits).image _ |>.subset hsub

omit [DecidableEq V] [G.LocallyFinite] in
theorem blockPlus_finite (L : ℕ) (z : ℤ × ℤ) : (P.blockPlus L z).Finite := by
  unfold DoublyPeriodic.blockPlus
  refine Set.Finite.biUnion ?_ (fun w _ => P.block_finite L w)
  refine (Set.finite_Icc (z.1 - 1, z.2 - 1) (z.1 + 1, z.2 + 1)).subset (fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw
  rw [max_le_iff, abs_le, abs_le] at hw
  simp only [Set.mem_Icc, Prod.le_def]
  omega

omit [DecidableEq V] [G.LocallyFinite] in
/-- The enlarged block `Q_z⁺` is the translate of `Q_0⁺` by `L z`. -/
theorem blockPlus_eq_image {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) :
    P.blockPlus L z = P.shift (L • z) '' P.blockPlus L 0 := by
  ext v
  constructor
  · intro hv
    refine ⟨P.shift (-(L • z)) v, ?_, P.shift_neg_shift _ _⟩
    rw [P.mem_blockPlus_iff hL] at hv ⊢
    have : P.blockIndex L v = z + P.blockIndex L (P.shift (-(L • z)) v) := by
      rw [← P.blockIndex_shift hL z, P.shift_neg_shift]
    rw [this] at hv
    simpa using hv
  · rintro ⟨w, hw, rfl⟩
    rw [P.mem_blockPlus_iff hL] at hw ⊢
    rw [P.blockIndex_shift hL]
    simpa using hw

omit [DecidableEq V] [G.LocallyFinite] in
theorem ncard_blockPlus {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) :
    (P.blockPlus L z).ncard = (P.blockPlus L 0).ncard := by
  rw [P.blockPlus_eq_image hL z]
  exact Set.ncard_image_of_injective _ (fun a b h => by
    have := congrArg (P.shift (-(L • z))) h
    simpa [P.shift_shift_neg] using this)

end DoublyPeriodic

end Rotor

import Rotor.Support.PathBlocks
import Rotor.Support.BlockGeom

/-!
From the block event to the reach event, `rotor.tex:1476-1481` (proof of Theorem 1.1, the
verification of `eq:block-crossing-hypothesis`): a live path that starts in `Q_z` and leaves
`Q_z⁺` starts with one of at most `C L` directed edges leaving `Q_z` and reaches graph
distance at least `c L` from its first vertex.
-/

open Finset MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)

omit [DecidableEq V] [G.LocallyFinite] in
/-- Coordinates move by at most `K` per edge, hence by at most `K · dist` along a walk. -/
theorem linf_coord_le_mul_dist (hG : G.Connected) {K : ℤ}
    (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K) (u w : V) :
    linf (P.coord w - P.coord u) ≤ K * G.dist u w := by
  have key : ∀ (a b : V) (p : G.Walk a b), linf (P.coord b - P.coord a) ≤ K * p.length := by
    intro a b p
    induction p with
    | nil => simp [linf]
    | cons h p ih =>
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      calc linf (P.coord _ - P.coord _)
          ≤ linf (P.coord _ - P.coord _) + linf (P.coord _ - P.coord _) := linf_triangle _ _ _
        _ ≤ K * p.length + K := add_le_add ih (hK _ _ h)
        _ = K * (p.length + 1) := by ring
  obtain ⟨p, hp⟩ := (hG.preconnected u w).exists_walk_length_eq_dist
  have := key u w p
  rwa [hp] at this

omit [DecidableEq V] [G.LocallyFinite] in
/-- Leaving `Q_z⁺` from `Q_z` changes a coordinate by at least `L`. -/
theorem le_linf_coord_of_block {L : ℕ} (hL : 0 < L) {z : ℤ × ℤ} {u w : V}
    (hu : u ∈ P.block L z) (hw : w ∉ P.blockPlus L z) :
    (L : ℤ) ≤ linf (P.coord w - P.coord u) := by
  rw [P.mem_block_iff hL] at hu
  rw [P.mem_blockPlus_iff hL, not_le, ← hu] at hw
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  simp only [DoublyPeriodic.blockIndex, Prod.mk_sub_mk, linf, lt_max_iff, lt_abs] at hw
  rw [linf, le_max_iff, Prod.fst_sub, Prod.snd_sub]
  have h1 := Int.ediv_mul_le (P.coord u).1 hL'.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (P.coord u).1 hL'
  have h3 := Int.ediv_mul_le (P.coord w).1 hL'.ne'
  have h4 := Int.lt_ediv_add_one_mul_self (P.coord w).1 hL'
  have h5 := Int.ediv_mul_le (P.coord u).2 hL'.ne'
  have h6 := Int.lt_ediv_add_one_mul_self (P.coord u).2 hL'
  have h7 := Int.ediv_mul_le (P.coord w).2 hL'.ne'
  have h8 := Int.lt_ediv_add_one_mul_self (P.coord w).2 hL'
  rw [add_mul, one_mul] at h2 h4 h6 h8
  rcases hw with (hw | hw) | (hw | hw)
  · left
    have := mul_le_mul_of_nonneg_right
      (show (P.coord u).1 / L + 2 ≤ (P.coord w).1 / L by omega) hL'.le
    rw [add_mul] at this
    exact le_abs.2 (Or.inl (by linarith))
  · left
    have := mul_le_mul_of_nonneg_right
      (show (P.coord w).1 / L + 2 ≤ (P.coord u).1 / L by omega) hL'.le
    rw [add_mul] at this
    exact le_abs.2 (Or.inr (by linarith))
  · right
    have := mul_le_mul_of_nonneg_right
      (show (P.coord u).2 / L + 2 ≤ (P.coord w).2 / L by omega) hL'.le
    rw [add_mul] at this
    exact le_abs.2 (Or.inl (by linarith))
  · right
    have := mul_le_mul_of_nonneg_right
      (show (P.coord w).2 / L + 2 ≤ (P.coord u).2 / L by omega) hL'.le
    rw [add_mul] at this
    exact le_abs.2 (Or.inr (by linarith))

omit [DecidableEq V] [G.LocallyFinite] in
/-- The graph distance from `Q_z` to the complement of `Q_z⁺` is at least `L / K`. -/
theorem le_mul_dist_of_block (hG : G.Connected) {K : ℤ}
    (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K) {L : ℕ} (hL : 0 < L)
    {z : ℤ × ℤ} {u w : V} (hu : u ∈ P.block L z) (hw : w ∉ P.blockPlus L z) :
    (L : ℤ) ≤ K * G.dist u w :=
  (le_linf_coord_of_block P hL hu hw).trans (linf_coord_le_mul_dist P hG hK u w)

omit [DecidableEq V] [G.LocallyFinite] in
/-- Along a path the distance from the first vertex takes every value up to its final
value. -/
theorem exists_dist_eq_of_chain (hG : G.Connected) {l : List V} (hch : l.IsChain G.Adj)
    (h0 : 0 < l.length) : ∀ (i : ℕ) (hi : i < l.length) (R : ℕ),
      R ≤ G.dist (l[0]'h0) (l[i]'hi) → ∃ j, ∃ hj : j < l.length, G.dist (l[0]'h0) (l[j]'hj) = R
  | 0, _, R, hR => ⟨0, h0, by simp at hR; rw [hR]; simp⟩
  | i + 1, hi, R, hR => by
    rcases le_or_gt R (G.dist (l[0]'h0) (l[i]'(by omega))) with hle | hgt
    · exact exists_dist_eq_of_chain hG hch h0 i (by omega) R hle
    · refine ⟨i + 1, hi, le_antisymm ?_ hR⟩
      have hadj : G.Adj (l[i]'(by omega)) (l[i + 1]'hi) :=
        List.isChain_iff_getElem.1 hch i hi
      calc G.dist (l[0]'h0) (l[i + 1]'hi)
          ≤ G.dist (l[0]'h0) (l[i]'(by omega)) + G.dist (l[i]'(by omega)) (l[i + 1]'hi) :=
            hG.dist_triangle
        _ = G.dist (l[0]'h0) (l[i]'(by omega)) + 1 := by
            rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj]
        _ ≤ R := by omega

/-- The block event is contained in the union of the reach events over the directed edges
leaving `Q_z` (`rotor.tex:1476-1481`). -/
theorem blockEvent_subset_biUnion (π : Mechanism G) (hG : G.Connected) {K : ℤ} (hK0 : 0 ≤ K)
    (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K) {L : ℕ} (hL : 0 < L)
    (z : ℤ × ℤ) {R : ℕ} (hR : (R : ℤ) * (K + 1) ≤ L) :
    blockEvent π P L z ⊆
      ⋃ (u ∈ P.block L z) (v ∈ G.neighborFinset u), liveReachEvent π u v R := by
  rintro ρ ⟨l, hpath, hlive, ⟨h0, hu⟩, -, hlast⟩
  have hne : l ≠ [] := List.ne_nil_of_length_pos h0
  have hlast' : l.getLast hne ∉ P.blockPlus L z :=
    hlast _ (List.getLast?_eq_some_getLast hne)
  rw [List.getLast_eq_getElem] at hlast'
  rw [List.get_eq_getElem] at hu
  have hlen : 2 ≤ l.length := by
    by_contra hlt
    have h1 : l.length = 1 := by omega
    have : l[l.length - 1]'(by omega) = l[0]'h0 := by simp [h1]
    rw [this] at hlast'
    exact hlast' (block_subset_blockPlus P hL z hu)
  have hdist := le_mul_dist_of_block P hG hK hL hu hlast'
  have hRd : R ≤ G.dist (l[0]'h0) (l[l.length - 1]'(by omega)) := by
    have h1 : (R : ℤ) * (K + 1) ≤ (K + 1) * G.dist (l[0]'h0) (l[l.length - 1]'(by omega)) := by
      have := mul_le_mul_of_nonneg_left (show K ≤ K + 1 by omega)
        (Int.natCast_nonneg (G.dist (l[0]'h0) (l[l.length - 1]'(by omega))))
      nlinarith
    have h2 : (0 : ℤ) < K + 1 := by omega
    rw [mul_comm] at h1
    exact_mod_cast le_of_mul_le_mul_left h1 h2
  obtain ⟨j, hj, hdj⟩ := exists_dist_eq_of_chain hG hpath.2 h0 (l.length - 1) (by omega) R hRd
  have hadj : G.Adj (l[0]'h0) (l[1]'(by omega)) := List.isChain_iff_getElem.1 hpath.2 0 (by omega)
  refine Set.mem_iUnion₂.2 ⟨l[0]'h0, hu, Set.mem_iUnion₂.2 ⟨l[1]'(by omega),
    (G.mem_neighborFinset _ _).2 hadj, ?_⟩⟩
  refine ⟨l, hpath, hlive, ?_, ?_, l[j]'hj, List.getElem_mem hj, hdj⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
  · rw [List.getElem?_eq_getElem (by omega)]

omit [G.LocallyFinite] in
/-- `Q⁺_0` has at most `(3L+1)² |Q|` vertices. -/
theorem ncard_blockPlus_zero_le {L : ℕ} (hL : 0 < L) {Q : Finset V} (hQ : ↑Q = Set.range P.rep) :
    (P.blockPlus L 0).ncard ≤ (3 * L + 1) ^ 2 * Q.card := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  set box : Finset (ℤ × ℤ) := Finset.Icc (-(L : ℤ)) (2 * L) ×ˢ Finset.Icc (-(L : ℤ)) (2 * L)
    with hbox
  have hsub : P.blockPlus L 0 ⊆ ↑((box ×ˢ Q).image (fun p => P.shift p.1 p.2)) := by
    intro v hv
    rw [P.mem_blockPlus_iff hL, sub_zero, linf_le_iff] at hv
    simp only [DoublyPeriodic.blockIndex, abs_le] at hv
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(P.coord v, P.rep v), ?_, P.shift_coord_rep v⟩)
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, by rw [← Finset.mem_coe, hQ]; exact ⟨v, rfl⟩⟩
    · have := Int.ediv_mul_le (P.coord v).1 hL'.ne'
      nlinarith [hv.1.1]
    · have := Int.lt_ediv_add_one_mul_self (P.coord v).1 hL'
      nlinarith [hv.1.2]
    · have := Int.ediv_mul_le (P.coord v).2 hL'.ne'
      nlinarith [hv.2.1]
    · have := Int.lt_ediv_add_one_mul_self (P.coord v).2 hL'
      nlinarith [hv.2.2]
  calc (P.blockPlus L 0).ncard ≤ (↑((box ×ˢ Q).image (fun p => P.shift p.1 p.2)) : Set V).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((box ×ˢ Q).image (fun p => P.shift p.1 p.2)).card := Set.ncard_coe_finset _
    _ ≤ (box ×ˢ Q).card := Finset.card_image_le
    _ = (3 * L + 1) ^ 2 * Q.card := by
        rw [Finset.card_product, hbox, Finset.card_product, Int.card_Icc]
        have : (2 * (L : ℤ) + 1 - -(L : ℤ)).toNat = 3 * L + 1 := by omega
        rw [this]; ring

/-- The block event has probability at most `|Q⁺| · D · C e^{-cR}`. -/
theorem uniformLaw_blockEvent_le (π : Mechanism G) (hG : G.Connected) {K : ℤ} (hK0 : 0 ≤ K)
    (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K) {L : ℕ} (hL : 0 < L)
    (z : ℤ × ℤ) {R : ℕ} (hR : (R : ℤ) * (K + 1) ≤ L) {D : ℕ} (hD : ∀ v, G.degree v ≤ D)
    (b : ENNReal) (hpass : ∀ u v : V, G.Adj u v → uniformLaw π (liveReachEvent π u v R) ≤ b) :
    uniformLaw π (blockEvent π P L z) ≤ ((P.blockPlus L 0).ncard * D : ENNReal) * b := by
  classical
  have hfin := P.block_finite L z
  have hsub : blockEvent π P L z ⊆
      ⋃ u ∈ hfin.toFinset, ⋃ v ∈ G.neighborFinset u, liveReachEvent π u v R := by
    refine (blockEvent_subset_biUnion P π hG hK0 hK hL z hR).trans ?_
    intro ρ hρ
    obtain ⟨u, hu, hρ'⟩ := Set.mem_iUnion₂.1 hρ
    exact Set.mem_iUnion₂.2 ⟨u, hfin.mem_toFinset.2 hu, hρ'⟩
  calc uniformLaw π (blockEvent π P L z)
      ≤ uniformLaw π (⋃ u ∈ hfin.toFinset, ⋃ v ∈ G.neighborFinset u, liveReachEvent π u v R) :=
        measure_mono hsub
    _ ≤ ∑ u ∈ hfin.toFinset, uniformLaw π (⋃ v ∈ G.neighborFinset u, liveReachEvent π u v R) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ hfin.toFinset, ∑ v ∈ G.neighborFinset u, uniformLaw π (liveReachEvent π u v R) :=
        Finset.sum_le_sum (fun u _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ u ∈ hfin.toFinset, ∑ v ∈ G.neighborFinset u, b :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v hv =>
          hpass u v ((G.mem_neighborFinset _ _).1 hv)))
    _ = ∑ u ∈ hfin.toFinset, (G.degree u : ENNReal) * b := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    _ ≤ ∑ u ∈ hfin.toFinset, (D : ENNReal) * b := by
        refine Finset.sum_le_sum (fun u _ => ?_)
        gcongr
        exact_mod_cast hD u
    _ = (hfin.toFinset.card : ENNReal) * D * b := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ ((P.blockPlus L 0).ncard * D : ENNReal) * b := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card _ hfin, ← P.ncard_blockPlus hL z]
        exact_mod_cast Set.ncard_le_ncard (block_subset_blockPlus P hL z) (P.blockPlus_finite L z)

end Rotor

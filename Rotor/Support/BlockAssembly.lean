/-
Assembly of the block estimate: on the cover event, the witness path forces the marked
block events along a duplicate-free king path of block indices of `m₀` steps
(`rotor.tex:1263-1273`).
-/
import Rotor.Support.Witness
import Rotor.Support.PathBlocks
import Rotor.Support.BlockChain

open MeasureTheory
open scoped ENNReal

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

omit [G.LocallyFinite] in
/-- A path whose failures are all marked is live at every unmarked internal vertex. -/
theorem isLiveUnmarked_of_covers {p : MPair G} {l : List V} (h : CoversFailures π p.1 p.2 l) :
    IsLiveUnmarked π p l := by
  classical
  intro i hi hi0
  by_cases hl : LiveAtIndex π p.1 l i
  · exact Or.inr hl
  · left
    refine h i ?_ (by omega)
    simp only [liveFailures, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hi0, hi, hl⟩

/-- Among nine distinct points different from `z`, one is at sup-distance at least two. -/
theorem exists_far_of_nine {z : ℤ × ℤ} {l : List (ℤ × ℤ)} (hnd : l.Nodup) (hlen : 9 ≤ l.length)
    (hne : ∀ x ∈ l, x ≠ z) : ∃ x ∈ l, 2 ≤ linf (x - z) := by
  by_contra hcon
  push_neg at hcon
  have hsub : l.toFinset ⊆ kingNbrs z := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact mem_kingNbrs.2 ⟨(hne x hx).symm, by have := hcon x hx; omega⟩
  have := Finset.card_le_card hsub
  rw [card_kingNbrs, List.toFinset_card_of_nodup hnd] at this
  omega

omit [G.LocallyFinite] in
/-- On the cover event, the marked block events hold along every element of the first
`m₀ + 1` blocks of the coarse path, provided the coarse path has at least ten more elements. -/
theorem coverEvent_subset {K : ℤ} (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K)
    {L : ℕ} (hL : K < L) (hL0 : 0 < L) (η : ℝ) (u v : V) (R : ℕ) (m₀ : ℕ)
    (hm₀ : ∀ w : V, G.dist u w = R → (m₀ : ℤ) + 10 ≤ linf (P.blockIndex L w - P.blockIndex L u) + 1) :
    coverEvent π η u v R ⊆
      ⋃ q ∈ (kingSeqs (P.blockIndex L u) m₀).filter (fun q => q.Nodup),
        ⋂ z ∈ q, markedBlockEvent π P L z := by
  classical
  rintro p ⟨l, ⟨hpath, hhead, -, ⟨w, hw, hdist⟩, -⟩, hcov⟩
  -- the prefix of `l` ending at `w`
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  set l' := infixAt l 0 (j + 1) with hl'
  have hk : 0 + (j + 1) ≤ l.length := by omega
  have hlen' : l'.length = j + 1 := length_infixAt l 0 (j + 1) hk
  have hpath' : IsPath G l' := isPath_infixAt hpath 0 (j + 1)
  have hlive' : IsLiveUnmarked π p l' :=
    isLiveUnmarked_infixAt π p l 0 (j + 1) hk (isLiveUnmarked_of_covers π hcov)
  have hne' : l' ≠ [] := by rintro h0; rw [h0] at hlen'; simp at hlen'
  have hhead' : l'.head? = some u := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), getElem_infixAt]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    simpa using hhead
  have hlast' : l'.getLast? = some l[j] := by
    rw [List.getLast?_eq_getElem?, hlen', Nat.add_sub_cancel, List.getElem?_eq_getElem (by omega),
      getElem_infixAt]
    simp
  -- the coarse king path
  obtain ⟨c, hcc, hnd, hsub, hch, hcl⟩ := exists_blockChain P hK hL l' hpath'.2 hne'
  have hchu : c.head? = some (P.blockIndex L u) := by
    rw [hch, List.head?_map, hhead']; rfl
  have hclw : c.getLast? = some (P.blockIndex L l[j]) := by
    rw [hcl, List.getLast?_map, hlast']; rfl
  have hclen : m₀ + 10 ≤ c.length := by
    have h1 := linf_le_of_kingChain c hcc _ hchu _ hclw
    have h2 := hm₀ l[j] hdist
    have h3 : 0 < c.length := by
      rcases c with _ | ⟨x, c⟩
      · simp at hchu
      · simp
    omega
  -- the first `m₀ + 1` blocks
  set q := (c.take (m₀ + 1)).reverse with hq
  have htake_len : (c.take (m₀ + 1)).length = m₀ + 1 := by
    rw [List.length_take]; omega
  have hqmem : q ∈ (kingSeqs (P.blockIndex L u) m₀).filter (fun q => q.Nodup) := by
    rw [Finset.mem_filter]
    refine ⟨reverse_mem_kingSeqs _ m₀ _ htake_len ?_ (hcc.take _) (hnd.sublist (List.take_sublist _ _)),
      List.nodup_reverse.2 (hnd.sublist (List.take_sublist _ _))⟩
    rw [List.head?_take, hchu]
    simp
  refine Set.mem_iUnion₂.2 ⟨q, hqmem, Set.mem_iInter₂.2 (fun z hz => ?_)⟩
  rw [hq, List.mem_reverse] at hz
  -- `z = c[i]` with `i ≤ m₀`, and some later element of `c` is at distance at least two
  obtain ⟨i, hi, hzi⟩ := List.getElem_of_mem hz
  rw [List.getElem_take] at hzi
  subst hzi
  have hi' : i < m₀ + 1 := by rw [htake_len] at hi; exact hi
  have hnine : 9 ≤ ((c.drop (i + 1)).take 9).length := by
    rw [List.length_take, List.length_drop]; omega
  have hne9 : ∀ x ∈ (c.drop (i + 1)).take 9, x ≠ c.get ⟨i, by omega⟩ := by
    intro x hx hxz
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take, List.getElem_drop] at hxz
    have := (List.Nodup.getElem_inj_iff hnd).1 hxz
    omega
  obtain ⟨z', hz'mem, hz'far⟩ := exists_far_of_nine
    (hnd.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))) hnine hne9
  obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hz'mem
  rw [List.getElem_take, List.getElem_drop] at hz'far
  obtain ⟨a, b, hab, ha, hb⟩ := Sublist.exists_lt_of_lt hsub (i := i) (j := i + 1 + j')
    (by omega) (by rw [List.length_take, List.length_drop] at hj'; omega)
  simp only [List.get_eq_getElem, List.getElem_map] at ha hb
  refine markedBlockEvent_of_visit π P hL0 _ p l' hpath' hlive' a (by simpa using a.isLt) ?_ b
    (by simpa using b.isLt) hab ?_
  · rw [P.mem_block_iff hL0]
    exact ha
  · rw [P.mem_blockPlus_iff hL0, hb]
    exact fun h => absurd h (not_le.2 (lt_of_lt_of_le (by norm_num : (1 : ℤ) < 2) hz'far))

theorem ennreal_seven_eighths (m : ℕ) :
    ((8 * 7 ^ m : ℕ) : ℝ≥0∞) * (1 / 8 : ℝ≥0∞) ^ (m + 1) = (7 / 8 : ℝ≥0∞) ^ m := by
  have h1 : (1 / 8 : ℝ≥0∞) = ENNReal.ofReal (1 / 8) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have h2 : (7 / 8 : ℝ≥0∞) = ENNReal.ofReal (7 / 8) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h1, h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  rw [pow_succ, show (8 : ℝ) * 7 ^ m * ((1 / 8) ^ m * (1 / 8)) = (7 * (1 / 8)) ^ m * (8 * (1 / 8)) by
    rw [mul_pow]; ring]
  norm_num

/-- The cover event has probability at most `(7/8)^{m₀}` (`rotor.tex:1268-1273`). -/
theorem mLaw_coverEvent_le {K : ℤ} (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K)
    {L : ℕ} (hL : K < L) (hL0 : 0 < L) (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] (s : NNReal) (hs : s ≤ 1) {ε : ℝ}
    (hLSS : ∀ μ : Measure (ℤ × ℤ → Bool), IsProbabilityMeasure μ →
      External.KDependent 2 μ → (∀ z, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
      ∀ A : Set (ℤ × ℤ → Bool), MeasurableSet A → External.IsIncreasing A →
        μ A ≤ External.bernoulliField (1 / 8) External.eighth_le_one A)
    (hsite : ∀ z, mLaw ν s hs (markedBlockEvent π P L z) ≤ ENNReal.ofReal (2 * ε))
    (η : ℝ) (u v : V) (R : ℕ) (m₀ : ℕ)
    (hm₀ : ∀ w : V, G.dist u w = R → (m₀ : ℤ) + 10 ≤ linf (P.blockIndex L w - P.blockIndex L u) + 1) :
    mLaw ν s hs (coverEvent π η u v R) ≤ (7 / 8 : ℝ≥0∞) ^ m₀ := by
  classical
  calc mLaw ν s hs (coverEvent π η u v R)
      ≤ mLaw ν s hs (⋃ q ∈ (kingSeqs (P.blockIndex L u) m₀).filter (fun q => q.Nodup),
          ⋂ z ∈ q, markedBlockEvent π P L z) :=
        measure_mono (coverEvent_subset π P hK hL hL0 η u v R m₀ hm₀)
    _ ≤ ∑ q ∈ (kingSeqs (P.blockIndex L u) m₀).filter (fun q => q.Nodup),
          mLaw ν s hs (⋂ z ∈ q, markedBlockEvent π P L z) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ (kingSeqs (P.blockIndex L u) m₀).filter (fun q => q.Nodup),
          (1 / 8 : ℝ≥0∞) ^ (m₀ + 1) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.mem_filter] at hq
        have hlen := (mem_kingSeqs _ _ hq.1).1
        have hZ : (⋂ z ∈ q, markedBlockEvent π P L z) = ⋂ z ∈ q.toFinset, markedBlockEvent π P L z := by
          ext p; simp
        rw [hZ]
        have := mLaw_iInter_markedBlockEvent_le π P L ν s hs hL0 hLSS hsite q.toFinset
        rwa [List.toFinset_card_of_nodup hq.2, hlen] at this
    _ = ((kingSeqs (P.blockIndex L u) m₀).filter (fun q => q.Nodup)).card * (1 / 8 : ℝ≥0∞) ^ (m₀ + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 * 7 ^ m₀ : ℕ) * (1 / 8 : ℝ≥0∞) ^ (m₀ + 1) := by
        gcongr
        exact_mod_cast (Finset.card_filter_le _ _).trans (card_kingSeqs _ m₀)
    _ = (7 / 8 : ℝ≥0∞) ^ m₀ := ennreal_seven_eighths m₀

end Rotor

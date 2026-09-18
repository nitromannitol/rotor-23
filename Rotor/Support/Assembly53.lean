import Rotor.Support.Surgery

open Finset Classical

namespace Rotor

/-! ### From connections to box crossings -/

/-- A path from `x` reaching `ℓ^∞` distance `r` crosses the box. -/
theorem boxCrossing_of_path {ω : BondConfig} {x : Site} {r : ℕ} {l : List Site}
    (hl : IsOpenPath ω l) (hh : l.head? = some x) (hfar : ∃ v ∈ l, (r : ℤ) ≤ linfDist v x) :
    ω ∈ boxCrossing x r := by
  have hex : ∃ i : ℕ, ∃ v, l[i]? = some v ∧ (r : ℤ) ≤ linfDist v x := by
    obtain ⟨v, hv, hr⟩ := hfar
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
    exact ⟨i, v, hi, hr⟩
  obtain ⟨w, hw, hwr⟩ := Nat.find_spec hex
  set k := Nat.find hex with hk
  have hmin : ∀ i < k, ∀ v, l[i]? = some v → linfDist v x < r := by
    intro i hi v hv
    by_contra hcon
    exact Nat.find_min hex hi ⟨v, hv, by omega⟩
  have hkl : k < l.length := (List.getElem?_eq_some_iff.1 hw).1
  have hx0 : l[0]? = some x := by rw [← List.head?_eq_getElem?]; exact hh
  have hwr' : linfDist w x = r := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, hx0] at hw
      have hwx : w = x := (Option.some.inj hw).symm
      rw [hwx] at hwr ⊢
      have : linfDist x x = 0 := by simp [linfDist]
      omega
    · obtain ⟨u, hu⟩ : ∃ u, l[k - 1]? = some u := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hur := hmin (k - 1) (by omega) u hu
      have hadj : squareGraph.Adj u w :=
        isChain_getElem? hl.1.2 hu (by rw [show k - 1 + 1 = k by omega]; exact hw)
      have := linfDist_adj_le (r := x) hadj
      omega
  refine ⟨l.take (k + 1), isOpenPath_take hl (k + 1), ?_, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_take, if_pos (by omega), hx0]
  · intro v hv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
    rw [List.getElem?_take] at hi
    split_ifs at hi with hik
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hik) with hlt | heq
    · exact (hmin i hlt v hi).le
    · rw [heq, hw] at hi
      rw [← Option.some.inj hi, hwr']
  · refine ⟨w, ?_, hwr'⟩
    rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega),
      Nat.add_sub_cancel, List.getElem?_take, if_pos (by omega)]
    exact hw

/-! ### The sphere -/

/-- The `ℓ^∞` sphere of radius `r` about `x`. -/
noncomputable def sphere (x : Site) (r : ℕ) : Finset Site :=
  ((Icc (x.1 - r) (x.1 + r)) ×ˢ (Icc (x.2 - r) (x.2 + r))).filter (fun y => linfDist y x = r)

theorem mem_sphere {x : Site} {r : ℕ} {y : Site} : y ∈ sphere x r ↔ linfDist y x = r := by
  unfold sphere
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    unfold linfDist at h
    have h1 := abs_le.1 (le_trans (le_max_left _ _) h.le)
    have h2 := abs_le.1 (le_trans (le_max_right _ _) h.le)
    omega

theorem card_sphere_le (x : Site) (r : ℕ) : (sphere x r).card ≤ (2 * r + 1) ^ 2 := by
  refine le_trans (card_filter_le _ _) ?_
  rw [card_product, Int.card_Icc, Int.card_Icc,
    show x.1 + r + 1 - (x.1 - r) = 2 * r + 1 by ring,
    show x.2 + r + 1 - (x.2 - r) = 2 * r + 1 by ring]
  have : (2 * (r : ℤ) + 1).toNat = 2 * r + 1 := by omega
  rw [this, sq]

/-! ### The events on the bonds -/

/-- Open pattern-free paths from `x` to `y` in the box. -/
def PFEvent (x y : Site) (r : ℕ) : Set BondConfig :=
  {ω | ∃ l, IsOpenPath ω l ∧ l.head? = some x ∧ l.getLast? = some y ∧
    (∀ v ∈ l, v ∈ Dset x y r) ∧ ¬ ContainsPattern l}

/-- Open paths from `x` to `y` in the box. -/
def ConnEvent (x y : Site) (r : ℕ) : Set BondConfig :=
  {ω | ∃ l, IsOpenPath ω l ∧ l.head? = some x ∧ l.getLast? = some y ∧ ∀ v ∈ l, v ∈ Dset x y r}

theorem isOpenPath_congr_F {x y : Site} {r : ℕ} {ω₁ ω₂ : BondConfig}
    (h : ∀ b ∈ Fset x y r, ω₁ b = ω₂ b) {l : List Site} (hD : ∀ v ∈ l, v ∈ Dset x y r)
    (hl : IsOpenPath ω₁ l) : IsOpenPath ω₂ l := by
  refine isOpenPath_of_agree hl (fun i hi => ?_)
  have hadj := (List.isChain_iff_getElem.1 hl.1.2) i hi
  exact (h _ (mem_Fset.2 ⟨l[i], l[i + 1], hD _ (List.getElem_mem _), hD _ (List.getElem_mem _),
    hadj, rfl⟩)).symm

theorem pfEvent_determined (x y : Site) (r : ℕ) :
    BondDetermined (Fset x y r) (PFEvent x y r) := by
  intro ω ω' h
  constructor
  · rintro ⟨l, hl, hh, hlast, hD, hp⟩
    exact ⟨l, isOpenPath_congr_F h hD hl, hh, hlast, hD, hp⟩
  · rintro ⟨l, hl, hh, hlast, hD, hp⟩
    exact ⟨l, isOpenPath_congr_F (fun b hb => (h b hb).symm) hD hl, hh, hlast, hD, hp⟩

theorem connEvent_determined (x y : Site) (r : ℕ) :
    BondDetermined (Fset x y r) (ConnEvent x y r) := by
  intro ω ω' h
  constructor
  · rintro ⟨l, hl, hh, hlast, hD⟩
    exact ⟨l, isOpenPath_congr_F h hD hl, hh, hlast, hD⟩
  · rintro ⟨l, hl, hh, hlast, hD⟩
    exact ⟨l, isOpenPath_congr_F (fun b hb => (h b hb).symm) hD hl, hh, hlast, hD⟩

theorem constrainedCrossing_subset (x : Site) (r : ℕ) :
    constrainedCrossing x r ⊆ ⋃ y ∈ sphere x r, PFEvent x y r := by
  rintro ω ⟨l, hl, hh, hin, ⟨y, hy, hyr⟩, hp⟩
  rw [Set.mem_iUnion₂]
  exact ⟨y, mem_sphere.2 hyr, l, hl, hh, hy, fun v hv => mem_Dset_of_linf hyr (hin v hv), hp⟩

theorem connEvent_subset_boxCrossing {x y : Site} {r : ℕ} (hy : linfDist y x = r) :
    ConnEvent x y r ⊆ boxCrossing x r := by
  rintro ω ⟨l, hl, hh, hlast, -⟩
  refine boxCrossing_of_path hl hh ⟨y, ?_, hy.ge⟩
  rw [List.getLast?_eq_getElem?] at hlast
  exact List.mem_of_getElem? hlast

theorem containsPattern_of_traverses {l : List Site} {c : Site} (h : Traverses l (copyAt c)) :
    ContainsPattern l := by
  obtain ⟨i, h⟩ := h
  have hlen : (copyAt c).length = 6 := copyAt_length c
  have heq : copyAt c = pstar.map (· + ((1, 1) + c)) := by
    unfold copyAt copy0
    rw [List.map_map]
    try (refine List.map_congr_left (fun v _ => ?_); simp [Function.comp, add_assoc])
  rw [hlen] at h
  exact ⟨i, (1, 1) + c, heq ▸ h⟩

/-! ### The real-number bound -/

theorem poly_exp_bound {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ) (hr : 1 ≤ r) :
    (((2 * r + 1) ^ 2 : ℕ) : ℝ) * (C * Real.exp (-c * r)) ≤
      144 * C / c ^ 2 * Real.exp (-(c / 2) * r) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hc0 : c ≠ 0 := hc.ne'
  have hexp := Real.add_one_le_exp (c * r / 4)
  have h1 : (r : ℝ) ≤ 4 / c * Real.exp (c * r / 4) := by
    calc (r : ℝ) = 4 / c * (c * r / 4) := by field_simp
      _ ≤ 4 / c * Real.exp (c * r / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have hsq : Real.exp (c * r / 4) ^ 2 = Real.exp (c * r / 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : (r : ℝ) ^ 2 ≤ 16 / c ^ 2 * Real.exp (c * r / 2) := by
    calc (r : ℝ) ^ 2 ≤ (4 / c * Real.exp (c * r / 4)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 16 / c ^ 2 * Real.exp (c * r / 2) := by rw [mul_pow, div_pow, hsq]; norm_num
  have h3 : (((2 * r + 1) ^ 2 : ℕ) : ℝ) ≤ 9 * (r : ℝ) ^ 2 := by
    push_cast
    nlinarith [hr']
  calc (((2 * r + 1) ^ 2 : ℕ) : ℝ) * (C * Real.exp (-c * r))
      ≤ 9 * (r : ℝ) ^ 2 * (C * Real.exp (-c * r)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ ≤ 9 * (16 / c ^ 2 * Real.exp (c * r / 2)) * (C * Real.exp (-c * r)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by positivity)
    _ = 144 * C / c ^ 2 * Real.exp (-(c / 2) * r) := by
        rw [show -(c / 2) * r = c * r / 2 + (-c * r) by ring, Real.exp_add]
        field_simp
        ring

end Rotor

import Rotor.Support.ReachBound
import Rotor.Support.LiveRecurrence
import Rotor.Support.SquareBasics
import Rotor.Frozen.Square.DualPath
import Rotor.Frozen.Square.Exploration

/-!
Proposition 5.1 (`prop:square-passage`), part 8: from live paths to the reach event.  A live
path reaching graph distance `R` yields (Lemma 5.2) a directed open dual path from the face on
the right of its first edge to a face at `ℓ^∞` distance about `R/2`; if the exploration from
that face terminates, Lemma 5.4 (ii) puts the far face in the visited set or in a finite
component of its complement, so a visited face is at least as far; if it never terminates, the
visited set is unbounded, since no bond is tested twice.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-! ### Distances -/

theorem dist_le_l1 (u w : Site) : (squareGraph.dist u w : ℤ) ≤ |w.1 - u.1| + |w.2 - u.2| := by
  have hconn := squareGraph_connected
  suffices h : ∀ n : ℕ, ∀ u w : Site, (|w.1 - u.1| + |w.2 - u.2|).toNat = n →
      (squareGraph.dist u w : ℤ) ≤ |w.1 - u.1| + |w.2 - u.2| from h _ u w rfl
  intro n
  induction n with
  | zero =>
    intro u w hn
    have h0 : |w.1 - u.1| + |w.2 - u.2| = 0 := by
      have := Int.toNat_of_nonneg (show 0 ≤ |w.1 - u.1| + |w.2 - u.2| by positivity)
      omega
    have hu : u = w := by
      obtain ⟨u1, u2⟩ := u; obtain ⟨w1, w2⟩ := w
      simp only [abs_eq_max_neg] at h0
      ext <;> simp <;> omega
    subst hu
    simp
  | succ n ih =>
    intro u w hn
    obtain ⟨u1, u2⟩ := u; obtain ⟨w1, w2⟩ := w
    -- a neighbour `u'` of `u` one step closer to `w`
    obtain ⟨u', hadj, hdist⟩ : ∃ u' : Site, squareGraph.Adj (u1, u2) u' ∧
        (|w1 - u'.1| + |w2 - u'.2|).toNat = n := by
      rcases lt_trichotomy u1 w1 with h | h | h
      · refine ⟨(u1 + 1, u2), ?_, ?_⟩
        · rw [squareGraph_adj]; simp
        · simp only at hn ⊢
          rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
      · subst h
        rcases lt_trichotomy u2 w2 with h2 | h2 | h2
        · refine ⟨(u1, u2 + 1), ?_, ?_⟩
          · rw [squareGraph_adj]; simp
          · simp only at hn ⊢
            rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
        · subst h2; simp at hn
        · refine ⟨(u1, u2 - 1), ?_, ?_⟩
          · rw [squareGraph_adj]; simp
          · simp only at hn ⊢
            rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
      · refine ⟨(u1 - 1, u2), ?_, ?_⟩
        · rw [squareGraph_adj]; simp
        · simp only at hn ⊢
          rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
    have h1 := ih u' (w1, w2) hdist
    have htri := hconn.dist_triangle (u := (u1, u2)) (v := u') (w := (w1, w2))
    have hone : squareGraph.dist (u1, u2) u' = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj
    have htri' : (squareGraph.dist (u1, u2) (w1, w2) : ℤ) ≤
        (squareGraph.dist (u1, u2) u' : ℤ) + squareGraph.dist u' (w1, w2) := by exact_mod_cast htri
    have hone' : (squareGraph.dist (u1, u2) u' : ℤ) = 1 := by exact_mod_cast hone
    have hsum : |w1 - u1| + |w2 - u2| = |w1 - u'.1| + |w2 - u'.2| + 1 := by
      have := Int.toNat_of_nonneg (show 0 ≤ |w1 - u1| + |w2 - u2| by positivity)
      have := Int.toNat_of_nonneg (show 0 ≤ |w1 - u'.1| + |w2 - u'.2| by positivity)
      dsimp only at hn
      omega
    dsimp only at h1 ⊢
    omega

theorem dist_le_two_linf (u w : Site) : (squareGraph.dist u w : ℤ) ≤ 2 * linfDist w u := by
  have := dist_le_l1 u w
  unfold linfDist
  obtain ⟨u1, u2⟩ := u; obtain ⟨w1, w2⟩ := w
  simp only at this ⊢
  have h1 : |w1 - u1| ≤ max |w1 - u1| |w2 - u2| := le_max_left _ _
  have h2 : |w2 - u2| ≤ max |w1 - u1| |w2 - u2| := le_max_right _ _
  omega

theorem linfDist_comm (a b : Site) : linfDist a b = linfDist b a := by
  simp [linfDist, abs_sub_comm]

theorem rightFace_near (v : Site) (a : Dir) : linfDist (rightFace v a) v ≤ 1 := by
  obtain ⟨v1, v2⟩ := v
  fin_cases a <;> simp [rightFace, dirVec, linfDist, abs_eq_max_neg]

/-! ### Finite components have visited faces beyond them -/

theorem exists_far_visited {V : Finset Site} {g f₀ : Site} (h : InFiniteComponent V g) :
    ∃ g' ∈ V, linfDist g f₀ ≤ linfDist g' f₀ := by
  rw [inFiniteComponent_iff] at h
  obtain ⟨hgV, hfin⟩ := h
  have hgS : g ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact Relation.ReflTransGen.refl
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun z => linfDist z f₀) ⟨g, hgS⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hz
  have hzV : z ∉ V := AvoidReach.notMem hgV hz
  -- a neighbour of `z` one step farther from `f₀`
  obtain ⟨z', hadj, hfar⟩ : ∃ z' : Site, squareGraph.Adj z z' ∧ linfDist z' f₀ = linfDist z f₀ + 1 := by
    obtain ⟨z1, z2⟩ := z; obtain ⟨f1, f2⟩ := f₀
    simp only [linfDist]
    rcases le_or_gt |z2 - f2| |z1 - f1| with hx | hx
    · rcases le_or_gt 0 (z1 - f1) with hs | hs
      · refine ⟨(z1 + 1, z2), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
      · refine ⟨(z1 - 1, z2), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
    · rcases le_or_gt 0 (z2 - f2) with hs | hs
      · refine ⟨(z1, z2 + 1), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
      · refine ⟨(z1, z2 - 1), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
  by_cases hz'V : z' ∈ V
  · refine ⟨z', hz'V, ?_⟩
    have := hmax g hgS
    simp only at this
    omega
  · exfalso
    have hz'S : z' ∈ hfin.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Relation.ReflTransGen.tail hz ⟨hzV, hz'V, hadj⟩
    have := hmax z' hz'S
    simp only at this
    omega

/-! ### An infinite exploration is unbounded -/

/-- The exploration never terminates. -/
def NonTerm (f d : Site) : Set (Config squareGraph) :=
  {ρ | ∀ n, (explore ρ f d n).active ≠ []}

theorem nonTerm_subset_reach (f : Site) {d : Site} (hd : IsUnit d) (R' : ℕ) :
    NonTerm f d ⊆ ReachEvent f d R' := by
  intro ρ hρ
  by_contra hnot
  simp only [ReachEvent, Set.mem_setOf_eq, not_exists, not_and, not_le] at hnot
  set N := (boxBonds f R').card + 1 with hN
  have hact := hρ N
  have hlen : (history ρ f d N).length = N := history_length_eq ρ f d N hact
  have hnd := tested_bonds_nodup ρ f hd N
  have hinv := explInv_explore ρ f hd N
  have hsub : ((explore ρ f d N).tested.map (fun t => s(t.1, t.2.1))).toFinset ⊆ boxBonds f R' := by
    intro b hb
    rw [List.mem_toFinset, List.mem_map] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    have htail := hinv.tested_tail t ht
    have hadj := hinv.tested_adj t ht
    have h1 := hnot N t.1 htail
    have h2 := linfDist_adj_le (r := f) hadj
    exact mem_boxBonds_of (by omega) (by omega)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at hcard
  unfold history at hlen
  rw [List.length_map] at hlen
  omega

/-! ### Live paths reach far faces -/

theorem liveAtIndex_take {ρ : Config squareGraph} {l : List Site} {m j : ℕ}
    (h : LiveAtIndex clockwise ρ l j) (hj : j + 1 < (l.take m).length) :
    LiveAtIndex clockwise ρ (l.take m) j := by
  obtain ⟨⟨hj0, hj1⟩, hlive⟩ := h
  refine ⟨⟨hj0, hj⟩, ?_⟩
  simp only [List.get_eq_getElem, List.getElem_take] at hlive ⊢
  exact hlive

theorem isLive_take {ρ : Config squareGraph} {l : List Site} (h : IsLive clockwise ρ l) (m : ℕ) :
    IsLive clockwise ρ (l.take m) := by
  intro j hj0 hj1
  have hj1' : j + 1 < l.length := by
    rw [List.length_take] at hj1; omega
  exact liveAtIndex_take (h j hj0 hj1') hj1

theorem liveReach_subset (u v : Site) (R : ℕ) (hR : 8 ≤ R) :
    liveReachEvent clockwise u v R ⊆
      ReachEvent (rightFace u (dirOf (v - u))) (1, 0) (R / 2 - 3) ∪
        NonTerm (rightFace u (dirOf (v - u))) (1, 0) := by
  set f₀ := rightFace u (dirOf (v - u)) with hf₀
  have hd₀ : squareGraph.Adj f₀ (f₀ + (1, 0)) := adj_of_unit (by left; abel)
  have hdu : IsUnit ((1, 0) : Site) := by left; rfl
  rintro ρ ⟨l, hl, hlive, hhead, h1, w, hw, hdist⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hl0 : l[0]? = some u := by rwa [List.head?_eq_getElem?] at hhead
  have hi1 : 1 ≤ i := by
    by_contra h0
    have : i = 0 := by omega
    subst this
    rw [List.getElem?_eq_getElem hi] at hl0
    simp only [Option.some.injEq] at hl0
    rw [hl0, SimpleGraph.dist_self] at hdist
    omega
  -- the prefix up to `w`
  set l' := l.take (i + 1) with hl'
  have hlen' : l'.length = i + 1 := by rw [hl', List.length_take, min_eq_left (by omega)]
  have hl'path : IsPath squareGraph l' := ⟨hl.1.sublist (List.take_sublist _ _), hl.2.take _⟩
  have hl'live : IsLive clockwise ρ l' := isLive_take hlive _
  have hget : ∀ k, k < i + 1 → l'[k]? = l[k]? := fun k hk => List.getElem?_take_of_lt hk
  have hy0 : l'[l'.length - 2]? = l[i - 1]? := by rw [hlen', show i + 1 - 2 = i - 1 by omega]; exact hget _ (by omega)
  have hy1 : l'[l'.length - 1]? = some l[i] := by
    rw [hlen', Nat.add_sub_cancel, hget i (by omega)]; exact List.getElem?_eq_getElem hi
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, l[i - 1]? = some y₀ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [hy₀] at hy0
  obtain ⟨q, hq, hqhead, hqlast⟩ := Rotor.Frozen.square_dual_path ρ l' hl'path hl'live
    (by rw [hlen']; omega) u v y₀ l[i] (by rw [hget 0 (by omega)]; exact hl0)
    (by rw [hget 1 (by omega)]; exact h1) hy0 hy1
  set g := rightFace y₀ (dirOf (l[i] - y₀)) with hg
  have hreach : DualReachable ρ f₀ g := ⟨q, hq, hqhead, hqlast⟩
  -- the distance of `g` from `f₀`
  have hadj_y : squareGraph.Adj y₀ l[i] :=
    isChain_getElem? hl.2 (i := i - 1) hy₀
      (by rw [show i - 1 + 1 = i by omega]; exact List.getElem?_eq_getElem hi)
  have hgfar : ((R / 2 - 3 : ℕ) : ℤ) ≤ linfDist g f₀ := by
    have e1 : linfDist g y₀ ≤ 1 := rightFace_near y₀ _
    have e2 : linfDist f₀ u ≤ 1 := rightFace_near u _
    have e3 : linfDist l[i] u ≤ linfDist y₀ u + 1 := linfDist_adj_le (r := u) hadj_y
    have t2 : linfDist y₀ f₀ ≤ linfDist y₀ g + linfDist g f₀ := linfDist_triangle _ _ _
    have hlu : linfDist y₀ u ≤ linfDist y₀ f₀ + linfDist f₀ u := linfDist_triangle _ _ _
    have hcomm2 : linfDist g y₀ = linfDist y₀ g := linfDist_comm _ _
    have hd2 : (R : ℤ) ≤ 2 * linfDist l[i] u := by
      have := dist_le_two_linf u l[i]; rwa [hdist] at this
    have hcast : ((R / 2 - 3 : ℕ) : ℤ) = ((R / 2 : ℕ) : ℤ) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hhalf : ((R / 2 : ℕ) : ℤ) * 2 ≤ R := by
      have := Nat.div_mul_le_self R 2; exact_mod_cast this
    rw [hcast]
    omega
  by_cases hterm : ∃ n, (explore ρ f₀ (1, 0) n).active = []
  · left
    obtain ⟨n, hn⟩ := hterm
    have h54 := (Rotor.Frozen.square_exploration f₀ (1, 0) hd₀).2.1 ρ n hn g hreach
    rcases h54 with hvis | hfin
    · exact ⟨n, g, hvis, hgfar⟩
    · obtain ⟨g', hg', hle⟩ := exists_far_visited (f₀ := f₀) hfin
      exact ⟨n, g', hg', hgfar.trans hle⟩
  · right
    push_neg at hterm
    exact hterm

/-! ### Non-termination has probability zero -/

theorem nonTerm_measure_zero (f : Site) {d : Site} (hd : IsUnit d) {C' c' : ℝ} (hc' : 0 < c')
    (hC' : 0 < C')
    (hR : ∀ R' : ℕ, 1 ≤ R' →
      uniformLaw clockwise (ReachEvent f d R') ≤ ENNReal.ofReal (C' * Real.exp (-c' * R'))) :
    uniformLaw clockwise (NonTerm f d) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  rw [zero_add]
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨R', hR'⟩ := exists_nat_gt (C' / (ε * c'))
  have hR'1 : 1 ≤ R' := by
    have h0 : (0 : ℝ) < C' / (ε * c') := div_pos hC' (mul_pos hεpos hc')
    have h1 : (0 : ℝ) < R' := lt_trans h0 hR'
    have h2 : 0 < R' := by exact_mod_cast h1
    omega
  have hR'pos : (0 : ℝ) < R' := by exact_mod_cast hR'1
  have hreal : C' * Real.exp (-c' * R') ≤ ε := by
    have h1 : c' * R' + 1 ≤ Real.exp (c' * R') := by
      have := Real.add_one_le_exp (c' * R'); linarith
    have h2 : Real.exp (-c' * R') ≤ 1 / (c' * R') := by
      rw [neg_mul, Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have h3 : C' / (ε * c') < R' := hR'
    have h4 : C' < ε * c' * R' := by
      rw [div_lt_iff₀ (mul_pos hεpos hc')] at h3
      linarith [h3]
    calc C' * Real.exp (-c' * R') ≤ C' * (1 / (c' * R')) := by gcongr
      _ = C' / (c' * R') := by ring
      _ ≤ ε := by rw [div_le_iff₀ (mul_pos hc' hR'pos)]; linarith
  calc uniformLaw clockwise (NonTerm f d)
      ≤ uniformLaw clockwise (ReachEvent f d R') := measure_mono (nonTerm_subset_reach f hd R')
    _ ≤ ENNReal.ofReal (C' * Real.exp (-c' * R')) := hR R' hR'1
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
    _ = ε := ENNReal.ofReal_coe_nnreal

/-! ### Proposition 5.1 -/

theorem square_passage_proof (hSub : External.SubcriticalDecay) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (u v : Site), squareGraph.Adj u v → ∀ R : ℕ, 1 ≤ R →
      uniformLaw clockwise (liveReachEvent clockwise u v R) ≤
        ENNReal.ofReal (C * Real.exp (-c * R)) := by
  obtain ⟨c, C, hc, hC, hCB⟩ := Rotor.Frozen.square_constrained_bonds hSub
  obtain ⟨C', c', hc', hC', hreach⟩ := reach_exp_bound hc hC hCB
  refine ⟨c' / 2, C' * Real.exp (7 * c' / 2) + Real.exp (4 * c'), by positivity, by positivity,
    fun u v _ R hR => ?_⟩
  set f₀ := rightFace u (dirOf (v - u)) with hf₀
  have hd₀ : squareGraph.Adj f₀ (f₀ + (1, 0)) := adj_of_unit (by left; abel)
  have hdu : IsUnit ((1, 0) : Site) := by left; rfl
  have hnull := nonTerm_measure_zero f₀ hdu hc' hC' (hreach f₀ (1, 0) hd₀)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  rcases Nat.lt_or_ge R 8 with hR8 | hR8
  · have hR8' : (R : ℝ) < 8 := by exact_mod_cast hR8
    calc uniformLaw clockwise (liveReachEvent clockwise u v R) ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (Real.exp (4 * c') * Real.exp (-(c' / 2) * R)) := by
          rw [← Real.exp_add, ← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          apply Real.one_le_exp_iff.2
          nlinarith
      _ ≤ ENNReal.ofReal ((C' * Real.exp (7 * c' / 2) + Real.exp (4 * c')) * Real.exp (-(c' / 2) * R)) := by
          apply ENNReal.ofReal_le_ofReal
          have : 0 ≤ C' * Real.exp (7 * c' / 2) := by positivity
          nlinarith [Real.exp_pos (-(c' / 2) * R)]
  · have hsub := liveReach_subset u v R hR8
    have hR' : 1 ≤ R / 2 - 3 := by omega
    calc uniformLaw clockwise (liveReachEvent clockwise u v R)
        ≤ uniformLaw clockwise (ReachEvent f₀ (1, 0) (R / 2 - 3) ∪ NonTerm f₀ (1, 0)) :=
          measure_mono hsub
      _ ≤ uniformLaw clockwise (ReachEvent f₀ (1, 0) (R / 2 - 3)) +
          uniformLaw clockwise (NonTerm f₀ (1, 0)) := measure_union_le _ _
      _ = uniformLaw clockwise (ReachEvent f₀ (1, 0) (R / 2 - 3)) := by rw [hnull, add_zero]
      _ ≤ ENNReal.ofReal (C' * Real.exp (-c' * ((R / 2 - 3 : ℕ) : ℝ))) := hreach f₀ (1, 0) hd₀ _ hR'
      _ ≤ ENNReal.ofReal ((C' * Real.exp (7 * c' / 2) + Real.exp (4 * c')) * Real.exp (-(c' / 2) * R)) := by
          apply ENNReal.ofReal_le_ofReal
          have hcast : ((R / 2 - 3 : ℕ) : ℝ) = ((R / 2 : ℕ) : ℝ) - 3 := by
            rw [Nat.cast_sub (by omega)]; norm_num
          have hhalf := half_floor_ge R
          have hexp : Real.exp (-c' * ((R / 2 - 3 : ℕ) : ℝ)) ≤
              Real.exp (7 * c' / 2) * Real.exp (-(c' / 2) * R) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            rw [hcast]
            nlinarith
          have : 0 ≤ Real.exp (4 * c') * Real.exp (-(c' / 2) * R) := by positivity
          calc C' * Real.exp (-c' * ((R / 2 - 3 : ℕ) : ℝ))
              ≤ C' * (Real.exp (7 * c' / 2) * Real.exp (-(c' / 2) * R)) := by gcongr
            _ ≤ _ := by nlinarith

end Rotor

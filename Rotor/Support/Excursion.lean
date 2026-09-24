import Rotor.Support.SquareExits
import Rotor.Support.Boundary
import Rotor.Support.KingWalks

/-!
The excursion argument of the pendant counterexample (`rotor.tex:2247-2290`), for the
clockwise rotor walk on `ℤ²` started at `o`.  If the walk returns to `o` at time `r` for the
first time and the traversals before `r` are distinct, then with `k(v)` the number of
departures from `v` before `r`:

* every vertex has in-degree `k(v)`, `k(v) ≤ 4`, and `k(o) = 1`;
* the departures from `v` leave in the directions `ρ(v) + 1, …, ρ(v) + k(v)`;
* for `U` the king-connected component of `o` in `{1 ≤ k ≤ 3}`, the steps out of `U` sum to
  zero (`eq:boundary-cancellation`), by the balance of the traversed edges inside `U` and the
  discrete divergence theorem on the boundary of `H = {k = 4}`;
* hence at least a third of the sites of `U` do not carry a west rotor.
-/

open Finset Fin.NatCast

namespace Rotor

/-- The sum of the two coordinates. -/
def cs (p : Site) : ℤ := p.1 + p.2

theorem cs_sum {ι : Type*} (s : Finset ι) (f : ι → Site) : cs (∑ i ∈ s, f i) = ∑ i ∈ s, cs (f i) := by
  simp only [cs, Prod.fst_sum, Prod.snd_sum, sum_add_distrib]

/-- The coordinate sum of the first `k ≤ 4` exits after the direction `d` is at least `-2`. -/
theorem cs_exits_ge (d : Dir) (k : ℕ) (hk : k ≤ 4) :
    -2 ≤ cs (∑ j ∈ range k, dirVec (d + (j : Dir) + 1)) := by
  fin_cases d <;> interval_cases k <;> decide

/-- A west rotor contributes `1, 2, 1` for `k = 1, 2, 3`. -/
theorem cs_exits_west (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    1 ≤ cs (∑ j ∈ range k, dirVec ((3 : Dir) + (j : Dir) + 1)) := by
  interval_cases k <;> decide

theorem kingStep_of_adj {v w : Site} (h : squareGraph.Adj v w) : KingStep v w := by
  refine ⟨h.ne, ?_⟩
  rcases adj_sub_mem h with h' | h' | h' | h' <;> rw [h'] <;> simp [linf]

section

variable (σ : Config squareGraph) (o : Site) (r : ℕ)

local notation "Y" => X clockwise σ o

/-- The walk returns to `o` at time `r` for the first time, and its traversals before `r` are
distinct. -/
structure FirstReturn : Prop where
  pos : 1 ≤ r
  ret : Y r = o
  first : ∀ s, 1 ≤ s → s < r → Y s ≠ o
  inj : ∀ a b, a < b → b < r → (Y a, Y (a + 1)) ≠ (Y b, Y (b + 1))

/-- The out-degree `k(v)`: departures from `v` before `r`. -/
def kOut (v : Site) : ℕ := deps σ o v r

/-- The in-degree: arrivals at `v` before `r`. -/
def kIn (v : Site) : ℕ := ((range r).filter (fun a => Y (a + 1) = v)).card

theorem kOut_eq (v : Site) : kOut σ o r v = ((range r).filter (fun a => Y a = v)).card := rfl

/-- Balance: the closed walk enters each vertex as often as it leaves it. -/
theorem kIn_eq_kOut (h : FirstReturn σ o r) (v : Site) : kIn σ o r v = kOut σ o r v := by
  unfold kIn kOut deps
  rw [card_filter, card_filter]
  have h1 := sum_range_succ (fun a => if Y a = v then 1 else 0) r
  have h2 := sum_range_succ' (fun a => if Y a = v then 1 else 0) r
  simp only [show Y 0 = o from rfl, h.ret] at h1 h2
  omega

theorem deps_mono (v : Site) {a b : ℕ} (hab : a ≤ b) : deps σ o v a ≤ deps σ o v b := by
  unfold deps
  exact card_le_card (filter_subset_filter _ (Finset.range_mono hab))

theorem deps_lt_of_eq (v : Site) {a b : ℕ} (hab : a < b) (ha : Y a = v) :
    deps σ o v a < deps σ o v b := by
  have h1 := deps_succ σ o v a
  rw [if_pos ha] at h1
  have h2 := deps_mono σ o v (show a + 1 ≤ b by omega)
  omega

theorem deps_lt_kOut {v : Site} {a : ℕ} (ha : a < r) (hv : Y a = v) :
    deps σ o v a < kOut σ o r v :=
  deps_lt_of_eq σ o v ha hv

/-- Every rank below the out-degree is realized by a departure. -/
theorem exists_deps_eq {v : Site} {j : ℕ} (hj : j < kOut σ o r v) :
    ∃ a, a < r ∧ Y a = v ∧ deps σ o v a = j := by
  classical
  have hex : ∃ a, j < deps σ o v (a + 1) := by
    obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := by
      rcases r with _ | r'
      · simp [kOut, deps] at hj
      · exact ⟨r', rfl⟩
    exact ⟨r', by rw [← hr']; exact hj⟩
  let a := Nat.find hex
  have ha : j < deps σ o v (a + 1) := Nat.find_spec hex
  have hle : deps σ o v a ≤ j := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]; simp [deps]
    · have := Nat.find_min hex (show a - 1 < a by omega)
      rw [show a - 1 + 1 = a by omega] at this
      omega
  have hs := deps_succ σ o v a
  refine ⟨a, ?_, ?_, ?_⟩
  · obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := by
      rcases r with _ | r'
      · simp [kOut, deps] at hj
      · exact ⟨r', rfl⟩
    have : a ≤ r' := Nat.find_min' hex (by rw [← hr']; exact hj)
    omega
  · by_contra hne
    rw [if_neg hne] at hs
    omega
  · split_ifs at hs with hv
    · omega
    · omega

theorem adj_succ (a : ℕ) : squareGraph.Adj (Y a) (Y (a + 1)) := by
  rw [X_succ_eq]
  exact adj_add_dirVec _ _

theorem sub_succ (a : ℕ) :
    Y (a + 1) - Y a = dirVec (dir0 σ (Y a) + (deps σ o (Y a) a : Dir) + 1) := by
  rw [X_succ_eq]
  abel

/-- `k(v) ≤ 4`: five departures would repeat a traversal. -/
theorem kOut_le_four (h : FirstReturn σ o r) (v : Site) : kOut σ o r v ≤ 4 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, hva, hda⟩ := exists_deps_eq σ o r (show 0 < kOut σ o r v by omega)
  obtain ⟨b, hb, hvb, hdb⟩ := exists_deps_eq σ o r (show 4 < kOut σ o r v by omega)
  have hab : a < b := by
    rcases lt_trichotomy a b with h' | h' | h'
    · exact h'
    · subst h'; omega
    · have := deps_lt_of_eq σ o v h' hvb; omega
  apply h.inj a b hab hb
  have h4 : ((4 : ℕ) : Dir) = ((0 : ℕ) : Dir) := by decide
  have e1 := sub_succ σ o a
  have e2 := sub_succ σ o b
  rw [hva, hda] at e1
  rw [hvb, hdb, h4] at e2
  rw [Prod.mk.injEq, hva, hvb]
  refine ⟨rfl, ?_⟩
  have : Y (a + 1) - v = Y (b + 1) - v := e1.trans e2.symm
  exact sub_left_inj.1 this

/-- `k(o) = 1`. -/
theorem kOut_o (h : FirstReturn σ o r) : kOut σ o r o = 1 := by
  rw [kOut_eq]
  have : (range r).filter (fun a => Y a = o) = {0} := by
    ext a
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨ha, hao⟩
      by_contra h0
      exact h.first a (by omega) ha hao
    · rintro rfl
      exact ⟨h.pos, rfl⟩
  rw [this, card_singleton]

/-- The steps out of `v` are the first `k(v)` directions after the initial rotor. -/
theorem sum_exits (v : Site) :
    ∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a) =
      ∑ j ∈ range (kOut σ o r v), dirVec (dir0 σ v + (j : Dir) + 1) := by
  refine sum_bij (fun a _ => deps σ o v a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_range] at ha
    exact mem_range.2 (deps_lt_kOut σ o r ha.1 ha.2)
  · intro a ha b hb hab
    simp only [mem_filter, mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · have := deps_lt_of_eq σ o v h' ha.2; omega
    · have := deps_lt_of_eq σ o v h' hb.2; omega
  · intro j hj
    obtain ⟨a, ha, hva, hda⟩ := exists_deps_eq σ o r (mem_range.1 hj)
    exact ⟨a, by simp [ha, hva], hda⟩
  · intro a ha
    simp only [mem_filter, mem_range] at ha
    rw [sub_succ, ha.2]

/-- The coordinate sum of the steps out of `v`. -/
theorem cs_sum_exits_ge (h : FirstReturn σ o r) (v : Site) :
    -2 ≤ cs (∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a)) := by
  rw [sum_exits]
  exact cs_exits_ge _ _ (kOut_le_four σ o r h v)

theorem cs_sum_exits_west (v : Site) (hW : dir0 σ v = 3) (h1 : 1 ≤ kOut σ o r v)
    (h3 : kOut σ o r v ≤ 3) :
    1 ≤ cs (∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a)) := by
  rw [sum_exits, hW]
  exact cs_exits_west _ h1 h3

/-! ### The sets `U` and `H` -/

/-- The sites departed from before `r`. -/
def visitedSet : Finset Site := (range r).image Y

/-- The sites with `1 ≤ k(v) ≤ 3`. -/
def lowSet : Finset Site :=
  (visitedSet σ o r).filter (fun v => 1 ≤ kOut σ o r v ∧ kOut σ o r v ≤ 3)

/-- `H = {v : k(v) = 4}`. -/
def highSet : Finset Site := (visitedSet σ o r).filter (fun v => kOut σ o r v = 4)

/-- The relation generating `U`: a king step into `{1 ≤ k ≤ 3}`. -/
def lowStep (a b : Site) : Prop := b ∈ lowSet σ o r ∧ KingStep a b

open Classical in
/-- `U`: the king-connected component of `o` in `{1 ≤ k ≤ 3}`. -/
noncomputable def Uset : Finset Site :=
  (lowSet σ o r).filter (fun v => Relation.ReflTransGen (lowStep σ o r) o v)

theorem mem_visitedSet {v : Site} : v ∈ visitedSet σ o r ↔ ∃ a, a < r ∧ Y a = v := by
  simp [visitedSet]

theorem kOut_pos_iff (v : Site) : 1 ≤ kOut σ o r v ↔ v ∈ visitedSet σ o r := by
  rw [kOut_eq, Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty,
    mem_visitedSet]
  simp [Finset.Nonempty]

theorem mem_lowSet {v : Site} : v ∈ lowSet σ o r ↔ 1 ≤ kOut σ o r v ∧ kOut σ o r v ≤ 3 := by
  rw [lowSet, mem_filter, ← kOut_pos_iff]
  tauto

theorem mem_highSet {v : Site} : v ∈ highSet σ o r ↔ kOut σ o r v = 4 := by
  rw [highSet, mem_filter, ← kOut_pos_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

open Classical in
theorem mem_Uset {v : Site} :
    v ∈ Uset σ o r ↔ v ∈ lowSet σ o r ∧ Relation.ReflTransGen (lowStep σ o r) o v := by
  unfold Uset
  exact mem_filter

theorem Uset_subset_lowSet : Uset σ o r ⊆ lowSet σ o r := fun _ hv => ((mem_Uset σ o r).1 hv).1

theorem o_mem_Uset (h : FirstReturn σ o r) : o ∈ Uset σ o r :=
  (mem_Uset σ o r).2 ⟨(mem_lowSet σ o r).2 (by rw [kOut_o σ o r h]; omega), Relation.ReflTransGen.refl⟩

theorem mem_Uset_of_step {v w : Site} (hv : v ∈ Uset σ o r) (hw : w ∈ lowSet σ o r)
    (hvw : KingStep v w) : w ∈ Uset σ o r :=
  (mem_Uset σ o r).2 ⟨hw, ((mem_Uset σ o r).1 hv).2.tail ⟨hw, hvw⟩⟩

theorem not_mem_highSet_of_mem_Uset {v : Site} (hv : v ∈ Uset σ o r) : v ∉ highSet σ o r := by
  intro hH
  have := ((mem_lowSet σ o r).1 (Uset_subset_lowSet σ o r hv)).2
  rw [mem_highSet] at hH
  omega

theorem not_mem_Uset_of_mem_highSet {v : Site} (hv : v ∈ highSet σ o r) : v ∉ Uset σ o r :=
  fun hU => not_mem_highSet_of_mem_Uset σ o r hU hv

/-- A site entered before `r` is `o` or has `k ≥ 1`. -/
theorem kOut_pos_of_arrival (h : FirstReturn σ o r) {a : ℕ} (ha : a < r) :
    Y (a + 1) = o ∨ 1 ≤ kOut σ o r (Y (a + 1)) := by
  rcases Nat.lt_or_ge (a + 1) r with h' | h'
  · right
    exact (kOut_pos_iff σ o r _).2 ((mem_visitedSet σ o r).2 ⟨a + 1, h', rfl⟩)
  · left
    have : a + 1 = r := by omega
    rw [this]
    exact h.ret

/-- A site of `H` traverses every edge out of it. -/
theorem exists_traverse_of_high {x v : Site} (hx : x ∈ highSet σ o r)
    (hadj : squareGraph.Adj x v) : ∃ a, a < r ∧ Y a = x ∧ Y (a + 1) = v := by
  rw [mem_highSet] at hx
  set d : Dir := dirOf (v - x) with hd
  have hv : x + dirVec d = v := dirVec_dirOf_of_adj hadj
  set j : ℕ := ((d - dir0 σ x - 1 : Dir) : ℕ) with hj
  have hj4 : j < kOut σ o r x := by rw [hx]; exact (d - dir0 σ x - 1).isLt
  obtain ⟨a, ha, hxa, hda⟩ := exists_deps_eq σ o r hj4
  refine ⟨a, ha, hxa, ?_⟩
  have e := sub_succ σ o a
  rw [hxa, hda, hj, Fin.cast_val_eq_self] at e
  rw [show dir0 σ x + (d - dir0 σ x - 1) + 1 = d by abel] at e
  rw [← hv, ← e]
  abel

/-- The outer endpoint of a boundary edge of `H` next to `U` lies in `U`. -/
theorem mem_Uset_of_adj_high (h : FirstReturn σ o r) {v v' x : Site} (hv : v ∈ Uset σ o r)
    (hx : x ∈ highSet σ o r) (hadj : squareGraph.Adj x v') (hv'H : v' ∉ highSet σ o r)
    (hstep : v' = v ∨ KingStep v v') : v' ∈ Uset σ o r := by
  rcases hstep with rfl | hstep
  · exact hv
  obtain ⟨a, ha, -, hav⟩ := exists_traverse_of_high σ o r hx hadj
  rcases kOut_pos_of_arrival σ o r h ha with h0 | h1
  · rw [hav] at h0
    rw [h0]
    exact o_mem_Uset σ o r h
  · rw [hav] at h1
    have h4 := kOut_le_four σ o r h v'
    rw [mem_highSet] at hv'H
    exact mem_Uset_of_step σ o r hv ((mem_lowSet σ o r).2 ⟨h1, by omega⟩) hstep

/-! ### Traversals across the boundary of `U` -/

/-- Departures from `U`. -/
noncomputable def outU : Finset ℕ := (range r).filter (fun a => Y a ∈ Uset σ o r)

/-- Arrivals in `U`. -/
noncomputable def inU : Finset ℕ := (range r).filter (fun a => Y (a + 1) ∈ Uset σ o r)

/-- Traversals inside `U`. -/
noncomputable def innerU : Finset ℕ := (range r).filter (fun a => Y a ∈ Uset σ o r ∧ Y (a + 1) ∈ Uset σ o r)

/-- Traversals leaving `U`. -/
noncomputable def crossOut : Finset ℕ := (range r).filter (fun a => Y a ∈ Uset σ o r ∧ Y (a + 1) ∉ Uset σ o r)

/-- Traversals entering `U`. -/
noncomputable def crossIn : Finset ℕ := (range r).filter (fun a => Y a ∉ Uset σ o r ∧ Y (a + 1) ∈ Uset σ o r)

/-- The adjacent pairs `(v, x)` with `v ∈ U` and `x ∈ H`. -/
noncomputable def bpairs : Finset (Site × Site) :=
  ((Uset σ o r) ×ˢ (highSet σ o r)).filter (fun p => squareGraph.Adj p.1 p.2)

theorem sum_outU_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ a ∈ outU σ o r, f a = ∑ a ∈ innerU σ o r, f a + ∑ a ∈ crossOut σ o r, f a := by
  rw [← sum_filter_add_sum_filter_not (outU σ o r) (fun a => Y (a + 1) ∈ Uset σ o r)]
  unfold outU innerU crossOut
  rw [filter_filter, filter_filter]

theorem sum_inU_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ a ∈ inU σ o r, f a = ∑ a ∈ innerU σ o r, f a + ∑ a ∈ crossIn σ o r, f a := by
  rw [← sum_filter_add_sum_filter_not (inU σ o r) (fun a => Y a ∈ Uset σ o r)]
  unfold inU innerU crossIn
  rw [filter_filter, filter_filter]
  congr 1
  · exact sum_congr (filter_congr (fun a _ => and_comm)) (fun _ _ => rfl)
  · exact sum_congr (filter_congr (fun a _ => and_comm)) (fun _ _ => rfl)

theorem filter_outU_eq {v : Site} (hv : v ∈ Uset σ o r) :
    (outU σ o r).filter (fun a => Y a = v) = (range r).filter (fun a => Y a = v) := by
  unfold outU
  rw [filter_filter]
  refine filter_congr (fun a _ => ?_)
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h ▸ hv, h⟩

theorem sum_outU_fiber {M : Type*} [AddCommMonoid M] (f : Site → M) :
    ∑ a ∈ outU σ o r, f (Y a) = ∑ v ∈ Uset σ o r, kOut σ o r v • f v := by
  rw [← sum_fiberwise_of_maps_to (s := outU σ o r) (t := Uset σ o r) (g := Y)
    (fun a ha => (mem_filter.1 ha).2)]
  refine sum_congr rfl (fun v hv => ?_)
  rw [filter_outU_eq σ o r hv, kOut_eq, ← sum_const]
  exact sum_congr rfl (fun a ha => by rw [(mem_filter.1 ha).2])

theorem sum_inU_fiber {M : Type*} [AddCommMonoid M] (f : Site → M) :
    ∑ a ∈ inU σ o r, f (Y (a + 1)) = ∑ v ∈ Uset σ o r, kIn σ o r v • f v := by
  rw [← sum_fiberwise_of_maps_to (s := inU σ o r) (t := Uset σ o r) (g := fun a => Y (a + 1))
    (fun a ha => (mem_filter.1 ha).2)]
  refine sum_congr rfl (fun v hv => ?_)
  have : (inU σ o r).filter (fun a => Y (a + 1) = v) = (range r).filter (fun a => Y (a + 1) = v) := by
    unfold inU
    rw [filter_filter]
    refine filter_congr (fun a _ => ?_)
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hv, h⟩
  rw [this, kIn, ← sum_const]
  exact sum_congr rfl (fun a ha => by rw [(mem_filter.1 ha).2])

/-- Balance of `U`: the departure points and the arrival points have the same sum. -/
theorem sum_outU_eq_sum_inU (h : FirstReturn σ o r) :
    ∑ a ∈ outU σ o r, Y a = ∑ a ∈ inU σ o r, Y (a + 1) := by
  rw [sum_outU_fiber σ o r (fun v => v), sum_inU_fiber σ o r (fun v => v)]
  exact sum_congr rfl (fun v _ => by rw [kIn_eq_kOut σ o r h])

theorem card_outU_eq_card_inU (h : FirstReturn σ o r) : (outU σ o r).card = (inU σ o r).card := by
  rw [card_eq_sum_ones, card_eq_sum_ones]
  have h1 := sum_outU_fiber σ o r (fun _ => (1 : ℕ))
  have h2 := sum_inU_fiber σ o r (fun _ => (1 : ℕ))
  rw [h1, h2]
  exact sum_congr rfl (fun v _ => by rw [kIn_eq_kOut σ o r h])

theorem card_crossOut_eq_card_crossIn (h : FirstReturn σ o r) :
    (crossOut σ o r).card = (crossIn σ o r).card := by
  have h1 := card_outU_eq_card_inU σ o r h
  rw [card_eq_sum_ones, card_eq_sum_ones, sum_outU_split, sum_inU_split] at h1
  rw [← card_eq_sum_ones, ← card_eq_sum_ones, ← card_eq_sum_ones] at h1
  omega

theorem traversal_injOn (h : FirstReturn σ o r) :
    Set.InjOn (fun a => (Y a, Y (a + 1))) ↑(range r) := by
  intro a ha b hb hab
  simp only [coe_range, Set.mem_Iio] at ha hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact h.inj a b h' hb hab
  · exact h.inj b a h' ha hab.symm

theorem crossOut_maps (h : FirstReturn σ o r) {a : ℕ} (ha : a ∈ crossOut σ o r) :
    (Y a, Y (a + 1)) ∈ bpairs σ o r := by
  obtain ⟨har, hU, hnU⟩ := mem_filter.1 ha
  rw [mem_range] at har
  refine mem_filter.2 ⟨mem_product.2 ⟨hU, ?_⟩, adj_succ σ o a⟩
  show Y (a + 1) ∈ highSet σ o r
  rcases kOut_pos_of_arrival σ o r h har with h0 | h1
  · rw [h0] at hnU
    exact absurd (o_mem_Uset σ o r h) hnU
  · have h4 := kOut_le_four σ o r h (Y (a + 1))
    rw [mem_highSet]
    by_contra hne
    exact hnU (mem_Uset_of_step σ o r hU ((mem_lowSet σ o r).2 ⟨h1, by omega⟩)
      (kingStep_of_adj (adj_succ σ o a)))

theorem crossIn_maps (h : FirstReturn σ o r) {a : ℕ} (ha : a ∈ crossIn σ o r) :
    (Y (a + 1), Y a) ∈ bpairs σ o r := by
  obtain ⟨har, hnU, hU⟩ := mem_filter.1 ha
  rw [mem_range] at har
  refine mem_filter.2 ⟨mem_product.2 ⟨hU, ?_⟩, (adj_succ σ o a).symm⟩
  show Y a ∈ highSet σ o r
  have h1 : 1 ≤ kOut σ o r (Y a) := (kOut_pos_iff σ o r _).2 ((mem_visitedSet σ o r).2 ⟨a, har, rfl⟩)
  have h4 := kOut_le_four σ o r h (Y a)
  rw [mem_highSet]
  by_contra hne
  exact hnU (mem_Uset_of_step σ o r hU ((mem_lowSet σ o r).2 ⟨h1, by omega⟩)
    (kingStep_of_adj (adj_succ σ o a)).symm)

theorem crossIn_image (h : FirstReturn σ o r) :
    (crossIn σ o r).image (fun a => (Y (a + 1), Y a)) = bpairs σ o r := by
  ext p
  simp only [mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact crossIn_maps σ o r h ha
  · intro hp
    obtain ⟨hp, hadj⟩ := mem_filter.1 hp
    obtain ⟨hv, hx⟩ := mem_product.1 hp
    obtain ⟨a, ha, hxa, hav⟩ := exists_traverse_of_high σ o r hx hadj.symm
    refine ⟨a, mem_filter.2 ⟨mem_range.2 ha, ?_, ?_⟩, ?_⟩
    · rw [hxa]; exact not_mem_Uset_of_mem_highSet σ o r hx
    · rw [hav]; exact hv
    · rw [hxa, hav]

theorem card_crossIn (h : FirstReturn σ o r) : (crossIn σ o r).card = (bpairs σ o r).card := by
  rw [← crossIn_image σ o r h, card_image_of_injOn]
  intro a ha b hb hab
  have hinj := traversal_injOn σ o r h
  refine hinj (mem_coe.2 (mem_of_mem_filter a ha)) (mem_coe.2 (mem_of_mem_filter b hb)) ?_
  simp only [Prod.mk.injEq] at hab ⊢
  exact ⟨hab.2, hab.1⟩

theorem crossOut_image (h : FirstReturn σ o r) :
    (crossOut σ o r).image (fun a => (Y a, Y (a + 1))) = bpairs σ o r := by
  refine eq_of_subset_of_card_le ?_ ?_
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    exact crossOut_maps σ o r h ha
  · have hinj : Set.InjOn (fun a => (Y a, Y (a + 1))) ↑(crossOut σ o r) :=
      (traversal_injOn σ o r h).mono
        (fun a ha => mem_coe.2 (mem_of_mem_filter a (mem_coe.1 ha)))
    rw [card_image_of_injOn hinj, card_crossOut_eq_card_crossIn σ o r h, card_crossIn σ o r h]

theorem sum_crossOut (h : FirstReturn σ o r) {M : Type*} [AddCommMonoid M] (g : Site × Site → M) :
    ∑ a ∈ crossOut σ o r, g (Y a, Y (a + 1)) = ∑ p ∈ bpairs σ o r, g p := by
  rw [← crossOut_image σ o r h, sum_image]
  exact (traversal_injOn σ o r h).mono
    (fun a ha => mem_coe.2 (mem_of_mem_filter a (mem_coe.1 ha)))

theorem sum_crossIn (h : FirstReturn σ o r) {M : Type*} [AddCommMonoid M] (g : Site × Site → M) :
    ∑ a ∈ crossIn σ o r, g (Y (a + 1), Y a) = ∑ p ∈ bpairs σ o r, g p := by
  rw [← crossIn_image σ o r h, sum_image]
  intro a ha b hb hab
  refine (traversal_injOn σ o r h) (mem_coe.2 (mem_of_mem_filter a ha))
    (mem_coe.2 (mem_of_mem_filter b hb)) ?_
  simp only [Prod.mk.injEq] at hab ⊢
  exact ⟨hab.2, hab.1⟩

/-! ### The discrete divergence theorem on `H` -/

theorem bpairs_swap_subset : (bpairs σ o r).image Prod.swap ⊆ bdry (highSet σ o r) := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := mem_image.1 he
  obtain ⟨hp, hadj⟩ := mem_filter.1 hp
  obtain ⟨hv, hx⟩ := mem_product.1 hp
  exact mem_bdry.2 ⟨hx, not_mem_highSet_of_mem_Uset σ o r hv, hadj.symm⟩

theorem bpairs_swap_invariant (h : FirstReturn σ o r) :
    ∀ e ∈ (bpairs σ o r).image Prod.swap,
      bsucc (highSet σ o r) e ∈ (bpairs σ o r).image Prod.swap := by
  intro e he
  have hb := bpairs_swap_subset σ o r he
  obtain ⟨p, hp, rfl⟩ := mem_image.1 he
  obtain ⟨hp, -⟩ := mem_filter.1 hp
  obtain ⟨hv, -⟩ := mem_product.1 hp
  have hmem := bsucc_mem hb
  obtain ⟨hx', hv', hadj'⟩ := mem_bdry.1 hmem
  have hstep := bsucc_outer _ hb
  refine mem_image.2 ⟨(bsucc (highSet σ o r) (Prod.swap p)).swap, ?_, Prod.swap_swap _⟩
  refine mem_filter.2 ⟨mem_product.2 ⟨?_, hx'⟩, hadj'.symm⟩
  exact mem_Uset_of_adj_high σ o r h hv hx' hadj' hv' hstep

theorem sum_bpairs (h : FirstReturn σ o r) : ∑ p ∈ bpairs σ o r, (p.2 - p.1) = 0 := by
  have h0 := sum_bdry_eq_zero (highSet σ o r) _ (bpairs_swap_subset σ o r)
    (bpairs_swap_invariant σ o r h)
  rw [sum_image (fun _ _ _ _ hab => Prod.swap_injective hab)] at h0
  simp only [Prod.snd_swap, Prod.fst_swap] at h0
  have : ∑ p ∈ bpairs σ o r, (p.2 - p.1) = -∑ p ∈ bpairs σ o r, (p.1 - p.2) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl (fun p _ => (neg_sub _ _).symm)
  rw [this, h0, neg_zero]

/-! ### The boundary cancellation `eq:boundary-cancellation` -/

theorem sum_Uset_exits (h : FirstReturn σ o r) :
    ∑ v ∈ Uset σ o r, ∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a) = 0 := by
  have e0 : ∑ v ∈ Uset σ o r, ∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a) =
      ∑ a ∈ outU σ o r, (Y (a + 1) - Y a) := by
    rw [← sum_fiberwise_of_maps_to (s := outU σ o r) (t := Uset σ o r) (g := Y)
      (fun a ha => (mem_filter.1 ha).2)]
    exact sum_congr rfl (fun v hv => by rw [filter_outU_eq σ o r hv])
  have e1 := sum_outU_split σ o r (fun a => Y (a + 1) - Y a)
  have e2 := sum_outU_split σ o r (fun a => Y a)
  have e3 := sum_inU_split σ o r (fun a => Y (a + 1))
  have e4 := sum_outU_eq_sum_inU σ o r h
  have e5 := sum_crossOut σ o r h (fun p => p.1)
  have e6 := sum_crossIn σ o r h (fun p => p.1)
  have e7 := sum_crossOut σ o r h (fun p => p.2 - p.1)
  have e8 := sum_bpairs σ o r h
  have e9 := sum_sub_distrib (s := innerU σ o r) (fun a => Y (a + 1)) (fun a => Y a)
  simp only at e5 e6 e7
  rw [e0]
  linear_combination e1 + e9 + e7 + e8 - e3 - e4 + e2 + e5 - e6

/-! ### The counting inequality -/

theorem reflTransGen_Uset {v : Site} (hv : v ∈ Uset σ o r) :
    Relation.ReflTransGen (fun a b => b ∈ Uset σ o r ∧ KingStep a b) o v := by
  have hv' := ((mem_Uset σ o r).1 hv).2
  clear hv
  induction hv' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    exact ih.tail ⟨(mem_Uset σ o r).2 ⟨hbc.1, hab.tail hbc⟩, hbc.2⟩

/-- At least a third of the sites of `U` do not carry a west rotor. -/
theorem excursion_core (h : FirstReturn σ o r) :
    ∃ U : Finset Site, KConn o U ∧ U.card ≤ 3 * (U.filter (fun v => dir0 σ v ≠ 3)).card := by
  refine ⟨Uset σ o r, kconn_of_reflTransGen (o_mem_Uset σ o r h)
    (fun v hv => reflTransGen_Uset σ o r hv), ?_⟩
  have h0 : ∑ v ∈ Uset σ o r, cs (∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a)) = 0 := by
    rw [← cs_sum, sum_Uset_exits σ o r h]
    rfl
  have hle : ∑ v ∈ Uset σ o r, (if dir0 σ v = 3 then (1 : ℤ) else -2) ≤
      ∑ v ∈ Uset σ o r, cs (∑ a ∈ (range r).filter (fun a => Y a = v), (Y (a + 1) - Y a)) := by
    refine sum_le_sum (fun v hv => ?_)
    split_ifs with hW
    · obtain ⟨h1, h3⟩ := (mem_lowSet σ o r).1 (Uset_subset_lowSet σ o r hv)
      exact cs_sum_exits_west σ o r v hW h1 h3
    · exact cs_sum_exits_ge σ o r h v
  rw [h0, sum_ite, sum_const, sum_const] at hle
  have hc := card_filter_add_card_filter_not (s := Uset σ o r) (p := fun v => dir0 σ v = 3)
  simp only [nsmul_eq_mul, mul_one, mul_neg] at hle
  simp only [ne_eq]
  omega

end

end Rotor

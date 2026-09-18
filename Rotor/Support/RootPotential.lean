import Rotor.Support.IntervalReach

/-!
Proposition 5.1 (`prop:square-passage`), part 6: roots and reach.  A minimal history with
positive probability ends with a forced open test of the sole active edge, so its interval
starts at the head of that edge; the reach of the visited set grows across an interval by at
most one plus the reach of the interval from its root.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-! ### The structure of a minimal history -/

theorem minF_structure (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {j : ℕ} (hj : 1 ≤ j)
    {h : List Bool} (hm : MinF f d j h) (hpos : Pm f d h ≠ 0) :
    ∃ (h₁ : List Bool) (t r : Site), h = h₁ ++ [true] ∧ (replay f d h₁).active = [(t, r)] ∧
      TestedAs (replay f d h₁).tested (sideW t r) false := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h₁, o, rfl⟩
  · exfalso
    have := hm.1
    simp [replay, explInit] at this
    omega
  rw [List.concat_eq_append] at hm hpos ⊢
  have hprev : (replay f d h₁).forced < j := by
    have := hm.2 h₁.length (by simp)
    rwa [List.take_left' rfl] at this
  have hN' := hm.1
  rcases hact : (replay f d h₁).active with _ | ⟨g, rest⟩
  · exfalso
    rw [forced_append_nil f d h₁ hact] at hN'
    omega
  have hforced : TestedAs (replay f d h₁).tested (sideW g.1 g.2) false := by
    by_contra hnf
    rw [forced_append_cons f d h₁ hact, if_neg hnf] at hN'
    omega
  have ho : o = true := by
    rcases o with _ | _
    · exact absurd (Pm_forced f d hd h₁ hact hforced).2 hpos
    · rfl
  subst ho
  have hpos₁ : Pm f d h₁ ≠ 0 := fun h0 => hpos (le_antisymm
    ((Pm_append_le f d h₁ true).trans (le_of_eq h0)) (zero_le))
  obtain ⟨-, -, -, hL55⟩ := state_facts hd hpos₁
  have hrest : rest = [] := (hL55 g rest hact).1 (Or.inl hforced)
  subst hrest
  exact ⟨h₁, g.1, g.2, rfl, by rw [hact], hforced⟩

/-- Roots: the initial history for `j = 0`, the minimal histories for `j ≥ 1`. -/
def IsRoot (f d : Site) : ℕ → List Bool → Prop
  | 0, h => h = []
  | j + 1, h => MinF f d (j + 1) h

theorem isRoot_forced {f d : Site} {j : ℕ} {h : List Bool} (hr : IsRoot f d j h) :
    (replay f d h).forced = j := by
  cases j with
  | zero => simp only [IsRoot] at hr; subst hr; rfl
  | succ j => exact hr.1

theorem intervalStart_of_root (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {j : ℕ}
    {h : List Bool} (hr : IsRoot f d j h) (hpos : Pm f d h ≠ 0) :
    IntervalStart f d h (rootOf f d h) := by
  cases j with
  | zero =>
    simp only [IsRoot] at hr
    subst hr
    rw [rootOf_nil]
    exact intervalStart_nil f d
  | succ j =>
    obtain ⟨h₁, t, r, rfl, hact, -⟩ := minF_structure f hd (by omega) hr hpos
    rw [rootOf_append f d h₁ hact]
    exact intervalStart_forced f d h₁ hact

/-! ### The reach of the visited set -/

theorem linfDist_nonneg (a b : Site) : 0 ≤ linfDist a b :=
  le_max_of_le_left (abs_nonneg _)

theorem linfDist_triangle (a b c : Site) : linfDist a c ≤ linfDist a b + linfDist b c := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  simp only [linfDist, abs_eq_max_neg]
  omega

/-- The reach of the visited set from `f`. -/
noncomputable def reachN (f d : Site) (h : List Bool) : ℕ :=
  (replay f d h).visited.sup (fun g => (linfDist g f).toNat)

theorem le_reachN {f d : Site} {h : List Bool} {g : Site} (hg : g ∈ (replay f d h).visited) :
    linfDist g f ≤ reachN f d h := by
  have := Finset.le_sup (f := fun g => (linfDist g f).toNat) hg
  have h2 : linfDist g f = ((linfDist g f).toNat : ℤ) :=
    (Int.toNat_of_nonneg (linfDist_nonneg _ _)).symm
  rw [h2]
  exact_mod_cast this

theorem reachN_nil (f d : Site) : reachN f d [] = 0 := by
  simp [reachN, replay, explInit, linfDist_self]

theorem reachN_le_of_forall {f d : Site} {h : List Bool} {n : ℕ}
    (hn : ∀ g ∈ (replay f d h).visited, linfDist g f ≤ n) : reachN f d h ≤ n := by
  refine Finset.sup_le (fun g hg => ?_)
  have := hn g hg
  omega

/-- The reach of the nonforced part of the interval from its root. -/
noncomputable def intD (f d : Site) (h₀ h' : List Bool) : ℕ :=
  ((replay f d h'.dropLast).visited \ (replay f d h₀).visited).sup
    (fun g => (linfDist g (rootOf f d h₀)).toNat)

theorem le_intD {f d : Site} {h₀ h' : List Bool} {g : Site}
    (hg : g ∈ (replay f d h'.dropLast).visited) (hg0 : g ∉ (replay f d h₀).visited) :
    linfDist g (rootOf f d h₀) ≤ intD f d h₀ h' := by
  have := Finset.le_sup (f := fun g => (linfDist g (rootOf f d h₀)).toNat)
    (Finset.mem_sdiff.2 ⟨hg, hg0⟩)
  have h2 : linfDist g (rootOf f d h₀) = ((linfDist g (rootOf f d h₀)).toNat : ℤ) :=
    (Int.toNat_of_nonneg (linfDist_nonneg _ _)).symm
  rw [h2]
  exact_mod_cast this

theorem intD_ge_iff {f d : Site} {h₀ h' : List Bool} {s : ℕ} (hs : 1 ≤ s) :
    s ≤ intD f d h₀ h' ↔ ∃ g ∈ (replay f d h'.dropLast).visited, g ∉ (replay f d h₀).visited ∧
      (s : ℤ) ≤ linfDist g (rootOf f d h₀) := by
  unfold intD
  rw [Finset.le_sup_iff (show (⊥ : ℕ) < s from Nat.pos_of_ne_zero (by omega))]
  constructor
  · rintro ⟨g, hg, hgs⟩
    rw [Finset.mem_sdiff] at hg
    refine ⟨g, hg.1, hg.2, ?_⟩
    have h2 : linfDist g (rootOf f d h₀) = ((linfDist g (rootOf f d h₀)).toNat : ℤ) :=
      (Int.toNat_of_nonneg (linfDist_nonneg _ _)).symm
    rw [h2]; exact_mod_cast hgs
  · rintro ⟨g, hg, hg0, hgs⟩
    refine ⟨g, Finset.mem_sdiff.2 ⟨hg, hg0⟩, ?_⟩
    have h2 : linfDist g (rootOf f d h₀) = ((linfDist g (rootOf f d h₀)).toNat : ℤ) :=
      (Int.toNat_of_nonneg (linfDist_nonneg _ _)).symm
    rw [h2] at hgs
    exact_mod_cast hgs

/-- Across one interval the reach grows by at most one plus the interval's reach. -/
theorem reachN_succ_le (f : Site) {d : Site} (hd : IsUnit d) {h₀ h' : List Bool}
    (hroot : rootOf f d h₀ ∈ (replay f d h₀).visited) (hp : h₀ <+: h') (hne : h' ≠ []) :
    reachN f d h' ≤ reachN f d h₀ + 1 + intD f d h₀ h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', o, rfl⟩
  · exact absurd rfl hne
  rw [List.concat_eq_append] at hp ⊢
  by_cases heq : h₀ = h'' ++ [o]
  · rw [heq]; omega
  have hp'' : h₀ <+: h'' := List.prefix_of_prefix_length_le hp (List.prefix_append _ _) (by
    have h1 := hp.length_le
    have h2 : h₀.length ≠ (h'' ++ [o]).length := fun h => heq (hp.eq_of_length h)
    simp at h1 h2 ⊢; omega)
  have hmono := visited_mono_prefix f d hp''
  -- a face of `h''` is within the bound
  have hbound : ∀ g ∈ (replay f d h'').visited,
      linfDist g f ≤ reachN f d h₀ + intD f d h₀ (h'' ++ [o]) := by
    intro g hg
    by_cases hg0 : g ∈ (replay f d h₀).visited
    · have := le_reachN hg0; omega
    · have h1 := le_intD (f := f) (d := d) (h₀ := h₀) (h' := h'' ++ [o])
        (by simpa using hg) hg0
      have h2 := le_reachN hroot
      have h3 := linfDist_triangle g (rootOf f d h₀) f
      omega
  refine reachN_le_of_forall (fun g hg => ?_)
  rcases hact : (replay f d h'').active with _ | ⟨e, rest⟩
  · rw [replay_append, explStepWith_nil hact] at hg
    have := hbound g hg; omega
  · rw [replay_append, explStepWith_cons hact] at hg
    simp only at hg
    split_ifs at hg with ho
    · rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · have htail : e.1 ∈ (replay f d h'').visited :=
          (explInv_replay f hd h'').active_tail e (by rw [hact]; exact List.mem_cons_self)
        have hadj := (explInv_replay f hd h'').active_adj e (by rw [hact]; exact List.mem_cons_self)
        have h1 := hbound e.1 htail
        have h2 := linfDist_adj_le (r := f) hadj
        omega
      · have := hbound g hg; omega
    · have := hbound g hg; omega

theorem Pm_le_of_prefix (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h') :
    Pm f d h' ≤ Pm f d h₀ := by
  obtain ⟨t, rfl⟩ := hp
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t o ih =>
    rw [← List.append_assoc]
    exact (Pm_append_le f d _ o).trans ih

/-! ### The layer cake over one interval -/

theorem sum_minF_succ_le_Pm (f : Site) {d : Site} (hd : IsUnit d) {j : ℕ} {h₀ : List Bool}
    (F : Finset (List Bool)) (hF : ∀ h' ∈ F, MinF f d (j + 1) h' ∧ h₀ <+: h') :
    ∑ h' ∈ F, Pm f d h' ≤ Pm f d h₀ := by
  unfold Pm
  rw [← measure_biUnion_finset ?_ (fun h' _ => measurableSet_history_len f hd h')]
  · apply measure_mono
    intro ρ hρ
    simp only [Set.mem_iUnion, exists_prop] at hρ
    obtain ⟨h', hh', hρ'⟩ := hρ
    exact history_of_prefix f d (hF h' hh').2 hρ'
  · intro h₁ hh₁ h₂ hh₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ρ h1 h2
    exact hne (minF_unique f d (hF h₁ hh₁).1 (hF h₂ hh₂).1 h1 h2)

theorem pow_eq_one_add_sum {a : ℝ≥0∞} (ha : 1 ≤ a) :
    ∀ n : ℕ, a ^ n = 1 + ∑ s ∈ Finset.range n, (a ^ (s + 1) - a ^ s)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← add_assoc, ← pow_eq_one_add_sum ha n]
    exact (add_tsub_cancel_of_le (pow_le_pow_right₀ ha (Nat.le_succ n))).symm

/-- The constant `M` of the layer cake. -/
noncomputable def Mconst (a : ℝ≥0∞) (c C : ℝ) : ℝ≥0∞ :=
  1 + ∑' s : ℕ, (a ^ (s + 1) - a ^ s) * ENNReal.ofReal (C * Real.exp (-c * (s + 1)))

/-- The expected `a`-power of the interval reach, over a finite family of next roots. -/
theorem sum_pow_intD_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {c C : ℝ}
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r)))
    {j : ℕ} {h₀ : List Bool} (hm0 : (replay f d h₀).forced = j)
    (hs0 : IntervalStart f d h₀ (rootOf f d h₀)) {a : ℝ≥0∞} (ha : 1 ≤ a)
    (F : Finset (List Bool)) (hF : ∀ h' ∈ F, MinF f d (j + 1) h' ∧ h₀ <+: h') :
    ∑ h' ∈ F, Pm f d h' * a ^ intD f d h₀ h' ≤ Pm f d h₀ * Mconst a c C := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  set N := F.sup (fun h' => intD f d h₀ h') with hN
  have hDN : ∀ h' ∈ F, intD f d h₀ h' ≤ N := fun h' hh' => Finset.le_sup (f := fun h' => intD f d h₀ h') hh'
  -- layer cake
  have hlayer : ∀ h' ∈ F, Pm f d h' * a ^ intD f d h₀ h' =
      Pm f d h' + ∑ s ∈ Finset.range N,
        (if s < intD f d h₀ h' then Pm f d h' * (a ^ (s + 1) - a ^ s) else 0) := by
    intro h' hh'
    rw [pow_eq_one_add_sum ha, mul_add, mul_one, Finset.mul_sum]
    congr 1
    rw [← Finset.sum_filter]
    have : (Finset.range N).filter (fun s => s < intD f d h₀ h') = Finset.range (intD f d h₀ h') := by
      ext s; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨lt_of_lt_of_le h (hDN h' hh'), h⟩
    rw [this]
  rw [Finset.sum_congr rfl hlayer, Finset.sum_add_distrib, Finset.sum_comm]
  unfold Mconst
  rw [mul_add, mul_one]
  gcongr
  · exact sum_minF_succ_le_Pm f hdu F hF
  · -- each layer
    calc ∑ s ∈ Finset.range N, ∑ h' ∈ F,
          (if s < intD f d h₀ h' then Pm f d h' * (a ^ (s + 1) - a ^ s) else 0)
        ≤ ∑ s ∈ Finset.range N,
          Pm f d h₀ * ((a ^ (s + 1) - a ^ s) * ENNReal.ofReal (C * Real.exp (-c * (s + 1)))) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          rw [← Finset.sum_filter, ← Finset.sum_mul]
          have hsub := sum_minF_succ_le f hdu hm0 (s := s + 1)
            (F.filter (fun h' => s < intD f d h₀ h')) (fun h' hh' => by
              rw [Finset.mem_filter] at hh'
              refine ⟨(hF h' hh'.1).1, (hF h' hh'.1).2, ?_⟩
              exact (intD_ge_iff (by omega)).1 hh'.2)
          have hint := intReach_measure_le f hd hCB hs0 (s := s + 1) (by omega)
          calc (∑ h' ∈ F.filter (fun h' => s < intD f d h₀ h'), Pm f d h') * (a ^ (s + 1) - a ^ s)
              ≤ Pm f d h₀ * ENNReal.ofReal (C * Real.exp (-c * ↑(s + 1))) * (a ^ (s + 1) - a ^ s) := by
                gcongr; exact hsub.trans hint
            _ = _ := by push_cast; ring
      _ = Pm f d h₀ * ∑ s ∈ Finset.range N,
          (a ^ (s + 1) - a ^ s) * ENNReal.ofReal (C * Real.exp (-c * (s + 1))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _

/-! ### The root prefix -/

theorem exists_take_forced_eq (f d : Site) : ∀ (h' : List Bool) (k : ℕ),
    k ≤ (replay f d h').forced → ∃ m ≤ h'.length, (replay f d (h'.take m)).forced = k := by
  intro h'
  induction h' using List.reverseRecOn with
  | nil =>
    intro k hk
    simp [replay, explInit] at hk
    exact ⟨0, le_rfl, by simp [replay, explInit, hk]⟩
  | append_singleton h'' o ih =>
    intro k hk
    rcases Nat.lt_or_ge (replay f d h'').forced k with hlt | hle
    · have h1 := forced_append_le f d h'' o
      refine ⟨(h'' ++ [o]).length, le_rfl, ?_⟩
      rw [List.take_length]
      omega
    · obtain ⟨m, hm, hmk⟩ := ih k hle
      refine ⟨m, by simp; omega, ?_⟩
      rw [List.take_append_of_le_length hm]
      exact hmk

/-- The length of the root prefix at level `j`. -/
noncomputable def rootLen (f d : Site) (j : ℕ) (h' : List Bool) : ℕ :=
  if hex : ∃ m, m ≤ h'.length ∧ (replay f d (h'.take m)).forced = j then Nat.find hex else 0

/-- The root prefix at level `j`. -/
noncomputable def rootPrefix (f d : Site) (j : ℕ) (h' : List Bool) : List Bool :=
  h'.take (rootLen f d j h')

theorem rootPrefix_prefix (f d : Site) (j : ℕ) (h' : List Bool) : rootPrefix f d j h' <+: h' :=
  List.take_prefix _ _

theorem rootPrefix_isRoot (f d : Site) {j : ℕ} {h' : List Bool} (hr : IsRoot f d (j + 1) h') :
    IsRoot f d j (rootPrefix f d j h') := by
  classical
  have hex : ∃ m, m ≤ h'.length ∧ (replay f d (h'.take m)).forced = j :=
    exists_take_forced_eq f d h' j (by rw [hr.1]; omega)
  unfold rootPrefix rootLen
  rw [dif_pos hex]
  obtain ⟨hm, hmj⟩ := Nat.find_spec hex
  cases j with
  | zero =>
    have h0 : Nat.find hex = 0 := by
      rw [Nat.find_eq_zero]
      exact ⟨Nat.zero_le _, by simp [replay, explInit]⟩
    simp [IsRoot, h0]
  | succ j =>
    refine ⟨hmj, fun i hi => ?_⟩
    rw [List.length_take, min_eq_left hm] at hi
    rw [List.take_take, min_eq_left hi.le]
    have hne : (replay f d (h'.take i)).forced ≠ j + 1 := by
      intro h
      have := Nat.find_min hex hi
      exact this ⟨by omega, h⟩
    have hle : (replay f d (h'.take i)).forced ≤ (replay f d (h'.take (Nat.find hex))).forced := by
      refine forced_mono_prefix f d ?_
      rw [show h'.take i = (h'.take (Nat.find hex)).take i by rw [List.take_take, min_eq_left hi.le]]
      exact List.take_prefix _ _
    omega

theorem rootPrefix_eq (f d : Site) {j : ℕ} {h₀ h' : List Bool} (hr0 : IsRoot f d j h₀)
    (hr1 : IsRoot f d (j + 1) h') (hp : h₀ <+: h') : rootPrefix f d j h' = h₀ := by
  classical
  have hex : ∃ m, m ≤ h'.length ∧ (replay f d (h'.take m)).forced = j :=
    exists_take_forced_eq f d h' j (by rw [hr1.1]; omega)
  unfold rootPrefix rootLen
  rw [dif_pos hex]
  have hp' := hp
  rw [List.prefix_iff_eq_take] at hp'
  have hspec : h₀.length ≤ h'.length ∧ (replay f d (h'.take h₀.length)).forced = j := by
    refine ⟨hp.length_le, ?_⟩
    rw [← hp']; exact isRoot_forced hr0
  have hle : Nat.find hex ≤ h₀.length := Nat.find_min' hex hspec
  rcases Nat.lt_or_ge (Nat.find hex) h₀.length with hlt | hge
  · exfalso
    obtain ⟨hm, hmj⟩ := Nat.find_spec hex
    cases j with
    | zero =>
      simp only [IsRoot] at hr0; subst hr0; simp at hlt
    | succ j =>
      have := hr0.2 (Nat.find hex) hlt
      rw [hp', List.take_take, min_eq_left hlt.le] at this
      omega
  · have : Nat.find hex = h₀.length := le_antisymm hle hge
    rw [this, ← hp']

/-! ### The potential -/

/-- The expected `a`-power of the reach at the `j`-th root. -/
noncomputable def Tpot (f d : Site) (a : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ∑' h : {h // IsRoot f d j h}, Pm f d h.1 * a ^ reachN f d h.1

theorem Pm_nil (f d : Site) : Pm f d [] = 1 := by
  unfold Pm
  have : {ρ : Config squareGraph | history ρ f d ([] : List Bool).length = []} = Set.univ := by
    ext ρ; simp [history, explore_zero, explInit]
  rw [this, measure_univ]

theorem Tpot_zero (f d : Site) (a : ℝ≥0∞) : Tpot f d a 0 = 1 := by
  unfold Tpot
  have huniq : ∀ x : {h // IsRoot f d 0 h}, x = ⟨[], rfl⟩ := fun x => Subtype.ext x.2
  rw [tsum_eq_single ⟨[], rfl⟩ (fun x hx => absurd (huniq x) hx)]
  simp [Pm_nil, reachN_nil]

theorem Tpot_succ_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {c C : ℝ}
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r)))
    {a : ℝ≥0∞} (ha : 1 ≤ a) (j : ℕ) :
    Tpot f d a (j + 1) ≤ a * Mconst a c C * Tpot f d a j := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  refine tsum_le_of_forall_finset _ _ (fun S => ?_)
  set S' := S.image Subtype.val with hS'
  have hS'root : ∀ h' ∈ S', IsRoot f d (j + 1) h' := fun h' hh' => by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hh'; exact x.2
  set P := S'.image (rootPrefix f d j) with hP
  have hProot : ∀ h₀ ∈ P, IsRoot f d j h₀ := fun h₀ hh₀ => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh₀; exact rootPrefix_isRoot f d (hS'root x hx)
  -- the fiber bound
  have hfiber : ∀ h₀ ∈ P, ∑ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀),
      Pm f d h' * a ^ reachN f d h' ≤ a * Mconst a c C * (Pm f d h₀ * a ^ reachN f d h₀) := by
    intro h₀ hh₀
    have hr0 := hProot h₀ hh₀
    have hF : ∀ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀),
        MinF f d (j + 1) h' ∧ h₀ <+: h' := fun h' hh' => by
      rw [Finset.mem_filter] at hh'
      exact ⟨hS'root h' hh'.1, hh'.2 ▸ rootPrefix_prefix f d j h'⟩
    by_cases hpos : Pm f d h₀ = 0
    · have : ∀ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀), Pm f d h' = 0 := fun h' hh' =>
        le_antisymm (le_trans (Pm_le_of_prefix f d (hF h' hh').2) (le_of_eq hpos)) (zero_le)
      rw [Finset.sum_eq_zero (fun h' hh' => by rw [this h' hh', zero_mul])]
      exact zero_le
    have hs0 := intervalStart_of_root f hd hr0 hpos
    have hroot : rootOf f d h₀ ∈ (replay f d h₀).visited := hs0.1
    calc ∑ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀), Pm f d h' * a ^ reachN f d h'
        ≤ ∑ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀),
          Pm f d h' * a ^ (reachN f d h₀ + 1 + intD f d h₀ h') := by
          refine Finset.sum_le_sum (fun h' hh' => ?_)
          have hne : h' ≠ [] := by
            intro h; have := (hF h' hh').1.1; rw [h] at this; simp [replay, explInit] at this
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ ha (reachN_succ_le f hdu hroot (hF h' hh').2 hne)) (zero_le)
      _ = a ^ (reachN f d h₀ + 1) * ∑ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀),
          Pm f d h' * a ^ intD f d h₀ h' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h' _ => ?_)
          rw [pow_add]; ring
      _ ≤ a ^ (reachN f d h₀ + 1) * (Pm f d h₀ * Mconst a c C) := by
          gcongr
          exact sum_pow_intD_le f hd hCB (isRoot_forced hr0) hs0 ha _ hF
      _ = a * Mconst a c C * (Pm f d h₀ * a ^ reachN f d h₀) := by rw [pow_succ]; ring
  calc ∑ x ∈ S, Pm f d x.1 * a ^ reachN f d x.1
      = ∑ h' ∈ S', Pm f d h' * a ^ reachN f d h' :=
        (Finset.sum_image (f := fun h' => Pm f d h' * a ^ reachN f d h')
          (fun _ _ _ _ h => Subtype.ext h)).symm
    _ = ∑ h₀ ∈ P, ∑ h' ∈ S'.filter (fun h' => rootPrefix f d j h' = h₀),
          Pm f d h' * a ^ reachN f d h' :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx)
          (fun h' => Pm f d h' * a ^ reachN f d h')).symm
    _ ≤ ∑ h₀ ∈ P, a * Mconst a c C * (Pm f d h₀ * a ^ reachN f d h₀) := Finset.sum_le_sum hfiber
    _ = a * Mconst a c C * ∑ h₀ ∈ P, Pm f d h₀ * a ^ reachN f d h₀ := by rw [Finset.mul_sum]
    _ ≤ a * Mconst a c C * Tpot f d a j := by
        gcongr
        unfold Tpot
        calc ∑ h₀ ∈ P, Pm f d h₀ * a ^ reachN f d h₀
            = ∑ x ∈ P.attach, Pm f d x.1 * a ^ reachN f d x.1 := (Finset.sum_attach _ _).symm
          _ = ∑ y ∈ P.attach.image (fun x => (⟨x.1, hProot x.1 x.2⟩ : {h // IsRoot f d j h})),
              Pm f d y.1 * a ^ reachN f d y.1 :=
              (Finset.sum_image (f := fun y : {h // IsRoot f d j h} => Pm f d y.1 * a ^ reachN f d y.1)
                (g := fun x : {h // h ∈ P} => (⟨x.1, hProot x.1 x.2⟩ : {h // IsRoot f d j h}))
                (fun x _ y _ h => Subtype.ext (by simp only [Subtype.mk.injEq] at h; exact h))).symm
          _ ≤ _ := ENNReal.sum_le_tsum _

theorem Tpot_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {c C : ℝ}
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r)))
    {a : ℝ≥0∞} (ha : 1 ≤ a) : ∀ j : ℕ, Tpot f d a j ≤ (a * Mconst a c C) ^ j
  | 0 => by rw [Tpot_zero, pow_zero]
  | j + 1 => by
    rw [pow_succ, mul_comm]
    exact (Tpot_succ_le f hd hCB ha j).trans (by gcongr; exact Tpot_le f hd hCB ha j)

/-! ### The reach event -/

/-- The exploration from `f` visits a face at distance at least `R`. -/
def ReachEvent (f d : Site) (R : ℕ) : Set (Config squareGraph) :=
  {ρ | ∃ n, ∃ g ∈ (explore ρ f d n).visited, (R : ℤ) ≤ linfDist g f}

/-- At least `N` forced tests. -/
def KEvent (f d : Site) (N : ℕ) : Set (Config squareGraph) :=
  {ρ | (N : ℕ∞) ≤ forcedCount ρ f d}

theorem history_take_of_lt_length (ρ : Config squareGraph) (f d : Site) {i n : ℕ} (hin : i ≤ n)
    (hi : i < (history ρ f d n).length) : (history ρ f d n).take i = history ρ f d i := by
  refine history_take ρ f d hin ?_
  intro hs
  have := explore_stuck ρ f d hin hs
  unfold history at hi
  rw [this] at hi
  have := history_length_le ρ f d i
  unfold history at this
  omega

theorem forced_explore_mono (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (hmn : m ≤ n) :
    (explore ρ f d m).forced ≤ (explore ρ f d n).forced := by
  rw [forced_explore, forced_explore]
  exact forced_mono_prefix f d (history_prefix ρ f d hmn)

/-- The root of the interval containing stage `n`. -/
theorem exists_root_of_stage (f d : Site) (ρ : Config squareGraph) (n : ℕ) : ∃ h₀, IsRoot f d (explore ρ f d n).forced h₀ ∧ history ρ f d h₀.length = h₀ ∧
      h₀.length ≤ n ∧ IntervalHist f d h₀ (history ρ f d n) := by
  set j := (explore ρ f d n).forced with hj
  -- the nonforced condition between stage `m` and `n`
  have hnf : ∀ h₀, history ρ f d h₀.length = h₀ → h₀.length ≤ n →
      (replay f d h₀).forced = j → IntervalHist f d h₀ (history ρ f d n) := by
    intro h₀ hρ0 hlen hf0
    refine ⟨?_, fun i hi hi' e rest he hW => ?_⟩
    · rw [← hρ0]; exact history_prefix ρ f d hlen
    · rw [history_take_of_lt_length ρ f d (by have := history_length_le ρ f d n; omega) hi'] at he hW
      have h1 : (explore ρ f d (i + 1)).forced = (explore ρ f d i).forced + 1 := by
        rw [forced_explore, forced_explore,
          history_succ_cons ρ f d i (by rw [explore_eq_replay]; exact he)]
        rw [forced_append_cons f d _ he, if_pos hW]
      have h2 : (explore ρ f d h₀.length).forced ≤ (explore ρ f d i).forced :=
        forced_explore_mono ρ f d hi
      have h3 : (explore ρ f d (i + 1)).forced ≤ j :=
        forced_explore_mono ρ f d (by have := history_length_le ρ f d n; omega)
      rw [forced_explore, hρ0] at h2
      omega
  cases hj0 : j with
  | zero =>
    refine ⟨[], rfl, by simp [history, explore_zero, explInit], Nat.zero_le _, ?_⟩
    exact hnf [] (by simp [history, explore_zero, explInit]) (Nat.zero_le _) (by rw [hj0]; rfl)
  | succ j' =>
    have hK : ((j' + 1 : ℕ) : ℕ∞) ≤ forcedCount ρ f d :=
      (le_forcedCount_iff ρ f d _).2 ⟨n, by rw [← hj0]⟩
    obtain ⟨h₀, hm, hρ0⟩ := minF_exists f d (by omega) hK
    have hlen : h₀.length ≤ n := by
      by_contra hlt
      push Not at hlt
      have hne : (explore ρ f d n).active ≠ [] := by
        intro hs
        have := explore_stuck ρ f d hlt.le hs
        unfold history at hρ0
        rw [this] at hρ0
        have := congrArg List.length hρ0
        have := history_length_le ρ f d n
        unfold history at this
        omega
      have htake := history_take ρ f d hlt.le hne
      rw [hρ0] at htake
      have := hm.2 n hlt
      rw [htake, ← forced_explore, ← hj, hj0] at this
      omega
    exact ⟨h₀, hm, hρ0, hlen, hnf h₀ hρ0 hlen (by rw [hm.1, hj0])⟩

/-- The decomposition of the reach event. -/
theorem reachEvent_subset (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) (R n₀ : ℕ) :
    ReachEvent f d R ⊆ KEvent f d n₀ ∪
      (⋃ j ∈ Finset.range n₀, ⋃ h₀ : {h₀ // IsRoot f d j h₀ ∧ Pm f d h₀ = 0},
        {ρ | history ρ f d h₀.1.length = h₀.1}) ∪
      (⋃ j ∈ Finset.range n₀, ⋃ h₀ : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀},
        {ρ | history ρ f d h₀.1.length = h₀.1}) ∪
      (⋃ j ∈ Finset.range n₀, ⋃ h₀ : {h₀ // IsRoot f d j h₀},
        ({ρ | history ρ f d h₀.1.length = h₀.1} ∩ IntReach f d h₀.1 (R - R / 2))) := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  rintro ρ ⟨n, g, hg, hdist⟩
  set j := (explore ρ f d n).forced with hj
  rcases Nat.lt_or_ge j n₀ with hjn | hjn
  · obtain ⟨h₀, hr, hρ0, hlen, hI⟩ := exists_root_of_stage f d ρ n
    rw [← hj] at hr
    by_cases hpos : Pm f d h₀ = 0
    · left; left; right
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, exists_prop]
      exact ⟨j, hjn, ⟨h₀, hr, hpos⟩, hρ0⟩
    by_cases hbig : R / 2 ≤ reachN f d h₀
    · left; right
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, exists_prop]
      exact ⟨j, hjn, ⟨h₀, hr, hbig⟩, hρ0⟩
    · right
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      refine ⟨j, hjn, ⟨h₀, hr⟩, hρ0, n, hI, g, hg, ?_, ?_⟩
      · show g ∉ (replay f d h₀).visited
        intro hg0
        have := le_reachN hg0
        omega
      · show ((R - R / 2 : ℕ) : ℤ) ≤ linfDist g (rootOf f d h₀)
        have hs0 := intervalStart_of_root f hd hr hpos
        have hrv := le_reachN hs0.1
        have htri := linfDist_triangle g (rootOf f d h₀) f
        have hcast : ((R - R / 2 : ℕ) : ℤ) = (R : ℤ) - ((R / 2 : ℕ) : ℤ) := by
          rw [Nat.cast_sub (Nat.div_le_self _ _)]
        rw [hcast]
        omega
  · left; left; left
    exact (le_forcedCount_iff ρ f d n₀).2 ⟨n, hjn⟩

theorem KEvent_zero (f d : Site) : KEvent f d 0 = Set.univ := by
  ext ρ; simp [KEvent]

theorem tsum_root_Pm (f : Site) {d : Site} (hd : IsUnit d) (j : ℕ) :
    ∑' h₀ : {h₀ // IsRoot f d j h₀}, Pm f d h₀.1 = uniformLaw clockwise (KEvent f d j) := by
  cases j with
  | zero =>
    have huniq : ∀ x : {h // IsRoot f d 0 h}, x = ⟨[], rfl⟩ := fun x => Subtype.ext x.2
    rw [tsum_eq_single ⟨[], rfl⟩ (fun x hx => absurd (huniq x) hx), KEvent_zero, measure_univ]
    exact Pm_nil f d
  | succ j =>
    rw [KEvent, K_measure_eq f hd (by omega)]
    rfl

/-- The measure bound for the reach event. -/
theorem reachEvent_measure_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {c C : ℝ}
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r)))
    {a : ℝ≥0∞} (ha : 1 ≤ a) (ha' : a ≠ ⊤) (R n₀ : ℕ) (hR : 1 ≤ R) :
    uniformLaw clockwise (ReachEvent f d R) ≤ uniformLaw clockwise (KEvent f d n₀) +
      ∑ j ∈ Finset.range n₀, ((a * Mconst a c C) ^ j / a ^ (R / 2) +
        ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) *
          uniformLaw clockwise (KEvent f d j)) := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  refine (measure_mono (reachEvent_subset f hd R n₀)).trans ?_
  refine (measure_union_le (μ := uniformLaw clockwise) _ _).trans ?_
  refine (add_le_add (measure_union_le (μ := uniformLaw clockwise) _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (measure_union_le (μ := uniformLaw clockwise) _ _) le_rfl)
    le_rfl).trans ?_
  -- the null part
  have hnull : uniformLaw clockwise (⋃ j ∈ Finset.range n₀,
      ⋃ h₀ : {h₀ // IsRoot f d j h₀ ∧ Pm f d h₀ = 0}, {ρ | history ρ f d h₀.1.length = h₀.1}) = 0 := by
    refine le_antisymm ((measure_biUnion_finset_le _ _).trans ?_) (zero_le)
    refine le_of_eq (Finset.sum_eq_zero (fun j _ => ?_))
    refine le_antisymm ((measure_iUnion_le _).trans ?_) (zero_le)
    refine le_of_eq (ENNReal.tsum_eq_zero.2 (fun h₀ => h₀.2.2))
  -- the big part
  have hbig : ∀ j, uniformLaw clockwise (⋃ h₀ : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀},
      {ρ | history ρ f d h₀.1.length = h₀.1}) ≤ (a * Mconst a c C) ^ j / a ^ (R / 2) := by
    intro j
    refine (measure_iUnion_le _).trans ?_
    have hapow : a ^ (R / 2) ≠ 0 := pow_ne_zero _ (by intro h; rw [h] at ha; exact absurd ha (by simp))
    have hapow' : a ^ (R / 2) ≠ ⊤ := ENNReal.pow_ne_top ha'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hapow) (Or.inl hapow')]
    calc (∑' h₀ : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀}, Pm f d h₀.1) * a ^ (R / 2)
        = ∑' h₀ : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀}, Pm f d h₀.1 * a ^ (R / 2) := by
          rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' h₀ : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀}, Pm f d h₀.1 * a ^ reachN f d h₀.1 :=
          ENNReal.tsum_le_tsum (fun x =>
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha x.2.2) (zero_le))
      _ ≤ ∑' h₀ : {h₀ // IsRoot f d j h₀}, Pm f d h₀.1 * a ^ reachN f d h₀.1 :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun x : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀} =>
              (⟨x.1, x.2.1⟩ : {h₀ // IsRoot f d j h₀}))
            (fun x y h => Subtype.ext (by simp only [Subtype.mk.injEq] at h; exact h)) _
      _ ≤ (a * Mconst a c C) ^ j := Tpot_le f hd hCB ha j
  -- the interval part
  have hint : ∀ j, uniformLaw clockwise (⋃ h₀ : {h₀ // IsRoot f d j h₀},
      ({ρ | history ρ f d h₀.1.length = h₀.1} ∩ IntReach f d h₀.1 (R - R / 2))) ≤
      ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) * uniformLaw clockwise (KEvent f d j) := by
    intro j
    refine (measure_iUnion_le _).trans ?_
    rw [← tsum_root_Pm f hdu j, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun h₀ => ?_)
    by_cases hpos : Pm f d h₀.1 = 0
    · calc uniformLaw clockwise ({ρ | history ρ f d h₀.1.length = h₀.1} ∩ IntReach f d h₀.1 (R - R / 2))
          ≤ Pm f d h₀.1 := measure_mono Set.inter_subset_left
        _ = 0 := hpos
        _ ≤ _ := zero_le
    · rw [mul_comm]
      exact intReach_measure_le f hd hCB (intervalStart_of_root f hd h₀.2 hpos) (by omega)
  rw [hnull, add_zero]
  calc uniformLaw clockwise (KEvent f d n₀) +
        uniformLaw clockwise (⋃ j ∈ Finset.range n₀, ⋃ h₀ : {h₀ // IsRoot f d j h₀ ∧ R / 2 ≤ reachN f d h₀},
          {ρ | history ρ f d h₀.1.length = h₀.1}) +
        uniformLaw clockwise (⋃ j ∈ Finset.range n₀, ⋃ h₀ : {h₀ // IsRoot f d j h₀},
          ({ρ | history ρ f d h₀.1.length = h₀.1} ∩ IntReach f d h₀.1 (R - R / 2)))
      ≤ uniformLaw clockwise (KEvent f d n₀) +
        ∑ j ∈ Finset.range n₀, (a * Mconst a c C) ^ j / a ^ (R / 2) +
        ∑ j ∈ Finset.range n₀, ENNReal.ofReal (C * Real.exp (-c * ((R - R / 2 : ℕ) : ℝ))) *
          uniformLaw clockwise (KEvent f d j) := by
        gcongr
        · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun j _ => hbig j))
        · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun j _ => hint j))
    _ = _ := by rw [add_assoc, ← Finset.sum_add_distrib]

end Rotor

import Rotor.Support.ExplProb
import Rotor.Support.ExplCover
import Rotor.Frozen.Square.Exploration

/-!
Lemma 5.6 (`lem:square-forced-tests`, `rotor.tex:2058-2170`), part 1: the probability of a
history.  `Pm f d h` is the law of the event that the first `h.length` outcomes are `h`; it is
measurable, splits over the next outcome, and Lemma 5.4 (iii) gives the split: a forced test
is open almost surely and a nonforced test closes with probability at least `1/2`.  The event
that `N` forced tests occur decomposes over the minimal histories `MinF f d N` at which the
forced count first reaches `N`; a terminal continuation with fewer forced tests is disjoint
from it (`escape`).
-/

open Finset List MeasureTheory ENNReal

namespace Rotor

/-! ### Measurability -/

theorem measurableSet_dualOpen {a b : Site} (h : squareGraph.Adj a b) :
    MeasurableSet {ρ : Config squareGraph | DualOpen ρ a b} := by
  have : {ρ : Config squareGraph | DualOpen ρ a b} =
      (fun ρ : Config squareGraph => ρ (primalTail a b)) ⁻¹'
        {x | openAt (primalDir a b) ((nbr (primalTail a b)).symm x) = true} := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have := dualOpen_iff_openAt ρ (primalTail a b) (primalDir a b)
    rw [dualEdge_primal h] at this
    rw [this]
    rfl
  rw [this]
  exact measurable_pi_apply _ MeasurableSet.of_discrete

open Classical in
theorem measurableSet_testEvent (C : List (Site × Site × Bool))
    (hadj : ∀ t ∈ C, squareGraph.Adj t.1 t.2.1) : MeasurableSet (testEvent C) := by
  induction C with
  | nil => rw [testEvent_nil]; exact MeasurableSet.univ
  | cons t C ih =>
    have hsplit : testEvent (t :: C) =
        {ρ | decide (DualOpen ρ t.1 t.2.1) = t.2.2} ∩ testEvent C := by
      ext ρ
      simp only [testEvent, Set.mem_setOf_eq, List.mem_cons, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨h t (Or.inl rfl), fun t' ht' => h t' (Or.inr ht')⟩
      · rintro ⟨h1, h2⟩ t' ht'
        rcases ht' with rfl | ht'
        · exact h1
        · exact h2 t' ht'
    rw [hsplit]
    refine MeasurableSet.inter ?_ (ih (fun t' ht' => hadj t' (List.mem_cons_of_mem _ ht')))
    have hm := measurableSet_dualOpen (hadj t List.mem_cons_self)
    rcases hb : t.2.2 with _ | _
    · have : {ρ : Config squareGraph | decide (DualOpen ρ t.1 t.2.1) = false} =
          {ρ | DualOpen ρ t.1 t.2.1}ᶜ := by ext ρ; simp
      rw [this]; exact hm.compl
    · have : {ρ : Config squareGraph | decide (DualOpen ρ t.1 t.2.1) = true} =
          {ρ | DualOpen ρ t.1 t.2.1} := by ext ρ; simp
      rw [this]; exact hm

/-! ### Histories along the exploration -/

theorem explore_stuck (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (hmn : m ≤ n)
    (h : (explore ρ f d m).active = []) : explore ρ f d n = explore ρ f d m := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · rw [explore_succ, ih (by omega), explStep_nil ρ h]
    · have : m = n + 1 := by omega
      subst this; rfl

theorem history_prefix (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (hmn : m ≤ n) :
    history ρ f d m <+: history ρ f d n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact List.prefix_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · refine (ih (by omega)).trans ?_
      rcases hs : (explore ρ f d n).active with _ | ⟨e, rest⟩
      · rw [history_succ_nil ρ f d n hs]
      · rw [history_succ_cons ρ f d n hs]
        exact List.prefix_append _ _
    · have : m = n + 1 := by omega
      subst this; exact List.prefix_refl _

/-- `history ρ n = h` for `n ≥ h.length` means the first `h.length` outcomes are `h` and,
if `n > h.length`, the exploration has terminated by then. -/
theorem history_eq_iff (ρ : Config squareGraph) (f d : Site) (n : ℕ) (h : List Bool) :
    history ρ f d n = h ↔
      history ρ f d h.length = h ∧ (h.length = n ∨ (h.length < n ∧ (replay f d h).active = [])) := by
  constructor
  · intro hn
    have hlen : h.length ≤ n := by rw [← hn]; exact history_length_le ρ f d n
    have hpre := history_prefix ρ f d hlen
    rw [hn] at hpre
    have hlen' := history_length_le ρ f d h.length
    have hm : history ρ f d h.length = h := by
      rcases Nat.lt_or_ge (history ρ f d h.length).length h.length with hlt | hge
      · exfalso
        have hstuck : (explore ρ f d h.length).active = [] := by
          by_contra hne
          have := history_length_eq ρ f d h.length hne
          omega
        have := explore_stuck ρ f d hlen hstuck
        unfold history at hn hlt
        rw [this] at hn
        rw [hn] at hlt
        exact lt_irrefl _ hlt
      · exact hpre.eq_of_length (by omega)
    refine ⟨hm, ?_⟩
    rcases Nat.lt_or_ge h.length n with hlt | hge
    · right
      refine ⟨hlt, ?_⟩
      by_contra hne
      have hne' : (explore ρ f d h.length).active ≠ [] := by
        rw [explore_eq_replay, hm]; exact hne
      rcases hs : (explore ρ f d h.length).active with _ | ⟨e, rest⟩
      · exact hne' hs
      have h1 := history_succ_cons ρ f d h.length hs
      rw [hm] at h1
      have h2 := history_prefix ρ f d (show h.length + 1 ≤ n by omega)
      rw [h1, hn] at h2
      have := h2.length_le
      simp at this
    · left; omega
  · rintro ⟨hm, hn | ⟨hlt, hstuck⟩⟩
    · rw [← hn]; exact hm
    · have hstuck' : (explore ρ f d h.length).active = [] := by
        rw [explore_eq_replay, hm]; exact hstuck
      unfold history
      rw [explore_stuck ρ f d hlt.le hstuck']
      exact hm

theorem measurableSet_history_len (f : Site) {d : Site} (hd : IsUnit d) (h : List Bool) :
    MeasurableSet {ρ : Config squareGraph | history ρ f d h.length = h} := by
  by_cases hpre : ∀ i < h.length, (replay f d (h.take i)).active ≠ []
  · rw [history_event f d h hpre]
    exact measurableSet_testEvent _ (explInv_replay f hd h).tested_adj
  · push_neg at hpre
    obtain ⟨i, hi, hstuck⟩ := hpre
    have : {ρ : Config squareGraph | history ρ f d h.length = h} = ∅ := by
      ext ρ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hρ
      have hpre' := history_prefix ρ f d hi.le
      rw [hρ] at hpre'
      have hlen : (history ρ f d i).length ≤ i := history_length_le ρ f d i
      have hleni : (history ρ f d i).length = i := by
        rcases Nat.lt_or_ge (history ρ f d i).length i with hlt | hge
        · exfalso
          have hs : (explore ρ f d i).active = [] := by
            by_contra hne
            have := history_length_eq ρ f d i hne
            omega
          have := explore_stuck ρ f d hi.le hs
          unfold history at hρ hlt
          rw [this] at hρ
          rw [hρ] at hlt
          omega
        · omega
      have hi' : history ρ f d i = h.take i := by
        rw [List.prefix_iff_eq_take] at hpre'
        rw [hpre', hleni]
      have hs : (explore ρ f d i).active = [] := by
        rw [explore_eq_replay, hi']; exact hstuck
      have := explore_stuck ρ f d hi.le hs
      unfold history at hρ
      rw [this] at hρ
      have := congrArg List.length hρ
      unfold history at hi'
      rw [hi'] at this
      simp only [List.length_take, min_eq_left hi.le] at this
      omega
    rw [this]; exact MeasurableSet.empty

theorem measurableSet_history (f : Site) {d : Site} (hd : IsUnit d) (n : ℕ) (h : List Bool) :
    MeasurableSet {ρ : Config squareGraph | history ρ f d n = h} := by
  have : {ρ : Config squareGraph | history ρ f d n = h} =
      {ρ | history ρ f d h.length = h} ∩
        {ρ | h.length = n ∨ (h.length < n ∧ (replay f d h).active = [])} := by
    ext ρ; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; exact history_eq_iff ρ f d n h
  rw [this]
  refine (measurableSet_history_len f hd h).inter ?_
  by_cases hc : h.length = n ∨ (h.length < n ∧ (replay f d h).active = [])
  · simp only [hc, Set.setOf_true]; exact MeasurableSet.univ
  · simp only [hc, Set.setOf_false]; exact MeasurableSet.empty

/-! ### The probability of a history -/

/-- The probability that the first `h.length` outcomes are `h`. -/
noncomputable def Pm (f d : Site) (h : List Bool) : ℝ≥0∞ :=
  uniformLaw clockwise {ρ | history ρ f d h.length = h}

theorem Pm_le_one (f d : Site) (h : List Bool) : Pm f d h ≤ 1 := prob_le_one

theorem Pm_ne_top (f d : Site) (h : List Bool) : Pm f d h ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (Pm_le_one f d h)

theorem history_of_append (ρ : Config squareGraph) (f d : Site) (h : List Bool) (o : Bool)
    (hρ : history ρ f d (h ++ [o]).length = h ++ [o]) : history ρ f d h.length = h := by
  have := history_prefix ρ f d (show h.length ≤ (h ++ [o]).length by simp)
  rw [hρ] at this
  have hlen : (history ρ f d h.length).length = h.length := by
    apply history_length_eq
    intro hs
    have h1 := history_succ_nil ρ f d h.length hs
    simp only [List.length_append, List.length_singleton] at hρ
    rw [hρ] at h1
    have := congrArg List.length h1
    have := history_length_le ρ f d h.length
    simp at *
    omega
  rw [List.prefix_iff_eq_take] at this
  rw [this, hlen, List.take_left' rfl]

theorem Pm_append_le (f d : Site) (h : List Bool) (o : Bool) : Pm f d (h ++ [o]) ≤ Pm f d h :=
  measure_mono (fun ρ hρ => history_of_append ρ f d h o hρ)

theorem Pm_stuck (f d : Site) (h : List Bool) (hs : (replay f d h).active = []) (o : Bool) :
    Pm f d (h ++ [o]) = 0 := by
  unfold Pm
  have : {ρ : Config squareGraph | history ρ f d (h ++ [o]).length = h ++ [o]} = ∅ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hρ
    have hm := history_of_append ρ f d h o hρ
    have hs' : (explore ρ f d h.length).active = [] := by rw [explore_eq_replay, hm]; exact hs
    have := history_succ_nil ρ f d h.length hs'
    rw [hm] at this
    simp only [List.length_append, List.length_singleton] at hρ
    rw [hρ] at this
    simp at this
  rw [this, measure_empty]

open Classical in
theorem history_append_eq (f d : Site) (h : List Bool) {e : Site × Site}
    {rest : List (Site × Site)} (he : (replay f d h).active = e :: rest) (o : Bool) :
    {ρ : Config squareGraph | history ρ f d (h ++ [o]).length = h ++ [o]} =
      {ρ | history ρ f d h.length = h} ∩ {ρ | decide (DualOpen ρ e.1 e.2) = o} := by
  ext ρ
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.length_append, List.length_singleton]
  rw [history_append_iff ρ f d h o (by rw [he]; exact List.cons_ne_nil _ _), outcome,
    curEdge_eq he]

theorem Pm_split (f : Site) {d : Site} (hd : IsUnit d) (h : List Bool) {e : Site × Site}
    {rest : List (Site × Site)} (he : (replay f d h).active = e :: rest) :
    Pm f d (h ++ [true]) + Pm f d (h ++ [false]) = Pm f d h := by
  classical
  unfold Pm
  rw [history_append_eq f d h he true, history_append_eq f d h he false]
  have hadj : squareGraph.Adj e.1 e.2 :=
    (explInv_replay f hd h).active_adj e (by rw [he]; exact List.mem_cons_self)
  have hm := measurableSet_dualOpen hadj
  have h1 : {ρ : Config squareGraph | decide (DualOpen ρ e.1 e.2) = true} =
      {ρ | DualOpen ρ e.1 e.2} := by ext ρ; simp
  have h2 : {ρ : Config squareGraph | decide (DualOpen ρ e.1 e.2) = false} =
      {ρ | DualOpen ρ e.1 e.2}ᶜ := by ext ρ; simp
  rw [h1, h2, ← measure_union (Set.disjoint_of_subset_right (Set.inter_subset_right)
    (Set.disjoint_of_subset_left Set.inter_subset_right disjoint_compl_right))
    ((measurableSet_history_len f hd h).inter hm.compl)]
  congr 1
  rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]

theorem Pm_true_eq (f d : Site) (h : List Bool) {e : Site × Site} {rest : List (Site × Site)}
    (he : (replay f d h).active = e :: rest) :
    Pm f d (h ++ [true]) =
      uniformLaw clockwise {ρ | history ρ f d h.length = h ∧ DualOpen ρ e.1 e.2} := by
  classical
  unfold Pm
  rw [history_append_eq f d h he true]
  congr 1
  ext ρ; simp

/-- A forced test is open almost surely. -/
theorem Pm_forced (f d : Site) (hd : squareGraph.Adj f (f + d)) (h : List Bool) {e : Site × Site}
    {rest : List (Site × Site)} (he : (replay f d h).active = e :: rest)
    (hW : TestedAs (replay f d h).tested (sideW e.1 e.2) false) :
    Pm f d (h ++ [true]) = Pm f d h ∧ Pm f d (h ++ [false]) = 0 := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  have key := ((Rotor.Frozen.square_exploration f d hd).2.2 h e rest he).1 hW
  rw [← Pm_true_eq f d h he] at key
  have hsplit := Pm_split f hdu h he
  refine ⟨key, ?_⟩
  rw [key] at hsplit
  have := Pm_ne_top f d h
  have h0 : Pm f d h + Pm f d (h ++ [false]) = Pm f d h + 0 := by rw [add_zero]; exact hsplit
  exact (ENNReal.add_right_inj this).1 h0

/-- A nonforced test closes with conditional probability at least `1/2`. -/
theorem Pm_nonforced (f d : Site) (hd : squareGraph.Adj f (f + d)) (h : List Bool)
    {e : Site × Site} {rest : List (Site × Site)} (he : (replay f d h).active = e :: rest)
    (hW : ¬ TestedAs (replay f d h).tested (sideW e.1 e.2) false) :
    Pm f d h ≤ 2 * Pm f d (h ++ [false]) := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  have key := (Rotor.Frozen.square_exploration f d hd).2.2 h e rest he
  have hsplit := Pm_split f hdu h he
  rw [← Pm_true_eq f d h he] at key
  by_cases hW' : TestedAs (replay f d h).tested (sideW e.1 e.2) true
  · have h0 := key.2.1 hW'
    rw [h0, zero_add] at hsplit
    rw [hsplit, two_mul]
    exact le_add_self
  · have hhalf := key.2.2 hW hW'
    rw [one_div, ← ENNReal.div_eq_inv_mul] at hhalf
    rw [hhalf] at hsplit
    have hhalves := ENNReal.add_halves (Pm f d h)
    rw [← hhalves] at hsplit
    have hne : Pm f d h / 2 ≠ ⊤ :=
      ne_top_of_le_ne_top (Pm_ne_top f d h) (ENNReal.half_le_self)
    have hfalse : Pm f d (h ++ [false]) = Pm f d h / 2 := (ENNReal.add_right_inj hne).1 hsplit
    rw [hfalse, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

/-! ### The forced count along histories -/

open Classical in
theorem forced_append_cons (f d : Site) (h : List Bool) {e : Site × Site}
    {rest : List (Site × Site)} (he : (replay f d h).active = e :: rest) (o : Bool) :
    (replay f d (h ++ [o])).forced =
      if TestedAs (replay f d h).tested (sideW e.1 e.2) false then (replay f d h).forced + 1
      else (replay f d h).forced := by
  rw [replay_append, explStepWith_cons he]

theorem forced_append_nil (f d : Site) (h : List Bool) (hs : (replay f d h).active = [])
    (o : Bool) : (replay f d (h ++ [o])).forced = (replay f d h).forced := by
  rw [replay_append, explStepWith_nil hs]

theorem forced_append_le (f d : Site) (h : List Bool) (o : Bool) :
    (replay f d (h ++ [o])).forced ≤ (replay f d h).forced + 1 := by
  rcases he : (replay f d h).active with _ | ⟨e, rest⟩
  · rw [forced_append_nil f d h he]; omega
  · rw [forced_append_cons f d h he]; split_ifs <;> omega

theorem le_forced_append (f d : Site) (h : List Bool) (o : Bool) :
    (replay f d h).forced ≤ (replay f d (h ++ [o])).forced := by
  rcases he : (replay f d h).active with _ | ⟨e, rest⟩
  · rw [forced_append_nil f d h he]
  · rw [forced_append_cons f d h he]; split_ifs <;> omega

theorem forced_mono_prefix (f d : Site) {h₁ h₂ : List Bool} (hp : h₁ <+: h₂) :
    (replay f d h₁).forced ≤ (replay f d h₂).forced := by
  obtain ⟨t, rfl⟩ := hp
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t o ih =>
    rw [← List.append_assoc]
    exact ih.trans (le_forced_append f d _ o)

theorem forced_explore (ρ : Config squareGraph) (f d : Site) (n : ℕ) :
    (explore ρ f d n).forced = (replay f d (history ρ f d n)).forced := by
  rw [← explore_eq_replay]

theorem le_forcedCount_iff (ρ : Config squareGraph) (f d : Site) (N : ℕ) :
    (N : ℕ∞) ≤ forcedCount ρ f d ↔ ∃ n, N ≤ (explore ρ f d n).forced := by
  constructor
  · intro hN
    by_contra hcon
    push_neg at hcon
    rcases N with _ | N
    · exact absurd (hcon 0) (Nat.not_lt_zero _)
    have hle : forcedCount ρ f d ≤ (N : ℕ∞) := by
      unfold forcedCount
      refine iSup_le (fun n => ?_)
      exact_mod_cast Nat.lt_succ_iff.1 (hcon n)
    have := hN.trans hle
    have h' : N + 1 ≤ N := by exact_mod_cast this
    omega
  · rintro ⟨n, hn⟩
    unfold forcedCount
    exact le_iSup_of_le n (by exact_mod_cast hn)

theorem forcedCount_of_history {ρ : Config squareGraph} (f d : Site) {h : List Bool}
    (hρ : history ρ f d h.length = h) :
    ((replay f d h).forced : ℕ∞) ≤ forcedCount ρ f d := by
  rw [le_forcedCount_iff]
  exact ⟨h.length, by rw [forced_explore, hρ]⟩

theorem forcedCount_eq_of_stuck {ρ : Config squareGraph} (f d : Site) {h : List Bool}
    (hρ : history ρ f d h.length = h) (hs : (replay f d h).active = []) :
    forcedCount ρ f d = (replay f d h).forced := by
  apply le_antisymm
  · unfold forcedCount
    refine iSup_le (fun n => ?_)
    rcases Nat.lt_or_ge n h.length with hlt | hge
    · have h1 := forced_mono_prefix f d (history_prefix ρ f d hlt.le)
      rw [hρ] at h1
      rw [forced_explore]
      exact_mod_cast h1
    · have hs' : (explore ρ f d h.length).active = [] := by
        rw [explore_eq_replay, hρ]; exact hs
      rw [explore_stuck ρ f d hge hs', explore_eq_replay, hρ]
  · exact forcedCount_of_history f d hρ

/-- The first `h.length` outcomes, when the exploration ran at least `h.length` tests. -/
theorem history_take (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (hmn : m ≤ n)
    (hne : (explore ρ f d m).active ≠ []) : (history ρ f d n).take m = history ρ f d m := by
  have hp := history_prefix ρ f d hmn
  rw [List.prefix_iff_eq_take] at hp
  rw [history_length_eq ρ f d m hne] at hp
  exact hp.symm

theorem history_of_prefix {ρ : Config squareGraph} (f d : Site) {h h' : List Bool} (hp : h <+: h')
    (hρ : history ρ f d h'.length = h') : history ρ f d h.length = h := by
  rcases Nat.lt_or_ge h.length h'.length with hlt | hge
  · have hne : (explore ρ f d h.length).active ≠ [] := by
      intro hs
      have := explore_stuck ρ f d hlt.le hs
      unfold history at hρ
      rw [this] at hρ
      have := congrArg List.length hρ
      have := history_length_le ρ f d h.length
      unfold history at this
      omega
    have h1 := history_take ρ f d hlt.le hne
    rw [hρ] at h1
    rw [List.prefix_iff_eq_take] at hp
    rw [← h1, ← hp]
  · have : h = h' := hp.eq_of_length (by have := hp.length_le; omega)
    subst this; exact hρ

theorem Pm_pos_config (f d : Site) {h : List Bool} (hne : Pm f d h ≠ 0) :
    ∃ ρ : Config squareGraph, history ρ f d h.length = h ∧ explore ρ f d h.length = replay f d h := by
  obtain ⟨ρ, hρ⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨ρ, hρ, by rw [explore_eq_replay, hρ]⟩

/-! ### Minimal histories reaching a forced count -/

/-- `h` is the history at which the forced count first reaches `N`. -/
def MinF (f d : Site) (N : ℕ) (h : List Bool) : Prop :=
  (replay f d h).forced = N ∧ ∀ i < h.length, (replay f d (h.take i)).forced < N

theorem minF_exists (f d : Site) {N : ℕ} (hN : 1 ≤ N) {ρ : Config squareGraph}
    (hρ : (N : ℕ∞) ≤ forcedCount ρ f d) : ∃ h, MinF f d N h ∧ history ρ f d h.length = h := by
  classical
  have hex : ∃ n, N ≤ (explore ρ f d n).forced := (le_forcedCount_iff ρ f d N).1 hρ
  set n₀ := Nat.find hex with hn₀def
  have hn₀ : N ≤ (explore ρ f d n₀).forced := Nat.find_spec hex
  have hmin : ∀ m < n₀, (explore ρ f d m).forced < N := fun m hm => by
    have := Nat.find_min hex hm; omega
  have hpos : 0 < n₀ := by
    by_contra h0
    push_neg at h0
    have h00 : n₀ = 0 := by omega
    rw [h00] at hn₀
    simp [explore_zero, explInit] at hn₀
    omega
  have hne : (explore ρ f d (n₀ - 1)).active ≠ [] := by
    intro hs
    have := explore_stuck ρ f d (show n₀ - 1 ≤ n₀ by omega) hs
    rw [this] at hn₀
    have := hmin (n₀ - 1) (by omega)
    omega
  rcases hs : (explore ρ f d (n₀ - 1)).active with _ | ⟨e, rest⟩
  · exact absurd hs hne
  have hsucc := history_succ_cons ρ f d (n₀ - 1) hs
  rw [show n₀ - 1 + 1 = n₀ by omega] at hsucc
  have hlen : (history ρ f d n₀).length = n₀ := by
    rw [hsucc, List.length_append, List.length_singleton, history_length_eq ρ f d _ hne]
    omega
  refine ⟨history ρ f d n₀, ⟨?_, ?_⟩, by rw [hlen]⟩
  · rw [← forced_explore]
    have h1 : (explore ρ f d n₀).forced ≤ (explore ρ f d (n₀ - 1)).forced + 1 := by
      rw [forced_explore, forced_explore, hsucc]
      exact forced_append_le f d _ _
    have := hmin (n₀ - 1) (by omega)
    omega
  · intro i hi
    rw [hlen] at hi
    rw [history_take ρ f d hi.le (by
      intro hs'
      have := explore_stuck ρ f d hi.le hs'
      rw [this] at hn₀
      have := hmin i hi; omega)]
    rw [← forced_explore]
    exact hmin i hi

theorem minF_unique (f d : Site) {N : ℕ} {h₁ h₂ : List Bool} (h1 : MinF f d N h₁)
    (h2 : MinF f d N h₂) {ρ : Config squareGraph} (hρ₁ : history ρ f d h₁.length = h₁)
    (hρ₂ : history ρ f d h₂.length = h₂) : h₁ = h₂ := by
  wlog hle : h₁.length ≤ h₂.length generalizing h₁ h₂
  · exact (this h2 h1 hρ₂ hρ₁ (by omega)).symm
  have hp := history_prefix ρ f d hle
  rw [hρ₁, hρ₂] at hp
  rcases Nat.lt_or_ge h₁.length h₂.length with hlt | hge
  · exfalso
    have := h2.2 h₁.length hlt
    rw [List.prefix_iff_eq_take] at hp
    rw [← hp] at this
    have := h1.1
    omega
  · exact hp.eq_of_length (by omega)

theorem K_event_eq (f d : Site) {N : ℕ} (hN : 1 ≤ N) :
    {ρ : Config squareGraph | (N : ℕ∞) ≤ forcedCount ρ f d} =
      ⋃ h : {h : List Bool // MinF f d N h}, {ρ | history ρ f d h.1.length = h.1} := by
  ext ρ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hρ
    obtain ⟨h, hm, hh⟩ := minF_exists f d hN hρ
    exact ⟨⟨h, hm⟩, hh⟩
  · rintro ⟨⟨h, hm⟩, hh⟩
    have := forcedCount_of_history f d hh
    rw [hm.1] at this
    exact this

theorem K_event_inter_eq (f d : Site) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (hNM : N ≤ M) :
    {ρ : Config squareGraph | (M : ℕ∞) ≤ forcedCount ρ f d} =
      ⋃ h : {h : List Bool // MinF f d N h},
        ({ρ | history ρ f d h.1.length = h.1} ∩ {ρ | (M : ℕ∞) ≤ forcedCount ρ f d}) := by
  ext ρ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hρ
    have hρN : (N : ℕ∞) ≤ forcedCount ρ f d := le_trans (by exact_mod_cast hNM) hρ
    obtain ⟨h, hm, hh⟩ := minF_exists f d hN hρN
    exact ⟨⟨h, hm⟩, hh, hρ⟩
  · rintro ⟨_, -, hρ⟩
    exact hρ

theorem K_disjoint (f d : Site) (N : ℕ)
    (S : {h : List Bool // MinF f d N h} → Set (Config squareGraph))
    (hS : ∀ h, S h ⊆ {ρ | history ρ f d h.1.length = h.1}) :
    Pairwise (Function.onFun _root_.Disjoint S) := by
  intro h₁ h₂ hne
  rw [Function.onFun, Set.disjoint_left]
  intro ρ h1 h2
  apply hne
  exact Subtype.ext (minF_unique f d h₁.2 h₂.2 (hS h₁ h1) (hS h₂ h2))

theorem measurableSet_K (f : Site) {d : Site} (hd : IsUnit d) (N : ℕ) :
    MeasurableSet {ρ : Config squareGraph | (N : ℕ∞) ≤ forcedCount ρ f d} := by
  have : {ρ : Config squareGraph | (N : ℕ∞) ≤ forcedCount ρ f d} =
      ⋃ n : ℕ, ⋃ h : {h : List Bool // N ≤ (replay f d h).forced},
        {ρ | history ρ f d n = h.1} := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, le_forcedCount_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, ⟨history ρ f d n, by rw [← forced_explore]; exact hn⟩, rfl⟩
    · rintro ⟨n, ⟨h, hh⟩, hρ⟩
      exact ⟨n, by rw [forced_explore, hρ]; exact hh⟩
  rw [this]
  exact MeasurableSet.iUnion (fun n =>
    MeasurableSet.iUnion (fun h => measurableSet_history f hd n h.1))

theorem K_measure_eq (f : Site) {d : Site} (hd : IsUnit d) {N : ℕ} (hN : 1 ≤ N) :
    uniformLaw clockwise {ρ | (N : ℕ∞) ≤ forcedCount ρ f d} =
      ∑' h : {h : List Bool // MinF f d N h}, Pm f d h.1 := by
  rw [K_event_eq f d hN, measure_iUnion (K_disjoint f d N _ (fun h => subset_rfl))
    (fun h => measurableSet_history_len f hd h.1)]
  rfl

theorem K_measure_step (f : Site) {d : Site} (hd : IsUnit d) {N : ℕ} (hN : 1 ≤ N) (M : ℕ)
    (hNM : N ≤ M) :
    uniformLaw clockwise {ρ | (M : ℕ∞) ≤ forcedCount ρ f d} =
      ∑' h : {h : List Bool // MinF f d N h},
        uniformLaw clockwise ({ρ | history ρ f d h.1.length = h.1} ∩
          {ρ | (M : ℕ∞) ≤ forcedCount ρ f d}) := by
  conv_lhs => rw [K_event_inter_eq f d hN M hNM]
  rw [measure_iUnion (K_disjoint f d N _ (fun h => Set.inter_subset_left))
    (fun h => (measurableSet_history_len f hd h.1).inter (measurableSet_K f hd M))]

/-- A terminal continuation `h'` of `h` with fewer than `N` forced tests is disjoint from the
event that `N` forced tests occur. -/
theorem escape (f : Site) {d : Site} (hd : IsUnit d) {h h' : List Bool} (hp : h <+: h')
    (hs : (replay f d h').active = []) {N : ℕ} (hN : (replay f d h').forced < N) :
    uniformLaw clockwise ({ρ | history ρ f d h.length = h} ∩
      {ρ | (N : ℕ∞) ≤ forcedCount ρ f d}) + Pm f d h' ≤ Pm f d h := by
  unfold Pm
  rw [← measure_union ?_ (measurableSet_history_len f hd h')]
  · apply measure_mono
    rintro ρ (⟨hρ, -⟩ | hρ)
    · exact hρ
    · exact history_of_prefix f d hp hρ
  · rw [Set.disjoint_left]
    rintro ρ ⟨-, hK⟩ hρ
    simp only [Set.mem_setOf_eq] at hK
    rw [forcedCount_eq_of_stuck f d hρ hs] at hK
    have : N ≤ (replay f d h').forced := by exact_mod_cast hK
    omega


end Rotor

import Rotor.Support.HistoryProb
import Rotor.Support.ActiveListLemma

/-!
Lemma 5.6 (`lem:square-forced-tests`), part 2: the cascade.  After a forced open test
`g = (t, w)` the active list is a sublist of the right turn `e` and the straight edge `f`
(the left turn returns to the visited tail of the closed side); the closed side of `g`
reversed is the `S` side of `f`, so `f` is never forced and, by Lemma 5.5, closing it
terminates the exploration.  Following the forced right turns through three stages, a single
terminal continuation of conditional probability at least `1/4` has fewer than three more
forced tests, whence `P{K ≥ 3k+1} ≤ (3/4)^k` and the explicit bound of the lemma.
-/

open Finset List MeasureTheory ENNReal

namespace Rotor

/-! ### The sides of the square in coordinates -/

theorem sideS_geom {t w : Site} (h : squareGraph.Adj t w) :
    sideS t w = (t + rotL (w - t), t) := by
  have h1 : w - t = rotR (rightFace (primalTail t w) (primalDir t w + 1) - t) := by
    have := corner_NE_sub_SE (primalTail t w) (primalDir t w)
    rwa [rightFace_primal h, leftFace_primal h] at this
  have hSW : rightFace (primalTail t w) (primalDir t w + 1) = t + rotL (w - t) := by
    rw [h1, rotL_rotR]; abel
  refine Prod.ext ?_ ?_
  · rw [sideS_fst, hSW]
  · rw [sideS_snd, rightFace_primal h]

theorem sideW_geom {t w : Site} (h : squareGraph.Adj t w) :
    sideW t w = (w + rotL (w - t), t + rotL (w - t)) := by
  have h1 : w - t = rotR (rightFace (primalTail t w) (primalDir t w + 1) - t) := by
    have := corner_NE_sub_SE (primalTail t w) (primalDir t w)
    rwa [rightFace_primal h, leftFace_primal h] at this
  have h2 : rightFace (primalTail t w) (primalDir t w + 2) -
      rightFace (primalTail t w) (primalDir t w + 1) = w - t := by
    have := corner_NW_sub_SW (primalTail t w) (primalDir t w)
    rwa [rightFace_primal h, leftFace_primal h] at this
  have hSW : rightFace (primalTail t w) (primalDir t w + 1) = t + rotL (w - t) := by
    rw [h1, rotL_rotR]; abel
  have hNW : rightFace (primalTail t w) (primalDir t w + 2) = w + rotL (w - t) := by
    rw [show w + rotL (w - t) = (t + rotL (w - t)) + (w - t) by abel, ← hSW, ← h2]; abel
  refine Prod.ext ?_ ?_
  · rw [sideW_fst, hNW]
  · rw [sideW_snd, hSW]

theorem rotR_rotR (u : Site) : rotR (rotR u) = -u := by
  obtain ⟨a, b⟩ := u; simp [rotR]

theorem rotL_ne_neg {u : Site} (hu : IsUnit u) : rotL u ≠ -u := by
  rcases hu with rfl | rfl | rfl | rfl <;> decide

theorem adj_of_isUnit {a b : Site} (h : IsUnit (b - a)) : squareGraph.Adj a b := adj_of_unit h

/-! ### After a forced open test -/

open Classical in
theorem after_forced_open {s : ExplState} (hinv : ExplInv s) (hout : ExplOuter s)
    (hcov : ∀ x ∈ s.visited, ∀ y, squareGraph.Adj x y →
      y ∈ s.visited ∨ InFiniteComponent s.visited y ∨ (x, y) ∈ s.active ∨ (x, y, false) ∈ s.tested)
    {t w : Site} (he : s.active = [(t, w)]) (hW : TestedAs s.tested (sideW t w) false) :
    (explStepWith s true).active <+ [(w, w + rotR (w - t)), (w, w + (w - t))] ∧
    (w + rotL (w - t), w, false) ∈ s.tested ∧
    (explStepWith s true).visited = insert w s.visited ∧
    (explStepWith s true).tested = s.tested ++ [(t, w, true)] ∧
    (explStepWith s true).forced = s.forced + 1 := by
  have hmem : (t, w) ∈ s.active := by rw [he]; exact List.mem_cons_self
  have hadj : squareGraph.Adj t w := hinv.active_adj _ hmem
  have hu : IsUnit (w - t) := isUnit_of_adj hadj
  have hW' : (w + rotL (w - t), t + rotL (w - t), false) ∈ s.tested := by
    have := hW; unfold TestedAs at this; rwa [sideW_geom hadj] at this
  have hz : w + rotL (w - t) ∈ s.visited := hinv.tested_tail _ hW'
  have hadjz : squareGraph.Adj (w + rotL (w - t)) w := by
    apply adj_of_isUnit
    rw [show w - (w + rotL (w - t)) = -(rotL (w - t)) by abel]
    exact isUnit_neg (isUnit_rotL hu)
  have hclosed : (w + rotL (w - t), w, false) ∈ s.tested := by
    rcases hcov _ hz w hadjz with h1 | h1 | h1 | h1
    · exact absurd h1 (hinv.active_head _ hmem)
    · exact absurd h1 (hout _ hmem)
    · exfalso
      rw [he, List.mem_singleton, Prod.mk.injEq] at h1
      apply rotL_ne_neg hu
      have : w + rotL (w - t) = w + -(w - t) := by rw [h1.1]; abel
      exact add_left_cancel this
    · exact h1
  refine ⟨?_, hclosed, ?_, ?_, ?_⟩
  · rw [explStepWith_cons he]
    simp only [if_true, List.append_nil, continuations_eq]
    have hzin : w + rotL (w - t) ∈ insert w s.visited := Finset.mem_insert_of_mem hz
    set P : Site × Site → Bool := fun g =>
      decide ¬(g.2 ∈ insert w s.visited ∨ InFiniteComponent (insert w s.visited) g.2) with hP
    have hl : P (w, w + rotL (w - t)) = false := by
      rw [hP]
      simp only [decide_eq_false_iff_not, not_not]
      exact Or.inl hzin
    have key : ∀ (e f l : Site × Site), P l = false → List.filter P [e, f, l] <+ [e, f] := by
      intro e f l hl
      rw [show [e, f, l] = [e, f] ++ [l] from rfl, List.filter_append,
        show List.filter P [l] = [] by simp [hl], List.append_nil]
      exact List.filter_sublist
    exact key _ _ _ hl
  · rw [explStepWith_cons he]; simp
  · rw [explStepWith_cons he]
  · rw [explStepWith_cons he]
    simp only
    rw [if_pos hW]

theorem sublist_pair {α : Type*} {a b : α} {l : List α} (h : l <+ [a, b]) :
    l = [] ∨ l = [a] ∨ l = [b] ∨ l = [a, b] := by
  rw [List.sublist_cons_iff] at h
  rcases h with h | ⟨r, rfl, hr⟩
  · rw [List.sublist_cons_iff] at h
    rcases h with h | ⟨r, rfl, hr⟩
    · left; exact List.sublist_nil.1 h
    · rw [List.sublist_nil] at hr; subst hr; right; right; left; rfl
  · rw [List.sublist_cons_iff] at hr
    rcases hr with hr | ⟨r', rfl, hr'⟩
    · rw [List.sublist_nil] at hr; subst hr; right; left; rfl
    · rw [List.sublist_nil] at hr'; subst hr'; right; right; right; rfl

/-! ### A stage of the cascade -/

/-- The history `h₀` ends with the sole active edge `(t, w)` about to be tested, forced. -/
structure Stage (f d : Site) (h₀ : List Bool) (t w : Site) : Prop where
  active : (replay f d h₀).active = [(t, w)]
  forced : TestedAs (replay f d h₀).tested (sideW t w) false
  pos : Pm f d h₀ ≠ 0

theorem visited_mono_replay (f d : Site) (h : List Bool) (o : Bool) :
    (replay f d h).visited ⊆ (replay f d (h ++ [o])).visited := by
  rw [replay_append]; exact visited_subset_step _ _

section Cascade

variable {f d : Site} (hd : squareGraph.Adj f (f + d))
include hd

theorem hdu : IsUnit d := by
  have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this

/-- The facts available at a history with positive probability. -/
theorem state_facts {h : List Bool} (hpos : Pm f d h ≠ 0) :
    ExplInv (replay f d h) ∧ ExplOuter (replay f d h) ∧
    (∀ x ∈ (replay f d h).visited, ∀ y, squareGraph.Adj x y →
      y ∈ (replay f d h).visited ∨ InFiniteComponent (replay f d h).visited y ∨
      (x, y) ∈ (replay f d h).active ∨ (x, y, false) ∈ (replay f d h).tested) ∧
    (∀ (e : Site × Site) (rest : List (Site × Site)), (replay f d h).active = e :: rest →
      ((TestedAs (replay f d h).tested (sideW e.1 e.2) false ∨
          TestedAs (replay f d h).tested (sideS e.1 e.2) false) → rest = []) ∧
      ¬ (TestedAs (replay f d h).tested (sideW e.1 e.2) false ∧
          TestedAs (replay f d h).tested (sideS e.1 e.2) false)) := by
  obtain ⟨ρ, -, hex⟩ := Pm_pos_config f d hpos
  refine ⟨explInv_replay f (hdu hd) h, ?_, ?_, ?_⟩
  · have := explOuter_explore ρ f (hdu hd) h.length
    rwa [hex] at this
  · have := (explCov_explore ρ f (hdu hd) h.length).cover
    rwa [hex] at this
  · intro e rest he
    have := square_active_list_proof f d hd ρ h.length e rest (by rw [hex]; exact he)
    rwa [hex] at this

/-- A closed nonforced test of the sole active edge terminates the exploration. -/
theorem close_sole {h : List Bool} {e : Site × Site} (he : (replay f d h).active = [e])
    (hW : ¬ TestedAs (replay f d h).tested (sideW e.1 e.2) false) :
    (replay f d (h ++ [false])).active = [] ∧
    (replay f d (h ++ [false])).forced = (replay f d h).forced ∧
    Pm f d h ≤ 2 * Pm f d (h ++ [false]) := by
  refine ⟨?_, ?_, Pm_nonforced f d hd h he hW⟩
  · rw [replay_append, explStepWith_cons he]; simp
  · rw [forced_append_cons f d h he, if_neg hW]

theorem stage_analysis {h₀ : List Bool} {t w : Site} (st : Stage f d h₀ t w) :
    (∃ h', (h₀ ++ [true]) <+: h' ∧ (replay f d h').active = [] ∧
        (replay f d h').forced = (replay f d (h₀ ++ [true])).forced ∧
        Pm f d (h₀ ++ [true]) ≤ 4 * Pm f d h') ∨
    (Stage f d (h₀ ++ [true]) w (w + rotR (w - t)) ∧
      (replay f d (h₀ ++ [true])).active = [(w, w + rotR (w - t))]) := by
  obtain ⟨hinv₀, hout₀, hcov₀, -⟩ := state_facts hd st.pos
  obtain ⟨hsub, hz, hvis, htest, hforced⟩ := after_forced_open hinv₀ hout₀ hcov₀ st.active st.forced
  rw [← replay_append] at hsub hvis htest hforced
  have hPm : Pm f d (h₀ ++ [true]) = Pm f d h₀ := (Pm_forced f d hd h₀ st.active st.forced).1
  have hpos : Pm f d (h₀ ++ [true]) ≠ 0 := by rw [hPm]; exact st.pos
  obtain ⟨hinv₁, hout₁, -, hL55⟩ := state_facts hd hpos
  have hadj : squareGraph.Adj t w := hinv₀.active_adj _ (by rw [st.active]; exact List.mem_cons_self)
  have hu : IsUnit (w - t) := isUnit_of_adj hadj
  have hadjf : squareGraph.Adj w (w + (w - t)) := adj_of_isUnit (by rwa [add_sub_cancel_left])
  have hSclosed : TestedAs (replay f d (h₀ ++ [true])).tested (sideS w (w + (w - t))) false := by
    unfold TestedAs
    rw [sideS_geom hadjf, add_sub_cancel_left, htest]
    exact List.mem_append_left _ hz
  rcases sublist_pair hsub with hact | hact | hact | hact
  · left
    exact ⟨h₀ ++ [true], List.prefix_refl _, hact, rfl,
      le_mul_of_one_le_left (zero_le _) (by norm_num)⟩
  · -- only the right turn
    by_cases hWe : TestedAs (replay f d (h₀ ++ [true])).tested
        (sideW (w, w + rotR (w - t)).1 (w, w + rotR (w - t)).2) false
    · right
      exact ⟨⟨hact, hWe, hpos⟩, hact⟩
    · left
      obtain ⟨h1, h2, h3⟩ := close_sole hd hact hWe
      exact ⟨h₀ ++ [true] ++ [false], List.prefix_append _ _, h1, h2,
        h3.trans (by gcongr; norm_num)⟩
  · -- only the straight edge
    left
    have hWf : ¬ TestedAs (replay f d (h₀ ++ [true])).tested
        (sideW (w, w + (w - t)).1 (w, w + (w - t)).2) false := fun hWf =>
      (hL55 _ _ hact).2 ⟨hWf, hSclosed⟩
    obtain ⟨h1, h2, h3⟩ := close_sole hd hact hWf
    exact ⟨h₀ ++ [true] ++ [false], List.prefix_append _ _, h1, h2,
      h3.trans (by gcongr; norm_num)⟩
  · -- both
    by_cases hWe : TestedAs (replay f d (h₀ ++ [true])).tested
        (sideW (w, w + rotR (w - t)).1 (w, w + rotR (w - t)).2) false
    · exfalso
      have := (hL55 _ _ hact).1 (Or.inl hWe)
      exact List.cons_ne_nil _ _ this
    · left
      -- the right turn closes, then the straight edge closes
      have hstep1 : (replay f d (h₀ ++ [true] ++ [false])).active = [(w, w + (w - t))] := by
        rw [replay_append, explStepWith_cons hact]
        simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
        rw [List.filter_eq_self.2 (fun g hg => by
          simp only [decide_eq_true_eq, not_or]
          have hg' : g ∈ (replay f d (h₀ ++ [true])).active := by
            rw [hact]; exact List.mem_cons_of_mem _ hg
          exact ⟨hinv₁.active_head g hg', hout₁ g hg'⟩)]
      have hf1 : (replay f d (h₀ ++ [true] ++ [false])).forced =
          (replay f d (h₀ ++ [true])).forced := by
        rw [forced_append_cons f d _ hact, if_neg hWe]
      have hP1 : Pm f d (h₀ ++ [true]) ≤ 2 * Pm f d (h₀ ++ [true] ++ [false]) :=
        Pm_nonforced f d hd _ hact hWe
      have hpos1 : Pm f d (h₀ ++ [true] ++ [false]) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hP1; exact hpos (le_antisymm hP1 (zero_le _))
      obtain ⟨-, -, -, hL55'⟩ := state_facts hd hpos1
      have hSclosed' : TestedAs (replay f d (h₀ ++ [true] ++ [false])).tested
          (sideS w (w + (w - t))) false := by
        unfold TestedAs at hSclosed ⊢
        rw [replay_append, explStepWith_cons hact]
        exact List.mem_append_left _ hSclosed
      have hWf : ¬ TestedAs (replay f d (h₀ ++ [true] ++ [false])).tested
          (sideW (w, w + (w - t)).1 (w, w + (w - t)).2) false := fun hWf =>
        (hL55' _ _ hstep1).2 ⟨hWf, hSclosed'⟩
      obtain ⟨h1, h2, h3⟩ := close_sole hd hstep1 hWf
      refine ⟨h₀ ++ [true] ++ [false] ++ [false], ?_, h1, by rw [h2, hf1], ?_⟩
      · exact (List.prefix_append _ _).trans (List.prefix_append _ _)
      · calc Pm f d (h₀ ++ [true]) ≤ 2 * Pm f d (h₀ ++ [true] ++ [false]) := hP1
          _ ≤ 2 * (2 * Pm f d (h₀ ++ [true] ++ [false] ++ [false])) := by gcongr
          _ = 4 * Pm f d (h₀ ++ [true] ++ [false] ++ [false]) := by rw [← mul_assoc]; norm_num

/-- After three consecutive forced right turns the right turn closes the square. -/
theorem stage_third {h₀ : List Bool} {t w : Site} (st₀ : Stage f d h₀ t w)
    (st₁ : Stage f d (h₀ ++ [true]) w (w + rotR (w - t)))
    (st₂ : Stage f d (h₀ ++ [true] ++ [true]) (w + rotR (w - t))
      (w + rotR (w - t) + rotR (w + rotR (w - t) - w))) :
    ∃ h', (h₀ ++ [true] ++ [true] ++ [true]) <+: h' ∧ (replay f d h').active = [] ∧
      (replay f d h').forced = (replay f d (h₀ ++ [true] ++ [true] ++ [true])).forced ∧
      Pm f d (h₀ ++ [true] ++ [true] ++ [true]) ≤ 4 * Pm f d h' := by
  rcases stage_analysis hd st₂ with h | ⟨-, hact⟩
  · exact h
  · exfalso
    have hinv₀ := explInv_replay f (hdu hd) h₀
    have ht : t ∈ (replay f d h₀).visited :=
      hinv₀.active_tail _ (by rw [st₀.active]; exact List.mem_cons_self)
    have ht3 : t ∈ (replay f d (h₀ ++ [true] ++ [true] ++ [true])).visited :=
      visited_mono_replay f d _ _ (visited_mono_replay f d _ _ (visited_mono_replay f d _ _ ht))
    have hinv₃ := explInv_replay f (hdu hd) (h₀ ++ [true] ++ [true] ++ [true])
    have hhead := hinv₃.active_head _ (by rw [hact]; exact List.mem_cons_self)
    apply hhead
    simp only
    have : w + rotR (w - t) + rotR (w + rotR (w - t) - w) +
        rotR (w + rotR (w - t) + rotR (w + rotR (w - t) - w) - (w + rotR (w - t))) = t := by
      rw [show w + rotR (w - t) - w = rotR (w - t) by abel,
        show w + rotR (w - t) + rotR (rotR (w - t)) - (w + rotR (w - t)) = rotR (rotR (w - t))
          by abel, rotR_rotR]
      have : rotR (-(w - t)) = -rotR (w - t) := by
        obtain ⟨a, b⟩ := w; obtain ⟨c, e⟩ := t; simp [rotR]
      rw [this]; abel
    rw [this]; exact ht3

theorem cascade {h₀ : List Bool} {t w : Site} (st : Stage f d h₀ t w) :
    ∃ h', (h₀ ++ [true]) <+: h' ∧ (replay f d h').active = [] ∧
      (replay f d h').forced < (replay f d (h₀ ++ [true])).forced + 3 ∧
      Pm f d (h₀ ++ [true]) ≤ 4 * Pm f d h' := by
  rcases stage_analysis hd st with ⟨h', hp, hs, hf, hPm⟩ | ⟨st₁, -⟩
  · exact ⟨h', hp, hs, by omega, hPm⟩
  have hf1 : (replay f d (h₀ ++ [true] ++ [true])).forced =
      (replay f d (h₀ ++ [true])).forced + 1 := by
    rw [forced_append_cons f d _ st₁.active, if_pos st₁.forced]
  have hP1 : Pm f d (h₀ ++ [true] ++ [true]) = Pm f d (h₀ ++ [true]) :=
    (Pm_forced f d hd _ st₁.active st₁.forced).1
  rcases stage_analysis hd st₁ with ⟨h', hp, hs, hf, hPm⟩ | ⟨st₂, -⟩
  · exact ⟨h', (List.prefix_append _ _).trans hp, hs, by omega, by rw [← hP1]; exact hPm⟩
  have hf2 : (replay f d (h₀ ++ [true] ++ [true] ++ [true])).forced =
      (replay f d (h₀ ++ [true] ++ [true])).forced + 1 := by
    rw [forced_append_cons f d _ st₂.active, if_pos st₂.forced]
  have hP2 : Pm f d (h₀ ++ [true] ++ [true] ++ [true]) = Pm f d (h₀ ++ [true] ++ [true]) :=
    (Pm_forced f d hd _ st₂.active st₂.forced).1
  obtain ⟨h', hp, hs, hf, hPm⟩ := stage_third hd st st₁ st₂
  exact ⟨h', ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans hp, hs, by omega,
    by rw [← hP1, ← hP2]; exact hPm⟩

/-- The bound for one minimal history: after the `N`-th forced test, three more occur with
conditional probability at most `3/4`. -/
theorem minF_bound {N : ℕ} (hN : 1 ≤ N) {h : List Bool} (hm : MinF f d N h) :
    4 * uniformLaw clockwise ({ρ | history ρ f d h.length = h} ∩
      {ρ | ((N + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) ≤ 3 * Pm f d h := by
  by_cases hpos : Pm f d h = 0
  · calc 4 * uniformLaw clockwise ({ρ | history ρ f d h.length = h} ∩
          {ρ | ((N + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) ≤ 4 * Pm f d h := by
          gcongr; exact measure_mono Set.inter_subset_left
      _ = 0 := by rw [hpos, mul_zero]
      _ ≤ 3 * Pm f d h := zero_le _
  rcases List.eq_nil_or_concat h with rfl | ⟨h₀, o, rfl⟩
  · exfalso
    have := hm.1
    simp [replay, explInit] at this
    omega
  rw [List.concat_eq_append] at hm hpos ⊢
  have hprev : (replay f d h₀).forced < N := by
    have := hm.2 h₀.length (by simp)
    rwa [List.take_left' rfl] at this
  have hN' := hm.1
  rcases hact : (replay f d h₀).active with _ | ⟨g, rest⟩
  · exfalso
    rw [forced_append_nil f d h₀ hact] at hN'
    omega
  have hforced : TestedAs (replay f d h₀).tested (sideW g.1 g.2) false := by
    by_contra hnf
    rw [forced_append_cons f d h₀ hact, if_neg hnf] at hN'
    omega
  have ho : o = true := by
    rcases o with _ | _
    · exfalso
      exact hpos (Pm_forced f d hd h₀ hact hforced).2
    · rfl
  subst ho
  have hpos₀ : Pm f d h₀ ≠ 0 := fun h0 => hpos (le_antisymm
    ((Pm_append_le f d h₀ true).trans (le_of_eq h0)) (zero_le _))
  obtain ⟨-, -, -, hL55⟩ := state_facts hd hpos₀
  have hrest : rest = [] := (hL55 g rest hact).1 (Or.inl hforced)
  subst hrest
  have st : Stage f d h₀ g.1 g.2 := ⟨by rw [hact], hforced, hpos₀⟩
  obtain ⟨h', hp, hs, hf, hPm⟩ := cascade hd st
  have hesc := escape f (hdu hd) hp hs (N := N + 3) (by rw [hN'] at hf; exact hf)
  have h4 : 4 * uniformLaw clockwise ({ρ | history ρ f d (h₀ ++ [true]).length = h₀ ++ [true]} ∩
      {ρ | ((N + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) + Pm f d (h₀ ++ [true]) ≤
      3 * Pm f d (h₀ ++ [true]) + Pm f d (h₀ ++ [true]) := by
    calc _ ≤ 4 * uniformLaw clockwise ({ρ | history ρ f d (h₀ ++ [true]).length = h₀ ++ [true]} ∩
          {ρ | ((N + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) + 4 * Pm f d h' := by gcongr
      _ = 4 * (uniformLaw clockwise ({ρ | history ρ f d (h₀ ++ [true]).length = h₀ ++ [true]} ∩
          {ρ | ((N + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) + Pm f d h') := by rw [mul_add]
      _ ≤ 4 * Pm f d (h₀ ++ [true]) := by gcongr
      _ = 3 * Pm f d (h₀ ++ [true]) + Pm f d (h₀ ++ [true]) := by
          rw [show (4 : ℝ≥0∞) = 3 + 1 by norm_num, add_mul, one_mul]
  exact ENNReal.le_of_add_le_add_right (Pm_ne_top f d _) h4

theorem K_step {N : ℕ} (hN : 1 ≤ N) :
    4 * uniformLaw clockwise {ρ | ((N + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d} ≤
      3 * uniformLaw clockwise {ρ | (N : ℕ∞) ≤ forcedCount ρ f d} := by
  rw [K_measure_step f (hdu hd) hN (N + 3) (by omega), K_measure_eq f (hdu hd) hN,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun h => minF_bound hd hN h.2)

theorem K_bound : ∀ k : ℕ,
    uniformLaw clockwise {ρ | ((3 * k + 1 : ℕ) : ℕ∞) ≤ forcedCount ρ f d} ≤ (3 / 4 : ℝ≥0∞) ^ k
  | 0 => by rw [pow_zero]; exact prob_le_one
  | k + 1 => by
    have h1 := K_step hd (N := 3 * k + 1) (by omega)
    have ih := K_bound k
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by ring, pow_succ]
    have h2 : uniformLaw clockwise {ρ | ((3 * k + 1 + 3 : ℕ) : ℕ∞) ≤ forcedCount ρ f d} ≤
        (3 * uniformLaw clockwise {ρ | ((3 * k + 1 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) / 4 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
      exact h1
    calc _ ≤ (3 * uniformLaw clockwise {ρ | ((3 * k + 1 : ℕ) : ℕ∞) ≤ forcedCount ρ f d}) / 4 := h2
      _ ≤ (3 * (3 / 4 : ℝ≥0∞) ^ k) / 4 := by gcongr
      _ = (3 / 4 : ℝ≥0∞) ^ k * (3 / 4) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (3 : ℝ≥0∞), mul_assoc]

end Cascade

/-! ### Lemma 5.6 -/

theorem square_forced_tests_proof (f d : Site) (hd : squareGraph.Adj f (f + d)) :
    ∀ m : ℕ, 1 ≤ m →
      uniformLaw clockwise {ρ | (m : ℕ∞) ≤ forcedCount ρ f d} ≤
        ENNReal.ofReal ((4 / 3) * (3 / 4) ^ ((m : ℝ) / 3)) := by
  intro m hm
  set k := (m - 1) / 3 with hk
  have h1 : 3 * k + 1 ≤ m := by omega
  have h2 : m ≤ 3 * k + 3 := by omega
  calc uniformLaw clockwise {ρ | (m : ℕ∞) ≤ forcedCount ρ f d}
      ≤ uniformLaw clockwise {ρ | ((3 * k + 1 : ℕ) : ℕ∞) ≤ forcedCount ρ f d} :=
        measure_mono (fun ρ hρ => by
          simp only [Set.mem_setOf_eq] at hρ ⊢
          exact le_trans (by exact_mod_cast h1) hρ)
    _ ≤ (3 / 4 : ℝ≥0∞) ^ k := K_bound hd k
    _ = ENNReal.ofReal ((3 / 4 : ℝ) ^ k) := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal ((4 / 3) * (3 / 4) ^ ((m : ℝ) / 3)) := by
        apply ENNReal.ofReal_le_ofReal
        have hb0 : (0 : ℝ) < 3 / 4 := by norm_num
        have hb1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
        have hexp : (m : ℝ) / 3 - 1 ≤ (k : ℝ) := by
          have : (m : ℝ) ≤ 3 * k + 3 := by exact_mod_cast h2
          linarith
        calc (3 / 4 : ℝ) ^ k = (3 / 4 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
          _ ≤ (3 / 4 : ℝ) ^ ((m : ℝ) / 3 - 1) := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hexp
          _ = (3 / 4 : ℝ) ^ ((m : ℝ) / 3) / (3 / 4) ^ (1 : ℝ) := Real.rpow_sub hb0 _ _
          _ = (4 / 3) * (3 / 4) ^ ((m : ℝ) / 3) := by
              rw [Real.rpow_one]; ring


end Rotor

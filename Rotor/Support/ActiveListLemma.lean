import Rotor.Support.ContourCases

/-!
# The active-list proof term for Lemma 5.5

Lemma 5.5 (`lem:square-active-list`), part 4: the second assertion (at most one of `W`, `S`
was tested closed, by relabelling the square at the earlier test of `S`) and the proof term
`square_active_list_proof` for the frozen statement.
-/

open Finset List Fin.NatCast

namespace Rotor

/-! ### The second assertion: at most one of `W` and `S` was tested closed -/

/-- Relabelling the square with `S` as the current edge: the old `W` is its `S`-side. -/
theorem sideS_sideS (a b : Site) :
    sideS (sideS a b).1 (sideS a b).2 = sideW a b := by
  rw [sideS_eq a b, sideW_eq a b]
  unfold dualEdge
  simp only
  rw [sideS_eq, primalTail_dual, primalDir_dual]
  unfold dualEdge
  rw [add_assoc]
  rfl

/-- The set of visited vertices only grows as the exploration proceeds: `m ≤ n` implies the
`visited` set at stage `m` is contained in the `visited` set at stage `n`. -/
theorem visited_mono (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (h : m ≤ n) :
    (explore ρ f d m).visited ⊆ (explore ρ f d n).visited := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact subset_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · refine (ih (by omega)).trans ?_
      rcases hs : (explore ρ f d n).active with _ | ⟨e, rest⟩
      · rw [explore_succ, explStep_nil ρ hs]
      · rw [explore_succ, explStep_cons ρ hs]
        exact visited_subset_step _ _
    · have : m = n + 1 := by omega
      subst this; exact subset_rfl

open Classical in
/-- One exploration step only appends to the `tested` list: it either stays the same (when
`active` is empty) or gains the single new test result for the current edge. -/
theorem tested_succ (ρ : Config squareGraph) (f d : Site) (n : ℕ) :
    ∃ t, (explore ρ f d (n + 1)).tested = (explore ρ f d n).tested ++ t := by
  rcases hs : (explore ρ f d n).active with _ | ⟨e, rest⟩
  · exact ⟨[], by rw [explore_succ, explStep_nil ρ hs, List.append_nil]⟩
  · exact ⟨[(e.1, e.2, decide (DualOpen ρ e.1 e.2))],
      by rw [explore_succ, explStep_cons ρ hs, explStepWith_cons hs]⟩

/-- Every edge recorded in `tested` at stage `m` is still recorded at any later stage `n ≥ m`,
by repeated application of `tested_succ`. -/
theorem tested_mono (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (h : m ≤ n) :
    ∀ t ∈ (explore ρ f d m).tested, t ∈ (explore ρ f d n).tested := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact fun t ht => ht
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · intro t ht
      obtain ⟨t', ht'⟩ := tested_succ ρ f d n
      rw [ht']
      exact List.mem_append_left _ (ih (by omega) t ht)
    · have : m = n + 1 := by omega
      subst this; exact fun t ht => ht

open Classical in
/-- The stage at which a tested edge was the current edge. -/
theorem exists_test_stage (ρ : Config squareGraph) (f d : Site) (n : ℕ) {t : Site × Site × Bool}
    (ht : t ∈ (explore ρ f d n).tested) :
    ∃ m < n, ∃ rest, (explore ρ f d m).active = (t.1, t.2.1) :: rest ∧
      explore ρ f d (m + 1) = explStepWith (explore ρ f d m) t.2.2 := by
  induction n with
  | zero => simp [explore_zero, explInit] at ht
  | succ n ih =>
    rcases hs : (explore ρ f d n).active with _ | ⟨e, rest⟩
    · rw [explore_succ, explStep_nil ρ hs] at ht
      obtain ⟨m, hm, rest, h1, h2⟩ := ih ht
      exact ⟨m, by omega, rest, h1, h2⟩
    · rw [explore_succ, explStep_cons ρ hs, explStepWith_cons hs] at ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · obtain ⟨m, hm, rest', h1, h2⟩ := ih ht
        exact ⟨m, by omega, rest', h1, h2⟩
      · refine ⟨n, by omega, rest, hs, ?_⟩
        rw [explore_succ, explStep_cons ρ hs]

/-- If the current active edge `e` at stage `n` has had both its `W`-side and its `S`-side tested
closed, this is contradictory: locating the earlier stages `m' < m` at which each side was tested
(via `exists_test_stage`), relabelling by `sideS_sideS` turns the `S`-side test at `m` into a
`W`-side-closed test for the relabelled square, forcing (via `active_list_S`) the active list at
`m` to become empty one step later, contradicting that `e` is still active at stage `n ≥ m`. -/
theorem not_both (f : Site) {d : Site} (hd : IsUnit d) (ρ : Config squareGraph) (n : ℕ)
    {e : Site × Site} {rest : List (Site × Site)} (he : (explore ρ f d n).active = e :: rest)
    (hW : TestedAs (explore ρ f d n).tested (sideW e.1 e.2) false)
    (hS : TestedAs (explore ρ f d n).tested (sideS e.1 e.2) false) : False := by
  have hinv := explInv_explore ρ f hd n
  have hadjE : squareGraph.Adj e.1 e.2 :=
    hinv.active_adj e (by rw [he]; exact List.mem_cons_self)
  obtain ⟨m, hmn, restS, hmS, hstepS⟩ := exists_test_stage ρ f d n hS
  obtain ⟨m', hm'n, restW, hmW, hstepW⟩ := exists_test_stage ρ f d n hW
  have hSWeq : (sideW e.1 e.2).2 = (sideS e.1 e.2).1 := by rw [sideW_snd, sideS_fst]
  have hinvm := explInv_explore ρ f hd m
  have hinvm' := explInv_explore ρ f hd m'
  have hSWvis : (sideS e.1 e.2).1 ∈ (explore ρ f d m).visited :=
    hinvm.active_tail _ (by rw [hmS]; exact List.mem_cons_self)
  have hSWnot : (sideW e.1 e.2).2 ∉ (explore ρ f d m').visited :=
    hinvm'.active_head _ (by rw [hmW]; exact List.mem_cons_self)
  have hlt : m' < m := by
    by_contra h
    push Not at h
    exact hSWnot (hSWeq ▸ visited_mono ρ f d h hSWvis)
  have hWm : TestedAs (explore ρ f d m).tested (sideW e.1 e.2) false := by
    have h1 : ((sideW e.1 e.2).1, (sideW e.1 e.2).2, false) ∈ (explore ρ f d (m' + 1)).tested := by
      rw [hstepW, explStepWith_cons hmW]
      simp
    exact tested_mono ρ f d (by omega : m' + 1 ≤ m) _ h1
  have hSS := sideS_sideS e.1 e.2
  have hrest : restS = [] := active_list_S f hd ρ m hmS (by
    show TestedAs _ (sideS (sideS e.1 e.2).1 (sideS e.1 e.2).2) false
    rw [hSS]; exact hWm)
  subst hrest
  have hnil : (explore ρ f d (m + 1)).active = [] := by
    rw [hstepS, explStepWith_cons hmS]
    simp
  have := active_nil_of_le ρ f d (by omega : m + 1 ≤ n) hnil
  rw [he] at this
  exact List.cons_ne_nil _ _ this

/-! ### Lemma 5.5 -/

/-- The proof term for Lemma 5.5's active-list statement: if the current active edge `e` has had
its `W`-side or its `S`-side tested closed then it is the sole remaining active edge (via
`active_list_W` or `active_list_S`), and it cannot have had both sides tested closed
(`not_both`). -/
theorem square_active_list_proof (f d : Site) (hd : squareGraph.Adj f (f + d))
    (ρ : Config squareGraph) (n : ℕ) (e : Site × Site) (rest : List (Site × Site))
    (he : (explore ρ f d n).active = e :: rest) :
    ((TestedAs (explore ρ f d n).tested (sideW e.1 e.2) false ∨
        TestedAs (explore ρ f d n).tested (sideS e.1 e.2) false) → rest = []) ∧
    ¬ (TestedAs (explore ρ f d n).tested (sideW e.1 e.2) false ∧
        TestedAs (explore ρ f d n).tested (sideS e.1 e.2) false) := by
  have hd' : IsUnit d := by have := isUnit_of_adj hd; simpa using this
  refine ⟨fun h => ?_, fun ⟨hW, hS⟩ => not_both f hd' ρ n he hW hS⟩
  rcases h with hW | hS
  · exact active_list_W f hd' ρ n he hW
  · exact active_list_S f hd' ρ n he hS


end Rotor

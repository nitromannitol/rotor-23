import Rotor.Support.DualGeom

/-!
Invariants of the depth-first exploration (`rotor.tex:1885-1913`): tails of tested and active
edges are visited, heads of active edges are unvisited, the active list has no repeated edge,
no active bond has been tested, and no bond is tested twice (Lemma 5.4 (i)).  Also the
bookkeeping of ruling M-021: `explore ρ f d n = replay f d (history ρ f d n)`.
-/

open Finset

namespace Rotor

/-- The invariant of the exploration states. -/
structure ExplInv (s : ExplState) : Prop where
  tested_tail : ∀ t ∈ s.tested, t.1 ∈ s.visited
  tested_adj : ∀ t ∈ s.tested, squareGraph.Adj t.1 t.2.1
  active_tail : ∀ e ∈ s.active, e.1 ∈ s.visited
  active_head : ∀ e ∈ s.active, e.2 ∉ s.visited
  active_adj : ∀ e ∈ s.active, squareGraph.Adj e.1 e.2
  active_nodup : s.active.Nodup
  active_tested : ∀ e ∈ s.active, ∀ t ∈ s.tested, bond e ≠ bond (t.1, t.2.1)
  tested_nodup : (s.tested.map (fun t => bond (t.1, t.2.1))).Nodup

theorem explInv_init (f : Site) {d : Site} (hd : IsUnit d) : ExplInv (explInit f d) where
  tested_tail := by simp [explInit]
  tested_adj := by simp [explInit]
  active_tail := fun e he => by
    simp only [explInit, mem_singleton]
    exact edgesFrom_tail f d e he
  active_head := fun e he => by
    simp only [explInit, mem_singleton]
    have h1 := edgesFrom_tail f d e he
    have h2 := edgesFrom_adj f hd e he
    rw [h1] at h2
    exact h2.ne.symm
  active_adj := fun e he => edgesFrom_adj f hd e he
  active_nodup := edgesFrom_nodup f hd
  active_tested := by simp [explInit]
  tested_nodup := by simp [explInit]

theorem explStepWith_nil {s : ExplState} (h : s.active = []) (o : Bool) : explStepWith s o = s := by
  unfold explStepWith
  rw [h]

open Classical in
theorem explStepWith_cons {s : ExplState} {e : Site × Site} {rest : List (Site × Site)}
    (h : s.active = e :: rest) (o : Bool) :
    explStepWith s o =
      { visited := if o then insert e.2 s.visited else s.visited,
        active := ((if o then continuations e.1 e.2 else []) ++ rest).filter
          (fun g => decide (¬ (g.2 ∈ (if o then insert e.2 s.visited else s.visited) ∨
            InFiniteComponent (if o then insert e.2 s.visited else s.visited) g.2))),
        tested := s.tested ++ [(e.1, e.2, o)],
        forced := if TestedAs s.tested (sideW e.1 e.2) false then s.forced + 1 else s.forced } := by
  unfold explStepWith
  rw [h]

theorem visited_subset_step (s : ExplState) (o : Bool) : s.visited ⊆ (explStepWith s o).visited := by
  rcases h : s.active with _ | ⟨e, rest⟩
  · rw [explStepWith_nil h]
  · rw [explStepWith_cons h]
    dsimp only
    split_ifs
    · exact subset_insert _ _
    · exact subset_rfl

theorem explInv_step {s : ExplState} (hs : ExplInv s) (o : Bool) : ExplInv (explStepWith s o) := by
  rcases h : s.active with _ | ⟨e, rest⟩
  · rw [explStepWith_nil h]; exact hs
  rw [explStepWith_cons h]
  have he : e ∈ s.active := by rw [h]; exact List.mem_cons_self
  have hrest : ∀ g ∈ rest, g ∈ s.active := fun g hg => by rw [h]; exact List.mem_cons_of_mem _ hg
  have hadj : squareGraph.Adj e.1 e.2 := hs.active_adj e he
  have he2 : e.2 ∉ s.visited := hs.active_head e he
  set visited' := if o then insert e.2 s.visited else s.visited with hv'
  have hsub : s.visited ⊆ visited' := by
    rw [hv']; split_ifs
    · exact subset_insert _ _
    · exact subset_rfl
  have he2' : e.2 ∈ visited' ∨ o = false := by
    rw [hv']; cases o <;> simp
  set added := if o then continuations e.1 e.2 else [] with hadded
  have hadded_tail : ∀ g ∈ added, g.1 = e.2 := by
    rw [hadded]; split_ifs
    · exact continuations_tail e.1 e.2
    · simp
  have hadded_adj : ∀ g ∈ added, squareGraph.Adj g.1 g.2 := by
    rw [hadded]; split_ifs
    · exact continuations_adj hadj
    · simp
  have hadded_ne : ∀ g ∈ added, g.2 ≠ e.1 := by
    rw [hadded]; split_ifs
    · exact continuations_ne hadj
    · simp
  have hadded_nodup : added.Nodup := by
    rw [hadded]; split_ifs
    · exact continuations_nodup hadj
    · exact List.nodup_nil
  have hadded_vis : ∀ g ∈ added, g.1 ∈ visited' := by
    intro g hg
    rw [hadded_tail g hg, hv']
    have : o = true := by
      rw [hadded] at hg
      cases o
      · simp at hg
      · rfl
    rw [this]; simp
  have hrest_nodup : rest.Nodup := (List.nodup_cons.1 (h ▸ hs.active_nodup)).2
  have he_rest : e ∉ rest := (List.nodup_cons.1 (h ▸ hs.active_nodup)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact hsub (hs.tested_tail t ht)
    · rw [List.mem_singleton] at ht
      subst ht
      exact hsub (hs.active_tail e he)
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact hs.tested_adj t ht
    · rw [List.mem_singleton] at ht
      subst ht
      exact hadj
  · intro g hg
    rcases List.mem_append.1 (List.mem_of_mem_filter hg) with hg' | hg'
    · exact hadded_vis g hg'
    · exact hsub (hs.active_tail g (hrest g hg'))
  · intro g hg
    have := List.of_mem_filter hg
    simp only [decide_eq_true_eq, not_or] at this
    exact this.1
  · intro g hg
    rcases List.mem_append.1 (List.mem_of_mem_filter hg) with hg' | hg'
    · exact hadded_adj g hg'
    · exact hs.active_adj g (hrest g hg')
  · refine List.Nodup.filter _ (List.nodup_append.2 ⟨hadded_nodup, hrest_nodup, ?_⟩)
    intro g hg₁ g' hg₂ hgg'
    subst hgg'
    have h1 := hadded_tail g hg₁
    have h2 := hs.active_tail g (hrest g hg₂)
    rw [h1] at h2
    exact he2 h2
  · intro g hg t ht
    have hg2 : g.2 ∉ visited' := by
      have := List.of_mem_filter hg
      simp only [decide_eq_true_eq, not_or] at this
      exact this.1
    rcases List.mem_append.1 (List.mem_of_mem_filter hg) with hg' | hg'
    · -- `g` is a continuation
      have hg1 := hadded_tail g hg'
      rcases List.mem_append.1 ht with ht | ht
      · intro hb
        simp only [bond, Sym2.eq_iff] at hb
        rcases hb with ⟨h1, -⟩ | ⟨-, h2⟩
        · have : e.2 ∈ s.visited := by rw [← hg1, h1]; exact hs.tested_tail t ht
          exact he2 this
        · exact hg2 (hsub (by rw [h2]; exact hs.tested_tail t ht))
      · rw [List.mem_singleton] at ht
        subst ht
        intro hb
        simp only [bond, Sym2.eq_iff] at hb
        rcases hb with ⟨h1, -⟩ | ⟨-, h2⟩
        · rw [hg1] at h1
          exact hadj.ne h1.symm
        · exact hadded_ne g hg' h2
    · rcases List.mem_append.1 ht with ht | ht
      · exact hs.active_tested g (hrest g hg') t ht
      · rw [List.mem_singleton] at ht
        subst ht
        intro hb
        simp only [bond, Sym2.eq_iff] at hb
        rcases hb with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact he_rest (by rw [show g = e from Prod.ext h1 h2] at hg'; exact hg')
        · exact he2 (by rw [← h1]; exact hs.active_tail g (hrest g hg'))
  · rw [List.map_append, List.map_singleton]
    refine List.nodup_append.2 ⟨hs.tested_nodup, List.nodup_singleton _, ?_⟩
    intro b hb b' hb' hbb'
    rw [List.mem_singleton] at hb'
    subst hb'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    exact hs.active_tested e he t ht hbb'.symm

theorem explInv_replay (f : Site) {d : Site} (hd : IsUnit d) (h : List Bool) :
    ExplInv (replay f d h) := by
  unfold replay
  induction h using List.reverseRecOn with
  | nil => exact explInv_init f hd
  | append_singleton h o ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact explInv_step ih o

open Classical in
theorem explStep_eq (ρ : Config squareGraph) (s : ExplState) :
    explStep ρ s = match s.active with
      | [] => s
      | e :: _ => explStepWith s (decide (DualOpen ρ e.1 e.2)) := rfl

theorem explStep_nil (ρ : Config squareGraph) {s : ExplState} (h : s.active = []) :
    explStep ρ s = s := by
  rw [explStep_eq, h]

open Classical in
theorem explStep_cons (ρ : Config squareGraph) {s : ExplState} {e : Site × Site}
    {rest : List (Site × Site)} (h : s.active = e :: rest) :
    explStep ρ s = explStepWith s (decide (DualOpen ρ e.1 e.2)) := by
  rw [explStep_eq, h]

theorem explore_succ (ρ : Config squareGraph) (f d : Site) (n : ℕ) :
    explore ρ f d (n + 1) = explStep ρ (explore ρ f d n) := by
  unfold explore
  rw [Function.iterate_succ_apply']

theorem explore_zero (ρ : Config squareGraph) (f d : Site) : explore ρ f d 0 = explInit f d := rfl

theorem explInv_explore (ρ : Config squareGraph) (f : Site) {d : Site} (hd : IsUnit d) (n : ℕ) :
    ExplInv (explore ρ f d n) := by
  induction n with
  | zero => exact explInv_init f hd
  | succ n ih =>
    rw [explore_succ]
    rcases h : (explore ρ f d n).active with _ | ⟨e, rest⟩
    · rw [explStep_nil ρ h]; exact ih
    · rw [explStep_cons ρ h]; exact explInv_step ih _

/-- Lemma 5.4 (i): no bond is tested twice. -/
theorem tested_bonds_nodup (ρ : Config squareGraph) (f : Site) {d : Site} (hd : IsUnit d) (n : ℕ) :
    ((explore ρ f d n).tested.map (fun t => s(t.1, t.2.1))).Nodup :=
  (explInv_explore ρ f hd n).tested_nodup

/-! ### The history (ruling M-021) -/

theorem history_succ_nil (ρ : Config squareGraph) (f d : Site) (n : ℕ)
    (h : (explore ρ f d n).active = []) : history ρ f d (n + 1) = history ρ f d n := by
  unfold history
  rw [explore_succ, explStep_nil ρ h]

open Classical in
theorem history_succ_cons (ρ : Config squareGraph) (f d : Site) (n : ℕ) {e : Site × Site}
    {rest : List (Site × Site)} (h : (explore ρ f d n).active = e :: rest) :
    history ρ f d (n + 1) = history ρ f d n ++ [decide (DualOpen ρ e.1 e.2)] := by
  unfold history
  rw [explore_succ, explStep_cons ρ h, explStepWith_cons h]
  simp

theorem replay_append (f d : Site) (h : List Bool) (o : Bool) :
    replay f d (h ++ [o]) = explStepWith (replay f d h) o := by
  unfold replay
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `explore ρ f d n = replay f d (history ρ f d n)`. -/
theorem explore_eq_replay (ρ : Config squareGraph) (f d : Site) : ∀ n : ℕ,
    explore ρ f d n = replay f d (history ρ f d n)
  | 0 => rfl
  | n + 1 => by
    rcases h : (explore ρ f d n).active with _ | ⟨e, rest⟩
    · rw [history_succ_nil ρ f d n h, explore_succ, explStep_nil ρ h, explore_eq_replay ρ f d n]
    · rw [history_succ_cons ρ f d n h, replay_append, explore_succ, explStep_cons ρ h,
        explore_eq_replay ρ f d n]

theorem active_nil_succ (ρ : Config squareGraph) (f d : Site) (n : ℕ)
    (h : (explore ρ f d n).active = []) : (explore ρ f d (n + 1)).active = [] := by
  rw [explore_succ, explStep_nil ρ h, h]

theorem active_nil_of_le (ρ : Config squareGraph) (f d : Site) {m n : ℕ} (hmn : m ≤ n)
    (h : (explore ρ f d m).active = []) : (explore ρ f d n).active = [] := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact h
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact active_nil_succ ρ f d n (ih (by omega))
    · have : m = n + 1 := by omega
      subst this; exact h

theorem tested_length_succ_cons (ρ : Config squareGraph) (f d : Site) (n : ℕ) {e : Site × Site}
    {rest : List (Site × Site)} (h : (explore ρ f d n).active = e :: rest) :
    (explore ρ f d (n + 1)).tested.length = (explore ρ f d n).tested.length + 1 := by
  rw [explore_succ, explStep_cons ρ h, explStepWith_cons h]
  simp

theorem history_length_le (ρ : Config squareGraph) (f d : Site) : ∀ n : ℕ,
    (history ρ f d n).length ≤ n
  | 0 => by simp [history, explore_zero, explInit]
  | n + 1 => by
    rcases h : (explore ρ f d n).active with _ | ⟨e, rest⟩
    · rw [history_succ_nil ρ f d n h]
      exact (history_length_le ρ f d n).trans (Nat.le_succ n)
    · rw [history_succ_cons ρ f d n h, List.length_append, List.length_singleton]
      exact Nat.add_le_add_right (history_length_le ρ f d n) 1

theorem history_length_eq (ρ : Config squareGraph) (f d : Site) : ∀ n : ℕ,
    (explore ρ f d n).active ≠ [] → (history ρ f d n).length = n
  | 0, _ => by simp [history, explore_zero, explInit]
  | n + 1, hne => by
    rcases h : (explore ρ f d n).active with _ | ⟨e, rest⟩
    · exact absurd (active_nil_succ ρ f d n h) hne
    · rw [history_succ_cons ρ f d n h, List.length_append, List.length_singleton,
        history_length_eq ρ f d n (by rw [h]; exact List.cons_ne_nil _ _)]

end Rotor

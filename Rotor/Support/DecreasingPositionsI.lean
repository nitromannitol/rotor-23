/-
`lem:decreasing-positions` (i) (`rotor.tex:883-928`): a particle of a
one-particle-at-a-time boundary routing that visits `y` forces a live path
from `S` to `y`.

  "stop the routing at its first visit to `y`.  By Lemma boundary-routing no
   directed edge is traversed twice, so the edges traversed out of a vertex
   `v ∉ S` are an initial segment of the cyclic order beginning immediately
   after the initial rotor at `v`.  Consider the completed particle routes and
   the current route, counting the initial boundary edge of each.  Every
   completed route runs from `S` to `S`, while the current route runs from
   `S` to `y`.  Hence every vertex outside `S ∪ {y}` has as many incoming as
   outgoing traversals, while `y` has one more incoming than outgoing.
   Deleting every pair of oppositely directed traversals preserves this, so
   the surviving edges contain a path from `S` to `y`.  ... The traversed
   edges out of `x_i` form an initial segment of the cyclic order, so
   `x_i → x_{i+1}` precedes `x_i → x_{i-1}` in that order."
-/
import Rotor.Support.EulerPath
import Rotor.Support.Passage

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### The current route starts at the tracked particle -/

theorem route_head (S : Finset V) (ρ : Config G) (es : List (V × V)) (n : ℕ) (p : V)
    (h : (oneRouting π S ρ es n).tracked = some p) :
    (oneRouting π S ρ es n).route.head? = some p := by
  induction n with
  | zero => simp [oneRouting] at h
  | succ n ih =>
    rw [oneRouting, Function.iterate_succ', Function.comp_apply, ← oneRouting] at h ⊢
    set s := oneRouting π S ρ es n with hs
    cases htr : s.tracked with
    | some q =>
      by_cases hq : q ∈ S
      · simp [oneStep, htr, hq] at h
      · simp only [oneStep, htr, hq, if_false, Option.some.injEq] at h
        simp [oneStep, htr, hq, h]
    | none =>
      cases hqe : s.queue with
      | nil => simp [oneStep, htr, hqe] at h
      | cons e rest =>
        obtain ⟨t, x⟩ := e
        simp only [oneStep, htr, hqe, Option.some.injEq] at h
        simp [oneStep, htr, hqe, h]

/-- At the first stage whose route contains `y`, the tracked particle is at `y`. -/
theorem tracked_of_first_visit (S : Finset V) (ρ : Config G) (es : List (V × V)) (y : V)
    (n : ℕ) (hn : y ∈ (oneRouting π S ρ es n).route)
    (hmin : ∀ m < n, y ∉ (oneRouting π S ρ es m).route) :
    (oneRouting π S ρ es n).tracked = some y := by
  cases n with
  | zero => simp [oneRouting] at hn
  | succ n =>
    have hprev := hmin n (Nat.lt_succ_self n)
    rw [oneRouting, Function.iterate_succ', Function.comp_apply, ← oneRouting] at hn ⊢
    set s := oneRouting π S ρ es n with hs
    cases htr : s.tracked with
    | some q =>
      by_cases hq : q ∈ S
      · simp only [oneStep, htr, hq, if_true] at hn
        exact absurd hn hprev
      · simp only [oneStep, htr, hq, if_false, List.mem_cons] at hn
        rcases hn with rfl | hn
        · simp [oneStep, htr, hq]
        · exact absurd hn hprev
    | none =>
      cases hqe : s.queue with
      | nil =>
        simp only [oneStep, htr, hqe] at hn
        exact absurd hn hprev
      | cons e rest =>
        obtain ⟨t, x⟩ := e
        simp only [oneStep, htr, hqe, List.mem_singleton] at hn
        subst hn
        simp [oneStep, htr, hqe]

/-! ### The traversed edges and their degrees -/

/-- The edges traversed so far: the started boundary edges and the actuation
edges. -/
noncomputable def travSet (S : Finset V) (ρ : Config G) (pre : List (V × V)) (s : OneState G) :
    Finset (V × V) :=
  (pre ++ traversed π S (boundaryInit S ρ) s.acted.reverse).toFinset

/-- The `k`-th actuation of `v` traverses `v → (next v)^k (ρ v)`, for
`1 ≤ k ≤ count v vs`. -/
theorem mem_traversed_of_le_count (S : Finset V) (ξ : RState G) (vs : List V) (v : V) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ vs.count v) :
    (v, (((π.next v) ^ k) (ξ.ρ v)).1) ∈ traversed π S ξ vs := by
  induction vs generalizing ξ k with
  | nil => simp at hk; omega
  | cons w vs ih =>
    rw [traversed_cons, List.mem_cons]
    by_cases hwv : w = v
    · subst hwv
      rw [List.count_cons_self] at hk
      rcases Nat.lt_or_ge 1 k with h1 | h1
      · right
        have := ih (actuate π S ξ w) (k - 1) (by omega) (by omega)
        rw [actuate_ρ_self] at this
        convert this using 3
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
        congr 2
        omega
      · left
        have hk1' : k = 1 := by omega
        subst hk1'
        simp
    · right
      rw [List.count_cons_of_ne hwv] at hk
      have := ih (actuate π S ξ w) k hk1 hk
      rwa [actuate_ρ_of_ne π S ξ w v (Ne.symm hwv)] at this

/-! ### Degrees in the traversed set -/

theorem card_filter_toFinset {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup)
    (p : α → Prop) [DecidablePred p] :
    (L.toFinset.filter p).card = L.countP (fun a => decide (p a)) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext a
  simp

omit [DecidableEq V] in
/-- The started boundary edges have tails in `S` and are adjacent. -/
theorem pre_mem_boundary (S : Finset V) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (pre rest : List (V × V)) (hpre : pre ++ rest = es) (e : V × V) (he : e ∈ pre) :
    e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 :=
  (hes.2 e).1 (hpre ▸ List.mem_append_left rest he)

/-- The traversed list is duplicate-free. -/
theorem trav_nodup [G.LocallyFinite] (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) (pre : List (V × V))
    (hpre : pre ++ (oneRouting π S ρ es n).queue = es) :
    (pre ++ traversed π S (boundaryInit S ρ) (oneRouting π S ρ es n).acted.reverse).Nodup := by
  have hleg := (oneInv_all π S ρ es hes n).legal
  have := boundaryTraversed_nodup π S ρ es _ hes hleg
  unfold boundaryTraversed at this
  have hsub : List.Sublist
      (pre ++ traversed π S (boundaryInit S ρ) (oneRouting π S ρ es n).acted.reverse)
      (es ++ traversed π S (boundaryInit S ρ) (oneRouting π S ρ es n).acted.reverse) := by
    refine List.Sublist.append_right ?_ _
    rw [← hpre]
    exact List.sublist_append_left _ _
  exact this.sublist hsub

/-- The degree identity: outside `S`, in-degree exceeds out-degree exactly at
the tracked particle. -/
theorem indeg_eq_outdeg_add [G.LocallyFinite] (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) (pre : List (V × V))
    (hpre : pre ++ (oneRouting π S ρ es n).queue = es) (v : V) (hv : v ∉ S) :
    indeg (travSet π S ρ pre (oneRouting π S ρ es n)) v =
      outdeg (travSet π S ρ pre (oneRouting π S ρ es n)) v +
        (if (oneRouting π S ρ es n).tracked = some v then 1 else 0) := by
  classical
  obtain ⟨hrun, hleg, -, hcount⟩ := oneInv_all π S ρ es hes n
  set s := oneRouting π S ρ es n with hs
  set L := pre ++ traversed π S (boundaryInit S ρ) s.acted.reverse with hL
  have hnd : L.Nodup := trav_nodup π S ρ es hes n pre hpre
  unfold indeg outdeg travSet
  rw [← hL, card_filter_toFinset L hnd, card_filter_toFinset L hnd, hL, List.countP_append,
    List.countP_append]
  -- the started edges have tails in `S`
  have hpre0 : pre.countP (fun e => decide (e.1 = v)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he
    have := (pre_mem_boundary S es hes pre _ hpre e he).1
    simp only [decide_eq_true_eq]
    exact fun h => hv (h ▸ this)
  -- the actuation edges have as many tails at `v` as actuations of `v`
  have hout : (traversed π S (boundaryInit S ρ) s.acted.reverse).countP (fun e => decide (e.1 = v)) =
      s.acted.reverse.count v := by
    have h := traversed_map_fst π S (boundaryInit S ρ) s.acted.reverse
    conv_rhs => rw [← h]
    rw [List.count_eq_countP, List.countP_map]
    rfl
  -- the particle count identity
  have hσ := run_σ_eq π S (boundaryInit S ρ) s.acted.reverse v hv hleg
  rw [← hrun] at hσ
  have hc := hcount v hv
  have hinit : (boundaryInit S ρ).σ v = es.countP (fun e => decide (e.2 = v)) := by
    simp only [boundaryInit, hv, if_false]
    exact (countP_boundaryOrder S es hes v hv).symm
  rw [← hpre, List.countP_append] at hinit
  unfold arrivals at hσ
  rw [hpre0, hout]
  omega

/-! ### Deleting oppositely directed pairs -/

/-- The surviving edges: those whose reverse was not traversed. -/
def survive (E : Finset (V × V)) : Finset (V × V) := E.filter (fun e => e.swap ∉ E)

theorem indeg_survive (E : Finset (V × V)) (v : V) :
    indeg (survive E) v + (E.filter (fun e => e.2 = v ∧ e.swap ∈ E)).card = indeg E v := by
  unfold indeg survive
  rw [Finset.filter_filter]
  have := Finset.card_filter_add_card_filter_not (s := E.filter (fun e => e.2 = v))
    (fun e => e.swap ∈ E)
  rw [Finset.filter_filter, Finset.filter_filter] at this
  rw [← this, add_comm]
  congr 2
  ext e
  simp only [Finset.mem_filter]
  tauto

theorem outdeg_survive (E : Finset (V × V)) (v : V) :
    outdeg (survive E) v + (E.filter (fun e => e.1 = v ∧ e.swap ∈ E)).card = outdeg E v := by
  unfold outdeg survive
  rw [Finset.filter_filter]
  have := Finset.card_filter_add_card_filter_not (s := E.filter (fun e => e.1 = v))
    (fun e => e.swap ∈ E)
  rw [Finset.filter_filter, Finset.filter_filter] at this
  rw [← this, add_comm]
  congr 2
  ext e
  simp only [Finset.mem_filter]
  tauto

/-- The paired in-edges and paired out-edges of `v` correspond under `swap`. -/
theorem card_paired_eq (E : Finset (V × V)) (v : V) :
    (E.filter (fun e => e.2 = v ∧ e.swap ∈ E)).card =
      (E.filter (fun e => e.1 = v ∧ e.swap ∈ E)).card := by
  refine Finset.card_bij (fun e _ => e.swap) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.2.2, by simp [he.2.1], by simpa using he.1⟩
  · intro e₁ _ e₂ _ h
    exact Prod.swap_injective h
  · intro e he
    rw [Finset.mem_filter] at he
    exact ⟨e.swap, Finset.mem_filter.2 ⟨he.2.2, by simp [he.2.1], by simpa using he.1⟩, by simp⟩

/-- Balance of the surviving edges outside `S`, with the excess at the tracked
particle. -/
theorem survive_balance [G.LocallyFinite] (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) (pre : List (V × V))
    (hpre : pre ++ (oneRouting π S ρ es n).queue = es) (v : V) (hv : v ∉ S) :
    outdeg (survive (travSet π S ρ pre (oneRouting π S ρ es n))) v +
      (if (oneRouting π S ρ es n).tracked = some v then 1 else 0) =
      indeg (survive (travSet π S ρ pre (oneRouting π S ρ es n))) v := by
  have h1 := indeg_survive (travSet π S ρ pre (oneRouting π S ρ es n)) v
  have h2 := outdeg_survive (travSet π S ρ pre (oneRouting π S ρ es n)) v
  have h3 := card_paired_eq (travSet π S ρ pre (oneRouting π S ρ es n)) v
  have h4 := indeg_eq_outdeg_add π S ρ es hes n pre hpre v hv
  omega

/-! ### From the surviving path to a live path -/

theorem rank'_le (ρ : Config G) (v w : V) (hw : G.Adj v w) (k : ℕ) (hk : 0 < k)
    (h : (((π.next v) ^ k) (ρ v)).1 = w) : rank' π ρ v w hw ≤ k :=
  Nat.find_min' _ ⟨hk, Subtype.ext h⟩

theorem lt_rank' (ρ : Config G) (v w : V) (hw : G.Adj v w) (C : ℕ)
    (h : ∀ k, 0 < k → k ≤ C → (((π.next v) ^ k) (ρ v)).1 ≠ w) : C < rank' π ρ v w hw := by
  unfold rank' rank
  rw [Nat.lt_find_iff]
  intro m hm ⟨hm0, hmw⟩
  exact h m hm0 hm (by rw [hmw])

/-- Every edge of the traversed set joins adjacent vertices. -/
theorem adj_of_mem_travSet (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (s : OneState G) (pre : List (V × V))
    (hpre : pre ++ s.queue = es) (e : V × V) (he : e ∈ travSet π S ρ pre s) : G.Adj e.1 e.2 := by
  unfold travSet at he
  rw [List.mem_toFinset, List.mem_append] at he
  rcases he with he | he
  · exact (pre_mem_boundary S es hes pre _ hpre e he).2.2
  · exact adj_of_mem_traversed π S _ _ e he

/-- An edge of the traversed set with tail outside `S` is an actuation edge. -/
theorem mem_traversed_of_mem_travSet (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (s : OneState G) (pre : List (V × V))
    (hpre : pre ++ s.queue = es) (e : V × V) (he : e ∈ travSet π S ρ pre s) (h1 : e.1 ∉ S) :
    e ∈ traversed π S (boundaryInit S ρ) s.acted.reverse := by
  unfold travSet at he
  rw [List.mem_toFinset, List.mem_append] at he
  rcases he with he | he
  · exact absurd (pre_mem_boundary S es hes pre _ hpre e he).1 h1
  · exact he

/-- Liveness at an internal vertex `v` with incoming `u → v` surviving and
outgoing `v → w` traversed: `v → w` comes before `v → u` in the cyclic order
after the initial rotor at `v`. -/
theorem liveAt_of_survive (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (s : OneState G) (pre : List (V × V))
    (hpre : pre ++ s.queue = es) (u v w : V) (hv : v ∉ S)
    (hin : (u, v) ∈ survive (travSet π S ρ pre s)) (hout : (v, w) ∈ survive (travSet π S ρ pre s)) :
    LiveAt π ρ u v w := by
  have hinE : (u, v) ∈ travSet π S ρ pre s := (Finset.mem_filter.1 hin).1
  have hnot : (v, u) ∉ travSet π S ρ pre s := by
    have := (Finset.mem_filter.1 hin).2
    simpa using this
  have houtE : (v, w) ∈ travSet π S ρ pre s := (Finset.mem_filter.1 hout).1
  have hadj_w : G.Adj v w := adj_of_mem_travSet π S ρ es hes s pre hpre _ houtE
  have hadj_u : G.Adj v u := G.adj_symm (adj_of_mem_travSet π S ρ es hes s pre hpre _ hinE)
  refine ⟨hadj_w, hadj_u, ?_⟩
  -- the outgoing edge is an actuation edge: `w = next^(c+1) (ρ v)` with `c + 1 ≤ count v`
  have hout' := mem_traversed_of_mem_travSet π S ρ es hes s pre hpre _ houtE hv
  obtain ⟨l₁, l₂, hsplit, hw⟩ := exists_split_of_mem_traversed π S _ _ _ hout'
  simp only at hsplit hw
  have hle : rank' π ρ v w hadj_w ≤ l₁.count v + 1 :=
    rank'_le π ρ v w hadj_w _ (Nat.succ_pos _) hw.symm
  have hcnt : l₁.count v + 1 ≤ s.acted.reverse.count v := by
    rw [hsplit, List.count_append, List.count_cons_self]; omega
  -- no actuation of `v` traversed `v → u`
  have hgt : s.acted.reverse.count v < rank' π ρ v u hadj_u := by
    refine lt_rank' π ρ v u hadj_u _ (fun k hk0 hk hkeq => hnot ?_)
    have := mem_traversed_of_le_count π S (boundaryInit S ρ) s.acted.reverse v k hk0 hk
    change (v, (((π.next v) ^ k) (ρ v)).1) ∈ _ at this
    rw [hkeq] at this
    unfold travSet
    rw [List.mem_toFinset]
    exact List.mem_append_right _ this
  omega

/-! ### The lemma -/

/-- `lem:decreasing-positions` (i), with the extra information that every
vertex of the path other than its first and last was actuated by the routing
(needed for part (ii)). -/
theorem decreasing_positions_i' [G.LocallyFinite] (S : Finset V) (ρ : Config G) (y : V)
    (hy : y ∉ S) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (hvis : OneVisits π S ρ es y) :
    ∃ l : List V, IsPath G l ∧ IsLive π ρ l ∧ 2 ≤ l.length ∧
      (∀ h : 0 < l.length, l.get ⟨0, h⟩ ∈ S) ∧
      (∀ (i : ℕ) (h : i < l.length), 1 ≤ i → l.get ⟨i, h⟩ ∉ S) ∧
      l.getLast? = some y ∧
      ∃ m, ∀ (i : ℕ) (h : i < l.length), 1 ≤ i → i + 1 < l.length →
        l.get ⟨i, h⟩ ∈ (oneRouting π S ρ es m).acted := by
  classical
  have hex : ∃ n, y ∈ (oneRouting π S ρ es n).route := hvis
  have hmem : y ∈ (oneRouting π S ρ es (Nat.find hex)).route := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, y ∉ (oneRouting π S ρ es m).route :=
    fun m hm => Nat.find_min hex hm
  have htr := tracked_of_first_visit π S ρ es y _ hmem hmin
  obtain ⟨pre, hpre⟩ := (oneInv_all π S ρ es hes (Nat.find hex)).queue_suffix
  have hbal : ∀ v, v ∉ S → v ≠ y →
      outdeg (survive (travSet π S ρ pre (oneRouting π S ρ es (Nat.find hex)))) v ≤
        indeg (survive (travSet π S ρ pre (oneRouting π S ρ es (Nat.find hex)))) v := by
    intro v hv hvy
    have := survive_balance π S ρ es hes _ pre hpre v hv
    rw [htr] at this
    have hne : ¬ (some y = some v) := fun h => hvy (Option.some_inj.1 h).symm
    simp only [hne, if_false, add_zero] at this
    omega
  have hexc : outdeg (survive (travSet π S ρ pre (oneRouting π S ρ es (Nat.find hex)))) y <
      indeg (survive (travSet π S ρ pre (oneRouting π S ρ es (Nat.find hex)))) y := by
    have := survive_balance π S ρ es hes _ pre hpre y hy
    rw [htr] at this
    simp only [if_true] at this
    omega
  obtain ⟨l, hl⟩ := exists_epath _ S y hy hbal hexc
  refine ⟨l, ⟨hl.nodup, ?_⟩, ?_, hl.two_le, hl.head_mem, hl.tail_not_mem, hl.last,
    Nat.find hex, ?_⟩
  · exact hl.chain.imp (fun a b hab =>
      adj_of_mem_travSet π S ρ es hes _ pre hpre _ (Finset.mem_filter.1 hab).1)
  · intro i hi0 hi1
    refine ⟨⟨hi0, hi1⟩, ?_⟩
    have hin := hl.chain.getElem (i - 1) (by omega)
    have hout := hl.chain.getElem i hi1
    simp only [List.get_eq_getElem]
    have hi' : i - 1 + 1 = i := by omega
    simp only [hi'] at hin
    exact liveAt_of_survive π S ρ es hes _ pre hpre _ _ _
      (by simpa only [List.get_eq_getElem] using hl.tail_not_mem i (by omega) hi0) hin hout
  · intro i hi hi1 hi2
    have hout := hl.chain.getElem i hi2
    have hE : (l[i], l[i + 1]) ∈ travSet π S ρ pre (oneRouting π S ρ es (Nat.find hex)) :=
      (Finset.mem_filter.1 hout).1
    have hnot : l[i] ∉ S := by simpa only [List.get_eq_getElem] using hl.tail_not_mem i hi hi1
    have := mem_traversed_of_mem_travSet π S ρ es hes _ pre hpre _ hE hnot
    have := fst_mem_of_mem_traversed π S _ _ _ this
    simp only [List.get_eq_getElem]
    simpa using this

/-- `lem:decreasing-positions` (i). -/
theorem decreasing_positions_i [G.LocallyFinite] (S : Finset V) (ρ : Config G) (y : V)
    (hy : y ∉ S) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (hvis : OneVisits π S ρ es y) :
    ∃ l : List V, IsPath G l ∧ IsLive π ρ l ∧ 2 ≤ l.length ∧
      (∀ h : 0 < l.length, l.get ⟨0, h⟩ ∈ S) ∧
      (∀ (i : ℕ) (h : i < l.length), 1 ≤ i → l.get ⟨i, h⟩ ∉ S) ∧
      l.getLast? = some y := by
  obtain ⟨l, h1, h2, h3, h4, h5, h6, -⟩ := decreasing_positions_i' π S ρ y hy es hes hvis
  exact ⟨l, h1, h2, h3, h4, h5, h6⟩

end Rotor

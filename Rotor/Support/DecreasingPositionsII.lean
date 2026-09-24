/-
`lem:decreasing-positions` (ii) (`rotor.tex:929-936`):

  "let `j` be the least integer with `y ∈ Φ^j({x})` and induct on `j` ...  set
   `S := Φ^{j-1}({x})`, so that `y ∈ Φ(S)` and `y ∉ S`.  A complete
   one-particle-at-a-time boundary routing of `S` has a particle that visits
   `y`, so part (i) gives a live path from a vertex `z ∈ S` to `y` that meets
   `S` only at `z` and lies in `Φ^j({x})`.  The inductive path from `x` to `z`
   lies in `S`, so the two meet only at `z` and concatenate to a path from `x`
   to `y` inside `Φ^j({x})`.  The live condition fails at most `j-2` times on
   the inductive path, never on the live path, and possibly once at the
   junction `z`, hence at most `j-1 ≤ n-1` times in all."
-/
import Rotor.Support.DecreasingPositionsI

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### Actuated vertices were visited -/

theorem oneVisits_of_mem_acted (S : Finset V) (ρ : Config G) (es : List (V × V)) (y : V)
    (n : ℕ) (h : y ∈ (oneRouting π S ρ es n).acted) : OneVisits π S ρ es y := by
  induction n with
  | zero => simp [oneRouting] at h
  | succ n ih =>
    rw [oneRouting, Function.iterate_succ', Function.comp_apply, ← oneRouting] at h
    set s := oneRouting π S ρ es n with hs
    cases htr : s.tracked with
    | some p =>
      by_cases hp : p ∈ S
      · simp only [oneStep, htr, hp, if_true] at h
        exact ih h
      · simp only [oneStep, htr, hp, if_false, List.mem_cons] at h
        rcases h with rfl | h
        · have := route_head π S ρ es n y htr
          exact ⟨n, List.mem_of_mem_head? this⟩
        · exact ih h
    | none =>
      cases hqe : s.queue with
      | nil => simp only [oneStep, htr, hqe] at h; exact ih h
      | cons e rest =>
        obtain ⟨t, x⟩ := e
        simp only [oneStep, htr, hqe] at h
        exact ih h

/-- A vertex of `Φ(S) ∖ S` is visited by every one-particle-at-a-time routing. -/
theorem oneVisits_of_mem_Φ (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite]
    (hG : G.Connected) (S : Finset V) (hS : S.Nonempty) (ρ : Config G) (hT : Terminates π S ρ)
    (es : List (V × V)) (hes : IsBoundaryOrder G S es) (y : V) (hy : y ∉ S)
    (hyΦ : y ∈ Φ π ρ S) : OneVisits π S ρ es y := by
  rw [Φ_of_terminates π ρ S hT, Finset.mem_union, List.mem_toFinset] at hyΦ
  rcases hyΦ with h | h
  · exact absurd h hy
  obtain ⟨m, hm⟩ := oneFinite_of_terminates π hAb hG S hS ρ es hes hT
  have hc := oneActed_count_eq π hAb hG S hS ρ es hes m hm _ (Classical.choose_spec hT) y
  have : y ∈ oneActed π S ρ es m := by
    rw [← List.count_pos_iff] at h ⊢
    omega
  unfold oneActed at this
  rw [List.mem_reverse] at this
  exact oneVisits_of_mem_acted π S ρ es y m this

/-- Every vertex actuated by the routing lies in `Φ(S)`. -/
theorem mem_Φ_of_mem_acted (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite]
    (hG : G.Connected) (S : Finset V) (hS : S.Nonempty) (ρ : Config G) (hT : Terminates π S ρ)
    (es : List (V × V)) (hes : IsBoundaryOrder G S es) (m : ℕ) (v : V)
    (hv : v ∈ (oneRouting π S ρ es m).acted) : v ∈ Φ π ρ S := by
  obtain ⟨ws, hws⟩ := hT
  have hleg := (oneInv_all π S ρ es hes m).legal
  have hc := ((hAb π inferInstance hG S hS _ ws _ hws.1 hleg).1 hws.2).2 v
  have hv' : v ∈ (oneRouting π S ρ es m).acted.reverse := List.mem_reverse.2 hv
  have : v ∈ ws := by
    rw [← List.count_pos_iff] at hv' ⊢
    omega
  exact mem_Φ_of_mem_complete π hAb hG S hS ρ ws hws v this

/-! ### A boundary order exists -/

open Classical in
theorem exists_boundaryOrder [G.LocallyFinite] (S : Finset V) :
    ∃ es : List (V × V), IsBoundaryOrder G S es := by
  refine ⟨(S.biUnion (fun s => ((G.neighborFinset s).filter (fun x => x ∉ S)).image
    (fun x => (s, x)))).toList, Finset.nodup_toList _, fun e => ?_⟩
  rw [Finset.mem_toList, Finset.mem_biUnion]
  constructor
  · rintro ⟨s, hs, he⟩
    rw [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hx
    exact ⟨hs, hx.2, hx.1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨e.1, h1, Finset.mem_image.2 ⟨e.2, Finset.mem_filter.2
      ⟨(G.mem_neighborFinset e.1 e.2).2 h3, h2⟩, rfl⟩⟩

/-! ### Failures of a concatenation -/

/-- Indices below the junction see the same triple in `P ++ Q'` as in `P`. -/
theorem liveAtIndex_append_left (ρ : Config G) (P Q' : List V) (i : ℕ) (hi : i + 1 < P.length) :
    LiveAtIndex π ρ (P ++ Q') i ↔ LiveAtIndex π ρ P i := by
  unfold LiveAtIndex
  have h1 : i + 1 < (P ++ Q').length := by rw [List.length_append]; omega
  constructor
  · rintro ⟨hh, h⟩
    refine ⟨⟨hh.1, hi⟩, ?_⟩
    simp only [List.get_eq_getElem] at h ⊢
    rwa [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
      List.getElem_append_left (by omega)] at h
  · rintro ⟨hh, h⟩
    refine ⟨⟨hh.1, h1⟩, ?_⟩
    simp only [List.get_eq_getElem] at h ⊢
    rwa [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
      List.getElem_append_left (by omega)]

/-- Indices past the junction of `P ++ Q'`, where `Q = z :: Q'` and `P` ends
at `z`, see a triple of `Q`, which is live. -/
theorem liveAtIndex_append_right (ρ : Config G) (P : List V) (z : V) (Q' : List V)
    (hP : P.getLast? = some z) (i : ℕ) (hi : P.length ≤ i) (hi1 : i + 1 < (P ++ Q').length)
    (hQ : IsLive π ρ (z :: Q')) : LiveAtIndex π ρ (P ++ Q') i := by
  have hne : P ≠ [] := by rintro rfl; simp at hP
  have hP0 : 0 < P.length := List.length_pos_of_ne_nil hne
  have hz : P[P.length - 1] = z := by
    rw [List.getLast?_eq_some_getLast hne, Option.some_inj, List.getLast_eq_getElem] at hP
    exact hP
  have hk1 : (i - P.length + 1) + 1 < (z :: Q').length := by
    rw [List.length_cons]; rw [List.length_append] at hi1; omega
  obtain ⟨hh, h⟩ := hQ (i - P.length + 1) (by omega) hk1
  refine ⟨⟨by omega, hi1⟩, ?_⟩
  simp only [List.get_eq_getElem] at h ⊢
  have e2 : (P ++ Q')[i] = (z :: Q')[i - P.length + 1] := by
    rw [List.getElem_append_right hi, List.getElem_cons_succ]
  have e3 : (P ++ Q')[i + 1] = (z :: Q')[i - P.length + 1 + 1] := by
    rw [List.getElem_append_right (by omega), List.getElem_cons_succ]
    have : i + 1 - P.length = i - P.length + 1 := by omega
    simp only [this]
  have e1 : (P ++ Q')[i - 1] = (z :: Q')[i - P.length + 1 - 1] := by
    rcases Nat.lt_or_ge (i - 1) P.length with h' | h'
    · rw [List.getElem_append_left h']
      have t1 : i - 1 = P.length - 1 := by omega
      have t2 : i - P.length + 1 - 1 = 0 := by omega
      simp only [t1, t2, hz, List.getElem_cons_zero]
    · rw [List.getElem_append_right h']
      have t : i - P.length + 1 - 1 = (i - 1 - P.length) + 1 := by omega
      simp only [t, List.getElem_cons_succ]
  rw [e1, e2, e3]
  exact h

/-- The failures of `P ++ Q'` are failures of `P` or the junction. -/
theorem liveFailures_append_subset (ρ : Config G) (P : List V) (z : V) (Q' : List V)
    (hP : P.getLast? = some z) (hQ : IsLive π ρ (z :: Q')) :
    liveFailures π ρ (P ++ Q') ⊆
      liveFailures π ρ P ∪ ({P.length - 1} : Finset ℕ).filter (fun i => 0 < i) := by
  classical
  intro i hi
  unfold liveFailures at hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨-, hi0, hi1, hnot⟩ := hi
  rw [Finset.mem_union]
  rcases Nat.lt_or_ge (i + 1) P.length with h | h
  · left
    unfold liveFailures
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hi0, h, fun hl => hnot ((liveAtIndex_append_left π ρ P Q' i h).2 hl)⟩
  · rcases Nat.lt_or_ge i P.length with h2 | h2
    · right
      rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨by omega, hi0⟩
    · exact absurd (liveAtIndex_append_right π ρ P z Q' hP i h2 hi1 hQ) hnot

theorem card_liveFailures_append (ρ : Config G) (P : List V) (z : V) (Q' : List V)
    (hP : P.getLast? = some z) (hQ : IsLive π ρ (z :: Q')) :
    (liveFailures π ρ (P ++ Q')).card ≤
      (liveFailures π ρ P).card + (if 2 ≤ P.length then 1 else 0) := by
  refine (Finset.card_le_card (liveFailures_append_subset π ρ P z Q' hP hQ)).trans ?_
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  split_ifs with h2
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · have : P.length - 1 = 0 := by omega
    simp [this]

/-! ### The induction -/

/-- `lem:decreasing-positions` (ii), for every `n` (with the bound `n - 1`,
which is `0` at `n = 0`). -/
theorem decreasing_positions_ii (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite]
    (hG : G.Connected) (ρ : Config G) (x : V) (n : ℕ) :
    ∀ y : V, IteratesDefined π ρ {x} n → y ∈ (Φ π ρ)^[n] {x} →
      ∃ l : List V, IsPath G l ∧ l.head? = some x ∧ l.getLast? = some y ∧
        (∀ v ∈ l, v ∈ (Φ π ρ)^[n] {x}) ∧ (liveFailures π ρ l).card ≤ n - 1 := by
  induction n with
  | zero =>
    intro y _ hy
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hy
    subst hy
    refine ⟨[y], ⟨by simp, by simp⟩, rfl, rfl, by simp, ?_⟩
    simp [liveFailures]
  | succ n ih =>
    intro y hdef hy
    have hdef' : IteratesDefined π ρ {x} n := fun i hi => hdef i (by omega)
    have hS : ((Φ π ρ)^[n] {x}).Nonempty := nonempty_Φ_iterate π ρ _ (by simp) n
    have hT : Terminates π ((Φ π ρ)^[n] {x}) ρ := hdef n (Nat.lt_succ_self n)
    rw [Function.iterate_succ_apply'] at hy
    by_cases hyS : y ∈ (Φ π ρ)^[n] {x}
    · obtain ⟨l, h1, h2, h3, h4, h5⟩ := ih y hdef' hyS
      refine ⟨l, h1, h2, h3, fun v hv => ?_, by omega⟩
      rw [Function.iterate_succ_apply']
      exact subset_Φ π ρ _ (h4 v hv)
    · obtain ⟨es, hes⟩ := exists_boundaryOrder (G := G) ((Φ π ρ)^[n] {x})
      have hvis := oneVisits_of_mem_Φ π hAb hG _ hS ρ hT es hes y hyS hy
      obtain ⟨Q, hQpath, hQlive, hQ2, hQhead, hQtail, hQlast, m, hQact⟩ :=
        decreasing_positions_i' π _ ρ y hyS es hes hvis
      obtain ⟨z, Q', rfl⟩ : ∃ z Q', Q = z :: Q' := by
        cases Q with
        | nil => simp at hQ2
        | cons z Q' => exact ⟨z, Q', rfl⟩
      have hz : z ∈ (Φ π ρ)^[n] {x} := hQhead (by simp)
      obtain ⟨P, hPpath, hPhead, hPlast, hPmem, hPfail⟩ := ih z hdef' hz
      have hPne : P ≠ [] := by rintro rfl; simp at hPhead
      have hQ'ne : Q' ≠ [] := by rintro rfl; simp at hQ2
      -- vertices of `Q'` lie outside `S`
      have hQ'notS : ∀ b ∈ Q', b ∉ (Φ π ρ)^[n] {x} := by
        intro b hb
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have := hQtail (j + 1) (by simp; omega) (by omega)
        simpa using this
      -- vertices of `Q'` lie in `Φ(S)`
      have hQ'mem : ∀ b ∈ Q', b ∈ Φ π ρ ((Φ π ρ)^[n] {x}) := by
        intro b hb
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        rcases Nat.lt_or_ge (j + 1 + 1) (z :: Q').length with hlt | hge
        · have := hQact (j + 1) (by simp; omega) (by omega) hlt
          simp only [List.get_eq_getElem, List.getElem_cons_succ] at this
          exact mem_Φ_of_mem_acted π hAb hG _ hS ρ hT es hes m _ this
        · -- the last vertex is `y`
          have hj' : j = Q'.length - 1 := by simp at hge; omega
          have hlast : Q'[Q'.length - 1] = y := by
            have h1 : (z :: Q').getLast? = some ((z :: Q').getLast (List.cons_ne_nil z Q')) :=
              List.getLast?_eq_some_getLast _
            rw [h1, Option.some_inj, List.getLast_cons hQ'ne, List.getLast_eq_getElem] at hQlast
            exact hQlast
          subst hj'
          rw [hlast]; exact hy
      refine ⟨P ++ Q', ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hPpath.1, (List.nodup_cons.1 hQpath.1).2, fun a ha b hb hab => ?_⟩
        exact hQ'notS b hb (hab ▸ hPmem a ha)
      · rw [List.isChain_append]
        refine ⟨hPpath.2, (List.isChain_cons.1 hQpath.2).2, fun a ha b hb => ?_⟩
        rw [hPlast, Option.mem_def, Option.some_inj] at ha
        subst ha
        exact (List.isChain_cons.1 hQpath.2).1 b hb
      · rw [List.head?_append_of_ne_nil _ hPne]; exact hPhead
      · rw [List.getLast?_append_of_ne_nil _ hQ'ne]
        have : (z :: Q').getLast? = Q'.getLast? := by
          cases Q' with
          | nil => exact absurd rfl hQ'ne
          | cons b l => simp
        rw [← this]; exact hQlast
      · intro v hv
        rw [Function.iterate_succ_apply']
        rw [List.mem_append] at hv
        rcases hv with hv | hv
        · exact subset_Φ π ρ _ (hPmem v hv)
        · exact hQ'mem v hv
      · have hb := card_liveFailures_append π ρ P z Q' hPlast hQlive
        split_ifs at hb with h2
        · -- with two vertices in `P`, `n ≥ 1`: for `n = 0`, `P ⊆ {x}` has one vertex
          have hn : 1 ≤ n := by
            by_contra hn0
            have hn0' : n = 0 := by omega
            subst hn0'
            have hsub : P.toFinset ⊆ {x} := by
              intro v hv
              rw [List.mem_toFinset] at hv
              simpa using hPmem v hv
            have := Finset.card_le_card hsub
            rw [List.toFinset_card_of_nodup hPpath.1, Finset.card_singleton] at this
            omega
          omega
        · omega

end Rotor

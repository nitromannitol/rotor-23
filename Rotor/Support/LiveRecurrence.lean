/-
`prop:live-recurrence` (`rotor.tex:938-970`): no infinite live path implies
that every boundary routing terminates, every circuit ends, and the walk is
recurrent.

  "Suppose that the boundary routing of some nonempty finite set `S` does not
   terminate, and choose a one-particle-at-a-time boundary routing of `S`.  By
   Lemma boundary-routing it is infinite and traverses no directed edge twice,
   and a finite set contains only finitely many directed edges, so the routing
   leaves every finite set.  Given an integer `R ≥ 1`, some particle therefore
   visits a vertex at graph distance `R` from `S`, and Lemma
   decreasing-positions (i) converts that visit into a live path of length at
   least `R` that starts in `S` and never returns to `S`.  All finite
   positive-length live paths that start in `S` and otherwise avoid `S` form a
   forest ... König's lemma gives an infinite branch there, whose union is an
   infinite live path, contrary to hypothesis.  Thus the boundary routing of
   every nonempty finite set terminates, and Proposition circuit-iterate gives
   `T(n) < ∞` for every `n` by induction.  Hence the walk returns to `o`
   infinitely often.  A rotor walk that visits one vertex infinitely often
   visits every vertex infinitely often [Holroyd--Propp, Lemma 6]."
-/
import Rotor.Support.Konig
import Rotor.Support.DecreasingPositionsII
import Rotor.Events
import Rotor.External.HolroydPropp

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### A non-terminating routing leaves every finite set -/

open Classical in
/-- The edges of a duplicate-free list with tail `v` are at most `deg v`. -/
theorem countP_tail_le [G.LocallyFinite] (L : List (V × V)) (hL : L.Nodup) (v : V)
    (hadj : ∀ e ∈ L, G.Adj e.1 e.2) :
    L.countP (fun e => decide (e.1 = v)) ≤ G.degree v := by
  rw [List.countP_eq_length_filter]
  have hsub : ∀ t ∈ (L.filter (fun e => decide (e.1 = v))).map Prod.snd, t ∈ G.neighborFinset v := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    rw [List.mem_filter, decide_eq_true_eq] at he
    rw [SimpleGraph.mem_neighborFinset]
    exact he.2 ▸ hadj e he.1
  have hnd : ((L.filter (fun e => decide (e.1 = v))).map Prod.snd).Nodup := by
    refine List.Nodup.map_on ?_ (hL.filter _)
    intro e₁ he₁ e₂ he₂ h
    rw [List.mem_filter, decide_eq_true_eq] at he₁ he₂
    exact Prod.ext (he₁.2.trans he₂.2.symm) h
  calc (L.filter (fun e => decide (e.1 = v))).length
      = ((L.filter (fun e => decide (e.1 = v))).map Prod.snd).length := (List.length_map _).symm
    _ = ((L.filter (fun e => decide (e.1 = v))).map Prod.snd).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (G.neighborFinset v).card :=
        Finset.card_le_card (fun t ht => hsub t (List.mem_toFinset.1 ht))
    _ = G.degree v := G.card_neighborFinset_eq_degree v

/-- A legal boundary routing actuates each vertex at most `deg` times. -/
theorem count_le_degree [G.LocallyFinite] (S : Finset V) (ρ : Config G) (vs : List V)
    (hleg : IsLegal π S (boundaryInit S ρ) vs) (v : V) : vs.count v ≤ G.degree v := by
  have h1 : vs.count v = (traversed π S (boundaryInit S ρ) vs).countP (fun e => decide (e.1 = v)) := by
    conv_lhs => rw [← traversed_map_fst π S (boundaryInit S ρ) vs]
    rw [List.count_eq_countP, List.countP_map]
    rfl
  rw [h1]
  exact countP_tail_le _ (traversed_nodup π S ρ vs hleg) v (adj_of_mem_traversed π S _ vs)

/-- If the boundary routing of `S` does not terminate, its one-particle
routing eventually actuates a vertex outside any given finite set. -/
theorem exists_acted_notMem [G.LocallyFinite] (S : Finset V) (ρ : Config G)
    (hnT : ¬ Terminates π S ρ) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (W : Finset V) : ∃ m, ∃ v ∈ (oneRouting π S ρ es m).acted, v ∉ W := by
  classical
  have hnd : ∀ m, ¬ OneDone π S ρ es m :=
    fun m hd => hnT (terminates_of_oneFinite π S ρ es hes ⟨m, hd⟩)
  set D := ∑ w ∈ W, G.degree w with hD
  set m := 2 * (D + 1) + es.length with hm
  refine ⟨m, ?_⟩
  by_contra hcon
  push Not at hcon
  have hlen := oneRouting_length π S ρ es hes m (fun k _ => hnd k)
  have hleg := (oneInv_all π S ρ es hes m).legal
  -- the actuations are all inside `W`, hence at most `D` of them
  have hsum : (oneRouting π S ρ es m).acted.reverse.length =
      ∑ v ∈ (oneRouting π S ρ es m).acted.reverse.toFinset,
        (oneRouting π S ρ es m).acted.reverse.count v :=
    (List.sum_toFinset_count_eq_length _).symm
  have hsub : (oneRouting π S ρ es m).acted.reverse.toFinset ⊆ W := by
    intro v hv
    rw [List.mem_toFinset, List.mem_reverse] at hv
    exact hcon v hv
  have hle : ∑ v ∈ (oneRouting π S ρ es m).acted.reverse.toFinset,
      (oneRouting π S ρ es m).acted.reverse.count v ≤ D := by
    calc _ ≤ ∑ v ∈ W, (oneRouting π S ρ es m).acted.reverse.count v :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ ≤ D := Finset.sum_le_sum (fun v _ => count_le_degree π S ρ _ hleg v)
  rw [List.length_reverse] at hsum
  omega

/-! ### Balls are finite -/

/-- The vertices within graph distance `R` of a finite set. -/
def ball (G : SimpleGraph V) (S : Finset V) (R : ℕ) : Set V :=
  {v | ∃ s ∈ S, G.dist s v ≤ R}

omit [DecidableEq V] in
theorem ball_finite [G.LocallyFinite] (hG : G.Connected) (S : Finset V) (R : ℕ) :
    (ball G S R).Finite := by
  induction R with
  | zero =>
    apply (S.finite_toSet).subset
    intro v hv
    obtain ⟨s, hs, hd⟩ := hv
    have := (hG.preconnected s v).dist_eq_zero_iff.1 (Nat.le_zero.1 hd)
    rw [← this]; exact hs
  | succ R ih =>
    -- a vertex at distance `R + 1` is a neighbor of a vertex at distance `≤ R`
    have hsub : ball G S (R + 1) ⊆ ball G S R ∪ ⋃ u ∈ ball G S R, (G.neighborSet u) := by
      intro v hv
      obtain ⟨s, hs, hd⟩ := hv
      rcases Nat.lt_or_ge (G.dist s v) (R + 1) with hlt | hge
      · exact Or.inl ⟨s, hs, by omega⟩
      · have heq : G.dist s v = R + 1 := le_antisymm hd hge
        obtain ⟨p, hp⟩ := (hG.preconnected s v).exists_walk_length_eq_dist
        right
        rw [Set.mem_iUnion₂]
        refine ⟨p.getVert R, ⟨s, hs, ?_⟩, ?_⟩
        · calc G.dist s (p.getVert R) ≤ (p.take R).length := G.dist_le _
            _ ≤ R := by rw [SimpleGraph.Walk.take_length]; exact min_le_left _ _
        · have := p.adj_getVert_succ (i := R) (by omega)
          rw [show R + 1 = p.length by omega, p.getVert_length] at this
          exact this
    refine (ih.union ?_).subset hsub
    exact ih.biUnion (fun u _ => (G.neighborSet u).toFinite)

end Rotor

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### Paths are at least as long as the distance -/

omit [DecidableEq V] in
theorem dist_le_length_of_chain (hG : G.Connected) (l : List V) (hl : l.IsChain G.Adj)
    (x y : V) (hx : l.head? = some x) (hy : l.getLast? = some y) :
    G.dist x y + 1 ≤ l.length := by
  induction l generalizing x with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.head?_cons, Option.some_inj] at hx
    subst hx
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some_inj] at hy
      subst hy
      simp
    | cons b l =>
      rw [List.isChain_cons] at hl
      have hab : G.Adj a b := hl.1 b rfl
      have hy' : (b :: l).getLast? = some y := by simpa using hy
      have := ih hl.2 b rfl hy'
      have htri := hG.dist_triangle (u := a) (v := b) (w := y)
      have h1 : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hab
      simp only [List.length_cons] at this ⊢
      omega

/-! ### The family of live paths from `S` -/

/-- The finite live paths starting in `S` and otherwise avoiding `S`, together
with the empty list: the family to which König's lemma is applied. -/
def LivePathFrom (ρ : Config G) (S : Finset V) (l : List V) : Prop :=
  l = [] ∨ (IsPath G l ∧ IsLive π ρ l ∧ (∀ h : 0 < l.length, l.get ⟨0, h⟩ ∈ S) ∧
    ∀ (i : ℕ) (h : i < l.length), 1 ≤ i → l.get ⟨i, h⟩ ∉ S)

/-- The family is closed under removing the last vertex. -/
theorem livePathFrom_prefix (ρ : Config G) (S : Finset V) (l : List V) (a : V)
    (h : LivePathFrom π ρ S (l ++ [a])) : LivePathFrom π ρ S l := by
  rcases l with _ | ⟨b, l⟩
  · exact Or.inl rfl
  right
  rcases h with h | ⟨⟨hnd, hch⟩, hlive, hhead, htail⟩
  · simp at h
  have hsub : List.Sublist (b :: l) (b :: l ++ [a]) := List.sublist_append_left _ _
  refine ⟨⟨hnd.sublist hsub, (List.isChain_append.1 hch).1⟩, ?_, ?_, ?_⟩
  · intro i hi0 hi1
    exact (liveAtIndex_append_left π ρ (b :: l) [a] i hi1).1
      (hlive i hi0 (by rw [List.length_append, List.length_singleton]; omega))
  · intro h0
    have := hhead (by simp)
    simp only [List.get_eq_getElem] at this ⊢
    rwa [List.getElem_append_left (by simp)] at this
  · intro i hi hi1
    have := htail i (by rw [List.length_append]; omega) hi1
    simp only [List.get_eq_getElem] at this ⊢
    rwa [List.getElem_append_left hi] at this

/-- The one-step extensions of a member are finitely many. -/
theorem livePathFrom_finite [G.LocallyFinite] (ρ : Config G) (S : Finset V) (l : List V) :
    Set.Finite {a | LivePathFrom π ρ S (l ++ [a])} := by
  rcases l with _ | ⟨b, l⟩
  · apply S.finite_toSet.subset
    intro a ha
    rcases ha with ha | ⟨-, -, hhead, -⟩
    · simp at ha
    · exact hhead (by simp)
  · apply (G.neighborSet ((b :: l).getLast (by simp))).toFinite.subset
    intro a ha
    rcases ha with ha | ⟨⟨-, hch⟩, -, -, -⟩
    · simp at ha
    · rw [List.isChain_append] at hch
      have := hch.2.2 _ (by rw [List.getLast?_eq_some_getLast (by simp)]; rfl) a rfl
      exact this

/-! ### The infinite live path -/

/-- From an infinite sequence all of whose prefixes are live paths from `S`,
an infinite live path. -/
theorem hasInfLivePath_of_prefixes (ρ : Config G) (S : Finset V) (x : ℕ → V)
    (hx : ∀ n, LivePathFrom π ρ S ((List.range n).map x)) : HasInfLivePath π ρ := by
  have hP : ∀ n, 0 < n → IsPath G ((List.range n).map x) ∧ IsLive π ρ ((List.range n).map x) := by
    intro n hn
    rcases hx n with h | ⟨h1, h2, -, -⟩
    · exfalso
      have := congrArg List.length h
      simp at this; omega
    · exact ⟨h1, h2⟩
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · -- injective: any two indices lie in a duplicate-free prefix
    intro i j hij
    by_contra hne
    have hnd := (hP (max i j + 1) (by omega)).1.1
    rw [List.nodup_iff_injective_get] at hnd
    have hi : i < ((List.range (max i j + 1)).map x).length := by
      simp only [List.length_map, List.length_range]; omega
    have hj : j < ((List.range (max i j + 1)).map x).length := by
      simp only [List.length_map, List.length_range]; omega
    have := @hnd ⟨i, hi⟩ ⟨j, hj⟩ (by simp [hij])
    simp only [Fin.mk.injEq] at this
    exact hne this
  · intro i
    have hch := (hP (i + 2) (by omega)).1.2
    have := hch.getElem i (by simp)
    simpa using this
  · intro i
    have hlive := (hP (i + 3) (by omega)).2
    obtain ⟨hh, h⟩ := hlive (i + 1) (by omega) (by simp)
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
      Nat.add_sub_cancel] at h
    exact h

/-- Arbitrarily long members exist when some boundary routing fails to
terminate. -/
theorem exists_long_livePath [G.LocallyFinite] (hG : G.Connected) (ρ : Config G)
    (S : Finset V) (hnT : ¬ Terminates π S ρ) (R : ℕ) :
    ∃ l, LivePathFrom π ρ S l ∧ R ≤ l.length := by
  classical
  obtain ⟨es, hes⟩ := exists_boundaryOrder (G := G) S
  obtain ⟨m, v, hv, hvW⟩ := exists_acted_notMem π S ρ hnT es hes (ball_finite hG S R).toFinset
  have hvS : v ∉ S := by
    intro h
    apply hvW
    rw [Set.Finite.mem_toFinset]
    exact ⟨v, h, by simp⟩
  have hvis := oneVisits_of_mem_acted π S ρ es v m hv
  obtain ⟨l, hpath, hlive, h2, hhead, htail, hlast⟩ := decreasing_positions_i π S ρ v hvS es hes hvis
  refine ⟨l, Or.inr ⟨hpath, hlive, hhead, htail⟩, ?_⟩
  -- the path from `s ∈ S` to `v` has length at least `dist s v + 1 > R + 1`
  obtain ⟨s, hs⟩ : ∃ s, l.head? = some s := by
    cases l with
    | nil => simp at h2
    | cons s l => exact ⟨s, rfl⟩
  have hsS : s ∈ S := by
    have := hhead (by omega)
    cases l with
    | nil => simp at hs
    | cons a l => simp at hs; subst hs; simpa using this
  have hd := dist_le_length_of_chain hG l hpath.2 s v hs hlast
  have hfar : R < G.dist s v := by
    by_contra hle
    apply hvW
    rw [Set.Finite.mem_toFinset]
    exact ⟨s, hsS, by omega⟩
  omega

/-- No infinite live path implies that every boundary routing terminates. -/
theorem allTerminate_of_no_infLivePath [G.LocallyFinite] (hG : G.Connected) (ρ : Config G)
    (h : ¬ HasInfLivePath π ρ) : AllTerminate π ρ := by
  intro S hS
  by_contra hnT
  apply h
  obtain ⟨x, hx⟩ := konig (LivePathFrom π ρ S) (livePathFrom_prefix π ρ S)
    (livePathFrom_finite π ρ S) (exists_long_livePath π hG ρ S hnT)
  exact hasInfLivePath_of_prefixes π ρ S x hx

/-! ### Recurrence -/

/-- `prop:live-recurrence`. -/
theorem live_recurrence_proof [G.LocallyFinite] (hFLP : External.OneCircuit G)
    (hAb : External.Abelian G) (hHP : External.VisitsAllOfVisitsOne G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (o : V) (h : ¬ HasInfLivePath π ρ) :
    AllTerminate π ρ ∧ (∀ n : ℕ, T π ρ o n < ⊤) ∧ Recurrent π ρ o := by
  have hall := allTerminate_of_no_infLivePath π hG ρ h
  have hT : ∀ n, T π ρ o n < ⊤ := fun n => (T_lt_and_A_eq π hFLP hAb hG ρ o hall n).1
  refine ⟨hall, hT, hHP π inferInstance hG ρ o o ?_⟩
  -- infinitely many visits to `o`: `visits (T n) ≥ deg o * n`
  have hdeg : 0 < G.degree o := by
    have := π.nonempty o
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_pos
  intro hfin
  have hcard : ∀ n, visits π ρ o n ≤ hfin.toFinset.card := by
    intro n
    unfold visits
    apply Finset.card_le_card
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Set.Finite.mem_toFinset]
    exact ht.2
  have := (T_mem π ρ o (hfin.toFinset.card + 1) (hT _)).2
  have := hcard (T π ρ o (hfin.toFinset.card + 1)).toNat
  nlinarith

end Rotor

import Rotor.Support.ExplInv

/-!
Lemma 5.4 (ii) (`rotor.tex:1906-1909`): if the exploration terminates, every face reachable
from `f` by an open directed dual path is visited or lies in a finite component of the
complement of the visited set.  The invariant: for every visited face `x` and neighbour `y`,
either `y` is visited, or `y` lies in a finite component of the complement, or `x → y` is
active, or `x → y` was tested closed; and every recorded outcome is the truth about `ρ`.
-/

open Finset

namespace Rotor

/-! ### Reachability through unvisited faces -/

/-- Reachability from `x` to `y` through faces outside `V`. -/
def AvoidReach (V : Finset Site) (x y : Site) : Prop :=
  Relation.ReflTransGen (fun a b => a ∉ V ∧ b ∉ V ∧ squareGraph.Adj a b) x y

theorem AvoidReach.notMem {V : Finset Site} {x y : Site} (hx : x ∉ V) (h : AvoidReach V x y) :
    y ∉ V := by
  induction h with
  | refl => exact hx
  | tail _ hbc _ => exact hbc.2.1

theorem reachable_induce_of_avoidReach (V : Finset Site) {x y : Site} (h : AvoidReach V x y)
    (hx : x ∉ V) (hy : y ∉ V) :
    (squareGraph.induce {z : Site | z ∉ V}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    have hb : b ∉ V := hbc.1
    refine (ih hb).trans (SimpleGraph.Adj.reachable ?_)
    exact hbc.2.2

theorem avoidReach_of_reachable_induce (V : Finset Site) :
    ∀ (p q : {z : Site // z ∉ V}), (squareGraph.induce {z : Site | z ∉ V}).Reachable p q →
      AvoidReach V p.1 q.1 := by
  intro p q h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ⟨b.2, c.2, hbc⟩

theorem inFiniteComponent_iff (V : Finset Site) (y : Site) :
    InFiniteComponent V y ↔ y ∉ V ∧ Set.Finite {z | AvoidReach V y z} := by
  unfold InFiniteComponent
  constructor
  · rintro ⟨hy, hfin⟩
    refine ⟨hy, hfin.subset ?_⟩
    intro z hz
    have hz' : z ∉ V := AvoidReach.notMem hy hz
    exact ⟨hz', hy, reachable_induce_of_avoidReach V hz hy hz'⟩
  · rintro ⟨hy, hfin⟩
    refine ⟨hy, hfin.subset ?_⟩
    rintro z ⟨hz, hy', hr⟩
    exact avoidReach_of_reachable_induce V ⟨y, hy'⟩ ⟨z, hz⟩ hr

theorem InFiniteComponent.mono {V V' : Finset Site} (hVV' : V ⊆ V') {y : Site}
    (h : InFiniteComponent V y) : y ∈ V' ∨ InFiniteComponent V' y := by
  by_cases hy : y ∈ V'
  · exact Or.inl hy
  right
  rw [inFiniteComponent_iff] at h ⊢
  refine ⟨hy, h.2.subset ?_⟩
  intro z hz
  exact Relation.ReflTransGen.mono
    (fun a b hab => ⟨fun h => hab.1 (hVV' h), fun h => hab.2.1 (hVV' h), hab.2.2⟩) _ _ hz

theorem InFiniteComponent.adj {V : Finset Site} {x y : Site} (h : InFiniteComponent V x)
    (hxy : squareGraph.Adj x y) : y ∈ V ∨ InFiniteComponent V y := by
  by_cases hy : y ∈ V
  · exact Or.inl hy
  right
  rw [inFiniteComponent_iff] at h ⊢
  refine ⟨hy, h.2.subset ?_⟩
  intro z hz
  exact (Relation.ReflTransGen.single ⟨h.1, hy, hxy⟩).trans hz

/-! ### The neighbours of a face are covered by the edges added at its visit -/

theorem edgesFrom_cover (f : Site) {d : Site} (hd : IsUnit d) {y : Site}
    (h : squareGraph.Adj f y) : (f, y) ∈ edgesFrom f d := by
  have hy : y = f + (y - f) := by abel
  rcases isUnit_of_adj h with hu | hu | hu | hu <;> rw [hu] at hy <;> subst hy <;>
  rcases hd with rfl | rfl | rfl | rfl <;> simp [edgesFrom, rotL]

theorem continuations_cover {a b : Site} (h : squareGraph.Adj a b) {y : Site}
    (hy : squareGraph.Adj b y) : y = a ∨ (b, y) ∈ continuations a b := by
  have hb : b = a + (b - a) := by abel
  have hy' : y = b + (y - b) := by abel
  rcases isUnit_of_adj hy with hu | hu | hu | hu <;> rw [hu] at hy' <;> subst hy' <;>
  rcases isUnit_of_adj h with hu' | hu' | hu' | hu' <;> rw [hu'] at hb <;> subst hb <;>
  simp [continuations, rotL, rotR, Prod.ext_iff]

/-! ### The covering invariant -/

open Classical in
/-- The covering invariant of the exploration driven by `ρ` from `f`. -/
structure ExplCov (ρ : Config squareGraph) (f : Site) (s : ExplState) : Prop where
  root_mem : f ∈ s.visited
  cover : ∀ x ∈ s.visited, ∀ y, squareGraph.Adj x y →
    y ∈ s.visited ∨ InFiniteComponent s.visited y ∨ (x, y) ∈ s.active ∨ (x, y, false) ∈ s.tested
  outcomes : ∀ t ∈ s.tested, t.2.2 = decide (DualOpen ρ t.1 t.2.1)

open Classical in
theorem explCov_init (ρ : Config squareGraph) (f : Site) {d : Site} (hd : IsUnit d) :
    ExplCov ρ f (explInit f d) where
  root_mem := by simp [explInit]
  cover := by
    intro x hx y hxy
    simp only [explInit, mem_singleton] at hx
    subst hx
    exact Or.inr (Or.inr (Or.inl (edgesFrom_cover x hd hxy)))
  outcomes := by simp [explInit]

open Classical in
theorem explCov_step (ρ : Config squareGraph) (f : Site) {s : ExplState} (hinv : ExplInv s)
    (hs : ExplCov ρ f s) : ExplCov ρ f (explStep ρ s) := by
  rcases h : s.active with _ | ⟨e, rest⟩
  · rw [explStep_nil ρ h]; exact hs
  rw [explStep_cons ρ h, explStepWith_cons h]
  have he : e ∈ s.active := by rw [h]; exact List.mem_cons_self
  have hadj : squareGraph.Adj e.1 e.2 := hinv.active_adj e he
  set o := decide (DualOpen ρ e.1 e.2) with ho
  set visited' := if o then insert e.2 s.visited else s.visited with hv'
  have hsub : s.visited ⊆ visited' := by
    rw [hv']; split_ifs
    · exact subset_insert _ _
    · exact subset_rfl
  set added := if o then continuations e.1 e.2 else [] with hadded
  -- an edge of `added ++ rest` is active afterwards or its head is covered
  have hfilter : ∀ g ∈ added ++ rest,
      g.2 ∈ visited' ∨ InFiniteComponent visited' g.2 ∨
        g ∈ (added ++ rest).filter
          (fun g => decide (¬ (g.2 ∈ visited' ∨ InFiniteComponent visited' g.2))) := by
    intro g hg
    by_cases hc : g.2 ∈ visited' ∨ InFiniteComponent visited' g.2
    · rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (List.mem_filter.2 ⟨hg, by simpa using hc⟩))
  refine ⟨hsub hs.root_mem, ?_, ?_⟩
  · intro x hx y hxy
    dsimp only
    by_cases hxold : x ∈ s.visited
    · rcases hs.cover x hxold y hxy with hy | hy | hy | hy
      · exact Or.inl (hsub hy)
      · rcases hy.mono hsub with hy' | hy'
        · exact Or.inl hy'
        · exact Or.inr (Or.inl hy')
      · rw [h, List.mem_cons] at hy
        rcases hy with hy | hy
        · -- the tested edge itself
          have hx1 : x = e.1 := congrArg Prod.fst hy
          have hy1 : y = e.2 := congrArg Prod.snd hy
          subst hx1 hy1
          rcases ho' : o with _ | _
          · right; right; right
            rw [← ho']
            simp
          · left
            rw [hv', ho']
            simp only [if_true]
            exact mem_insert_self _ _
        · rcases hfilter (x, y) (List.mem_append_right _ hy) with hc | hc | hc
          · exact Or.inl hc
          · exact Or.inr (Or.inl hc)
          · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr (List.mem_append_left _ hy)))
    · -- `x` is the newly visited face `e.2`
      have hxe : x = e.2 ∧ o = true := by
        rw [hv'] at hx
        rcases ho' : o with _ | _
        · rw [ho'] at hx; simp at hx; exact absurd hx hxold
        · rw [ho'] at hx; simp only [if_true, mem_insert] at hx
          rcases hx with hx | hx
          · exact ⟨hx, rfl⟩
          · exact absurd hx hxold
      obtain ⟨rfl, hotrue⟩ := hxe
      rcases continuations_cover hadj hxy with rfl | hy
      · exact Or.inl (hsub (hinv.active_tail e he))
      · have hy' : (e.2, y) ∈ added ++ rest := by
          apply List.mem_append_left
          rw [hadded, hotrue]
          simpa using hy
        rcases hfilter (e.2, y) hy' with hc | hc | hc
        · exact Or.inl hc
        · exact Or.inr (Or.inl hc)
        · exact Or.inr (Or.inr (Or.inl hc))
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact hs.outcomes t ht
    · rw [List.mem_singleton] at ht
      subst ht
      rfl

theorem explCov_explore (ρ : Config squareGraph) (f : Site) {d : Site} (hd : IsUnit d) (n : ℕ) :
    ExplCov ρ f (explore ρ f d n) := by
  induction n with
  | zero => exact explCov_init ρ f hd
  | succ n ih =>
    rw [explore_succ]
    exact explCov_step ρ f (explInv_explore ρ f hd n) ih

/-! ### Lemma 5.4 (ii) -/

theorem isChain_and {α : Type*} {R S : α → α → Prop} : ∀ {l : List α},
    l.IsChain R → l.IsChain S → l.IsChain (fun a b => R a b ∧ S a b)
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | _ :: _ :: _, hR, hS => by
    rw [List.isChain_cons_cons] at hR hS ⊢
    exact ⟨⟨hR.1, hS.1⟩, isChain_and hR.2 hS.2⟩

theorem forall_mem_of_isChain {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (hstep : ∀ a b, P a → R a b → P b) : ∀ {l : List α},
    l.IsChain R → (∀ z ∈ l.head?, P z) → ∀ z ∈ l, P z
  | [], _, _ => by simp
  | [a], _, hh => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at hh
    simpa using hh
  | a :: b :: l, hch, hh => by
    rw [List.isChain_cons_cons] at hch
    have ha : P a := by simpa using hh
    have hb : P b := hstep a b ha hch.1
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ha
    · exact forall_mem_of_isChain hstep hch.2 (by simpa using hb) z hz

theorem square_exploration_ii (f : Site) {d : Site} (hd : IsUnit d) (ρ : Config squareGraph)
    (n : ℕ) (hterm : (explore ρ f d n).active = []) (g : Site) (hg : DualReachable ρ f g) :
    g ∈ (explore ρ f d n).visited ∨ InFiniteComponent (explore ρ f d n).visited g := by
  obtain ⟨q, ⟨⟨-, hchain⟩, hopen⟩, hhead, hlast⟩ := hg
  have hcov := explCov_explore ρ f hd n
  set V := (explore ρ f d n).visited with hV
  have hall := forall_mem_of_isChain (R := fun a b => squareGraph.Adj a b ∧ DualOpen ρ a b)
    (P := fun z => z ∈ V ∨ InFiniteComponent V z) ?_ (isChain_and hchain hopen) ?_
  · exact hall g (List.mem_of_mem_getLast? hlast)
  · intro a b ha hab
    rcases ha with ha | ha
    · rcases hcov.cover a ha b hab.1 with hb | hb | hb | hb
      · exact Or.inl hb
      · exact Or.inr hb
      · rw [hterm] at hb; simp at hb
      · have := hcov.outcomes _ hb
        exact absurd hab.2 (decide_eq_false_iff_not.1 this.symm)
    · exact ha.adj hab.1
  · intro z hz
    rw [hhead, Option.mem_def, Option.some.injEq] at hz
    subst hz
    exact Or.inl hcov.root_mem

end Rotor

/-
Equivariance of the model under graph automorphisms compatible with the
mechanism.  The lattice translations of a doubly periodic graph with a doubly
periodic mechanism are such automorphisms (`rotor.tex:217-227`), and the
stationarity of the passage-time array in the proof of `prop:passage-limit`
(`rotor.tex:1096-1113`) is this equivariance.
-/
import Rotor.Periodic
import Rotor.Support.WalkBasics
import Rotor.Support.Passage

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-- An automorphism of `G` compatible with the mechanism `π`. -/
structure MechAut where
  /-- The bijection on vertices. -/
  σ : V ≃ V
  adj : ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v
  next : ∀ (v : V) (a : G.neighborSet v),
    (π.next (σ v) ⟨σ a.1, (adj v a.1).2 a.2⟩).1 = σ (π.next v a).1

namespace MechAut

variable {π} (φ : MechAut π)

/-- A neighbor of `v`, transported to a neighbor of `σ v`. -/
def nbr {v : V} (a : G.neighborSet v) : G.neighborSet (φ.σ v) := ⟨φ.σ a.1, (φ.adj v a.1).2 a.2⟩

/-- The action on rotor configurations: the rotor at `σ v` points to the image
of where the rotor at `v` points. -/
def act (ρ : Config G) : Config G := fun v =>
  ⟨φ.σ (ρ (φ.σ.symm v)).1, by
    have := (φ.adj _ _).2 (ρ (φ.σ.symm v)).2
    rwa [φ.σ.apply_symm_apply] at this⟩

omit [DecidableEq V] in
theorem act_apply (ρ : Config G) (v : V) : φ.act ρ (φ.σ v) = φ.nbr (ρ v) := by
  apply Subtype.ext
  show φ.σ (ρ (φ.σ.symm (φ.σ v))).1 = φ.σ (ρ v).1
  rw [Equiv.symm_apply_apply]

omit [DecidableEq V] in
@[simp] theorem act_apply_val (ρ : Config G) (v : V) : (φ.act ρ (φ.σ v)).1 = φ.σ (ρ v).1 := by
  rw [act_apply]; rfl

omit [DecidableEq V] in
theorem next_val (v : V) (a : G.neighborSet v) :
    (π.next (φ.σ v) (φ.nbr a)).1 = φ.σ (π.next v a).1 := φ.next v a

/-! ### The walk -/

theorem act_update (ρ : Config G) (v : V) (a : G.neighborSet v) :
    φ.act (Function.update ρ v a) = Function.update (φ.act ρ) (φ.σ v) (φ.nbr a) := by
  funext w
  apply Subtype.ext
  by_cases hw : w = φ.σ v
  · subst hw
    rw [Function.update_self, act_apply_val, Function.update_self]
    rfl
  · have hw' : φ.σ.symm w ≠ v := fun h => hw (by rw [← h, φ.σ.apply_symm_apply])
    rw [Function.update_of_ne hw]
    simp only [act, Function.update_of_ne hw']

theorem step_act (s : State G) :
    step π ⟨φ.σ s.pos, φ.act s.rotor⟩ = ⟨φ.σ (step π s).pos, φ.act (step π s).rotor⟩ := by
  simp only [step, act_apply]
  refine congrArg₂ State.mk ?_ ?_
  · exact φ.next_val _ _
  · rw [act_update]
    congr 1
    exact Subtype.ext (φ.next_val _ _)

theorem walk_act (ρ : Config G) (o : V) (t : ℕ) :
    walk π (φ.act ρ) (φ.σ o) t = ⟨φ.σ (X π ρ o t), φ.act (rot π ρ o t)⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [walk_succ, ih, X, X, rot, rot, walk_succ]
    exact φ.step_act (walk π ρ o t)

theorem X_act (ρ : Config G) (o : V) (t : ℕ) : X π (φ.act ρ) (φ.σ o) t = φ.σ (X π ρ o t) := by
  rw [X, walk_act]

theorem rot_act (ρ : Config G) (o : V) (t : ℕ) :
    rot π (φ.act ρ) (φ.σ o) t = φ.act (rot π ρ o t) := by
  rw [rot, walk_act]

theorem R_act (ρ : Config G) (o : V) (t : ℕ) :
    R π (φ.act ρ) (φ.σ o) t = (R π ρ o t).map φ.σ.toEmbedding := by
  ext x
  simp only [R, Finset.mem_image, Finset.mem_map, Equiv.coe_toEmbedding, X_act]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨X π ρ o s, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨s, hs, rfl⟩

theorem visits_act (ρ : Config G) (o : V) (t : ℕ) :
    visits π (φ.act ρ) (φ.σ o) t = visits π ρ o t := by
  unfold visits
  congr 1
  ext s
  simp [X_act, φ.σ.injective.eq_iff]

section
variable [G.LocallyFinite]

omit [DecidableEq V] in
theorem degree_act (v : V) : G.degree (φ.σ v) = G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  refine Fintype.card_congr ⟨fun a => ⟨φ.σ.symm a.1, ?_⟩, φ.nbr, ?_, ?_⟩
  · have := (φ.adj v (φ.σ.symm a.1)).1
    rw [φ.σ.apply_symm_apply] at this
    exact this a.2
  · intro a; apply Subtype.ext; simp [nbr]
  · intro a; apply Subtype.ext; simp [nbr]

theorem T_act (ρ : Config G) (o : V) (n : ℕ) : T π (φ.act ρ) (φ.σ o) n = T π ρ o n := by
  unfold T
  congr 1
  ext t
  simp [X_act, visits_act, degree_act, φ.σ.injective.eq_iff]

theorem A_act (ρ : Config G) (o : V) (n : ℕ) :
    A π (φ.act ρ) (φ.σ o) n = (A π ρ o n).map φ.σ.toEmbedding := by
  rw [A, A, T_act, R_act]

end

theorem recurrent_act (ρ : Config G) (o : V) :
    Recurrent π (φ.act ρ) (φ.σ o) ↔ Recurrent π ρ o := by
  unfold Recurrent
  constructor
  · intro h x
    have := h (φ.σ x)
    simpa [X_act, φ.σ.injective.eq_iff] using this
  · intro h x
    have := h (φ.σ.symm x)
    simpa [X_act, Equiv.apply_eq_iff_eq_symm_apply] using this

/-! ### Routings -/

/-- Transport of a particle-and-rotor state. -/
def actState (ξ : RState G) : RState G := ⟨fun v => ξ.σ (φ.σ.symm v), φ.act ξ.ρ⟩

omit [DecidableEq V] in
@[simp] theorem actState_σ (ξ : RState G) (v : V) : (φ.actState ξ).σ (φ.σ v) = ξ.σ v := by
  simp [actState]

omit [DecidableEq V] in
@[simp] theorem actState_ρ (ξ : RState G) : (φ.actState ξ).ρ = φ.act ξ.ρ := rfl

omit [DecidableEq V] in
theorem mem_map_iff (S : Finset V) (v : V) : φ.σ v ∈ S.map φ.σ.toEmbedding ↔ v ∈ S := by
  simp

omit [DecidableEq V] in
theorem RState_ext {ξ ξ' : RState G} (h1 : ξ.σ = ξ'.σ) (h2 : ξ.ρ = ξ'.ρ) : ξ = ξ' := by
  cases ξ; cases ξ'; simp only at h1 h2; subst h1; subst h2; rfl

theorem actuate_act (S : Finset V) (ξ : RState G) (v : V) :
    actuate π (S.map φ.σ.toEmbedding) (φ.actState ξ) (φ.σ v) = φ.actState (actuate π S ξ v) := by
  refine RState_ext ?_ ?_
  · funext w
    obtain ⟨u, rfl⟩ := φ.σ.surjective w
    simp only [actuate, actState, Equiv.symm_apply_apply, act_apply, next_val,
      φ.σ.injective.eq_iff, mem_map_iff]
  · simp only [actuate, actState_ρ, act_update, act_apply]
    congr 1
    exact Subtype.ext (φ.next_val _ _)

theorem run_act (S : Finset V) (ξ : RState G) (vs : List V) :
    run π (S.map φ.σ.toEmbedding) (φ.actState ξ) (vs.map φ.σ) = φ.actState (run π S ξ vs) := by
  induction vs generalizing ξ with
  | nil => rfl
  | cons v vs ih => rw [List.map_cons, run_cons, run_cons, actuate_act, ih]

theorem isLegal_act (S : Finset V) (ξ : RState G) (vs : List V) :
    IsLegal π (S.map φ.σ.toEmbedding) (φ.actState ξ) (vs.map φ.σ) ↔ IsLegal π S ξ vs := by
  induction vs generalizing ξ with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, isLegal_cons, isLegal_cons, mem_map_iff, actState_σ, actuate_act, ih]

omit [DecidableEq V] in
theorem stable_act (S : Finset V) (ξ : RState G) :
    Stable (S.map φ.σ.toEmbedding) (φ.actState ξ) ↔ Stable S ξ := by
  unfold Stable
  constructor
  · intro h v hv
    have := h (φ.σ v) (by rwa [mem_map_iff])
    rwa [actState_σ] at this
  · intro h w hw
    obtain ⟨v, rfl⟩ := φ.σ.surjective w
    rw [actState_σ]
    exact h v (by rwa [mem_map_iff] at hw)

theorem boundaryInit_act (S : Finset V) (ρ : Config G) :
    boundaryInit (S.map φ.σ.toEmbedding) (φ.act ρ) = φ.actState (boundaryInit S ρ) := by
  classical
  refine RState_ext ?_ rfl
  funext w
  obtain ⟨v, rfl⟩ := φ.σ.surjective w
  simp only [boundaryInit, actState, Equiv.symm_apply_apply, mem_map_iff]
  split_ifs with hv
  · rfl
  · apply Finset.card_bij (fun s _ => φ.σ.symm s)
    · intro s hs
      rw [Finset.mem_filter, Finset.mem_map] at hs
      obtain ⟨⟨t, ht, rfl⟩, hadj⟩ := hs
      rw [Finset.mem_filter]
      refine ⟨by simpa using ht, ?_⟩
      have := (φ.adj t v).1
      simpa using this hadj
    · intro s₁ _ s₂ _ h
      exact φ.σ.symm.injective h
    · intro t ht
      rw [Finset.mem_filter] at ht
      refine ⟨φ.σ t, Finset.mem_filter.2 ⟨Finset.mem_map_of_mem _ ht.1, (φ.adj t v).2 ht.2⟩, by simp⟩

theorem terminates_act (S : Finset V) (ρ : Config G) :
    Terminates π (S.map φ.σ.toEmbedding) (φ.act ρ) ↔ Terminates π S ρ := by
  constructor
  · rintro ⟨ws, hws⟩
    refine ⟨ws.map φ.σ.symm, ?_⟩
    have hws' : ws = (ws.map φ.σ.symm).map φ.σ := by simp [List.map_map]
    rw [hws', boundaryInit_act] at hws
    exact ⟨(φ.isLegal_act _ _ _).1 hws.1, by
      have := hws.2; rw [run_act, stable_act] at this; exact this⟩
  · rintro ⟨vs, hvs⟩
    refine ⟨vs.map φ.σ, ?_⟩
    rw [boundaryInit_act]
    exact ⟨(φ.isLegal_act _ _ _).2 hvs.1, by rw [run_act, stable_act]; exact hvs.2⟩

theorem allTerminate_act (ρ : Config G) : AllTerminate π (φ.act ρ) ↔ AllTerminate π ρ := by
  constructor
  · intro h S hS
    have := h (S.map φ.σ.toEmbedding) (by simpa using hS)
    rwa [terminates_act] at this
  · intro h S hS
    have hS' : S = (S.map φ.σ.symm.toEmbedding).map φ.σ.toEmbedding := by
      ext x; simp
    rw [hS', terminates_act]
    exact h _ (by simpa using hS)

/-! ### The circuit map, distances and the passage time -/

theorem Φ_act (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite] (hG : G.Connected)
    (ρ : Config G) (S : Finset V) (hS : S.Nonempty) :
    Φ π (φ.act ρ) (S.map φ.σ.toEmbedding) = (Φ π ρ S).map φ.σ.toEmbedding := by
  by_cases hT : Terminates π S ρ
  · have hT' : Terminates π (S.map φ.σ.toEmbedding) (φ.act ρ) := (φ.terminates_act S ρ).2 hT
    have hS' : (S.map φ.σ.toEmbedding).Nonempty := by simpa using hS
    ext w
    obtain ⟨x, rfl⟩ := φ.σ.surjective w
    rw [mem_map_iff φ (Φ π ρ S) x]
    constructor
    · intro hx
      rcases mem_Φ_imp π (φ.act ρ) _ _ hx with h | ⟨ws, hws, hxws⟩
      · exact subset_Φ π ρ S ((mem_map_iff φ S x).1 h)
      · have hws' : ws = (ws.map φ.σ.symm).map φ.σ := by simp [List.map_map]
        rw [hws', boundaryInit_act] at hws
        have hc : IsComplete π S (boundaryInit S ρ) (ws.map φ.σ.symm) :=
          ⟨(φ.isLegal_act _ _ _).1 hws.1, by
            have := hws.2; rwa [run_act, stable_act] at this⟩
        have hx' : x ∈ ws.map φ.σ.symm := by
          rw [List.mem_map]
          exact ⟨φ.σ x, hxws, by simp⟩
        exact mem_Φ_of_mem_complete π hAb hG S hS ρ _ hc x hx'
    · intro hx
      rcases mem_Φ_imp π ρ S x hx with h | ⟨ws, hws, hxws⟩
      · exact subset_Φ π _ _ ((mem_map_iff φ S x).2 h)
      · have hc : IsComplete π (S.map φ.σ.toEmbedding)
            (boundaryInit (S.map φ.σ.toEmbedding) (φ.act ρ)) (ws.map φ.σ) := by
          rw [boundaryInit_act]
          exact ⟨(φ.isLegal_act _ _ _).2 hws.1, by rw [run_act, stable_act]; exact hws.2⟩
        exact mem_Φ_of_mem_complete π hAb hG _ hS' _ _ hc _ (List.mem_map_of_mem hxws)
  · have hT' : ¬ Terminates π (S.map φ.σ.toEmbedding) (φ.act ρ) :=
      fun h => hT ((φ.terminates_act S ρ).1 h)
    unfold Φ
    rw [dif_neg hT, dif_neg hT']

theorem Φ_iterate_act (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite] (hG : G.Connected)
    (ρ : Config G) (S : Finset V) (hS : S.Nonempty) (n : ℕ) :
    (Φ π (φ.act ρ))^[n] (S.map φ.σ.toEmbedding) = ((Φ π ρ)^[n] S).map φ.σ.toEmbedding := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Φ_act φ hAb hG ρ _ (nonempty_Φ_iterate π ρ S hS n)]

/-- The automorphism as a graph isomorphism. -/
def iso : G ≃g G := ⟨φ.σ, fun {u v} => φ.adj u v⟩

omit [DecidableEq V] in
theorem dist_act (hG : G.Connected) (x y : V) : G.dist (φ.σ x) (φ.σ y) = G.dist x y := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := (hG.preconnected x y).exists_walk_length_eq_dist
    have := G.dist_le (p.map φ.iso.toHom)
    rwa [SimpleGraph.Walk.length_map, hp] at this
  · obtain ⟨p, hp⟩ := (hG.preconnected (φ.σ x) (φ.σ y)).exists_walk_length_eq_dist
    have := G.dist_le (p.map φ.iso.symm.toHom)
    rw [SimpleGraph.Walk.length_map, hp] at this
    have e1 : φ.iso.symm (φ.σ x) = x := φ.σ.symm_apply_apply x
    have e2 : φ.iso.symm (φ.σ y) = y := φ.σ.symm_apply_apply y
    simpa [e1, e2] using this

theorem τ_act (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite] (hG : G.Connected)
    (ρ : Config G) (x y : V) : τ π (φ.act ρ) (φ.σ x) (φ.σ y) = τ π ρ x y := by
  by_cases hall : AllTerminate π ρ
  · have hall' : AllTerminate π (φ.act ρ) := (φ.allTerminate_act ρ).2 hall
    rw [τ_of_allTerminate π _ hall', τ_of_allTerminate π ρ hall]
    congr 1
    ext n
    have h1 : ({φ.σ x} : Finset V) = ({x} : Finset V).map φ.σ.toEmbedding := by simp
    simp only [Set.mem_setOf_eq]
    rw [h1, Φ_iterate_act φ hAb hG ρ {x} (by simp) n, mem_map_iff φ]
  · have hall' : ¬ AllTerminate π (φ.act ρ) := fun h => hall ((φ.allTerminate_act ρ).1 h)
    rw [τ_of_not_allTerminate π _ hall', τ_of_not_allTerminate π ρ hall, dist_act φ hG]

end MechAut

/-! ### Lattice translations as automorphisms -/

namespace DoublyPeriodic

variable (P : DoublyPeriodic G)

/-- The translation by `z` of a doubly periodic graph with a doubly periodic
mechanism. -/
def mechAut (π : Mechanism G) (hπ : P.Periodic π) (z : ℤ × ℤ) : MechAut π where
  σ := ⟨P.shift z, P.shift (-z), P.shift_shift_neg z, P.shift_neg_shift z⟩
  adj u v := P.adj_shift z u v
  next v a := congrArg Subtype.val (hπ z v a)

omit [DecidableEq V] in
@[simp] theorem mechAut_σ (π : Mechanism G) (hπ : P.Periodic π) (z : ℤ × ℤ) (v : V) :
    (P.mechAut π hπ z).σ v = P.shift z v := rfl

omit [DecidableEq V] in
theorem mechAut_act (π : Mechanism G) (hπ : P.Periodic π) (z : ℤ × ℤ) (ρ : Config G) :
    (P.mechAut π hπ z).act ρ = P.shiftConfig z ρ := rfl

end DoublyPeriodic

end Rotor

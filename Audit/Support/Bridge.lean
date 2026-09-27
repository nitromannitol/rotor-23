import Mathlib
import Rotor.MainTheorems
import Audit.Support.Vocabulary

/-!
# Bridges from the Mathlib-only vocabulary to the repository

The challenge vocabulary (`Audit/Support/Vocabulary.lean`, namespace
`RotorAudit`) is a statement-level copy of the repository definitions.  Plain
definitions over shared Mathlib types (`squareGraph`, `uniformLaw`, `tvDist`,
`Kingman`, `LSS`, …) are definitionally equal to their repository
counterparts.  The four structures (`Mechanism`, `State`, `RState`,
`DoublyPeriodic`) are new inductive types, so this file converts between them
field by field and proves, by induction on time and on routing lists, that the
walk, its range, circuit times, circuit ranges, recurrence, traversals,
departures and routings agree.  From these, each cited-result proposition of the
vocabulary implies the repository's.
-/

universe u

namespace RotorAudit.Bridge

open MeasureTheory

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A vocabulary mechanism as a repository mechanism. -/
def toMech (π : RotorAudit.Mechanism G) : Rotor.Mechanism G := ⟨π.next, π.cyclic, π.nonempty⟩

/-- A repository mechanism as a vocabulary mechanism. -/
def ofMech (π : Rotor.Mechanism G) : RotorAudit.Mechanism G := ⟨π.next, π.cyclic, π.nonempty⟩

omit [DecidableEq V] in
@[simp] theorem toMech_ofMech (π : Rotor.Mechanism G) : toMech (ofMech π) = π := rfl

theorem step_eq (π : RotorAudit.Mechanism G) (s : RotorAudit.State G) (s' : Rotor.State G)
    (hp : s.pos = s'.pos) (hr : s.rotor = s'.rotor) :
    (RotorAudit.step π s).pos = (Rotor.step (toMech π) s').pos ∧
    (RotorAudit.step π s).rotor = (Rotor.step (toMech π) s').rotor := by
  obtain ⟨p, r⟩ := s
  obtain ⟨p', r'⟩ := s'
  simp only at hp hr
  subst hp hr
  exact ⟨rfl, rfl⟩

theorem walk_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) (t : ℕ) :
    (RotorAudit.walk π ρ o t).pos = (Rotor.walk (toMech π) ρ o t).pos ∧
    (RotorAudit.walk π ρ o t).rotor = (Rotor.walk (toMech π) ρ o t).rotor := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    have h1 : RotorAudit.walk π ρ o (t + 1) = RotorAudit.step π (RotorAudit.walk π ρ o t) :=
      Function.iterate_succ_apply' ..
    have h2 : Rotor.walk (toMech π) ρ o (t + 1) =
        Rotor.step (toMech π) (Rotor.walk (toMech π) ρ o t) :=
      Function.iterate_succ_apply' ..
    rw [h1, h2]
    exact step_eq π _ _ ih.1 ih.2

theorem X_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) (t : ℕ) :
    RotorAudit.X π ρ o t = Rotor.X (toMech π) ρ o t :=
  (walk_eq π ρ o t).1

theorem R_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) (t : ℕ) :
    RotorAudit.R π ρ o t = Rotor.R (toMech π) ρ o t := by
  unfold RotorAudit.R Rotor.R
  congr 1
  funext s
  exact X_eq π ρ o s

theorem visits_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) (t : ℕ) :
    RotorAudit.visits π ρ o t = Rotor.visits (toMech π) ρ o t := by
  simp only [RotorAudit.visits, Rotor.visits, X_eq]

theorem T_eq [G.LocallyFinite] (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V)
    (n : ℕ) : RotorAudit.T π ρ o n = Rotor.T (toMech π) ρ o n := by
  simp only [RotorAudit.T, Rotor.T, X_eq, visits_eq]

theorem A_eq [G.LocallyFinite] (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V)
    (n : ℕ) : RotorAudit.A π ρ o n = Rotor.A (toMech π) ρ o n := by
  simp only [RotorAudit.A, Rotor.A, T_eq, R_eq]

theorem Recurrent_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) :
    RotorAudit.Recurrent π ρ o = Rotor.Recurrent (toMech π) ρ o := by
  simp only [RotorAudit.Recurrent, Rotor.Recurrent, X_eq]

theorem traversal_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) (t : ℕ) :
    RotorAudit.traversal π ρ o t = Rotor.traversal (toMech π) ρ o t := by
  simp only [RotorAudit.traversal, Rotor.traversal, X_eq]

theorem departures_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o x : V)
    (a b : ℕ) : RotorAudit.departures π ρ o x a b = Rotor.departures (toMech π) ρ o x a b := by
  simp only [RotorAudit.departures, Rotor.departures, X_eq]

/-- A vocabulary particle-and-rotor state as a repository one. -/
def toRS (ξ : RotorAudit.RState G) : Rotor.RState G := ⟨ξ.σ, ξ.ρ⟩

/-- A repository particle-and-rotor state as a vocabulary one. -/
def ofRS (ξ : Rotor.RState G) : RotorAudit.RState G := ⟨ξ.σ, ξ.ρ⟩

omit [DecidableEq V] in
@[simp] theorem toRS_ofRS (ξ : Rotor.RState G) : toRS (ofRS ξ) = ξ := rfl

omit [DecidableEq V] in
theorem toRS_injective : Function.Injective (toRS (G := G)) := by
  rintro ⟨σ, ρ⟩ ⟨σ', ρ'⟩ h
  simp only [toRS, Rotor.RState.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem actuate_eq (π : RotorAudit.Mechanism G) (S : Finset V) (ξ : RotorAudit.RState G) (v : V) :
    toRS (RotorAudit.actuate π S ξ v) = Rotor.actuate (toMech π) S (toRS ξ) v := rfl

theorem run_eq (π : RotorAudit.Mechanism G) (S : Finset V) (vs : List V) :
    ∀ ξ : RotorAudit.RState G,
      toRS (RotorAudit.run π S ξ vs) = Rotor.run (toMech π) S (toRS ξ) vs := by
  induction vs with
  | nil => intro ξ; rfl
  | cons v vs ih =>
    intro ξ
    simp only [RotorAudit.run, Rotor.run]
    rw [ih, actuate_eq]

theorem isLegal_iff (π : RotorAudit.Mechanism G) (S : Finset V) (vs : List V) :
    ∀ ξ : RotorAudit.RState G,
      RotorAudit.IsLegal π S ξ vs ↔ Rotor.IsLegal (toMech π) S (toRS ξ) vs := by
  induction vs with
  | nil => intro ξ; simp [RotorAudit.IsLegal, Rotor.IsLegal]
  | cons v vs ih =>
    intro ξ
    simp only [RotorAudit.IsLegal, Rotor.IsLegal]
    rw [ih, actuate_eq]
    rfl

omit [DecidableEq V] in
theorem stable_iff (S : Finset V) (ξ : RotorAudit.RState G) :
    RotorAudit.Stable S ξ ↔ Rotor.Stable S (toRS ξ) := Iff.rfl

/-! ### The cited-result propositions -/

theorem oneCircuit [G.LocallyFinite] (h : RotorAudit.External.OneCircuit G) :
    Rotor.External.OneCircuit G := by
  intro π hG ρ o n
  have := h (ofMech π) hG ρ o n
  simp only [T_eq, A_eq, traversal_eq, departures_eq, toMech_ofMech] at this
  exact this

theorem abelian (h : RotorAudit.External.Abelian G) : Rotor.External.Abelian G := by
  intro π hV hG S hS ξ vs ws hvs hws
  have hvs' : RotorAudit.IsLegal (ofMech π) S (ofRS ξ) vs := (isLegal_iff _ S vs _).2 hvs
  have hws' : RotorAudit.IsLegal (ofMech π) S (ofRS ξ) ws := (isLegal_iff _ S ws _).2 hws
  obtain ⟨h1, h2⟩ := h (ofMech π) hV hG S hS (ofRS ξ) vs ws hvs' hws'
  have hr : ∀ us, Rotor.run π S ξ us = toRS (RotorAudit.run (ofMech π) S (ofRS ξ) us) := by
    intro us; rw [run_eq]; rfl
  refine ⟨fun hst => h1 ?_, fun hst hst' => ?_⟩
  · rw [stable_iff, ← hr]; exact hst
  · obtain ⟨e1, e2, e3⟩ := h2 (by rw [stable_iff, ← hr]; exact hst)
      (by rw [stable_iff, ← hr]; exact hst')
    exact ⟨e1, by rw [hr, hr, e2], e3⟩

theorem visitsAllOfVisitsOne (h : RotorAudit.External.VisitsAllOfVisitsOne G) :
    Rotor.External.VisitsAllOfVisitsOne G := by
  intro π hV hG ρ o x
  have := h (ofMech π) hV hG ρ o x
  simp only [X_eq, Recurrent_eq, toMech_ofMech] at this
  exact this

theorem recurrentOfRecurrent (h : RotorAudit.External.RecurrentOfRecurrent G) :
    Rotor.External.RecurrentOfRecurrent G := by
  intro π hV hG ρ o o'
  have := h (ofMech π) hV hG ρ o o'
  simp only [Recurrent_eq, toMech_ofMech] at this
  exact this

end General

theorem lss (h : RotorAudit.External.LSS) : Rotor.External.LSS := h

/-! ### Laws and doubly periodic data -/

section Laws

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem uniformAt_eq (π : RotorAudit.Mechanism G) (v : V) :
    RotorAudit.uniformAt π v = Rotor.uniformAt (toMech π) v := rfl

theorem uniformLaw_eq (π : RotorAudit.Mechanism G) :
    RotorAudit.uniformLaw π = Rotor.uniformLaw (toMech π) := rfl

omit [G.LocallyFinite] in
theorem productLaw_eq (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] : RotorAudit.productLaw ν = Rotor.productLaw ν := rfl

end Laws

section Periodic

variable {V : Type*} {G : SimpleGraph V}

/-- Vocabulary doubly periodic data as repository data. -/
def toDP (P : RotorAudit.DoublyPeriodic G) : Rotor.DoublyPeriodic G :=
  ⟨P.emb, P.emb_injective, P.shift, P.shift_zero, P.shift_add, P.b, P.b_indep, P.emb_shift,
    P.adj_shift, P.rep, P.coord, P.shift_coord_rep, P.rep_shift, P.finite_orbits⟩

theorem periodic_iff (P : RotorAudit.DoublyPeriodic G) (π : RotorAudit.Mechanism G) :
    P.Periodic π ↔ (toDP P).Periodic (toMech π) := Iff.rfl

theorem invariantMarginals_iff (P : RotorAudit.DoublyPeriodic G)
    (ν : ∀ v : V, Measure (G.neighborSet v)) :
    P.InvariantMarginals ν ↔ (toDP P).InvariantMarginals ν := Iff.rfl

end Periodic

/-! ### The concrete graphs and mechanisms -/

theorem squareGraph_eq : RotorAudit.squareGraph = Rotor.squareGraph := rfl

theorem toMech_clockwise : toMech RotorAudit.clockwise = Rotor.clockwise := rfl

theorem toDP_squarePeriodic : toDP RotorAudit.squarePeriodic = Rotor.squarePeriodic := rfl

theorem pendantGraph_eq (M : ℕ) : RotorAudit.pendantGraph M = Rotor.pendantGraph M := rfl

theorem toMech_pendantMech (M : ℕ) : toMech (RotorAudit.pendantMech M) = Rotor.pendantMech M :=
  rfl

end RotorAudit.Bridge

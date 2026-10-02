import Mathlib
import Rotor.MainTheorems
import RotorAudit.PendantCounterexample.SolutionBasic

/-!
# Bridge for `PendantCounterexample`: Mathlib-only vocabulary to the repository

The challenge vocabulary (namespace `RotorAudit`) is a statement-level copy of the repository
definitions.  It is compiled in `RotorAudit/PendantCounterexample/SolutionBasic.lean`, a verbatim
copy of the vocabulary block of `RotorAudit/PendantCounterexample/Challenge.lean`, which imports
only Mathlib.  This file is imported by `RotorAudit/PendantCounterexample/Solution.lean` only.

The statement of `PendantCounterexample` mentions the rotor walk, recurrence and the uniform
law of the initial rotors, on the graph `G_M` with its mechanism.  The vocabulary structure
`Mechanism` is a new inductive type, so `toMech` converts a vocabulary mechanism into a
repository one field by field, and `step_eq`, `walk_eq` (induction on time), `X_eq` and
`Recurrent_eq` prove, rather than assume, that the walk and recurrence agree.
`uniformLaw_eq` and `toMech_pendantMech` are `rfl`.  The statement carries no cited result.
-/

namespace RotorAudit.Bridge

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A vocabulary mechanism as a repository mechanism. -/
def toMech (π : RotorAudit.Mechanism G) : Rotor.Mechanism G := ⟨π.next, π.cyclic, π.nonempty⟩

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

theorem Recurrent_eq (π : RotorAudit.Mechanism G) (ρ : RotorAudit.Config G) (o : V) :
    RotorAudit.Recurrent π ρ o = Rotor.Recurrent (toMech π) ρ o := by
  simp only [RotorAudit.Recurrent, Rotor.Recurrent, X_eq]

end General

section Laws

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem uniformLaw_eq (π : RotorAudit.Mechanism G) :
    RotorAudit.uniformLaw π = Rotor.uniformLaw (toMech π) := rfl

end Laws

theorem toMech_pendantMech (M : ℕ) : toMech (RotorAudit.pendantMech M) = Rotor.pendantMech M :=
  rfl

end RotorAudit.Bridge

import Mathlib
import Rotor.MainTheorems
import RotorAudit.PerturbationsSquare.SolutionBasic

/-!
# Bridge for `PerturbationsSquare`: Mathlib-only vocabulary to the repository

The challenge vocabulary (namespace `RotorAudit`) is a statement-level copy of the repository
definitions.  It is compiled in `RotorAudit/PerturbationsSquare/SolutionBasic.lean`, a verbatim
copy of the vocabulary block of `RotorAudit/PerturbationsSquare/Challenge.lean`, which imports
only Mathlib.  This file is imported by `RotorAudit/PerturbationsSquare/Solution.lean` only.

The statement of `PerturbationsSquare` mentions the rotor walk, its range, circuit times
and circuit ranges and recurrence, on the square lattice with its clockwise mechanism, under
product laws of the initial rotors close to uniform.  The vocabulary structure `Mechanism` is a
new inductive type, so `toMech` converts a vocabulary mechanism into a repository one field by
field, and `step_eq`, `walk_eq` (induction on time), `X_eq`, `R_eq`, `visits_eq`, `T_eq`, `A_eq`
and `Recurrent_eq` prove, rather than assume, that the walk, the range, the circuit times, the
circuit ranges and recurrence agree.  `toMech_clockwise` is `rfl`, and `lss` is the identity on
the cited result `LSS`, whose two copies are definitionally equal.  Nothing is asserted.
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

end General

theorem lss (h : RotorAudit.External.LSS) : Rotor.External.LSS := h

theorem toMech_clockwise : toMech RotorAudit.clockwise = Rotor.clockwise := rfl

end RotorAudit.Bridge

/-
Model guards: computable witnesses that the definitions of `Rotor/Basic.lean`
say what the paper says.  The dominant failure mode of a formalization is a
vacuous or mistranscribed statement, not a wrong proof, so each guard pins one
value that can be checked by hand against the paper.
-/
import Rotor.Basic

namespace Rotor.Z2

/-- With every rotor initially pointing north, the first step turns the rotor at
the origin to east and moves the walker to `(1, 0)`: `rotor.tex:189-201` and
Figure `fig:mechanism`. -/
theorem X_allNorth_one : X (fun _ => (0 : Dir)) (0, 0) 1 = (1, 0) := by
  decide

/-- The rotor at the origin has been turned to east after one step. -/
theorem rot_allNorth_one : rot (fun _ => (0 : Dir)) (0, 0) 1 (0, 0) = 1 := by
  decide

/-- With all rotors north the walker never returns: every rotor it meets turns
to east, so after four steps it is at `(4, 0)`.  (A first draft of this guard
claimed a return to the origin; `decide` refuted it.  Recorded so the mistake is
not repeated.) -/
theorem X_allNorth_four : X (fun _ => (0 : Dir)) (0, 0) 4 = (4, 0) := by
  decide

/-- `T(0) = 0`: zero circuits are complete at time `0`. -/
theorem T_zero (ρ : RotorConfig) (o : Site) : T ρ o 0 = 0 :=
  le_antisymm (iInf₂_le (0 : ℕ) ⟨rfl, Nat.zero_le _⟩) zero_le

/-- `A_0 = {o}`, `rotor.tex:222-223`. -/
theorem A_zero (ρ : RotorConfig) (o : Site) : A ρ o 0 = {o} := by
  simp [A, T_zero, R, X, walk]

end Rotor.Z2

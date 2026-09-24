/-
Model guards: computable witnesses that the definitions of `Rotor/Basic.lean`
say what the paper says.  Each guard pins one value that can be checked by
hand against the paper.
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

/-- With all rotors north, every rotor the walker meets turns to east, so
after four steps the walker is at `(4, 0)`. -/
theorem X_allNorth_four : X (fun _ => (0 : Dir)) (0, 0) 4 = (4, 0) := by
  decide

/-- `T(0) = 0`: zero circuits are complete at time `0`. -/
theorem T_zero (ρ : RotorConfig) (o : Site) : T ρ o 0 = 0 :=
  le_antisymm (iInf₂_le (0 : ℕ) ⟨rfl, Nat.zero_le _⟩) zero_le

/-- `A_0 = {o}`, `rotor.tex:222-223`. -/
theorem A_zero (ρ : RotorConfig) (o : Site) : A ρ o 0 = {o} := by
  simp [A, T_zero, R, X, walk]

end Rotor.Z2

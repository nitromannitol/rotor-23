import Rotor.Support.SquareBasics
import Rotor.Support.WalkBasics
import Rotor.Support.Exploration4

/-!
The exits of the clockwise rotor walk on `ℤ²` (`rotor.tex:2264-2266`): "the edges in `F` with
tail `v` are the first `k(v)` edges after `ρ(v)`".  The rotor at `v` after `j` departures from
`v` points `j` positions clockwise of the initial rotor, and the `j`-th departure leaves in
the direction `ρ(v) + j`.
-/

open Finset Fin.NatCast

namespace Rotor

variable (σ : Config squareGraph) (o : Site)

/-- The number of departures from `v` before time `t`. -/
def deps (v : Site) (t : ℕ) : ℕ := ((range t).filter (fun s => X clockwise σ o s = v)).card

theorem deps_succ (v : Site) (t : ℕ) :
    deps σ o v (t + 1) = deps σ o v t + if X clockwise σ o t = v then 1 else 0 := by
  unfold deps
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

/-- The initial direction of the rotor at `v`. -/
def dir0 (v : Site) : Dir := (nbr v).symm (σ v)

/-- The rotor at `v` at time `t` points `deps v t` positions clockwise of the initial rotor. -/
theorem rot_eq_deps (v : Site) : ∀ t : ℕ,
    rot clockwise σ o t v = nbr v (dir0 σ v + (deps σ o v t : Dir))
  | 0 => by simp [dir0, deps]
  | t + 1 => by
    rw [rot_succ, deps_succ]
    by_cases h : X clockwise σ o t = v
    · subst h
      rw [Function.update_self, rot_eq_deps _ t]
      simp only [if_true]
      show turnAt _ _ = _
      rw [turnAt_nbr]
      congr 1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_natCast, Fin.val_one]
      omega
    · rw [Function.update_of_ne (Ne.symm h), rot_eq_deps v t]
      simp [h]

/-- The departure at time `t` from `X_t` goes in the direction one step clockwise of the current
rotor. -/
theorem X_succ_eq (t : ℕ) :
    X clockwise σ o (t + 1) =
      X clockwise σ o t + dirVec (dir0 σ (X clockwise σ o t) + (deps σ o (X clockwise σ o t) t : Dir) + 1) := by
  rw [X_succ, rot_eq_deps]
  show (turnAt _ _).1 = _
  rw [turnAt_nbr]
  rfl

end Rotor

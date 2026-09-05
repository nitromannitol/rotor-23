/-
The square lattice with the clockwise rotor mechanism, as an instance of the
general model of `Rotor/Model.lean`.

`rotor.tex:202-203`: "On the square lattice, the clockwise rotor mechanism has
cyclic order `N, E, S, W`."  The concrete encoding of `Rotor/Basic.lean`
(directions `Fin 4`, `0 = N, 1 = E, 2 = S, 3 = W`, clockwise `= +1`) is
transported to the neighbor sets of the lattice graph.
-/
import Rotor.Model
import Rotor.Basic

open Fin.NatCast

namespace Rotor

/-- The square lattice as a simple graph on `ℤ × ℤ`: `x ∼ y` when they differ
by a unit step. -/
def squareGraph : SimpleGraph Site where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm x y h := by
    show |y.1 - x.1| + |y.2 - x.2| = 1
    rw [abs_sub_comm y.1, abs_sub_comm y.2]; exact h
  loopless x h := by simp at h

theorem squareGraph_adj (x y : Site) : squareGraph.Adj x y ↔ |x.1 - y.1| + |x.2 - y.2| = 1 :=
  Iff.rfl

instance : DecidableRel squareGraph.Adj := fun x y => by
  unfold squareGraph; exact inferInstanceAs (Decidable (_ = _))

theorem adj_add_dirVec (v : Site) (a : Dir) : squareGraph.Adj v (v + dirVec a) := by
  rw [squareGraph_adj]
  fin_cases a <;> simp [dirVec]

/-- The direction of a unit step `d`: the inverse of `dirVec` on unit steps. -/
def dirOf (d : Site) : Dir :=
  if d = (0, 1) then 0 else if d = (1, 0) then 1 else if d = (0, -1) then 2 else 3

theorem dirOf_dirVec (a : Dir) : dirOf (dirVec a) = a := by
  fin_cases a <;> simp [dirOf, dirVec]

theorem dirVec_dirOf_of_adj {v w : Site} (h : squareGraph.Adj v w) :
    v + dirVec (dirOf (w - v)) = w := by
  rw [squareGraph_adj] at h
  obtain ⟨a, b⟩ := v
  obtain ⟨c, d⟩ := w
  simp only [Prod.mk_sub_mk, dirOf, dirVec, Prod.mk.injEq] at h ⊢
  rcases abs_cases (a - c) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases (b - d) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
  · split_ifs <;> simp_all <;> omega

/-- The four neighbors of a lattice site, indexed by direction. -/
def nbr (v : Site) : Dir ≃ squareGraph.neighborSet v where
  toFun a := ⟨v + dirVec a, adj_add_dirVec v a⟩
  invFun w := dirOf (w.1 - v)
  left_inv a := by simp [dirOf_dirVec]
  right_inv w := Subtype.ext (dirVec_dirOf_of_adj w.2)

instance : squareGraph.LocallyFinite := fun v => Fintype.ofEquiv Dir (nbr v)

/-- Turning by one direction, transported to the neighbors of `v`. -/
def turnAt (v : Site) : Equiv.Perm (squareGraph.neighborSet v) :=
  (nbr v).symm.trans ((Equiv.addRight (1 : Dir)).trans (nbr v))

theorem turnAt_nbr (v : Site) (a : Dir) : turnAt v (nbr v a) = nbr v (a + 1) := by
  simp [turnAt]

theorem turnAt_pow_nbr (v : Site) (k : ℕ) (a : Dir) :
    ((turnAt v) ^ k) (nbr v a) = nbr v (a + (k : Dir)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, turnAt_nbr]
    congr 1
    rw [Nat.cast_succ, add_assoc]

/-- The clockwise rotor mechanism on the square lattice: turn by one direction. -/
def clockwise : Mechanism squareGraph where
  next v := turnAt v
  cyclic v a b := by
    obtain ⟨i, rfl⟩ := (nbr v).surjective a
    obtain ⟨j, rfl⟩ := (nbr v).surjective b
    refine ⟨(j - i).val, ?_⟩
    rw [turnAt_pow_nbr, Fin.cast_val_eq_self]
    congr 1
    exact add_sub_cancel i j
  nonempty v := ⟨nbr v 0⟩

end Rotor

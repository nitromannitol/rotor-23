/-
Basic facts about routings (Section 2.1), used by the proofs of
`lem:boundary-routing`, `prop:circuit-iterate`, `prop:monotonicity` and
`prop:passage`.
-/
import Rotor.Traversal

/-!
# Basic facts about legal routings

Elementary lemmas about running a routing (`run`) and legality (`IsLegal`) of a chip
configuration under a sequence of actuations: running is compatible with list concatenation and
prefixes, and the rotor and chip count at a vertex change under an actuation elsewhere in a way
that depends only on that actuation's mechanism step. These facts are the common lemmas behind
`lem:boundary-routing`, `prop:circuit-iterate`, `prop:monotonicity` and `prop:passage`.
-/

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### Running a routing -/

/-- Running the empty routing list leaves the state `ξ` unchanged. -/
@[simp] theorem run_nil (S : Finset V) (ξ : RState G) : run π S ξ [] = ξ := rfl

/-- Running `v :: vs` actuates `v` first, then runs `vs` from the resulting state. -/
@[simp] theorem run_cons (S : Finset V) (ξ : RState G) (v : V) (vs : List V) :
    run π S ξ (v :: vs) = run π S (actuate π S ξ v) vs := rfl

/-- Running a concatenated routing `vs ++ ws` is running `vs` followed by running `ws` from the
resulting state. -/
theorem run_append (S : Finset V) (ξ : RState G) (vs ws : List V) :
    run π S ξ (vs ++ ws) = run π S (run π S ξ vs) ws := by
  induction vs generalizing ξ with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- The empty routing list is always legal. -/
@[simp] theorem isLegal_nil (S : Finset V) (ξ : RState G) : IsLegal π S ξ [] := trivial

/-- `v :: vs` is a legal routing iff `v` lies outside `S`, has a positive chip count, and `vs` is
legal from the state after actuating `v`. -/
theorem isLegal_cons (S : Finset V) (ξ : RState G) (v : V) (vs : List V) :
    IsLegal π S ξ (v :: vs) ↔ v ∉ S ∧ 0 < ξ.σ v ∧ IsLegal π S (actuate π S ξ v) vs := Iff.rfl

/-- A concatenated routing `vs ++ ws` is legal iff `vs` is legal and `ws` is legal from the state
after running `vs`. -/
theorem isLegal_append (S : Finset V) (ξ : RState G) (vs ws : List V) :
    IsLegal π S ξ (vs ++ ws) ↔ IsLegal π S ξ vs ∧ IsLegal π S (run π S ξ vs) ws := by
  induction vs generalizing ξ with
  | nil => simp
  | cons v vs ih => simp [isLegal_cons, ih, and_assoc]

/-- Every prefix `vs.take n` of a legal routing `vs` is itself legal, extracted from
`isLegal_append` applied to the split `vs = vs.take n ++ vs.drop n`. -/
theorem IsLegal.prefix (S : Finset V) (ξ : RState G) (vs : List V) (h : IsLegal π S ξ vs)
    (n : ℕ) : IsLegal π S ξ (vs.take n) := by
  have := (isLegal_append π S ξ (vs.take n) (vs.drop n)).1 (by simpa using h)
  exact this.1

/-! ### The rotor at a vertex depends only on the actuations there -/

/-- Actuating `v` advances the rotor at `v` itself by `π.next v`. -/
theorem actuate_ρ_self (S : Finset V) (ξ : RState G) (v : V) :
    (actuate π S ξ v).ρ v = π.next v (ξ.ρ v) := by
  simp [actuate]

/-- Actuating `v` leaves the rotor at every other vertex `w ≠ v` unchanged. -/
theorem actuate_ρ_of_ne (S : Finset V) (ξ : RState G) (v w : V) (h : w ≠ v) :
    (actuate π S ξ v).ρ w = ξ.ρ w := by
  simp [actuate, Function.update_of_ne h]

/-- After the routing `vs`, the rotor at `w` has advanced once per actuation of `w`. -/
theorem run_ρ (S : Finset V) (ξ : RState G) (vs : List V) (w : V) :
    (run π S ξ vs).ρ w = ((π.next w) ^ (vs.count w)) (ξ.ρ w) := by
  induction vs generalizing ξ with
  | nil => simp
  | cons v vs ih =>
    rw [run_cons, ih]
    by_cases h : v = w
    · subst h
      rw [actuate_ρ_self, List.count_cons_self, pow_succ, Equiv.Perm.mul_apply]
    · rw [actuate_ρ_of_ne π S ξ v w (Ne.symm h)]
      simp [h]

/-! ### Particle counts -/

/-- The particle count at `x` after actuating `v`: one leaves `v`, and one
arrives at the head of the new rotor at `v` unless that head is a sink. -/
theorem actuate_σ (S : Finset V) (ξ : RState G) (v x : V) :
    (actuate π S ξ v).σ x =
      (if x = v then ξ.σ x - 1 else ξ.σ x) +
        (if x = (π.next v (ξ.ρ v)).1 ∧ (π.next v (ξ.ρ v)).1 ∉ S then 1 else 0) := rfl

omit [DecidableEq V] in
/-- The head of the new rotor is never the actuated vertex itself. -/
theorem next_head_ne (ξ : RState G) (v : V) : (π.next v (ξ.ρ v)).1 ≠ v := by
  intro h
  have := (π.next v (ξ.ρ v)).2
  rw [h] at this
  exact G.irrefl this

end Rotor

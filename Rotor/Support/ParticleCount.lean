/-
Particle counts along a routing: the count at a vertex is its initial count,
plus the arrivals along traversed edges into it, minus its actuations.  This
is the bookkeeping behind `lem:boundary-routing` ("Legality would therefore
require at least `deg(u) + 1` incoming traversals at `u`").
-/
import Rotor.Support.RoutingBasics

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-- The number of traversed edges of the routing with head `x`, for `x ∉ S`:
the arrivals at `x`. -/
def arrivals (S : Finset V) (ξ : RState G) (vs : List V) (x : V) : ℕ :=
  (traversed π S ξ vs).countP (fun e => e.2 = x)

@[simp] theorem traversed_nil (S : Finset V) (ξ : RState G) : traversed π S ξ [] = [] := rfl

@[simp] theorem traversed_cons (S : Finset V) (ξ : RState G) (v : V) (vs : List V) :
    traversed π S ξ (v :: vs) =
      (v, (π.next v (ξ.ρ v)).1) :: traversed π S (actuate π S ξ v) vs := rfl

theorem traversed_append (S : Finset V) (ξ : RState G) (vs ws : List V) :
    traversed π S ξ (vs ++ ws) = traversed π S ξ vs ++ traversed π S (run π S ξ vs) ws := by
  induction vs generalizing ξ with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem length_traversed (S : Finset V) (ξ : RState G) (vs : List V) :
    (traversed π S ξ vs).length = vs.length := by
  induction vs generalizing ξ with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- The tails of the traversed edges are the actuated vertices, in order. -/
theorem traversed_map_fst (S : Finset V) (ξ : RState G) (vs : List V) :
    (traversed π S ξ vs).map Prod.fst = vs := by
  induction vs generalizing ξ with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- The particle count at `x ∉ S` after the routing `vs`, as an identity in `ℤ`
(the count never goes negative along a legal routing, but the identity is
about the arithmetic). -/
theorem run_σ_eq (S : Finset V) (ξ : RState G) (vs : List V) (x : V) (hx : x ∉ S)
    (hleg : IsLegal π S ξ vs) :
    ((run π S ξ vs).σ x : ℤ) = ξ.σ x + arrivals π S ξ vs x - vs.count x := by
  induction vs generalizing ξ with
  | nil => simp [arrivals]
  | cons v vs ih =>
    rw [isLegal_cons] at hleg
    obtain ⟨hv, hpos, hleg'⟩ := hleg
    rw [run_cons, ih _ hleg', actuate_σ]
    simp only [arrivals, traversed_cons, List.countP_cons, List.count_cons]
    push_cast
    by_cases hxv : x = v
    · subst hxv
      have hne : (π.next x (ξ.ρ x)).1 ≠ x := next_head_ne π ξ x
      have hne' : ¬ (x = (π.next x (ξ.ρ x)).1 ∧ (π.next x (ξ.ρ x)).1 ∉ S) := fun h => hne h.1.symm
      have h1 : ((ξ.σ x - 1 : ℕ) : ℤ) = (ξ.σ x : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      simp only [if_true, hne, hne', if_false, h1, decide_eq_true_eq, beq_self_eq_true]
      ring
    · have hvx : (v == x) = false := by
        simpa using Ne.symm hxv
      simp only [hxv, if_false, hvx, decide_eq_true_eq]
      by_cases hh : (π.next v (ξ.ρ v)).1 = x
      · simp only [hh, hx, not_false_eq_true, and_self, if_true, Bool.false_eq_true, if_false]
        ring
      · have hh' : ¬ (x = (π.next v (ξ.ρ v)).1 ∧ (π.next v (ξ.ρ v)).1 ∉ S) := fun h => hh h.1.symm
        simp only [hh, hh', if_false, Bool.false_eq_true]
        ring

end Rotor

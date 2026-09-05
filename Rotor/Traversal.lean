/-
Traversals and departures of the walk, and the edges traversed by a routing.
Vocabulary for `lem:one-circuit` (`rotor.tex:691-697`), `lem:boundary-routing`
(`rotor.tex:747-753`) and Section 6 (`rotor.tex:2246-2252`).
-/
import Rotor.Routing

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
variable (π : Mechanism G)

/-- The directed edge traversed by the walk at step `t`: `X_t → X_{t+1}`. -/
def traversal (ρ : Config G) (o : V) (t : ℕ) : V × V := (X π ρ o t, X π ρ o (t + 1))

/-- The number of departures from `x` during the time interval `[a, b)`:
`#{a ≤ t < b : X_t = x}`. -/
def departures (ρ : Config G) (o : V) (x : V) (a b : ℕ) : ℕ :=
  ((Ico a b).filter (fun t => X π ρ o t = x)).card

/-- The directed edges traversed by the routing `vs` from `ξ`, in order: each
actuation of `v` traverses `v → w` where `w` is the head of the new rotor at `v`. -/
def traversed (S : Finset V) : RState G → List V → List (V × V)
  | _, [] => []
  | ξ, v :: vs => (v, (π.next v (ξ.ρ v)).1) :: traversed S (actuate π S ξ v) vs

/-- The edges traversed by a boundary routing of `S`, counting the initial edges
from `S`: the boundary edges (in any fixed enumeration) followed by the edges of
the actuations. -/
noncomputable def boundaryTraversed (S : Finset V) (ρ : Config G) (es : List (V × V)) (vs : List V) :
    List (V × V) :=
  es ++ traversed π S (boundaryInit S ρ) vs

end Rotor

/-
Boundary routings and the circuit map, `rotor.tex:700-810` (Section 2.1).

  "Fix a nonempty finite set `S ⊆ V` and regard its vertices as sinks: they
   carry no rotors and remove every particle that enters them.  A
   particle-and-rotor state is a pair `ξ = (σ, ρ)` consisting of a particle
   configuration `σ : V ∖ S → ℤ_{≥0}` and a rotor configuration `ρ` on `V ∖ S`.
   A vertex is occupied when it contains at least one particle.  To actuate an
   occupied vertex, advance its rotor and move one particle along the new rotor
   edge, removing the particle if that edge enters `S`.
   A state `ξ'` is a successor of `ξ` if one actuation transforms `ξ` into
   `ξ'`, and a state is stable if no particles remain.  A legal routing is a
   finite or infinite sequence of states, each a successor of the one before.
   It is complete if it is finite and its last state is stable.  A boundary
   routing of `S` is a legal routing started with one particle at `x` for each
   directed edge `s → x` with `s ∈ S` and `x ∉ S`, and with the fixed initial
   rotors on `V ∖ S`.  We say that the boundary routing of `S` terminates if a
   complete boundary routing of `S` exists."

  "Call a boundary routing one-particle-at-a-time when it orders the directed
   edges `s → x` from `S` to `V ∖ S`, routes each corresponding particle until
   it enters `S` before starting the next, and stops only after the last
   particle enters `S`.  If a particle never enters `S`, the routing instead
   continues with that particle forever.  Rotor states are retained, and
   `s → x` counts as the first edge of the corresponding route."

  "Define the circuit map `Φ`, on the nonempty finite sets `S ⊆ V` whose
   boundary routing terminates, by
   `Φ(S) := S ∪ {x ∉ S : x is actuated in a complete routing}`.
   Set `Φ⁰(S) := S`; a positive iterate is defined only if every intervening
   boundary routing terminates."

  `rotor.tex:812-830`: "For `x, y ∈ V`, define `τ(x, y) := min {n ≥ 0 :
   y ∈ Φⁿ({x})}` if the boundary routing of every nonempty finite set
   terminates, and `d_G(x, y)` otherwise."

How the paper's objects are modelled here:

- A particle configuration is `σ : V → ℕ` and a state carries a full
  rotor configuration; values on the sink set `S` are never read, which
  is the paper's "on `V ∖ S`".  A legal routing is recorded by its
  initial state and the list (or, if infinite, the sequence) of
  actuated vertices; the paper's sequence of states is `run` of that
  list.  The two records determine each other, because an actuation
  moves one particle from the actuated vertex, which the loopless graph
  makes identifiable from the pair of states.  Actuation counts are
  `List.count`.
- `Φ S` is total: it chooses a complete boundary routing when one exists
  and returns `S` otherwise.  Every statement about `Φ S` carries
  `Terminates S`.  Independence of the choice is `lem:least-action`.
- "`Φⁿ(S)` is defined" is `IteratesDefined S n`: every intervening
  boundary routing terminates.
- `τ x y` is `sInf` over `ℕ` in the terminating case, so it would be the
  junk value `0` if `y` were in no iterate; under `AllTerminate` the set
  is nonempty (`prop:passage`, `eq:passage-upper`), so the junk value
  never arises.
-/
import Rotor.Model

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
variable (π : Mechanism G)

/-- A particle-and-rotor state `ξ = (σ, ρ)`. -/
structure RState (G : SimpleGraph V) where
  /-- The particle configuration `σ`. -/
  σ : V → ℕ
  /-- The rotor configuration `ρ`. -/
  ρ : Config G

/-- Actuate the vertex `v`: advance its rotor and move one particle along the
new rotor edge, removing the particle if that edge enters the sink set `S`. -/
def actuate (S : Finset V) (ξ : RState G) (v : V) : RState G :=
  let a := π.next v (ξ.ρ v)
  { σ := fun x => (if x = v then ξ.σ x - 1 else ξ.σ x) + (if x = a.1 ∧ a.1 ∉ S then 1 else 0),
    ρ := Function.update ξ.ρ v a }

/-- The state reached from `ξ` by actuating the vertices of `vs` in order. -/
def run (S : Finset V) : RState G → List V → RState G
  | ξ, [] => ξ
  | ξ, v :: vs => run S (actuate π S ξ v) vs

/-- A state is stable when no particles remain outside `S`. -/
def Stable (S : Finset V) (ξ : RState G) : Prop := ∀ v, v ∉ S → ξ.σ v = 0

/-- The list `vs` is a legal routing from `ξ`: each actuated vertex is outside
`S` and occupied at its turn. -/
def IsLegal (S : Finset V) : RState G → List V → Prop
  | _, [] => True
  | ξ, v :: vs => v ∉ S ∧ 0 < ξ.σ v ∧ IsLegal S (actuate π S ξ v) vs

/-- The first `n` terms of a sequence, as a list. -/
def prefixList (vs : ℕ → V) (n : ℕ) : List V := (List.range n).map vs

/-- An infinite legal routing from `ξ`. -/
def IsInfLegal (S : Finset V) (ξ : RState G) (vs : ℕ → V) : Prop :=
  ∀ n, IsLegal π S ξ (prefixList vs n)

/-- A complete routing from `ξ`: legal, and its final state is stable. -/
def IsComplete (S : Finset V) (ξ : RState G) (vs : List V) : Prop :=
  IsLegal π S ξ vs ∧ Stable S (run π S ξ vs)

open Classical in
/-- The initial state of a boundary routing of `S`: one particle at `x` for each
directed edge `s → x` with `s ∈ S`, `x ∉ S`, and the given rotors. -/
noncomputable def boundaryInit (S : Finset V) (ρ : Config G) : RState G where
  σ x := if x ∈ S then 0 else (S.filter (fun s => G.Adj s x)).card
  ρ := ρ

/-- The boundary routing of `S` terminates: a complete boundary routing exists. -/
def Terminates (S : Finset V) (ρ : Config G) : Prop :=
  ∃ vs : List V, IsComplete π S (boundaryInit S ρ) vs

open Classical in
/-- The circuit map `Φ` (`eq:phi-definition`), total. -/
noncomputable def Φ (ρ : Config G) (S : Finset V) : Finset V :=
  if h : Terminates π S ρ then S ∪ (Classical.choose h).toFinset else S

/-- `Φⁿ(S)` is defined: every intervening boundary routing terminates
. -/
def IteratesDefined (ρ : Config G) (S : Finset V) (n : ℕ) : Prop :=
  ∀ i < n, Terminates π ((Φ π ρ)^[i] S) ρ

/-- The boundary routing of every nonempty finite set terminates. -/
def AllTerminate (ρ : Config G) : Prop :=
  ∀ S : Finset V, S.Nonempty → Terminates π S ρ

/-- The passage time `τ(x, y)`, `eq:passage-definition`. -/
noncomputable def τ (ρ : Config G) (x y : V) : ℕ :=
  by classical exact
    if AllTerminate π ρ then sInf {n : ℕ | y ∈ (Φ π ρ)^[n] {x}} else G.dist x y

/-! ### One-particle-at-a-time boundary routings

The routing is driven by an ordering `es` of the directed edges `s → x` from
`S` to `V ∖ S`.  Its evolution is a deterministic state machine: the tracked
particle sits at `tracked`; while it is outside `S` its vertex is actuated and
it moves to the new rotor head; once it is in `S`, the next edge of the order
is started.  The state machine records the actuated vertices, so that its
actuation counts can be compared with those of any complete routing. -/

/-- The state of a one-particle-at-a-time routing. -/
structure OneState (G : SimpleGraph V) where
  /-- The particle-and-rotor state. -/
  ξ : RState G
  /-- The boundary edges not yet started, in order. -/
  queue : List (V × V)
  /-- The position of the particle being routed, if one is being routed. -/
  tracked : Option V
  /-- The vertices actuated so far, most recent first. -/
  acted : List V
  /-- The route of the particle being routed, most recent first. -/
  route : List V

/-- One move of the one-particle-at-a-time state machine. -/
def oneStep (S : Finset V) (s : OneState G) : OneState G :=
  match s.tracked with
  | some p =>
    if p ∈ S then { s with tracked := none }
    else
      let a := π.next p (s.ξ.ρ p)
      { s with ξ := actuate π S s.ξ p, tracked := some a.1, acted := p :: s.acted,
               route := a.1 :: s.route }
  | none =>
    match s.queue with
    | [] => s
    | (_, x) :: rest => { s with queue := rest, tracked := some x, route := [x] }

/-- The one-particle-at-a-time boundary routing of `S` from the rotors `ρ`, in
the order `es`, after `n` moves. -/
noncomputable def oneRouting (S : Finset V) (ρ : Config G) (es : List (V × V)) (n : ℕ) : OneState G :=
  (oneStep π S)^[n] { ξ := boundaryInit S ρ, queue := es, tracked := none, acted := [], route := [] }

variable (G) in
/-- `es` is an ordering of the directed edges from `S` to `V ∖ S`: it lists each
such edge exactly once. -/
def IsBoundaryOrder (S : Finset V) (es : List (V × V)) : Prop :=
  es.Nodup ∧ ∀ e : V × V, e ∈ es ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2

/-- The routing has finished at stage `n`: the queue is empty and no particle is
being routed. -/
def OneDone (S : Finset V) (ρ : Config G) (es : List (V × V)) (n : ℕ) : Prop :=
  (oneRouting π S ρ es n).queue = [] ∧ (oneRouting π S ρ es n).tracked = none

/-- The one-particle-at-a-time routing is finite: it finishes at some stage. -/
def OneFinite (S : Finset V) (ρ : Config G) (es : List (V × V)) : Prop :=
  ∃ n, OneDone π S ρ es n

/-- The vertices actuated by the one-particle-at-a-time routing up to stage `n`,
in order of actuation. -/
noncomputable def oneActed (S : Finset V) (ρ : Config G) (es : List (V × V)) (n : ℕ) : List V :=
  (oneRouting π S ρ es n).acted.reverse

/-- Some particle of the one-particle-at-a-time routing visits `y` by stage `n`,
counting the head of its initial boundary edge as its first vertex. -/
def OneVisits (S : Finset V) (ρ : Config G) (es : List (V × V)) (y : V) : Prop :=
  ∃ n, y ∈ (oneRouting π S ρ es n).route

end Rotor

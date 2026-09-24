/-
The depth-first exploration of the dual configuration, `rotor.tex:1870-1900`
(Section 5.3, `ssec:square-exploration`):

  "Fix a face `f` and a directed dual edge leaving it.  Initially the visited
   set is `{f}`, and the active list consists of the four edges leaving `f`, in
   counterclockwise order beginning with the chosen edge.  At each step, call
   the first active edge the current edge and reveal whether it is open or
   closed; we call this testing the edge.  Remove it from the active list.  If
   it is open, visit its head and prepend, in right-turn, straight, left-turn
   order, the three directed edges leaving that face other than the reverse of
   the current edge.  After either outcome, delete every active edge whose head
   is visited or lies in a finite component of the complement of the visited
   set.  Continue until the list is empty.  Whenever the current edge is the
   rotation of `v → w`, relabel the square formed by the rotations of the four
   edges out of `v`, writing `E` for the current edge and `N, W, S` for the
   other three sides in counterclockwise order."

  `rotor.tex:1919-1924`: "call the test of `E` forced if `W` was tested closed
   at an earlier step.  In that case `E` is necessarily open.  Let
   `K ∈ ℤ_{≥0} ∪ {∞}` be the number of forced tests."

- The exploration is a deterministic state machine driven by the test
  outcomes; `explore ρ f e₀ n` is its state after `n` tests with the
  outcomes read from `ρ`, and `replay f e₀ h` is the state after the
  prescribed outcomes `h`, so that `explore ρ f e₀ n = replay f e₀
  (history ρ n)`.  Conditional probabilities given the earlier outcomes
  are stated through these histories.  "Lies in a finite component of
  the complement of the visited set" is reachability in the subgraph of
  the dual lattice induced on the unvisited faces.
-/
import Rotor.Dual

open Finset

namespace Rotor

/-- Counterclockwise rotation of a unit step by `90°`. -/
def rotL (d : Site) : Site := (-d.2, d.1)

/-- Clockwise rotation of a unit step by `90°`. -/
def rotR (d : Site) : Site := (d.2, -d.1)

/-- The four directed dual edges leaving the face `a`, counterclockwise from
the step `d`. -/
def edgesFrom (a d : Site) : List (Site × Site) :=
  [(a, a + d), (a, a + rotL d), (a, a + rotL (rotL d)), (a, a + rotL (rotL (rotL d)))]

/-- After an open test of `a → b`: the three edges leaving `b` other than the
reverse, in right-turn, straight, left-turn order. -/
def continuations (a b : Site) : List (Site × Site) :=
  let d := b - a
  [(b, b + rotR d), (b, b + d), (b, b + rotL d)]

/-- The face `h` lies in a finite component of the complement of `visited`. -/
def InFiniteComponent (visited : Finset Site) (h : Site) : Prop :=
  h ∉ visited ∧ Set.Finite {y : Site | ∃ (hy : y ∉ visited) (hh : h ∉ visited),
    (squareGraph.induce {x : Site | x ∉ visited}).Reachable ⟨h, hh⟩ ⟨y, hy⟩}

/-- The state of the exploration. -/
structure ExplState where
  /-- The visited faces. -/
  visited : Finset Site
  /-- The active list; its head is the current edge. -/
  active : List (Site × Site)
  /-- The tested edges with their outcomes, oldest first. -/
  tested : List (Site × Site × Bool)
  /-- The number of forced tests so far. -/
  forced : ℕ

/-- The sides of the square of the current dual edge `a → b`: with `v` the tail
of the primal edge and `d` its direction, the side `E` is the current edge and
`N, W, S` are `dualEdge v (d - 1)`, `dualEdge v (d + 2)`, `dualEdge v (d + 1)`
(counterclockwise from `E`). -/
def sideW (a b : Site) : Site × Site :=
  let v := primalTail a b
  dualEdge v (primalDir a b + 2)

/-- The side `S` of the square of the current edge. -/
def sideS (a b : Site) : Site × Site :=
  let v := primalTail a b
  dualEdge v (primalDir a b + 1)

/-- `e` was tested with outcome `o` earlier in the history `h`. -/
def TestedAs (h : List (Site × Site × Bool)) (e : Site × Site) (o : Bool) : Prop :=
  (e.1, e.2, o) ∈ h

open Classical in
/-- One step with a prescribed outcome `o` for the current edge; the identity
when the active list is empty. -/
noncomputable def explStepWith (s : ExplState) (o : Bool) : ExplState :=
  match s.active with
  | [] => s
  | e :: rest =>
    let visited' := if o then insert e.2 s.visited else s.visited
    let added := if o then continuations e.1 e.2 else []
    let forced' := if TestedAs s.tested (sideW e.1 e.2) false then s.forced + 1 else s.forced
    { visited := visited',
      active := (added ++ rest).filter
        (fun g => ¬ (g.2 ∈ visited' ∨ InFiniteComponent visited' g.2)),
      tested := s.tested ++ [(e.1, e.2, o)],
      forced := forced' }

/-- The initial state: visited `{f}`, the four edges leaving `f` counterclockwise
from the chosen edge `f → f + d`. -/
def explInit (f d : Site) : ExplState :=
  { visited := {f}, active := edgesFrom f d, tested := [], forced := 0 }

open Classical in
/-- One step of the exploration with the outcome read from the rotors `ρ`. -/
noncomputable def explStep (ρ : Config squareGraph) (s : ExplState) : ExplState :=
  match s.active with
  | [] => s
  | e :: _ => explStepWith s (decide (DualOpen ρ e.1 e.2))

/-- The exploration from the face `f` along the edge `f → f + d`, after `n` tests. -/
noncomputable def explore (ρ : Config squareGraph) (f d : Site) (n : ℕ) : ExplState :=
  (explStep ρ)^[n] (explInit f d)

/-- The state after the prescribed outcomes `h`. -/
noncomputable def replay (f d : Site) (h : List Bool) : ExplState :=
  h.foldl explStepWith (explInit f d)

/-- The outcomes of the first `n` tests, oldest first. -/
noncomputable def history (ρ : Config squareGraph) (f d : Site) (n : ℕ) : List Bool :=
  (explore ρ f d n).tested.map (fun t => t.2.2)

/-- The exploration terminates. -/
def ExplTerminates (ρ : Config squareGraph) (f d : Site) : Prop :=
  ∃ n, (explore ρ f d n).active = []

/-- `K`, the number of forced tests, in `ℕ∞`. -/
noncomputable def forcedCount (ρ : Config squareGraph) (f d : Site) : ℕ∞ :=
  ⨆ n : ℕ, ((explore ρ f d n).forced : ℕ∞)

/-- The face `g` is reachable from `f` by a directed path of open dual edges. -/
def DualReachable (ρ : Config squareGraph) (f g : Site) : Prop :=
  ∃ q : List Site, IsOpenDualPath ρ q ∧ q.head? = some f ∧ q.getLast? = some g

end Rotor

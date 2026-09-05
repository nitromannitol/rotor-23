/-
Rotor walk on a general graph: the model.

Encodes Bou-Rabee--Peres, *Eulerian walkers on `ℤ²` have range exponent `2/3`*,
Section 1.1 (`ssec:main-results`), `rotor.tex:179-225`:

  "In this paper we consider only undirected graphs with no loops and no
   multiple edges.  Let `G = (V, E)` be a connected, locally finite graph ...
   Each edge `{x, y} ∈ E` gives two directed edges, `x → y` and `y → x`.  A
   rotor configuration assigns to each vertex `v` one outgoing directed edge
   `ρ(v)`.  A rotor mechanism specifies a cyclic permutation `π_v` of the
   directed edges out of each vertex `v`.  Given an initial position `X_0` and
   an initial rotor configuration `ρ_0`, define, for every integer `t ≥ 0`,
   `ρ_{t+1}(v) := π_v(ρ_t(v))` if `v = X_t`, and `ρ_t(v)` otherwise, and let
   `X_{t+1}` be determined by `ρ_{t+1}(X_t) = (X_t → X_{t+1})`.
   The range at time `t` is `R_t := {X_0, …, X_t}`.  The walk is recurrent if
   it visits every vertex infinitely often and transient otherwise.  Fix a
   starting vertex `o`.  A circuit consists of `deg(o)` successive returns to
   `o`.  Define the time at which the first `n` circuits have been completed by
   `T(n) := inf {t ≥ 0 : X_t = o and #{0 ≤ s < t : X_s = o} ≥ n deg(o)}`.
   When `T(n) < ∞`, let `A_n := R_{T(n)}`, the range after `n` circuits, and
   let `A_0 := {o}`."

Rulings (`ledger/decisions.md`):

  M-006  A graph is a Mathlib `SimpleGraph V` (loopless, no multiple edges,
         undirected), locally finite through `[G.LocallyFinite]`.  A directed
         edge out of `v` is an element of `G.neighborSet v`; the directed edge
         `x → y` of the paper is the pair `(x, y)` with `G.Adj x y`.
  M-007  A rotor mechanism is a family of permutations `next v` of
         `G.neighborSet v`, one per vertex, each cyclic: the powers of `next v`
         carry every neighbor to every other.  It also records that every
         vertex has a neighbor, which the paper's rotor configuration
         presupposes; on an infinite connected graph this is automatic.
  M-008  `T n : ℕ∞`, `⊤` when the defining set is empty; `A n` is defined
         through `(T n).toNat` and is the junk value `{o}` when `T n = ⊤`
         (ruling M-003, confirmed).
  M-009  Graph distance is Mathlib's `G.dist`, which is `0` between
         unreachable vertices; every statement that uses it assumes `G` is
         connected, so the junk value never arises.
-/
import Mathlib

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- A rotor mechanism on `G`: at each vertex `v`, a cyclic permutation `next v`
of the neighbors of `v` (ruling M-007).  `cyclic` says the powers of `next v`
act transitively, which for a finite set is exactly "a single cycle". -/
structure Mechanism where
  /-- `π_v`: the next directed edge out of `v` after a given one. -/
  next : ∀ v : V, Equiv.Perm (G.neighborSet v)
  /-- `π_v` is a cyclic permutation. -/
  cyclic : ∀ (v : V) (a b : G.neighborSet v), ∃ k : ℕ, ((next v) ^ k) a = b
  /-- every vertex has an outgoing directed edge. -/
  nonempty : ∀ v : V, Nonempty (G.neighborSet v)

/-- A rotor configuration: one outgoing directed edge at every vertex. -/
abbrev Config := ∀ v : V, G.neighborSet v

variable {G}

/-- The state of the rotor walk: the walker's position and the rotors. -/
structure State (G : SimpleGraph V) where
  /-- The walker's position `X_t`. -/
  pos : V
  /-- The rotor configuration `ρ_t`. -/
  rotor : Config G

variable (π : Mechanism G)

/-- One step of the walk: turn the rotor at the walker's site, then step along
it.  These are the two displays of `rotor.tex:190-201`. -/
def step (s : State G) : State G :=
  let a := π.next s.pos (s.rotor s.pos)
  { pos := a.1, rotor := Function.update s.rotor s.pos a }

/-- The walk started at `o` with initial rotors `ρ`, after `t` steps. -/
def walk (ρ : Config G) (o : V) (t : ℕ) : State G := (step π)^[t] ⟨o, ρ⟩

/-- The position `X_t`. -/
def X (ρ : Config G) (o : V) (t : ℕ) : V := (walk π ρ o t).pos

/-- The rotor configuration `ρ_t`. -/
def rot (ρ : Config G) (o : V) (t : ℕ) : Config G := (walk π ρ o t).rotor

/-- The range `R_t = {X_0, …, X_t}`, `rotor.tex:205-208`. -/
def R (ρ : Config G) (o : V) (t : ℕ) : Finset V :=
  (range (t + 1)).image (X π ρ o)

/-- The number of visits to `o` strictly before time `t`, `#{0 ≤ s < t : X_s = o}`. -/
def visits (ρ : Config G) (o : V) (t : ℕ) : ℕ :=
  ((range t).filter (fun s => X π ρ o s = o)).card

/-- `T(n)`, the completion time of the first `n` circuits, `eq:circ-time`, with
value `⊤` when no such time exists (ruling M-008). -/
noncomputable def T (ρ : Config G) (o : V) (n : ℕ) : ℕ∞ :=
  ⨅ t ∈ {t : ℕ | X π ρ o t = o ∧ G.degree o * n ≤ visits π ρ o t}, (t : ℕ∞)

/-- `A_n = R_{T(n)}`, the range after `n` circuits; meaningful only when
`T n < ⊤` (ruling M-008). -/
noncomputable def A (ρ : Config G) (o : V) (n : ℕ) : Finset V :=
  R π ρ o (T π ρ o n).toNat

/-- The walk is recurrent if it visits every vertex infinitely often,
`rotor.tex:209-210`. -/
def Recurrent (ρ : Config G) (o : V) : Prop :=
  ∀ x : V, Set.Infinite {t : ℕ | X π ρ o t = x}

/-! ### The cyclic order after the initial rotor

`rotor.tex:1295-1300` (Section 4) and `rotor.tex:1517-1527` (Section 5): for
`v ∼ w`, `r_v(w) ∈ {1, …, deg(v)}` is the position of `v → w` in the cyclic
order beginning immediately after the initial rotor at `v`.  The definition of
a live path in `rotor.tex:412-420` is phrased with this order: a path is live at
an internal vertex `x_i` when `x_i → x_{i+1}` occurs before `x_i → x_{i-1}`
in it, that is, when `r_{x_i}(x_{i+1}) < r_{x_i}(x_{i-1})`. -/

omit [DecidableEq V] [G.LocallyFinite] in
theorem rank_exists (ρ : Config G) (v : V) (w : G.neighborSet v) :
    ∃ k : ℕ, 0 < k ∧ ((π.next v) ^ k) (ρ v) = w := by
  obtain ⟨d, hd⟩ := π.cyclic v (π.next v (ρ v)) w
  exact ⟨d + 1, Nat.succ_pos d, by simpa only [pow_succ, Equiv.Perm.mul_apply] using hd⟩

/-- The number of rotor advances from `ρ v` until the directed edge `v → w` is
selected: the least `k ≥ 1` with `(next v)^k (ρ v) = w`.  It lies in
`{1, …, deg v}`. -/
noncomputable def rank (ρ : Config G) (v : V) (w : G.neighborSet v) : ℕ :=
  Nat.find (rank_exists π ρ v w)

/-- The rank of the directed edge `v → w`, for `w` a vertex adjacent to `v`. -/
noncomputable def rank' (ρ : Config G) (v w : V) (h : G.Adj v w) : ℕ :=
  rank π ρ v ⟨w, h⟩

/-! ### Paths and live paths

`rotor.tex:405-420`: "a path `x_0, x_1, …` is a finite or infinite sequence of
distinct vertices such that consecutive vertices are adjacent.  Its internal
vertices are all its vertices except the first and, for a finite path, the
last.  A path is live at an internal vertex `x_i` if, in the cyclic order
beginning immediately after the initial rotor at `x_i`, the edge `x_i → x_{i+1}`
occurs before `x_i → x_{i-1}`.  The path is live if this holds at every
internal vertex."

A finite path is a `List V`; an infinite path is a function `ℕ → V`. -/

variable (G) in
/-- A finite path: distinct vertices, consecutive ones adjacent. -/
def IsPath (l : List V) : Prop := l.Nodup ∧ l.IsChain G.Adj

variable (G) in
/-- An infinite path: distinct vertices, consecutive ones adjacent. -/
def IsInfPath (x : ℕ → V) : Prop := Function.Injective x ∧ ∀ i, G.Adj (x i) (x (i + 1))

/-- The live condition at the internal vertex `v` of a path entering from `u`
and leaving to `w`: `r_v(w) < r_v(u)`. -/
def LiveAt (ρ : Config G) (u v w : V) : Prop :=
  ∃ (hw : G.Adj v w) (hu : G.Adj v u), rank' π ρ v w hw < rank' π ρ v u hu

/-- The finite path `l = x_0, …, x_m` is live at its internal vertex `x_i`. -/
def LiveAtIndex (ρ : Config G) (l : List V) (i : ℕ) : Prop :=
  ∃ h : 0 < i ∧ i + 1 < l.length,
    LiveAt π ρ (l.get ⟨i - 1, by omega⟩) (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, h.2⟩)

open Classical in
/-- The set of internal indices at which the finite path `l` fails the live
condition. -/
noncomputable def liveFailures (ρ : Config G) (l : List V) : Finset ℕ :=
  (range l.length).filter (fun i => 0 < i ∧ i + 1 < l.length ∧ ¬ LiveAtIndex π ρ l i)

/-- A finite path is live when it is live at every internal vertex. -/
def IsLive (ρ : Config G) (l : List V) : Prop :=
  ∀ i, 0 < i → i + 1 < l.length → LiveAtIndex π ρ l i

/-- An infinite path is live when it is live at every internal vertex. -/
def IsInfLive (ρ : Config G) (x : ℕ → V) : Prop :=
  ∀ i, LiveAt π ρ (x i) (x (i + 1)) (x (i + 2))

end Rotor

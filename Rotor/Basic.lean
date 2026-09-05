/-
Rotor walk on the square lattice: the model.

Encodes Bou-Rabee--Peres, *Eulerian walkers on `ℤ²` have range exponent `2/3`*,
Section 1.1 (`ssec:main-results`), `rotor.tex:179-225`:

  "A rotor configuration assigns to each vertex `v` one outgoing directed edge
   `ρ(v)`.  A rotor mechanism specifies a cyclic permutation `π_v` of the
   directed edges out of each vertex `v`.  Given an initial position `X_0` and
   an initial rotor configuration `ρ_0`, define, for every integer `t ≥ 0`,
   `ρ_{t+1}(v) := π_v(ρ_t(v))` if `v = X_t` and `ρ_t(v)` otherwise, and let
   `X_{t+1}` be determined by `ρ_{t+1}(X_t) = (X_t → X_{t+1})`.  On the square
   lattice, the clockwise rotor mechanism has cyclic order `N, E, S, W`.
   The range at time `t` is `R_t := {X_0, …, X_t}`.  ...  A circuit consists of
   `deg(o)` successive returns to `o`.  Define the time at which the first `n`
   circuits have been completed by
   `T(n) := inf {t ≥ 0 : X_t = o and #{0 ≤ s < t : X_s = o} ≥ n deg(o)}`.
   When `T(n) < ∞`, let `A_n := R_{T(n)}`, the range after `n` circuits, and
   let `A_0 := {o}`."

Modelling decisions are numbered `M-***` and recorded in `ledger/decisions.md`.

  M-001  The graph is the square lattice only: a site is `ℤ × ℤ`, a directed
         edge out of a site is a direction `Fin 4`, and `deg ≡ 4`.
  M-002  Directions are numbered in the clockwise order of the paper:
         `0 = N`, `1 = E`, `2 = S`, `3 = W`; the clockwise mechanism is `+ 1`
         in `Fin 4`.
  M-003  `T n` takes values in `ℕ∞`, with `⊤` when no such time exists.  This
         is the paper's `inf ∅ = ∞`.  `A n` is defined through `(T n).toNat`,
         so when `T n = ⊤` it is the junk value `R 0 = {o}`; every statement
         about `A n` therefore carries `T n < ⊤`, or almost-sure recurrence,
         as a hypothesis.
-/
import Mathlib

namespace Rotor

/-- A site of the square lattice `ℤ²`. -/
abbrev Site := ℤ × ℤ

/-- A direction out of a site; equivalently the directed edge it names.  The
numbering is the paper's clockwise order `N, E, S, W` (ruling M-002). -/
abbrev Dir := Fin 4

/-- The unit step `N, E, S, W` in direction `a`. -/
def dirVec (a : Dir) : Site := ![((0 : ℤ), (1 : ℤ)), (1, 0), (0, -1), (-1, 0)] a

/-- The clockwise rotor mechanism `π_v`: advance one step in the cyclic order
`N, E, S, W`. -/
def turn (a : Dir) : Dir := a + 1

/-! The concrete walk on `ℤ²` lives in the namespace `Rotor.Z2`; the general
model of `Rotor/Model.lean` uses the same names for the general objects, and
`Rotor/Square.lean` relates the two. -/
namespace Z2

/-- A rotor configuration: one outgoing directed edge at every site. -/
abbrev RotorConfig := Site → Dir

/-- The state of the rotor walk: the walker's position and the rotors. -/
structure State where
  /-- The walker's position `X_t`. -/
  pos : Site
  /-- The rotor configuration `ρ_t`. -/
  rotor : RotorConfig

/-- One step of the walk: turn the rotor at the walker's site, then step
along it.  This is the two displays of `rotor.tex:190-201`. -/
def step (s : State) : State :=
  let a := turn (s.rotor s.pos)
  { pos := s.pos + dirVec a, rotor := Function.update s.rotor s.pos a }

/-- The walk started at `o` with initial rotors `ρ`, after `t` steps. -/
def walk (ρ : RotorConfig) (o : Site) (t : ℕ) : State := step^[t] ⟨o, ρ⟩

/-- The position `X_t`. -/
def X (ρ : RotorConfig) (o : Site) (t : ℕ) : Site := (walk ρ o t).pos

/-- The rotor configuration `ρ_t`. -/
def rot (ρ : RotorConfig) (o : Site) (t : ℕ) : RotorConfig := (walk ρ o t).rotor

/-- The range `R_t = {X_0, …, X_t}`, `rotor.tex:205-208`. -/
def R (ρ : RotorConfig) (o : Site) (t : ℕ) : Finset Site :=
  (Finset.range (t + 1)).image (X ρ o)

/-- The number of visits to `o` strictly before time `t`: `#{0 ≤ s < t : X_s = o}`. -/
def visits (ρ : RotorConfig) (o : Site) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s => X ρ o s = o)).card

/-- `T(n)`: the completion time of the first `n` circuits, `eq:circ-time`,
with `deg(o) = 4` (ruling M-001) and value `⊤` when no such time exists
(ruling M-003). -/
noncomputable def T (ρ : RotorConfig) (o : Site) (n : ℕ) : ℕ∞ :=
  ⨅ t ∈ {t : ℕ | X ρ o t = o ∧ 4 * n ≤ visits ρ o t}, (t : ℕ∞)

/-- `A_n = R_{T(n)}`, the range after `n` circuits; meaningful only when
`T n < ⊤` (ruling M-003). -/
noncomputable def A (ρ : RotorConfig) (o : Site) (n : ℕ) : Finset Site :=
  R ρ o (T ρ o n).toNat

/-- The walk is recurrent if it visits every site infinitely often
(`rotor.tex:209-210`). -/
def Recurrent (ρ : RotorConfig) (o : Site) : Prop :=
  ∀ x : Site, Set.Infinite {t : ℕ | X ρ o t = x}

end Z2

end Rotor

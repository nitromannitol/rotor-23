/-
The events of Sections 3, 4 and 5.

`rotor.tex:991-1002` (`eq:almost-live-path-event`): "For a directed edge
`e = u → v`, an integer `R ≥ 1`, and `η > 0`, define the almost-live-path
event `L_η(e, R) := {some path starts with e and reaches graph distance R
from u, and the live condition fails at no more than ηR internal vertices}`."

`rotor.tex:1008-1010` (`eq:criterion-path-hypothesis`):
`lim_{R→∞} sup_{u→v} ℙ{L_η(u→v, R)} = 0`.

`rotor.tex:1223-1226`: "Let `C_z` be the event that a live path starts in
`Q_z`, stays in `Q_z⁺` except for its last vertex, and ends outside `Q_z⁺`."

`rotor.tex:1385-1393` and `rotor.tex:1461-1468`: the event that a live path
starts with `u → v` and contains a vertex at graph distance `R` from `u`.

Ruling M-017: "reaches graph distance `R`" is "contains a vertex at graph
distance exactly `R`"; on a path from `u` this is the same as reaching
distance at least `R`, since consecutive vertices are at distance at most one
apart, and the first is the paper's wording in Section 4.
-/
import Rotor.Periodic

open MeasureTheory Filter Topology

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
variable (π : Mechanism G)

/-- The almost-live-path event `L_η(u → v, R)`. -/
def almostLiveEvent (η : ℝ) (u v : V) (R : ℕ) : Set (Config G) :=
  {ρ | ∃ l : List V, IsPath G l ∧ l.head? = some u ∧ l[1]? = some v ∧
    (∃ w ∈ l, G.dist u w = R) ∧ ((liveFailures π ρ l).card : ℝ) ≤ η * R}

/-- The hypothesis `eq:criterion-path-hypothesis` for the law `μ` and the
constant `η`: the probability of an almost-live path reaching distance `R`
tends to zero uniformly in its first edge. -/
def Criterion (μ : Measure (Config G)) (η : ℝ) : Prop :=
  Tendsto (fun R : ℕ => ⨆ e : G.Dart, μ (almostLiveEvent π η e.fst e.snd R)) atTop (𝓝 0)

/-- The event that a live path starts with `u → v` and contains a vertex at
graph distance `R` from `u`. -/
def liveReachEvent (u v : V) (R : ℕ) : Set (Config G) :=
  {ρ | ∃ l : List V, IsPath G l ∧ IsLive π ρ l ∧ l.head? = some u ∧ l[1]? = some v ∧
    ∃ w ∈ l, G.dist u w = R}

/-- The block event `C_z`: a live path starts in `Q_z`, stays in `Q_z⁺` except
for its last vertex, and ends outside `Q_z⁺`. -/
def blockEvent (P : DoublyPeriodic G) (L : ℕ) (z : ℤ × ℤ) : Set (Config G) :=
  {ρ | ∃ l : List V, IsPath G l ∧ IsLive π ρ l ∧
    (∃ h : 0 < l.length, l.get ⟨0, h⟩ ∈ P.block L z) ∧
    (∀ (i : ℕ) (h : i + 1 < l.length), l.get ⟨i, by omega⟩ ∈ P.blockPlus L z) ∧
    (∀ y ∈ l.getLast?, y ∉ P.blockPlus L z)}

/-- There is an infinite live path. -/
def HasInfLivePath (ρ : Config G) : Prop :=
  ∃ x : ℕ → V, IsInfPath G x ∧ IsInfLive π ρ x

end Rotor

/-
Proposition 4.2 of rotor.tex, frozen.  `rotor.tex:1385-1400` (label `prop:degree-three-passage`):

  "Let $G$ be a doubly periodic graph in $\R^2$ of maximum degree three,
   equipped with an arbitrary rotor mechanism and independent uniform initial
   rotors.  There are constants $c,C>0$ such that, for every directed edge
   $u\to v$ and every integer $R\geq1$,
   $\P\{\text{a live path starts with $u\to v$ and contains a vertex at graph
   distance $R$ from $u$}\}\leq Ce^{-cR}$."

The constants depend on the graph (through the growth of its balls), so they
are existential (ruling F-003).
-/
import Rotor.Events
import Rotor.Percolation
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.External.SubcriticalDecay
import Rotor.Support.DegreeThreePassage

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.degree_three_passage (P : DoublyPeriodic G) (π : Mechanism G) [Infinite V]
    (hG : G.Connected) (h3 : ∀ v : V, G.degree v ≤ 3) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (u v : V), G.Adj u v → ∀ R : ℕ, 1 ≤ R →
      uniformLaw π (liveReachEvent π u v R) ≤ ENNReal.ofReal (C * Real.exp (-c * R))
-- FROZEN-STATEMENT-END
:= degree_three_passage_proof π P hG h3

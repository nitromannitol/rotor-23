/-
Proposition 5.1 of rotor.tex, frozen.  `rotor.tex:1461-1470` (label `prop:square-passage`):

  "Let $G$ be the square lattice with the clockwise rotor mechanism and
   independent uniform initial rotors, and let $\P_0$ be their product law.
   There are constants $c,C>0$ such that, for every directed edge $u\to v$ and
   every integer $R\geq1$,
   $\P_0\{\text{a live path from $u\to v$ reaches graph distance $R$ from
   $u$}\}\leq Ce^{-cR}$."

The constants route through the subcritical percolation bound
(`External.SubcriticalDecay`), so they are existential (ruling F-003).
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
-/
import Rotor.Events
import Rotor.Percolation
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.External.SubcriticalDecay

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_passage (hSub : External.SubcriticalDecay) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (u v : Site), squareGraph.Adj u v → ∀ R : ℕ, 1 ≤ R →
      uniformLaw clockwise (liveReachEvent clockwise u v R) ≤
        ENNReal.ofReal (C * Real.exp (-c * R))
-- FROZEN-STATEMENT-END
:= by sorry

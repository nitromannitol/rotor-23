/-
Proposition 4.1 of rotor.tex, frozen.  `rotor.tex:1363-1369` (label `prop:subcubic-recurrence`):

  "Let $G$ be an infinite connected graph of maximum degree three, equipped
   with an arbitrary rotor mechanism.  If the initial rotors are independent
   and uniform, then almost surely $G$ contains no infinite live path."
-/
import Rotor.Events
import Rotor.Percolation
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.External.SubcriticalDecay
import Rotor.Support.SubcubicRecurrence

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.subcubic_recurrence (π : Mechanism G) [Infinite V] (hG : G.Connected)
    (h3 : ∀ v : V, G.degree v ≤ 3) :
    ∀ᵐ ρ ∂(uniformLaw π), ¬ HasInfLivePath π ρ
-- FROZEN-STATEMENT-END
:= subcubic_recurrence_proof π hG h3

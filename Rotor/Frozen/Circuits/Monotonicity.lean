/-
Proposition 2.5 of rotor.tex, frozen.  `rotor.tex:801-807` (label `prop:monotonicity`):

  "Let $S\subseteq T$ be nonempty finite sets whose boundary routings
   terminate.  Then $\Phi(S)\subseteq\Phi(T)$."

The paper's $T$ is `U` here, $T$ being the circuit time.  The paper derives
this from `lem:boundary-routing` and `lem:least-action`.
-/
import Rotor.Traversal
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.monotonicity (hAb : External.Abelian G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (ρ : Config G) (S U : Finset V) (hS : S.Nonempty)
    (hSU : S ⊆ U) (hTS : Terminates π S ρ) (hTU : Terminates π U ρ) :
    Φ π ρ S ⊆ Φ π ρ U
-- FROZEN-STATEMENT-END
:= by sorry

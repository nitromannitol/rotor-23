/-
Proposition 2.5 of rotor.tex, frozen.  `rotor.tex:820-826` (label `prop:monotonicity`):

  "Let $S\subseteq T$ be nonempty finite sets whose boundary routings
   terminate.  Then $\Phi(S)\subseteq\Phi(T)$."

The paper's $T$ is `U` here, $T$ being the circuit time.  The paper derives
this from `lem:boundary-routing` and `lem:least-action`.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
`[Infinite V]` and `hG` are the standing assumptions of Section 2 (`rotor.tex:678-680`:
"Throughout this section, `G` is infinite, connected, and locally finite, the rotor
mechanism and initial rotor configuration are fixed and arbitrary").
-/
import Rotor.Traversal
import Rotor.Support.Monotone
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.Bridge.Abelian

/-!
# Monotonicity of the traversal set

Proves the frozen statement `Rotor.Frozen.monotonicity`, the paper's Proposition 2.5:
if `S ⊆ U` are nonempty finite vertex sets whose boundary routings under a mechanism `π`
both terminate, then the traversal set `Φ π ρ S` is contained in `Φ π ρ U`. The proof
routes through `Φ_mono` from `Rotor.Support.Monotone`, using the cited external results
(`Rotor.External.OneCircuit`, `Rotor.External.Abelian`, `Rotor.External.HolroydPropp`)
via the abelian bridge `Rotor.Bridge.abelian_holds`.
-/

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- The paper assumes that both boundary routings terminate; the proof uses only
-- the termination for `U`, so `hTS` is unused.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.monotonicity (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (ρ : Config G) (S U : Finset V) (hS : S.Nonempty)
    (hSU : S ⊆ U) (hTS : Terminates π S ρ) (hTU : Terminates π U ρ) :
    Φ π ρ S ⊆ Φ π ρ U
-- FROZEN-STATEMENT-END
:= Φ_mono π (Rotor.Bridge.abelian_holds G) hG ρ S U hS hSU hTU

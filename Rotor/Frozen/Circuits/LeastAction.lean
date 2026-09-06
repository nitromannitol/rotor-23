/-
Lemma 2.2 of rotor.tex, frozen.  `rotor.tex:727-738` (label `lem:least-action`):

  "Let $\xi_0,\ldots,\xi_n$ and $\widehat\xi_0,\ldots,\widehat\xi_m$ be legal
   routings with $\widehat\xi_0=\xi_0$.
   (a) If $\xi_n$ is stable, then $m\leq n$, and each vertex is actuated no
   more often in the second routing than in the first.
   (b) If $\xi_n$ and $\widehat\xi_m$ are both stable, then $m=n$, their
   final states agree, and each vertex is actuated equally often in the two
   routings."

The paper cites HLMPPW Lemma 3.9 and gives no proof; `External.Abelian` is
its hypothesis.  A routing is its initial state `ξ` and its
list of actuated vertices: `vs` is `ξ_0, …, ξ_n`, `ws` is
`ξ̂_0, …, ξ̂_m`, `n = vs.length`, `m = ws.length`.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
`[Infinite V]` and `hG` are the standing assumptions of Section 2 (`rotor.tex:678-680`:
"Throughout this section, `G` is infinite, connected, and locally finite, the rotor
mechanism and initial rotor configuration are fixed and arbitrary").
-/
import Rotor.Traversal
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.least_action (hAb : External.Abelian G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (S : Finset V) (hS : S.Nonempty) (ξ : RState G)
    (vs ws : List V) (hvs : IsLegal π S ξ vs) (hws : IsLegal π S ξ ws) :
    (Stable S (run π S ξ vs) → ws.length ≤ vs.length ∧ ∀ v, ws.count v ≤ vs.count v) ∧
    (Stable S (run π S ξ vs) → Stable S (run π S ξ ws) →
      ws.length = vs.length ∧ run π S ξ ws = run π S ξ vs ∧ ∀ v, ws.count v = vs.count v)
-- FROZEN-STATEMENT-END
:= hAb π inferInstance hG S hS ξ vs ws hvs hws

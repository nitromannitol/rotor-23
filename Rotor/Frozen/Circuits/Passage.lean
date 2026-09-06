/-
Proposition 2.6 of rotor.tex, frozen.  `rotor.tex:852-866` (label `prop:passage`):

  "For all vertices $x$, $y$, and $z$, $\tau(x,z)\leq\tau(x,y)+\tau(y,z)$,
   and $\tau(x,y)\leq d_G(x,y)$.  If the boundary routing of every nonempty
   finite set terminates, then for every integer $n\geq0$,
   $A_n=\{x:\tau(o,x)\leq n\}$."

Three displays, three conjuncts.  The third asserts `T n < ⊤` alongside the
set identity, so that `A n` is never read at its junk value.
The proof uses `prop:monotonicity` and `prop:circuit-iterate`.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
`[Infinite V]` and `hG` are the standing assumptions of Section 2 (`rotor.tex:678-680`:
"Throughout this section, `G` is infinite, connected, and locally finite, the rotor
mechanism and initial rotor configuration are fixed and arbitrary").
-/
import Rotor.Traversal
import Rotor.Support.Passage
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.passage (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (π : Mechanism G) [Infinite V] (hG : G.Connected) (ρ : Config G) (o : V) :
    (∀ x y z : V, τ π ρ x z ≤ τ π ρ x y + τ π ρ y z) ∧
    (∀ x y : V, τ π ρ x y ≤ G.dist x y) ∧
    (AllTerminate π ρ → ∀ n : ℕ, T π ρ o n < ⊤ ∧ ∀ x : V, x ∈ A π ρ o n ↔ τ π ρ o x ≤ n)
-- FROZEN-STATEMENT-END
:= passage_proof π hFLP hAb hG ρ o

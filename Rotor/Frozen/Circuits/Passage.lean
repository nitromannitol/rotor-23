/-
Proposition 2.6 of rotor.tex, frozen.  `rotor.tex:833-846` (label `prop:passage`):

  "For all vertices $x$, $y$, and $z$, $\tau(x,z)\leq\tau(x,y)+\tau(y,z)$,
   and $\tau(x,y)\leq d_G(x,y)$.  If the boundary routing of every nonempty
   finite set terminates, then for every integer $n\geq0$,
   $A_n=\{x:\tau(o,x)\leq n\}$."

Three displays, three conjuncts.  The third asserts `T n < ⊤` alongside the
set identity, so that `A n` is never read at its junk value (ruling M-008).
The proof uses `prop:monotonicity` and `prop:circuit-iterate`.
-/
import Rotor.Traversal
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
:= by sorry

/-
Proposition 2.4 of rotor.tex, frozen.  `rotor.tex:774-782` (label `prop:circuit-iterate`):

  "Let $n\geq0$ and suppose that $T(n)<\infty$.  Then $T(n+1)<\infty$ if and
   only if the boundary routing of $A_n$ terminates, and in that case
   $A_{n+1}=\Phi(A_n)$."

`Terminates π (A π ρ o n) ρ` and `Φ π ρ` are taken with the initial rotors
`ρ`, as the paper's boundary routing is ("with the fixed initial rotors on
`V ∖ S`", `rotor.tex:717-719`).  The proof uses `lem:one-circuit`,
`lem:boundary-routing` and `lem:least-action`.
-/
import Rotor.Traversal
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.circuit_iterate (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (π : Mechanism G) [Infinite V] (hG : G.Connected) (ρ : Config G) (o : V) (n : ℕ)
    (hn : T π ρ o n < ⊤) :
    (T π ρ o (n + 1) < ⊤ ↔ Terminates π (A π ρ o n) ρ) ∧
    (T π ρ o (n + 1) < ⊤ → A π ρ o (n + 1) = Φ π ρ (A π ρ o n))
-- FROZEN-STATEMENT-END
:= by sorry

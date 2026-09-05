/-
Proposition 2.8 of rotor.tex, frozen.  `rotor.tex:938-942` (label `prop:live-recurrence`):

  "If $G$ contains no infinite live path, then the boundary routing of every
   nonempty finite set terminates, $T(n)<\infty$ for every $n$, and the rotor
   walk is recurrent."

Three assertions, three conjuncts.  The proof uses König's lemma (Mathlib),
`lem:boundary-routing`, `lem:decreasing-positions`, `prop:circuit-iterate`,
and Holroyd--Propp Lemma 6 (`External.VisitsAllOfVisitsOne`).  The paper also
cites Angel--Holroyd Theorem 1 (recurrence does not depend on the starting
vertex); the statement as frozen is for the fixed start `o` and does not need it.
-/
import Rotor.Traversal
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.live_recurrence (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (π : Mechanism G) [Infinite V] (hG : G.Connected)
    (ρ : Config G) (o : V) (h : ¬ ∃ x : ℕ → V, IsInfPath G x ∧ IsInfLive π ρ x) :
    AllTerminate π ρ ∧ (∀ n : ℕ, T π ρ o n < ⊤) ∧ Recurrent π ρ o
-- FROZEN-STATEMENT-END
:= by sorry

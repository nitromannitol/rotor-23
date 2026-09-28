/-
Proposition 2.8 of rotor.tex, frozen.  `rotor.tex:957-961` (label `prop:live-recurrence`):

  "If $G$ contains no infinite live path, then the boundary routing of every
   nonempty finite set terminates, $T(n)<\infty$ for every $n$, and the rotor
   walk is recurrent."

Three assertions, three conjuncts.  The proof uses König's lemma (Mathlib),
`lem:boundary-routing`, `lem:decreasing-positions`, `prop:circuit-iterate`,
and Holroyd--Propp Lemma 6 (`External.VisitsAllOfVisitsOne`).  The paper also
cites Angel--Holroyd Theorem 1 (recurrence does not depend on the starting
vertex); the statement as frozen is for the fixed start `o` and does not need it.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
`[Infinite V]` and `hG` are the standing assumptions of Section 2 (`rotor.tex:678-680`:
"Throughout this section, `G` is infinite, connected, and locally finite, the rotor
mechanism and initial rotor configuration are fixed and arbitrary").
-/
import Rotor.Traversal
import Rotor.Support.LiveRecurrence
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.Bridge.Abelian
import Rotor.Bridge.OneCircuit
import Rotor.Bridge.HolroydPropp

/-!
# Live recurrence

States Proposition 2.8 of `rotor.tex` as a frozen, pinned theorem: if `G` contains no infinite
live path, then the boundary routing of every nonempty finite set terminates, `T(n) < ⊤` for
every `n`, and the rotor walk is recurrent. The proof combines König's lemma with
`lem:boundary-routing`, `lem:decreasing-positions`, `prop:circuit-iterate`, and Holroyd-Propp
Lemma 6, all assembled by `live_recurrence_proof`.
-/

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.live_recurrence
    (π : Mechanism G) [Infinite V] (hG : G.Connected)
    (ρ : Config G) (o : V) (h : ¬ ∃ x : ℕ → V, IsInfPath G x ∧ IsInfLive π ρ x) :
    AllTerminate π ρ ∧ (∀ n : ℕ, T π ρ o n < ⊤) ∧ Recurrent π ρ o
-- FROZEN-STATEMENT-END
:= live_recurrence_proof π (Rotor.Bridge.oneCircuit_holds G) (Rotor.Bridge.abelian_holds G)
    (Rotor.Bridge.visitsAllOfVisitsOne_holds G) hG ρ o h

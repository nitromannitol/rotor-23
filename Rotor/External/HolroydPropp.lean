/-
External input: Holroyd--Propp, *Rotor walks and Markov chains*, Lemma 6, as
the paper uses it in the proof of `prop:live-recurrence` (`rotor.tex:966-969`):

  "A rotor walk that visits one vertex infinitely often visits every vertex
   infinitely often."

With the standing assumptions of Section 2.

No longer assumed outright: `Rotor.Bridge.visitsAllOfVisitsOne_holds` in
`Rotor/Bridge/HolroydPropp.lean` proves it unconditionally, by propagating
infinitely-many-visits along a walk between any two vertices of the
(preconnected) graph; this `Prop` itself carries no manifest node any
longer (see ledger node `ext-holroyd-propp`, which now points at that
proof).
-/
import Rotor.Model

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- Holroyd--Propp Lemma 6. -/
def Rotor.External.VisitsAllOfVisitsOne : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o x : V), Set.Infinite {t : ℕ | X π ρ o t = x} → Recurrent π ρ o


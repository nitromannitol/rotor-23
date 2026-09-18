/-
External input: Holroyd--Propp, *Rotor walks and Markov chains*, Lemma 6, as
the paper uses it in the proof of `prop:live-recurrence` (`rotor.tex:966-969`):

  "A rotor walk that visits one vertex infinitely often visits every vertex
   infinitely often."

Assumed here, with the standing assumptions of Section 2.
-/
import Rotor.Model

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
/-- Holroyd--Propp Lemma 6, assumed. -/
def Rotor.External.VisitsAllOfVisitsOne : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o x : V), Set.Infinite {t : ℕ | X π ρ o t = x} → Recurrent π ρ o
-- FROZEN-STATEMENT-END


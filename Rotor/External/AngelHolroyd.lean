/-
External input: Angel--Holroyd, *Recurrent rotor-router configurations*
(2012), Theorem 1, as the paper uses it (`rotor.tex:968-969`): "recurrence
does not depend on the starting vertex".  Ruling X-001, with the standing
assumptions of Section 2.
-/
import Rotor.Model

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
/-- Angel--Holroyd Theorem 1, assumed. -/
def Rotor.External.RecurrentOfRecurrent : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o o' : V), Recurrent π ρ o → Recurrent π ρ o'
-- FROZEN-STATEMENT-END

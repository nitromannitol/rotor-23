/-
External input: Angel--Holroyd, *Recurrent rotor-router configurations*
(2012), Theorem 1, as the paper uses it (`rotor.tex:968-969`): "recurrence
does not depend on the starting vertex".  With the standing
assumptions of Section 2.

No longer assumed outright: `Rotor.Bridge.recurrentOfRecurrent_holds` in
`Rotor/Bridge/AngelHolroyd.lean` proves it unconditionally, along the route
Angel--Holroyd's own proof uses, through `Rotor.Bridge.abelian_holds`; this
`Prop` itself carries no manifest node any longer (see ledger node
`ext-angel-holroyd`, which now points at that proof).
-/
import Rotor.Model

/-!
# Angel–Holroyd recurrence-does-not-depend-on-the-vertex statement

This file records, as a `Prop`, the statement of Angel–Holroyd's Theorem 1 that for a rotor walk
on an infinite, connected, locally finite graph, recurrence at one vertex implies recurrence at
every other vertex. The statement is no longer taken as an external assumption: it is proved
unconditionally in `Rotor.Bridge.AngelHolroyd`, via the same route as Angel–Holroyd's own proof,
through the abelian property established in this development.
-/

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- Angel--Holroyd Theorem 1. -/
def Rotor.External.RecurrentOfRecurrent : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o o' : V), Recurrent π ρ o → Recurrent π ρ o'

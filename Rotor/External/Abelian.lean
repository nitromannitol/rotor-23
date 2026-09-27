/-
External input: the abelian property, Holroyd--Levine--Mészáros--Peres--Propp--
Wilson, *Chip-firing and rotor-routing on directed graphs*, Lemma 3.9, as the
paper states it in `lem:least-action` (`rotor.tex:727-741`):

  "Let `ξ_0, …, ξ_n` and `ξ̂_0, …, ξ̂_m` be legal routings with `ξ̂_0 = ξ_0`.
   (a) If `ξ_n` is stable, then `m ≤ n`, and each vertex is actuated no more
   often in the second routing than in the first.
   (b) If `ξ_n` and `ξ̂_m` are both stable, then `m = n`, their final states
   agree, and each vertex is actuated equally often in the two routings."

A routing is its initial state and its list of actuated vertices; `n` and `m`
are the lengths of those lists and actuation counts are `List.count`.

No longer assumed outright: `Rotor.Bridge.abelian_holds` in
`Rotor/Bridge/Abelian.lean` proves it unconditionally by induction on
legal routings (the standard diamond-lemma argument for the abelian
property); this `Prop` itself carries no manifest node any longer (see
ledger node `ext-abelian`, which now points at that proof).
-/
import Rotor.Routing

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- HLMPPW Lemma 3.9 (`lem:least-action`). -/
def Rotor.External.Abelian : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (S : Finset V), S.Nonempty → ∀ (ξ : RState G) (vs ws : List V),
      IsLegal π S ξ vs → IsLegal π S ξ ws →
      (Stable S (run π S ξ vs) → ws.length ≤ vs.length ∧ ∀ v, ws.count v ≤ vs.count v) ∧
      (Stable S (run π S ξ vs) → Stable S (run π S ξ ws) →
        ws.length = vs.length ∧ run π S ξ ws = run π S ξ vs ∧ ∀ v, ws.count v = vs.count v)


/-
External input: Florescu--Levine--Peres, *The range of a rotor walk*,
Lemmas 2.1 and 2.4, as the paper states them in `lem:one-circuit`
(`rotor.tex:691-697`):

  "For every integer `n ≥ 0` such that `T(n) < ∞`, the walk traverses each
   directed edge at most once during the time interval `T(n) ≤ t < T(n+1)`.
   If `T(n+1) < ∞`, then during this interval the walk departs from every
   vertex `x ∈ A_n` exactly `deg(x)` times."

It is a `Prop` and, before this development, entered only as
an explicit hypothesis.  FLP state their lemmas for connected locally finite
graphs, finite or infinite, and `prop:circuit-clock` (`rotor.tex:1148-1151`)
uses `lem:one-circuit` on "a connected locally finite graph", so infinitude is
not assumed here; the node `lem-one-circuit` adds Section 2's standing
assumption `[Infinite V]` when it restates the lemma.

No longer assumed outright: `Rotor.Bridge.oneCircuit_holds` in
`Rotor/Bridge/OneCircuit.lean` proves it unconditionally, by an injectivity
argument on the walk's traversed edges together with incoming/outgoing
degree counts at circuit times; this `Prop` itself carries no manifest node
any longer (see ledger node `ext-one-circuit`, which now points at that
proof).
-/
import Rotor.Traversal

/-!
# External input: FLP's one-circuit property

Packages `Rotor.External.OneCircuit`, the `Prop` form of Florescu-Levine-Peres' Lemmas 2.1 and
2.4 (`lem:one-circuit`): while `T(n) < ∞`, the walk traverses each directed edge at most once
during `[T(n), T(n+1))`, and if also `T(n+1) < ∞` it departs from every vertex of `A_n` exactly
`deg` many times during that interval. It is stated here only as a `Prop`;
`Rotor.Bridge.oneCircuit_holds` proves it unconditionally, and no certified statement carries it
as a hypothesis any longer.
-/

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- FLP Lemmas 2.1 and 2.4 (`lem:one-circuit`). -/
def Rotor.External.OneCircuit : Prop :=
  ∀ (π : Mechanism G), G.Connected →
    ∀ (ρ : Config G) (o : V) (n : ℕ), T π ρ o n < ⊤ →
      (∀ s t : ℕ, T π ρ o n ≤ (s : ℕ∞) → s < t → (t : ℕ∞) < T π ρ o (n + 1) →
          traversal π ρ o s ≠ traversal π ρ o t) ∧
      (T π ρ o (n + 1) < ⊤ → ∀ x ∈ A π ρ o n,
          departures π ρ o x (T π ρ o n).toNat (T π ρ o (n + 1)).toNat = G.degree x)


/-
External input: Florescu--Levine--Peres, *The range of a rotor walk*,
Lemmas 2.1 and 2.4, as the paper states them in `lem:one-circuit`
(`rotor.tex:691-697`):

  "For every integer `n ≥ 0` such that `T(n) < ∞`, the walk traverses each
   directed edge at most once during the time interval `T(n) ≤ t < T(n+1)`.
   If `T(n+1) < ∞`, then during this interval the walk departs from every
   vertex `x ∈ A_n` exactly `deg(x)` times."

This is assumed here.  It is a `Prop` and enters only as
an explicit hypothesis.  FLP state their lemmas for connected locally finite
graphs, finite or infinite, and `prop:circuit-clock` (`rotor.tex:1148-1151`)
uses `lem:one-circuit` on "a connected locally finite graph", so infinitude is
not assumed here; the node `lem-one-circuit` adds Section 2's standing
assumption `[Infinite V]` when it restates the lemma.
-/
import Rotor.Traversal

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
/-- FLP Lemmas 2.1 and 2.4 (`lem:one-circuit`), assumed. -/
def Rotor.External.OneCircuit : Prop :=
  ∀ (π : Mechanism G), G.Connected →
    ∀ (ρ : Config G) (o : V) (n : ℕ), T π ρ o n < ⊤ →
      (∀ s t : ℕ, T π ρ o n ≤ (s : ℕ∞) → s < t → (t : ℕ∞) < T π ρ o (n + 1) →
          traversal π ρ o s ≠ traversal π ρ o t) ∧
      (T π ρ o (n + 1) < ⊤ → ∀ x ∈ A π ρ o n,
          departures π ρ o x (T π ρ o n).toNat (T π ρ o (n + 1)).toNat = G.degree x)
-- FROZEN-STATEMENT-END


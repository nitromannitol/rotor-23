/-
External input: Florescu--Levine--Peres, *The range of a rotor walk*,
Lemmas 2.1 and 2.4, as the paper states them in `lem:one-circuit`
(`rotor.tex:691-697`):

  "For every integer `n ≥ 0` such that `T(n) < ∞`, the walk traverses each
   directed edge at most once during the time interval `T(n) ≤ t < T(n+1)`.
   If `T(n+1) < ∞`, then during this interval the walk departs from every
   vertex `x ∈ A_n` exactly `deg(x)` times."

Ruling X-001: this is assumed in phase one.  It is a `Prop` and enters only as
an explicit hypothesis.  The standing assumptions of Section 2
(`rotor.tex:678-680`: `G` infinite, connected, locally finite; mechanism and
rotors arbitrary) are part of the assumed statement.
-/
import Rotor.Traversal

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
/-- FLP Lemmas 2.1 and 2.4 (`lem:one-circuit`), assumed. -/
def Rotor.External.OneCircuit : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o : V) (n : ℕ), T π ρ o n < ⊤ →
      (∀ s t : ℕ, T π ρ o n ≤ (s : ℕ∞) → s < t → (t : ℕ∞) < T π ρ o (n + 1) →
          traversal π ρ o s ≠ traversal π ρ o t) ∧
      (T π ρ o (n + 1) < ⊤ → ∀ x ∈ A π ρ o n,
          departures π ρ o x (T π ρ o n).toNat (T π ρ o (n + 1)).toNat = G.degree x)
-- FROZEN-STATEMENT-END


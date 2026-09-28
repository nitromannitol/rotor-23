/-
External input: Kesten, *The critical probability of bond percolation on the
square lattice equals 1/2* (1980), together with the standard subcritical
bound, Grimmett, *Percolation*, Theorem 3.4 (Menshikov; Aizenman--Barsky), as
the paper states them (`rotor.tex:1658-1668`, `eq:square-subcritical-tail`):

  "for each `p < 1/2`, uniformly in `x` and `r ≥ 1`,
   `ℙ_p{x is joined to {y : |y-x|_∞ = r} inside {y : |y-x|_∞ ≤ r}} ≤ Ce^{-cr}`."

No longer assumed outright: `Rotor.Bridge.subcriticalDecay_holds` in
`Rotor/Bridge/SubcriticalDecay.lean` proves it unconditionally from the
percolation library `PercolationContinuity`; this `Prop` itself carries no
manifest node any longer (see ledger node `ext-subcritical-decay`, which now
points at that proof).
-/
import Rotor.Percolation

/-!
# Kesten's exponential decay below the critical bond probability

States, as a `Prop`, Kesten's theorem that the critical bond probability of the square lattice
is `1/2` together with the exponential tail bound of Menshikov and of Aizenman-Barsky for
`p < 1/2`, as cited in `rotor.tex:1658-1668`. It is no longer assumed as a hypothesis: it is
proved unconditionally in `Rotor.Bridge.subcriticalDecay_holds` from the percolation library
`PercolationContinuity`.
-/

open Rotor

/-- Kesten's theorem with exponential decay below `p_c = 1/2`. -/
def Rotor.External.SubcriticalDecay : Prop :=
  ∀ (p : NNReal) (hp : p ≤ 1), p < 1 / 2 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw p hp (boxCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r))

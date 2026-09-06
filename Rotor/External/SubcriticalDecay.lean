/-
External input: Kesten, *The critical probability of bond percolation on the
square lattice equals 1/2* (1980), together with the standard subcritical
bound, Grimmett, *Percolation*, Theorem 3.4 (Menshikov; Aizenman--Barsky), as
the paper states them (`rotor.tex:1658-1668`, `eq:square-subcritical-tail`):

  "for each `p < 1/2`, uniformly in `x` and `r ≥ 1`,
   `ℙ_p{x is joined to {y : |y-x|_∞ = r} inside {y : |y-x|_∞ ≤ r}} ≤ Ce^{-cr}`."

Assumed here.
-/
import Rotor.Percolation

open Rotor

-- FROZEN-STATEMENT-BEGIN
/-- Kesten's theorem with exponential decay below `p_c = 1/2`, assumed. -/
def Rotor.External.SubcriticalDecay : Prop :=
  ∀ (p : NNReal) (hp : p ≤ 1), p < 1 / 2 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw p hp (boxCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r))
-- FROZEN-STATEMENT-END

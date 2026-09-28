/-
Lemma 5.6 of rotor.tex, frozen.  `rotor.tex:2077-2084` (label `lem:square-forced-tests`):

  "Let $K$ be the number of forced tests.  There are constants $c,C>0$ such
   that, for every integer $m\geq1$, $\P_0\{K\geq m\}\leq Ce^{-cm}$."

The constants are explicit: the proof gives
$\P_0\{K\geq3k+1\}\leq(3/4)^k$, hence $\P_0\{K\geq m\}\leq(4/3)(3/4)^{m/3}$,
that is $C = 4/3$ and $e^{-c} = (3/4)^{1/3}$.
-/
import Rotor.Exploration
import Rotor.Support.ForcedCascade

open Rotor MeasureTheory

/-!
# Exponential tail for the number of forced tests

States Lemma 5.6 of `rotor.tex`: the number `K` of forced tests along a step of the exploration
process has an exponentially decaying tail, `P{K ≥ m} ≤ C e^{-cm}`, with the explicit constants
`C = 4/3` and `e^{-c} = (3/4)^{1/3}` coming from the geometric bound `P{K ≥ 3k+1} ≤ (3/4)^k`
proved along the way.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_forced_tests (f d : Site) (hd : squareGraph.Adj f (f + d)) :
    ∀ m : ℕ, 1 ≤ m →
      uniformLaw clockwise {ρ | (m : ℕ∞) ≤ forcedCount ρ f d} ≤
        ENNReal.ofReal ((4 / 3) * (3 / 4) ^ ((m : ℝ) / 3))
-- FROZEN-STATEMENT-END
:= square_forced_tests_proof f d hd

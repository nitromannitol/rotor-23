/-
Lemma 5.6 of rotor.tex, frozen.  `rotor.tex:2058-2065` (label `lem:square-forced-tests`):

  "Let $K$ be the number of forced tests.  There are constants $c,C>0$ such
   that, for every integer $m\geq1$, $\P_0\{K\geq m\}\leq Ce^{-cm}$."

The constants are explicit (ruling F-003): the proof gives
$\P_0\{K\geq3k+1\}\leq(3/4)^k$, hence $\P_0\{K\geq m\}\leq(4/3)(3/4)^{m/3}$,
that is $C = 4/3$ and $e^{-c} = (3/4)^{1/3}$.
-/
import Rotor.Exploration

open Rotor MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_forced_tests (f d : Site) (hd : squareGraph.Adj f (f + d)) :
    ∀ m : ℕ, 1 ≤ m →
      uniformLaw clockwise {ρ | (m : ℕ∞) ≤ forcedCount ρ f d} ≤
        ENNReal.ofReal ((4 / 3) * (3 / 4) ^ ((m : ℝ) / 3))
-- FROZEN-STATEMENT-END
:= by sorry

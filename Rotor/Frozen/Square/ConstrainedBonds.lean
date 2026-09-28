/-
Lemma 5.3 of rotor.tex, frozen.  `rotor.tex:1696-1711` (label `lem:square-constrained-bonds`):

  "There are constants $c,C>0$ such that the following holds for every
   $x\in\Z^2$ and every integer $r\geq1$.  For bond percolation on $\Z^2$ with
   parameter $1/2$,
   $\P_{1/2}\{$there is an open path from $x$ to $\{y:|y-x|_\infty=r\}$ inside
   $\{y:|y-x|_\infty\leq r\}$ containing no translate of $P_\star$, in either
   direction, as a consecutive subpath$\}\leq Ce^{-cr}$."

The constants route through `External.SubcriticalDecay` (the subcritical bound
at `1/2 - ε`), so they are existential.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
-/
import Rotor.Dual
import Rotor.External.SubcriticalDecay
import Rotor.Bridge.SubcriticalDecay
import Rotor.Support.ConstrainedBondsProof

/-!
# The constrained-bonds bound (Lemma 5.3)

The certified statement `Rotor.Frozen.square_constrained_bonds` of Lemma 5.3
(`lem:square-constrained-bonds`): for critical bond percolation on `Z^2`, the probability that
an open path from `x` to the boundary of an `L^∞` ball of radius `r` avoids every translate of
the forbidden pattern `P_⋆`, in either direction, decays exponentially in `r`, with universal
constants `c, C > 0`. The constants come from `External.SubcriticalDecay`, the subcritical
exponential decay bound at parameter `1/2 - ε`, discharged here by
`Rotor.Bridge.subcriticalDecay_holds`.
-/

open Rotor

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_constrained_bonds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) Rotor.half_le_one (constrainedCrossing x r) ≤
        ENNReal.ofReal (C * Real.exp (-c * r))
-- FROZEN-STATEMENT-END
:= square_constrained_bonds_proof Rotor.Bridge.subcriticalDecay_holds

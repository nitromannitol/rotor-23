/-
Lemma 5.3 of rotor.tex, frozen.  `rotor.tex:1677-1692` (label `lem:square-constrained-bonds`):

  "There are constants $c,C>0$ such that the following holds for every
   $x\in\Z^2$ and every integer $r\geq1$.  For bond percolation on $\Z^2$ with
   parameter $1/2$,
   $\P_{1/2}\{$there is an open path from $x$ to $\{y:|y-x|_\infty=r\}$ inside
   $\{y:|y-x|_\infty\leq r\}$ containing no translate of $P_\star$, in either
   direction, as a consecutive subpath$\}\leq Ce^{-cr}$."

The constants route through `External.SubcriticalDecay` (the subcritical bound
at `1/2 - ε`), so they are existential (ruling F-003).
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
-/
import Rotor.Dual
import Rotor.External.SubcriticalDecay

open Rotor

theorem Rotor.half_le_one : (1 / 2 : NNReal) ≤ 1 := by
  rw [div_le_one (by norm_num)]; norm_num

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_constrained_bonds (hSub : External.SubcriticalDecay) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) Rotor.half_le_one (constrainedCrossing x r) ≤
        ENNReal.ofReal (C * Real.exp (-c * r))
-- FROZEN-STATEMENT-END
:= by sorry

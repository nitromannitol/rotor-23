/-
Proposition 1.3 of rotor.tex, frozen.  `rotor.tex:309-314` (label `prop:pendant-counterexample`):

  "There exists $M_0<\infty$ such that for every $M\geq M_0$, the rotor walk on
   $G_M$ with the clockwise rotor mechanism and independent uniform initial
   rotors is transient."

"Transient" is "not recurrent" (`rotor.tex:209-210`), asserted almost surely
for every starting vertex.  $M_0$ is explicit: the proof's
bound $\sum_{n\geq1}(128(3/(M+4))^{1/3})^n<1$ holds exactly when
$M+4>3\cdot256^3$, that is $M\geq3\cdot256^3-3=50331645$.  The proof uses
`lem:one-circuit` (`External.OneCircuit`), and its last step, from positive
probability of $T(1)=\infty$ to almost-sure transience, uses that recurrence
does not depend on the starting vertex (`External.RecurrentOfRecurrent`)
together with ergodicity of the uniform law, which the paper's proof leaves
implicit.
Both cited results are proved rather than assumed: `External.OneCircuit` by
`Rotor.Bridge.oneCircuit_holds` and `External.RecurrentOfRecurrent` by
`Rotor.Bridge.recurrentOfRecurrent_holds`, so neither appears as a hypothesis
of the frozen statement below.
-/
import Rotor.Pendant
import Rotor.External.OneCircuit
import Rotor.Bridge.OneCircuit
import Rotor.Bridge.AngelHolroyd
import Rotor.Support.MainPendant

/-!
# The pendant counterexample: transience

States Proposition 1.3 of the paper (frozen below): for every `M` above an explicit threshold,
the clockwise rotor walk on the pendant graph `G_M` with independent uniform initial rotors is
almost surely transient from every vertex. The two external ingredients this draws on,
`External.OneCircuit` and `External.RecurrentOfRecurrent`, are proved elsewhere rather than
assumed, so neither appears as a hypothesis of the frozen statement.
-/

open Rotor MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.pendant_counterexample :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o
-- FROZEN-STATEMENT-END
:= pendant_counterexample_proof (fun M => Rotor.Bridge.oneCircuit_holds (pendantGraph M))
    (fun _M => Rotor.Bridge.recurrentOfRecurrent_holds)

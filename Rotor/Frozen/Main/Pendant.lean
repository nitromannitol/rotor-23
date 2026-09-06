/-
Proposition 1.3 of rotor.tex, frozen.  `rotor.tex:300-305` (label `prop:pendant-counterexample`):

  "There exists $M_0<\infty$ such that for every $M\geq M_0$, the rotor walk on
   $G_M$ with the clockwise rotor mechanism and independent uniform initial
   rotors is transient."

"Transient" is "not recurrent" (`rotor.tex:209-210`), asserted almost surely
for every starting vertex.  $M_0$ is explicit (ruling F-003): the proof's
bound $\sum_{n\geq1}(128(3/(M+4))^{1/3})^n<1$ holds exactly when
$M+4>3\cdot256^3$, that is $M\geq3\cdot256^3-3=50331645$.  The proof uses
`lem:one-circuit` (`External.OneCircuit`), and its last step, from positive
probability of $T(1)=\infty$ to almost-sure transience, uses that recurrence
does not depend on the starting vertex (`External.RecurrentOfRecurrent`)
together with ergodicity of the uniform law, which the paper's proof leaves
implicit; see `ledger/ERRATA.md`, E-001.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
-/
import Rotor.Pendant
import Rotor.External.OneCircuit
import Rotor.External.AngelHolroyd
import Rotor.Support.MainPendant

open Rotor MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.pendant_counterexample
    (hFLP : ∀ M : ℕ, External.OneCircuit (pendantGraph M))
    (hAH : ∀ M : ℕ, External.RecurrentOfRecurrent (pendantGraph M)) :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o
-- FROZEN-STATEMENT-END
:= pendant_counterexample_proof hFLP hAH

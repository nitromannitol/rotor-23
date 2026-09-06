/-
Proposition 3.2 of rotor.tex, frozen.  `rotor.tex:1113-1123` (label `prop:passage-limit`):

  "There is a deterministic continuous subadditive function
   $\mu:\R^2\to[0,\infty)$ such that $\mu(\theta x)=\theta\mu(x)$ for every
   $\theta\geq0$ and $\lim_{R\to\infty}\sup_{|x|\geq R}|\tau(o,x)-\mu(x)|/|x|=0$
   almost surely.  The function $\mu$ does not depend on the base point $o$."

Standing assumptions (`rotor.tex:1059-1064`): those of `prop:path-reduction`
(iii): the graph and mechanism doubly periodic, the law invariant and ergodic,
and the almost-live-path hypothesis.  The vertex `o` is identified with the
origin, so `|x|` is `‖emb x - emb o‖` and `μ` is evaluated at
`emb x - emb o`; the uniform limit is written in `ε`-`R₀` form.  That `μ`
does not depend on `o` is the position of `∃ μ` before `∀ o`.  The paper
writes `μ` for both the law and the function; the function is `f` here.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
-/
import Rotor.Events
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.Support.PassageUniform

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- The paper's standing assumptions (`hFLP`, `hHP`, the criterion) are not used by the
-- proof: the passage function exists for every invariant ergodic law.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.passage_limit (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) (P : DoublyPeriodic G) (hπ : P.Periodic π)
    (hinv : P.Invariant μ) (herg : P.Ergodic μ) :
    ∃ f : Plane → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x y, f (x + y) ≤ f x + f y) ∧
      (∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x) ∧
      ∀ o : V, ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : V, R₀ ≤ ‖P.emb x - P.emb o‖ →
        |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ ε * ‖P.emb x - P.emb o‖
-- FROZEN-STATEMENT-END
:= passage_limit_proof π P hK hπ hAb hG μ hinv herg

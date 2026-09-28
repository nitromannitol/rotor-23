/-
Lemma 3.5 of rotor.tex, frozen.  `rotor.tex:1246-1257` (label `lem:block-live-paths`):

  "There are $\varepsilon>0$ and $L_0\geq1$ with the following property.  Let
   $L\geq L_0$ and suppose that $\sup_{z\in\Z^2}\P_0(\mathcal C_z)<\varepsilon$.
   Then \eqref{eq:criterion-path-hypothesis} holds under $\P_0$ for some
   $\eta>0$.  There is also $\delta>0$ such that the same $\eta$ works for
   every product law whose marginal at each vertex $x$ is within total
   variation distance $\delta$ of $\nu_x$."

Setting (`rotor.tex:1212-1226`): `G` doubly periodic with an arbitrary
mechanism, `ν` the one-vertex laws, `ℙ_0` their product.  Quantifier order
as in the paper: `ε, L₀` first, then `L` and the block hypothesis, then `η`,
then `δ`; `ε, L₀` are bound before `ν`, which the proof supports.  The
proof uses LSS domination (`External.LSS`).
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
-/
import Rotor.Events
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.Support.BlockFinalC

/-!
# Lemma 3.5: the block criterion forces a live-path criterion

States `lem:block-live-paths`: for a doubly periodic graph with an arbitrary mechanism, once the
supremum over blocks of the block event's probability is small enough, the resulting criterion
holds for the initial product law, with a fixed exponent `η` that continues to work for every
product law whose one-vertex marginals stay within a fixed total variation distance of the
original ones. The statement is frozen; its proof, `block_live_paths_proof`, is supplied
elsewhere and uses LSS domination.
-/

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.block_live_paths (hLSS : External.LSS) (P : DoublyPeriodic G)
    (π : Mechanism G) [Infinite V] (hG : G.Connected) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℕ, 1 ≤ L₀ ∧
      ∀ (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)],
      ∀ L : ℕ, L₀ ≤ L →
        (⨆ z : ℤ × ℤ, productLaw ν (blockEvent π P L z)) < ENNReal.ofReal ε →
        ∃ η : ℝ, 0 < η ∧ Criterion π (productLaw ν) η ∧
          ∃ δ : ℝ, 0 < δ ∧
            ∀ (ν' : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν' v)],
              (∀ v, tvDist (ν' v) (ν v) ≤ δ) → Criterion π (productLaw ν') η
-- FROZEN-STATEMENT-END
:= block_live_paths_proof π P hLSS hG

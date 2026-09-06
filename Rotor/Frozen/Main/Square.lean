/-
Theorem 1.1 of rotor.tex, the square-lattice case, frozen.  `rotor.tex:228-250`
(label `thm:main`):

  "Let $G$ be either the square lattice with its clockwise rotor mechanism, or
   a doubly periodic graph in $\R^2$ of maximum degree 3, with a doubly
   periodic rotor mechanism.  Suppose that the initial rotors are independent
   and uniform among the directed edges out of each vertex, and start the
   rotor walk at a fixed vertex $o$.  The following statements hold almost
   surely.
   (i) The walk is recurrent.
   (ii) There exist a deterministic compact convex set $B\subset\R^2$,
   containing the origin in its interior, and a deterministic constant
   $\kappa>0$ such that, in Hausdorff distance, $n^{-1}A_n\to B$ and
   $t^{-1/3}R_t\to\kappa B$.
   (iii) The limit $\lim_{t\to\infty}|R_t|t^{-2/3}$ exists, is deterministic,
   and is positive and finite."

The theorem is split into two nodes, one per case (`thm-main-square`,
`thm-main-degree-three`).  Conventions: `B`, `κ` and the limit `c` are
bound before the almost-sure quantifier; `T(n) < ∞` is
asserted so that `A_n` is never its junk value; (ii) is frozen both as
Hausdorff limits and as the sandwich of `prop:circuit-shape`; the
lattice is drawn by `squareEmb` relative to `o`.  The external inputs are
those of Sections 2, 3 and 5.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
-/
import Rotor.Events
import Rotor.Percolation
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.External.SubcriticalDecay
import Rotor.Support.MainSquare

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.main_square (hFLP : External.OneCircuit squareGraph)
    (hAb : External.Abelian squareGraph) (hHP : External.VisitsAllOfVisitsOne squareGraph)
    (hK : External.Kingman.{0}) (hLSS : External.LSS) (hSub : External.SubcriticalDecay)
    (o : Site) :
    ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ᵐ ρ ∂(uniformLaw clockwise), Recurrent clockwise ρ o ∧ (∀ n : ℕ, T clockwise ρ o n < ⊤) ∧
        Tendsto (fun n : ℕ => Metric.hausdorffDist
          ((n : ℝ)⁻¹ • ((fun x => squareEmb x - squareEmb o) '' (A clockwise ρ o n : Set Site))) B) atTop (𝓝 0) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
          (∀ x : Site, squareEmb x - squareEmb o ∈ ((1 - ε) * n) • B → x ∈ A clockwise ρ o n) ∧
          (∀ x ∈ A clockwise ρ o n, squareEmb x - squareEmb o ∈ ((1 + ε) * n) • B)) ∧
        Tendsto (fun t : ℕ => Metric.hausdorffDist
          (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => squareEmb x - squareEmb o) '' (R clockwise ρ o t : Set Site)))
          (κ • B)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℕ => ((R clockwise ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)
-- FROZEN-STATEMENT-END
:= main_square_proof hFLP hAb hHP hK hLSS hSub o

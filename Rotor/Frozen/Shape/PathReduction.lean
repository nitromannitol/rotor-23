/-
Proposition 3.1 of rotor.tex, frozen.  `rotor.tex:1033-1066` (label `prop:path-reduction`):

  "Let $G$ be an infinite connected graph of bounded degree with an arbitrary
   rotor mechanism, and let $\P$ be a law for the initial rotors.  Suppose
   that, for some $\eta>0$, $\lim_{R\to\infty}\sup_{u\to v}\P\{\mathcal
   L_\eta(u\to v,R)\}=0$.  Then the following statements hold.
   (i) Almost surely, the boundary routing of every nonempty finite set
   terminates and the walk is recurrent.
   (ii) Writing $\tau$ for the passage time, there is $a>0$ such that
   $\lim_{R\to\infty}\sup_{d_G(x,y)\geq R}\P\{\tau(x,y)\leq ad_G(x,y)\}=0$.
   (iii) If, in addition, $G$ and the rotor mechanism are doubly periodic and
   the rotor law is invariant and ergodic under the translation lattice, then
   there exist a deterministic compact convex set $B\subset\R^2$ containing
   the origin in its interior and deterministic constants $\kappa,c_*>0$ such
   that, almost surely, $n^{-1}A_n\to B$, $t^{-1/3}R_t\to\kappa B$,
   $|R_t|=c_*t^{2/3}+o(t^{2/3})$, where the set limits are in Hausdorff
   distance."

Three items, three conjuncts.  In (i) the walk from every start is recurrent
(the paper fixes no start there).  In (iii) the start `o` is arbitrary, the
sets are drawn through `P.emb` relative to `o` (the paper identifies `o` with
the origin), `T(n) < ∞` is asserted so that `A_n` is
never its junk value, and `B`, `κ`, `c_*` are bound before
the almost-sure quantifier.  The proof uses Sections 2 and 3,
hence the external inputs of Section 2 and Kingman's theorem.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed
here: they are not derived in this repository and the certificate lists them.
-/
import Rotor.Events
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS
import Rotor.Support.PathReductionIII

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.path_reduction (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (hdeg : ∃ D : ℕ, ∀ v, G.degree v ≤ D)
    (μ : Measure (Config G)) [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η)
    (hcrit : Criterion π μ η) :
    (∀ᵐ ρ ∂μ, AllTerminate π ρ ∧ ∀ o : V, Recurrent π ρ o) ∧
    (∃ a : ℝ, 0 < a ∧
      Tendsto (fun R : ℕ => ⨆ (x : V) (y : V) (_ : R ≤ G.dist x y),
        μ {ρ | (τ π ρ x y : ℝ) ≤ a * G.dist x y}) atTop (𝓝 0)) ∧
    (∀ P : DoublyPeriodic G, P.Periodic π → P.Invariant μ → P.Ergodic μ → ∀ o : V,
      ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
      ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
        ∀ᵐ ρ ∂μ, (∀ n : ℕ, T π ρ o n < ⊤) ∧
          Tendsto (fun n : ℕ =>
            Metric.hausdorffDist ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V))) B) atTop (𝓝 0) ∧
          Tendsto (fun t : ℕ =>
            Metric.hausdorffDist (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => P.emb x - P.emb o) '' (R π ρ o t : Set V)))
              (κ • B)) atTop (𝓝 0) ∧
          Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c))
-- FROZEN-STATEMENT-END
:= path_reduction_proof π hFLP hAb hHP hK hG hdeg μ η hη hcrit

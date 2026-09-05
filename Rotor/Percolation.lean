/-
Bernoulli bond percolation on `ℤ²`, `rotor.tex:1658-1668`:

  "Write `ℙ_p` for Bernoulli bond percolation on `ℤ²` with parameter `p`.  We
   use `p_c(ℤ²) = 1/2` [Kesten] and the standard subcritical bound [Grimmett,
   Theorem 3.4]: for each `p < 1/2`, uniformly in `x` and `r ≥ 1`,
   `ℙ_p{x is joined to {y : |y-x|_∞ = r} inside {y : |y-x|_∞ ≤ r}} ≤ Ce^{-cr}`."

  M-018  A bond configuration is a function `Sym2 Site → Bool`; the coordinates
         at non-edges are never read, so the product of Bernoulli(`p`) laws
         over `Sym2 Site` is Bernoulli bond percolation on the bonds of `ℤ²`
         with independent unused coins elsewhere.
-/
import Rotor.Square
import Rotor.External.LSS

open MeasureTheory

namespace Rotor

/-- A bond configuration on `ℤ²` (ruling M-018). -/
abbrev BondConfig := Sym2 Site → Bool

/-- Bernoulli bond percolation `ℙ_p`. -/
noncomputable def bondLaw (p : NNReal) (hp : p ≤ 1) : Measure BondConfig :=
  Measure.infinitePi (fun _ : Sym2 Site => External.bernoulli p hp)

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (bondLaw p hp) := by
  unfold bondLaw; infer_instance

/-- The `ℓ^∞` distance on `ℤ²`. -/
def linfDist (x y : Site) : ℤ := max |x.1 - y.1| |x.2 - y.2|

/-- An open path: consecutive sites are adjacent and the bond between them is open. -/
def IsOpenPath (ω : BondConfig) (l : List Site) : Prop :=
  IsPath squareGraph l ∧ l.IsChain (fun u v => ω s(u, v) = true)

/-- `x` is joined to `{y : |y-x|_∞ = r}` by an open path inside `{y : |y-x|_∞ ≤ r}`. -/
def boxCrossing (x : Site) (r : ℕ) : Set BondConfig :=
  {ω | ∃ l : List Site, IsOpenPath ω l ∧ l.head? = some x ∧ (∀ y ∈ l, linfDist y x ≤ r) ∧
    ∃ y ∈ l.getLast?, linfDist y x = r}

end Rotor

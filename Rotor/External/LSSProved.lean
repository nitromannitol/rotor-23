import Rotor.External.LSS
import LatticeProb.Prob.Percolation.LSS.Planar

/-!
# The Liggett--Schonmann--Stacey domination input, proved

`Rotor.External.LSS` states, in the instance used by the paper, the domination theorem of
Liggett, Schonmann and Stacey: some `ε > 0` makes every `2`-dependent `{0,1}`-field on `ℤ²` whose
one-site probabilities are at most `2ε` dominated, on increasing events, by independent
Bernoulli(`1/8`) variables.  The library `Lattice-Probability` proves this bound
(`LatticeProb.Percolation.LSS.exists_consumerThin`) with the dependence predicate, the increasing
events and the product field written exactly as `Rotor.External` defines them, so the statement
follows by unfolding `External.LSS`.
-/

namespace Rotor.External

/-- The Liggett--Schonmann--Stacey domination input `External.LSS`, proved from the domination
bound of the library `Lattice-Probability`. -/
theorem lss_holds : LSS :=
  LatticeProb.Percolation.LSS.exists_consumerThin

end Rotor.External

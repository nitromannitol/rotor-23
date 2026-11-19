import Rotor.Frozen.Unconditional.BlockLivePaths
import Rotor.Frozen.Unconditional.MainSquareUnconditional
import Rotor.Frozen.Unconditional.MainDegreeThreeUnconditional
import Rotor.Frozen.Unconditional.PerturbationsSquareUnconditional
import Rotor.Frozen.Unconditional.PerturbationsDegreeThreeUnconditional
import Rotor.MainTheoremsUnconditional

/-!
# Axioms audit

Building this module prints the axiom dependencies of the five main theorems
of `Rotor/MainTheorems.lean`.  Each must report exactly the three standard
foundational axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The unconditional forms use the proved domination theorem.

This file is not imported by the library root; the report runs when it is built
explicitly (`lake build Rotor.Meta.AxiomsAudit`), as continuous integration
does on every push.
-/

#print axioms Rotor.main_square
#print axioms Rotor.main_degree_three
#print axioms Rotor.perturbations_square
#print axioms Rotor.perturbations_degree_three
#print axioms Rotor.pendant_counterexample

#print axioms Rotor.External.lss_holds
#print axioms Rotor.main_square_unconditional
#print axioms Rotor.main_degree_three_unconditional
#print axioms Rotor.perturbations_square_unconditional
#print axioms Rotor.perturbations_degree_three_unconditional

#print axioms Rotor.Frozen.block_live_paths_unconditional
#print axioms Rotor.Frozen.main_square_unconditional
#print axioms Rotor.Frozen.main_degree_three_unconditional
#print axioms Rotor.Frozen.perturbations_square_unconditional
#print axioms Rotor.Frozen.perturbations_degree_three_unconditional

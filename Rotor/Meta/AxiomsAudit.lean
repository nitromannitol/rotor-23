import Rotor.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the five main theorems
of `Rotor/MainTheorems.lean`.  Each must report exactly the three standard
foundational axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The results the paper cites without proof are not axioms here: each is a
`Prop` in `Rotor/External/` taken as an explicit hypothesis of the theorems
that use it, so it appears in the statement, not in this list.

This file is not imported by the library root; the report runs when it is built
explicitly (`lake build Rotor.Meta.AxiomsAudit`), as continuous integration
does on every push.
-/

#print axioms Rotor.main_square
#print axioms Rotor.main_degree_three
#print axioms Rotor.perturbations_square
#print axioms Rotor.perturbations_degree_three
#print axioms Rotor.pendant_counterexample

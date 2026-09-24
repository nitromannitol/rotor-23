import Audit.Support.Statements
import Audit.MainSquare.Solution
import Audit.MainDegreeThree.Solution
import Audit.PerturbationsSquare.Solution
import Audit.PerturbationsDegreeThree.Solution
import Audit.PendantCounterexample.Solution

/-!
# Statement regression for the comparator solutions

For each audited theorem, checks that the type of the solution theorem is
exactly the proposition elaborated in the challenge environment
(`Audit/Support/Statements.lean`), and that it mentions no constant of the
repository namespace `Rotor`.  Building this module prints one line per
theorem; any mismatch is an error.  This is a local proxy for the
statement-identity part of `leanprover/comparator`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (thm, stmt) in [
    (`RotorAudit.main_square, `RotorAudit.Statements.mainSquare),
    (`RotorAudit.main_degree_three, `RotorAudit.Statements.mainDegreeThree),
    (`RotorAudit.perturbations_square, `RotorAudit.Statements.perturbationsSquare),
    (`RotorAudit.perturbations_degree_three, `RotorAudit.Statements.perturbationsDegreeThree),
    (`RotorAudit.pendant_counterexample, `RotorAudit.Statements.pendantCounterexample)] do
    let some ti := env.find? thm | throwError "missing theorem {thm}"
    let some si := env.find? stmt | throwError "missing statement {stmt}"
    let some v := si.value? | throwError "statement {stmt} has no value"
    -- A `def` abstracts the proofs inside its value into auxiliary lemmas
    -- (`RotorAudit.Statements.*._proof_i`, shared between declarations);
    -- put their proof terms back before comparing.
    let v := v.replace fun e => match e with
      | .const n ls =>
        if (`RotorAudit.Statements).isPrefixOf n && n.isInternal then
          (env.find? n).bind fun ci => (ci.value? (allowOpaque := true)).map (·.instantiateLevelParams ci.levelParams ls)
        else none
      | _ => none
    let v ← liftCoreM (Core.betaReduce v)
    let ty ← liftCoreM (Core.betaReduce ti.type)
    unless ty == v do
      throwError "{thm}: the solution statement differs from the challenge statement"
    for c in ti.type.getUsedConstants do
      if (`Rotor).isPrefixOf c then
        throwError "{thm} mentions the repository constant {c}"
    logInfo m!"{thm}: identical to the challenge statement; no repository constant"

#print axioms RotorAudit.main_square
#print axioms RotorAudit.main_degree_three
#print axioms RotorAudit.perturbations_square
#print axioms RotorAudit.perturbations_degree_three
#print axioms RotorAudit.pendant_counterexample

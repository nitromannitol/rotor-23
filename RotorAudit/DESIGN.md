# Comparator design memo: vocabulary, bridges, deltas

This memo records how the five comparator pairs are built, for whoever checks
or extends them.  Each pair `RotorAudit/<Thm>/` has the same four files, and
each pair has its own bridge under `RotorAudit/Support/`.

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object its theorem mentions: the rotor walk on a locally
  finite graph, its range, circuit times and circuit ranges, recurrence, the
  product law of the initial rotors, doubly periodic graphs, the square lattice
  and the graph `G_M`, and the cited results.  It states the theorem and ends in
  a single `sorry`.  This file is the object of trust: a reader checks what it
  says, not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`).  It imports
  only `Mathlib`, so the vocabulary elaborates in the solution exactly as in the
  challenge.
- `Solution.lean` imports the repository together with its own `SolutionBasic`
  and its own bridge `RotorAudit/Support/<Thm>Bridge.lean`, restates the
  challenge theorem byte-for-byte, and proves it from the corresponding theorem
  of `Rotor/MainTheorems.lean`.
- `comparator.json` names the challenge module, the solution module, the theorem
  and the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and
  enables the nanoda kernel.

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  The vocabulary is therefore compiled in a module that
imports **only Mathlib** (`<Thm>/SolutionBasic.lean`), and `Solution.lean`
imports the repository, that module, and the pair's bridge, and states the
theorem with the challenge's bytes.

The five challenges share one vocabulary block, byte-identical in each
(`bash RotorAudit/check_standalone.sh --vocabulary` compares each challenge with
its `SolutionBasic.lean`), so the five `SolutionBasic.lean` files carry the same
block.  The block contains a few definitions that a given challenge does not use
(for instance `G_M` in the square-lattice challenges); they do not enter that
theorem's dependency closure.

The Lean namespace of the audit surface is `RotorAudit` and its modules live
under `RotorAudit.*`.

## 1. Definitionally shared vocabulary

Every definition of the vocabulary that is not a structure is a token-for-token
copy of the repository's, over Mathlib types.  These are definitionally equal
to their repository counterparts.  A bridge states the equality with `rfl` where
the solution rewrites with it; elsewhere the solution's `exact` unfolds it:

| Vocabulary | Repository | Bridge lemma, in the bridge of |
| --- | --- | --- |
| `clockwise` (after `toMech`) | `Rotor.clockwise` | `toMech_clockwise`: `MainSquare`, `PerturbationsSquare` |
| `pendantMech M` (after `toMech`) | `Rotor.pendantMech M` | `toMech_pendantMech`: `PendantCounterexample` |
| `uniformLaw` | the repository's, at `toMech π` | `uniformLaw_eq`: `MainSquare`, `MainDegreeThree`, `PendantCounterexample` |
| `External.LSS` | `Rotor.External.LSS` | `lss`: the four pairs that carry it |
| `DoublyPeriodic.Periodic` | the repository's, at `toDP P` | `periodic_iff`: `MainDegreeThree`, `PerturbationsDegreeThree` |
| `squareGraph`, `squarePeriodic` (after `toDP`), `pendantGraph M`, `uniformAt`, `productLaw`, `DoublyPeriodic.InvariantMarginals`, `tvDist`, `squareEmb`, `Plane`, the `σ`-algebra instance on neighbor sets | the repository's | none: used definitionally |

The `rfl` proofs and the `exact` of each solution unfold the vocabulary's own
instances (`squareGraph.LocallyFinite`, `(pendantGraph M).LocallyFinite`, the
discrete `σ`-algebra) against the repository's; they are not asserted, they
are checked by the kernel.

## 2. Structure copies

Four vocabulary declarations are structures, hence new inductive types:
`Mechanism`, `State`, `RState`, `DoublyPeriodic`.  Each bridge converts, field
by field, the structures that its statement mentions (`toMech`, and `toDP` where
the statement has a doubly periodic graph) and proves, rather than assumes, that
the objects built on them agree:

- `step_eq`, `walk_eq` (induction on time): the vocabulary walk and the
  repository walk at `toMech π` have the same position and rotors at every
  time;
- `X_eq`, `R_eq`, `visits_eq`, `T_eq`, `A_eq`, `Recurrent_eq`: consequences of
  `walk_eq`.

The bridge of `PendantCounterexample` stops at `X_eq` and `Recurrent_eq`, since
its statement mentions no range, circuit time or circuit range.  The routings
(`RState`) and the cited-result propositions `OneCircuit`, `Abelian`,
`VisitsAllOfVisitsOne` and `RecurrentOfRecurrent` occur in no audited statement,
so no bridge converts `RState` or relates those propositions to the
repository's; the vocabulary defines them because its block is shared.

## 3. Theorem-level bridges

Each solution applies the theorem of `Rotor/MainTheorems.lean` to the
transported hypotheses (`lss`, and `toDP`, `toMech` and `periodic_iff` where the
statement has a doubly periodic graph), rewrites the goal with the
identifications its statement needs (`T_eq`, `A_eq`, `R_eq`, `Recurrent_eq` and,
where they occur, `uniformLaw_eq`, `toMech_clockwise`, `toMech_pendantMech`), and
closes it with `exact`; the remaining identifications (`squareGraph`,
`squareEmb`, `P.emb` against `(toDP P).emb`, `tvDist`, `squarePeriodic.shiftNbr`,
the product laws) are definitional.

## 4. Presentation deltas

None at the level of the displayed statements: each challenge theorem is the
statement of the corresponding theorem of `Rotor/MainTheorems.lean`, which is
the certified statement in `Rotor/Frozen/Main/`, with every repository name
replaced by its vocabulary copy.  The theorems carry exactly the hypotheses of
their library counterparts: `External.LSS` for `main_square`,
`main_degree_three`, `perturbations_square` and `perturbations_degree_three`,
and none for `pendant_counterexample`.  The other six cited results are proved
in `Rotor/Bridge/` and are not hypotheses of any audited theorem.

How each statement reads the paper, clause by clause, is recorded in the
repository ledger (`tools/check_clauses.py`) and summarized in
[`CORRESPONDENCE.md`](../CORRESPONDENCE.md).  The comparator does not check
that reading: it checks that the library proves exactly the displayed
statement, over definitions that can be read without the library.

## 5. What the comparator does not certify

- The cited results.  The challenges take them as hypotheses, restated in the
  vocabulary.  A proof conditional on a proposition does not show that the
  proposition is a faithful rendering of the cited theorem; that reading is
  the subject of `ASSUMPTIONS.md` and of the ledger.
- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the repository's definitions, so the comparator shows that nothing in the
  statements depends on the library beyond what the vocabulary displays; a
  reader still has to check the vocabulary against the paper.

## 6. What the comparator checks

The comparator itself checks each solution statement against its challenge,
constant by constant through the whole dependency closure, the closure against
Mathlib, and the axioms of the solution against the permitted three.  Each
solution imports both the repository and its own vocabulary, and both declare a
high-priority discrete `σ`-algebra on `G.neighborSet v`; the closure check is
what shows that no solution statement picked up a repository constant, in
particular not the repository's instance.  Every pair passes with the Lean
kernel and with the independent nanoda kernel; see
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the results and the reproduction
steps.  There is no separate local regression: the five solutions cannot be
imported into one module, because each pair has its own copy of the vocabulary.

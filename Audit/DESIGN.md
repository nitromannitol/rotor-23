# Comparator design memo: vocabulary, bridges, deltas

This memo records how the five comparator pairs are built, for whoever checks
or extends them.  The files are `Audit/<Thm>/Challenge.lean`,
`Audit/<Thm>/Solution.lean`, `Audit/Support/Vocabulary.lean` (the
Mathlib-only copy of the vocabulary), `Audit/Support/Bridge.lean` (the
transports), `Audit/Support/Statements.lean` and
`Audit/StatementRegression.lean` (the local statement check).

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining` and
`Superdiffusion` repositories, the vocabulary is therefore compiled in a module
that imports **only Mathlib** (`Audit/Support/Vocabulary.lean`, the analogue
of their per-challenge `SolutionBasic.lean`), and `Solution.lean` imports the
repository, that module, and the bridges, and states the theorem with the
challenge's bytes.

The five challenges share one vocabulary block, byte-identical in each
(`bash Audit/check_standalone.sh --vocabulary`), so one `Vocabulary.lean`
serves all five solutions.  The block contains a few definitions that a given
challenge does not use (for instance `G_M` in the square-lattice challenges);
they do not enter that theorem's dependency closure.

## 1. Definitionally shared vocabulary

Every definition of the vocabulary that is not a structure is a token-for-token
copy of the repository's, over Mathlib types.  These are definitionally equal
to their repository counterparts, and the bridges state it with `rfl`:

| Vocabulary | Repository | Bridge |
| --- | --- | --- |
| `squareGraph` | `Rotor.squareGraph` | `squareGraph_eq` |
| `clockwise` (after `toMech`) | `Rotor.clockwise` | `toMech_clockwise` |
| `squarePeriodic` (after `toDP`) | `Rotor.squarePeriodic` | `toDP_squarePeriodic` |
| `pendantGraph M`, `pendantMech M` | `Rotor.pendantGraph M`, `Rotor.pendantMech M` | `pendantGraph_eq`, `toMech_pendantMech` |
| `uniformAt`, `uniformLaw`, `productLaw` | the repository's, at `toMech π` | `uniformAt_eq`, `uniformLaw_eq`, `productLaw_eq` |
| `External.LSS` | `Rotor.External.LSS` | `lss` |
| `DoublyPeriodic.Periodic`, `InvariantMarginals` | the repository's, at `toDP P` | `periodic_iff`, `invariantMarginals_iff` |
| `tvDist`, `squareEmb`, `Plane`, the `σ`-algebra instance on neighbor sets | the repository's | used definitionally |

The `rfl` proofs of the concrete-graph equalities unfold the vocabulary's own
instances (`squareGraph.LocallyFinite`, `(pendantGraph M).LocallyFinite`, the
discrete `σ`-algebra) against the repository's; they are not asserted, they
are checked by the kernel.

## 2. Structure copies

Four vocabulary declarations are structures, hence new inductive types:
`Mechanism`, `State`, `RState`, `DoublyPeriodic`.  The bridges convert field by
field (`toMech`/`ofMech`, `toRS`/`ofRS`, `toDP`) and prove, rather than assume,
that the objects built on them agree:

- `step_eq`, `walk_eq` (induction on time): the vocabulary walk and the
  repository walk at `toMech π` have the same position and rotors at every
  time;
- `X_eq`, `R_eq`, `visits_eq`, `T_eq`, `A_eq`, `Recurrent_eq`,
  `traversal_eq`, `departures_eq`: consequences of `walk_eq`;
- `actuate_eq`, `run_eq` (induction on the routing list), `isLegal_iff`,
  `stable_iff`, `toRS_injective`: the routings of the abelian property.

From these, each cited-result proposition of the vocabulary implies the
repository's (`oneCircuit`, `abelian`, `visitsAllOfVisitsOne`,
`recurrentOfRecurrent`): given a repository mechanism `π`, apply the
vocabulary hypothesis to `ofMech π`, and rewrite with the equalities above and
`toMech (ofMech π) = π`.

## 3. Theorem-level bridges

Each solution applies the theorem of `Rotor/MainTheorems.lean` to the
transported hypotheses, rewrites the goal with `T_eq`, `A_eq`, `R_eq`,
`Recurrent_eq` (and, where they occur, `uniformLaw_eq`, `toMech_clockwise`,
`toMech_pendantMech`), and closes it with `exact`; the remaining identifications
(`squareGraph`, `squareEmb`, `P.emb` against `(toDP P).emb`, `tvDist`,
`squarePeriodic.shiftNbr`, the product laws) are definitional.

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

## 6. Uncertainties

- **U1 (instance environments).**  The solutions import both the repository
  and the vocabulary, and both declare a high-priority discrete `σ`-algebra on
  `G.neighborSet v`.  `Audit/StatementRegression.lean` checks that no solution
  statement picked up a repository constant, in particular not the
  repository's instance.
- **U2 (local regression and comparator).**  The local regression compares the
  solution types with the challenge-environment types up to the auxiliary
  proof lemmas that a `def` abstracts; the comparator's own closure check is
  stricter, and it passes on all five pairs with the Lean kernel and with the
  independent nanoda kernel (see `Audit/COMPARATOR_RUNS.md`).

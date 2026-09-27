# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the five main
theorems of the formalization of *Eulerian walkers on `ℤ²` have range exponent
`2/3`* (Bou-Rabee–Peres, arXiv:2608.23545): Theorem 1.1 and Proposition 1.2,
each for the square lattice and for doubly periodic graphs of maximum degree
three, and Proposition 1.3.  Each comparator lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `MainSquare/` | Theorem 1.1, square lattice | `RotorAudit.main_square` | `Rotor.main_square` |
| `MainDegreeThree/` | Theorem 1.1, degree three | `RotorAudit.main_degree_three` | `Rotor.main_degree_three` |
| `PerturbationsSquare/` | Proposition 1.2, square lattice | `RotorAudit.perturbations_square` | `Rotor.perturbations_square` |
| `PerturbationsDegreeThree/` | Proposition 1.2, degree three | `RotorAudit.perturbations_degree_three` | `Rotor.perturbations_degree_three` |
| `PendantCounterexample/` | Proposition 1.3 | `RotorAudit.pendant_counterexample` | `Rotor.pendant_counterexample` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in all
five challenges: the rotor walk on a locally finite graph (mechanisms,
configurations, the step rule, `X_t`, `R_t`, the circuit times `T(n)`, the
circuit ranges `A_n`, recurrence), particle-and-rotor routings, the product law
of the initial rotors and total variation, doubly periodic graphs in the plane,
the square lattice with its clockwise mechanism, the graph `G_M` of
Proposition 1.3 with its mechanism, and the five cited results.

## What Is Checked

The theorems are conditional on results the paper cites without proof, and so
are the challenges: each carries, as explicit hypotheses, the cited results
its library theorem uses, restated in the vocabulary.

| Directory | Cited results carried as hypotheses |
| --- | --- |
| `MainSquare/`, `PerturbationsSquare/` | `LSS` |
| `MainDegreeThree/`, `PerturbationsDegreeThree/` | `LSS` |

Kingman's subadditive ergodic theorem, subcritical exponential decay for
Bernoulli bond percolation, the abelian property of rotor-routing, the
one-circuit property of a rotor walk, Holroyd–Propp's Lemma 6, and
Angel–Holroyd's theorem that recurrence does not depend on the starting
vertex, which the frozen statements also take as hypotheses, are not
hypotheses here: `Rotor/Bridge/Kingman.lean`,
`Rotor/Bridge/SubcriticalDecay.lean`, `Rotor/Bridge/Abelian.lean`,
`Rotor/Bridge/OneCircuit.lean`, `Rotor/Bridge/HolroydPropp.lean` and
`Rotor/Bridge/AngelHolroyd.lean` prove them (from the shared library
`Lattice-Probability`, the percolation library `PercolationContinuity`, by
induction on legal routings, by an injectivity argument on traversed edges
together with incoming/outgoing degree counts at circuit times, by
propagating infinitely-many-visits along a walk between any two vertices, and
by that same propagation combined with the abelian property, respectively),
and `Rotor/MainTheorems.lean` discharges them.  The vocabulary still defines
`Abelian`, `OneCircuit`, `VisitsAllOfVisitsOne` and `RecurrentOfRecurrent`
(for byte-identity across the five challenges and for definitional
record-keeping) but no audited theorem's signature uses any of the four
any longer.

- **`MainSquare`** (Theorem 1.1): on `ℤ²` with the clockwise mechanism and
  independent uniform initial rotors, there are a compact convex `B` with the
  origin in its interior and constants `κ, c > 0` such that almost surely the
  walk is recurrent, every circuit completes, `n⁻¹ A_n → B` and
  `t^{-1/3} R_t → κ B` in Hausdorff distance, the inner and outer bounds
  `((1 - ε) n) • B ⊆ A_n ⊆ ((1 + ε) n) • B` hold eventually on lattice points,
  and `|R_t| / t^{2/3} → c`.
- **`MainDegreeThree`**: the same conclusions for a connected infinite graph
  of maximum degree three with doubly periodic drawing `P` and doubly periodic
  mechanism `π`, in the coordinates `P.emb`.
- **`PerturbationsSquare`** (Proposition 1.2): one `δ > 0` such that, for
  independent rotor laws within total variation `δ` of uniform at every
  vertex, the walk is almost surely recurrent from every start, and, when the
  marginals are invariant under a finite-index subgroup `Λ ≤ ℤ²`, the shape,
  range and volume conclusions hold.
- **`PerturbationsDegreeThree`**: the same for the degree-three graphs, with
  invariance under the translation lattice of `P`.
- **`PendantCounterexample`** (Proposition 1.3): on `G_M` with
  `M ≥ 50331645`, from every start, the walk is almost surely not recurrent.

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorems, in the namespace `RotorAudit`.

| Challenge declaration | Repository source |
| --- | --- |
| `Mechanism`, `Config`, `State`, `step`, `walk`, `X`, `R`, `visits`, `T`, `A`, `Recurrent` | `Rotor/Model.lean` |
| `RState`, `actuate`, `run`, `Stable`, `IsLegal` | `Rotor/Routing.lean` |
| `traversal`, `departures` | `Rotor/Traversal.lean` |
| `neighborSet.measurableSpace`, `productLaw`, `uniformAt`, `uniformLaw` | `Rotor/Law.lean` |
| `Plane`, `DoublyPeriodic`, `shiftNbr`, `Periodic`, `InvariantMarginals`, `tvDist` | `Rotor/Periodic.lean` |
| `Site`, `Dir`, `dirVec` | `Rotor/Basic.lean` |
| `squareGraph`, `dirOf`, `nbr`, `turnAt`, `clockwise`, `squareEmb`, `squarePeriodic` | `Rotor/Square.lean` |
| `PVertex`, `pendantAdj`, `pendantGraph`, `pendantNbrLattice`, `pendantNbrLeaf`, `pendantTurn`, `pendantMech` | `Rotor/Pendant.lean` |
| `External.OneCircuit`, `External.Abelian`, `External.VisitsAllOfVisitsOne`, `External.RecurrentOfRecurrent` | `Rotor/External/{OneCircuit,Abelian,HolroydPropp,AngelHolroyd}.lean` |
| `External.Kingman` | `Rotor/External/Kingman.lean` |
| `External.LSS`, `bernoulli`, `bernoulliField`, `IsIncreasing`, `KDependent` | `Rotor/External/LSS.lean` |

## Solutions

Each `Solution.lean` imports the repository together with
`Audit/Support/Vocabulary.lean`, a verbatim copy of the vocabulary block that
imports only Mathlib, and proves the byte-identical statement from the
corresponding theorem of `Rotor/MainTheorems.lean` through the bridges in
`Audit/Support/Bridge.lean` (see [`DESIGN.md`](DESIGN.md)).

`Audit/StatementRegression.lean` is a local check of the statement-identity
part of the comparator: it elaborates each statement in the challenge
environment (`Audit/Support/Statements.lean`, which imports only Mathlib and
the vocabulary), checks that each solution theorem has exactly that type and
mentions no constant of the repository namespace `Rotor`, and prints the axioms
of each solution theorem.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/MainSquare/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block is
the same in every challenge and in `Audit/Support/Vocabulary.lean`.  The
solutions and the regression build with

```bash
lake build Audit.StatementRegression
```

which prints, for each of the five theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Status.**  All five solutions build, and the statement regression and the
axiom prints pass locally.  `leanprover/comparator` was run on all five pairs
most recently on 2026-09-27, at commit `fce8250`, and every pair passed with
the Lean kernel and with the independent nanoda kernel.  Results and
reproduction steps are in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  The
workflow [`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
runs it on request.

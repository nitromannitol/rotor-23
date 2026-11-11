# Eulerian walkers on ℤ² have range exponent 2/3

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Yuval Peres,
> *Eulerian walkers on `ℤ²` have range exponent `2/3`*,
> [arXiv:2608.23545](https://arxiv.org/abs/2608.23545).

The paper's source is included under [`paper/`](paper/). The 5 main theorems of the paper are
proved, in the form in which its introduction states them: Theorem 1.1 and Proposition 1.2,
each for the square lattice and for doubly periodic graphs of maximum degree three, and
Proposition 1.3. The first four are proved from one result cited from the literature,
Liggett–Schonmann–Stacey domination, which enters as an explicit hypothesis; Proposition 1.3
is unconditional. See [Assumed literature inputs](#assumed-literature-inputs).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
two public libraries: the percolation library `PercolationContinuity` of
[`anthropics/formal-math`](https://github.com/anthropics/formal-math), and the shared library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability), a library of
lattice probability and potential theory.

[![CI](https://github.com/nitromannitol/rotor-23/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/rotor-23/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/rotor-23/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/rotor-23/actions/workflows/comparator.yml)

## What is proved

A rotor configuration assigns to each site of `ℤ²` one of the four directions `N, E, S, W`,
and the clockwise mechanism cycles them in that order. A walker at `X_t` turns the rotor at
`X_t` one step clockwise and moves along it. From a fixed start `o`, `R_t = {X_0, …, X_t}` is
the range, `T(n)` is the time at which `n` circuits (each `deg(o)` successive returns to `o`)
are complete, and `A_n = R_{T(n)}`. Theorem 1.1 of the paper says that when the initial rotors
are independent and uniform, then almost surely the walk is recurrent, `n⁻¹ A_n` converges in
Hausdorff distance to a deterministic compact convex set `B` with the origin in its interior,
`t^{-1/3} R_t` converges to `κ B` for a deterministic `κ > 0`, and `|R_t| t^{-2/3}` converges
to a deterministic constant in `(0, ∞)`. The theorem also covers doubly periodic plane graphs
of maximum degree three; Proposition 1.2 extends it to independent rotor laws close to
uniform in total variation, and Proposition 1.3 gives a doubly periodic plane graph, the
square lattice with `M` leaves attached to every vertex, on which the walk is transient for
large `M`. The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The 5 main results, formalized as stated in the introduction of the paper, are collected in
[`Rotor/MainTheorems.lean`](Rotor/MainTheorems.lean). Each is proved by direct application of
its certified counterpart in [`Rotor/Frozen/Main/`](Rotor/Frozen/Main), so the statements
displayed there are byte-faithful to the certified ones.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1, square lattice | `Rotor.main_square` | recurrence, limit shape and range exponent of the clockwise rotor walk on `ℤ²` |
| Theorem 1.1, degree three | `Rotor.main_degree_three` | the same on a doubly periodic graph of maximum degree three |
| Proposition 1.2, square lattice | `Rotor.perturbations_square` | recurrence, and the limit shape under periodic marginals, for rotor laws close to uniform |
| Proposition 1.2, degree three | `Rotor.perturbations_degree_three` | the same on a doubly periodic graph of maximum degree three |
| Proposition 1.3 | `Rotor.pendant_counterexample` | the walk on the square lattice with `M` leaves at every vertex is almost surely not recurrent for large `M` |

**Theorem 1.1, square lattice (`Rotor.main_square`).** On `ℤ²` with the clockwise mechanism
and independent uniform initial rotors, there are a compact convex `B` with the origin in its
interior and constants `κ, c > 0` such that almost surely:

1. *Recurrence.* The walk is recurrent and every circuit completes.
2. *Limit shape.* `n⁻¹ A_n → B` and `t^{-1/3} R_t → κ B` in Hausdorff distance (coordinates
   centered at `o`), and the inner and outer bounds `((1 - ε) n) • B` and `((1 + ε) n) • B`
   on `A_n` hold eventually.
3. *Range exponent.* `|R_t| / t^{2/3} → c`.

Hypothesis: Liggett–Schonmann–Stacey.

**Theorem 1.1, degree three (`Rotor.main_degree_three`).** The same conclusions on a
connected infinite graph of maximum degree three with a doubly periodic drawing
`P : DoublyPeriodic G` and a doubly periodic mechanism, in the coordinates `P.emb`. Same
hypothesis.

**Proposition 1.2 (`Rotor.perturbations_square`, `Rotor.perturbations_degree_three`).** There
is one `δ > 0` such that for independent rotor laws within total variation `δ` of uniform at
every vertex the walk is almost surely recurrent from every start, and, when the marginals are
invariant under the translation lattice, the conclusions of Theorem 1.1 hold. Same hypothesis.

<!-- SQUARE-PERTURBATIONS-BEGIN (generated by tools/sync_docs.py) -->

Proposition 1.2 on the square lattice gives one `δ > 0` for all independent
rotor laws whose marginal at every vertex has total variation distance less
than `δ` from uniform. The walk is almost surely recurrent from each start.
For every finite-index translation sublattice `Λ ≤ ℤ²`, invariance of the
marginal laws under `Λ` also gives a deterministic compact convex body `B`
with the origin in its interior and positive constants `κ, c`. In coordinates
centered at the starting vertex,
`n^(-1) A_n → B`, `t^(-1/3) R_t → κ B`, and `|R_t| / t^(2/3) → c` almost surely.
The radius is independent of `Λ`. The frozen statement also includes finite
circuit times and the inner and outer lattice-point bounds.

See [`Rotor.Frozen.perturbations_square`](Rotor/Frozen/Main/PerturbSquare.lean); its cited inputs are listed below.

<!-- SQUARE-PERTURBATIONS-END -->

**Proposition 1.3 (`Rotor.pendant_counterexample`).** On the square lattice with
`M ≥ 50331645 = 3 · 256³ - 3` leaves attached to every vertex and the clockwise order
`N, E, S, W, L_1, …, L_M`, the walk with independent uniform initial rotors is almost surely
not recurrent, from every start. Unconditional.

This repository formalizes every theorem, lemma and proposition of the paper: Theorem 1.1 and
Proposition 1.2, each for the square lattice and for doubly periodic graphs of maximum degree
three, Proposition 1.3, and the results of Sections 2 to 6.

## Standing assumptions and scope

1. **Every theorem is about every walk that satisfies its hypotheses.** Theorem 1.1 holds for
   the square lattice with the clockwise mechanism and for every connected infinite
   `SimpleGraph` with `LocallyFinite` and maximum degree at most three that carries a doubly
   periodic drawing `P : Rotor.DoublyPeriodic G` and a doubly periodic mechanism
   (`P.Periodic π`), from every start vertex `o`. Proposition 1.2 holds for the same graphs
   with one `δ > 0` for all independent rotor laws within total variation `δ` of uniform.
   Proposition 1.3 holds for every `M ≥ 50331645` and every start vertex. A doubly periodic
   graph is the data `P : DoublyPeriodic G`: an injective embedding `V → ℝ²`, a `ℤ²`-action
   by graph automorphisms with a basis of the translation lattice, and a choice of orbit
   representatives. Connectedness and infiniteness of `V` are hypotheses of the statements,
   not fields of `P`.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems take 1 cited
   result as an explicit hypothesis, listed under
   [Assumed literature inputs](#assumed-literature-inputs); nothing else is assumed.
3. **What is not formalized.** The open questions of Section 7, the figures, the simulations,
   and the survey of related work in Section 1.3.
4. **Modelling conventions.**
   - A graph is a Mathlib `SimpleGraph`, locally finite; a directed edge out of `v` is an
     element of `G.neighborSet v`; a rotor mechanism is a family of cyclic permutations of the
     neighbor sets (`Rotor/Model.lean`). The square lattice is `ℤ × ℤ` with the directions
     numbered `0 = N, 1 = E, 2 = S, 3 = W`, as an instance of the general model
     (`Rotor/Square.lean`).
   - `T n` takes values in `ℕ∞`, with `⊤` when no such time exists (the paper's
     `inf ∅ = ∞`). `A n` is defined through `(T n).toNat`, so at `T n = ⊤` it is the value
     `R 0 = {o}`; every statement about `A n` carries `T n < ⊤`, or almost-sure recurrence.
   - In Theorem 1.1, `B`, `κ` and the limit constant are bound before the almost-sure
     quantifier, so they are deterministic. Conclusion 2 is stated both as Hausdorff
     convergence and as the inner and outer bounds `((1 - ε) n) • B` and `((1 + ε) n) • B`
     on `A n`.
   - The law of the initial rotors is a product law, Mathlib's `Measure.infinitePi` over the
     neighbor sets with their discrete σ-algebra; almost-sure statements are `∀ᵐ ρ ∂μ`. The
     total variation distance between two laws on a finite set is `sup_s |μ s - ν s|` over
     all subsets.
   - Proposition 1.3 is stated with the explicit `M₀ = 50331645` and asserts almost-sure
     non-recurrence from every start vertex.
5. **Explicit versus implicit.** Three Lean statements are not literally the paper's: a
   routing is its initial state and its list of actuated vertices; `prop:passage` is conjoined
   with `T(n) < ⊤`; `prop:live-recurrence` is asserted for the fixed start `o`.
6. **Statements without a formal counterpart.** Every theorem, lemma and proposition of the
   paper has a registered Lean declaration. The paper-to-Lean map, node by node, is
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md). Every statement that transcribes a paper
   statement has a recorded clause-by-clause reading against it
   (`tools/check_clauses.py`), its quantifier order is checked mechanically
   (`tools/check_constants.py`), and its exponents are matched against the paper's
   (`tools/check_exponents.py`).

## Assumed literature inputs

The paper quotes seven results from the literature without proof. Each is stated in Lean as a
proposition in [`Rotor/External/`](Rotor/External), and every theorem whose proof uses one
takes it as an explicit hypothesis, so the statement shows exactly which of them it rests on.
Six of the seven are proved in [`Rotor/Bridge/`](Rotor/Bridge): subcritical exponential decay
for Bernoulli bond percolation on `ℤ²`, from the percolation library; Kingman's subadditive
ergodic theorem, from the shared library Lattice-Probability; the abelian property of
rotor-routing (Holroyd–Levine–Mészáros–Peres–Propp–Wilson), by induction on legal routings;
Florescu–Levine–Peres' one-circuit property, by an injectivity argument on the walk's
traversed edges together with incoming/outgoing degree counts at circuit times;
Holroyd–Propp's Lemma 6 (a rotor walk that visits one vertex infinitely often visits every
vertex infinitely often), by propagating infinitely-many-visits along a walk between any two
vertices; and Angel–Holroyd's theorem that recurrence does not depend on the starting vertex,
by the same propagation combined with the abelian property. The remaining one is **not proved
here**; [`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists it with its verbatim Lean statement.

| Hypothesis | Content | Source | Used by |
| --- | --- | --- | --- |
| `Rotor.External.LSS` (`hLSS`) | there is `ε > 0` such that every `2`-dependent `{0,1}`-field on `ℤ²` with one-site probabilities at most `2ε` is dominated, on increasing events, by independent Bernoulli(`1/8`) variables | Liggett, Schonmann and Stacey, *Domination by product measures* (1997), Theorem 0.0(ii), used in the proof of `lem:block-live-paths` | `Rotor.main_square`, `Rotor.main_degree_three`, `Rotor.perturbations_square`, `Rotor.perturbations_degree_three` |

## Registered statements

Every statement of the paper is registered: one Lean declaration per theorem, lemma or
proposition (Theorem 1.1 and Proposition 1.2 as two each), and one proposition per cited
result. A registered statement's text between the lines `-- FROZEN-STATEMENT-BEGIN` and
`-- FROZEN-STATEMENT-END` is pinned by the SHA-256 of those bytes in
[`ledger/manifest.yaml`](ledger/manifest.yaml), together with the paper `\label` and line
range it transcribes; the proof after the end marker may be rewritten freely. In the manifest,
a registered statement is `PROVED` when it is proved with an axiom closure of exactly the
three standard axioms, and `FROZEN` when it is a cited result assumed rather than proved.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **33 registered statements: 1 `FROZEN`, 32 `PROVED`.**  Every node's proof is machine-checked: no `sorry`, no axiom added by
this development, and every axiom closure is exactly Lean's three
standard axioms `propext`, `Classical.choice` and `Quot.sound`.  The
`FROZEN` nodes are results cited from the literature, stated as
hypotheses rather than proved here; theorems that use them are proved
conditional on them, and the rest are unconditional.  Run
`python3 tools/check_axioms.py` to confirm.  These counts are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`.

<!-- STATUS-END -->

The paper's TeX source is [`paper/rotor.tex`](paper/rotor.tex), pinned by the SHA-256 recorded
in `ledger/manifest.yaml`; the line ranges cited in [`CORRESPONDENCE.md`](CORRESPONDENCE.md)
and in the docstrings of the frozen statements refer to it.

## Guarantees

- **No `sorry`.** The library has none, and `tools/check_manifest.py` rejects any `sorry`,
  `admit` or `axiom` token that is not registered. The 5 comparator challenges under
  [`RotorAudit/`](RotorAudit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution file proves.
- **Standard axioms only.** The axiom report of each of the 5 main theorems lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`Rotor/Meta/AxiomsAudit.lean`](Rotor/Meta/AxiomsAudit.lean) prints the reports, and the
  axiom-audit step of the CI workflow builds it and fails on any warning, a `sorry` warning
  included. [`CERTIFICATE.md`](CERTIFICATE.md) records the axiom closure of every registered
  statement. The assumed result is a hypothesis, not an axiom.
- **Builds from a clean checkout.** In continuous integration, `lake build` of a fresh
  checkout completes 8,864 jobs without error, and the build fails on any warning or `sorry`
  warning.
- **Independent check of the statements.** The 5 main theorems are restated in
  [`RotorAudit/`](RotorAudit/) using mathlib alone, one challenge file per theorem
  ([`MainSquare`](RotorAudit/MainSquare/Challenge.lean),
  [`MainDegreeThree`](RotorAudit/MainDegreeThree/Challenge.lean),
  [`PerturbationsSquare`](RotorAudit/PerturbationsSquare/Challenge.lean),
  [`PerturbationsDegreeThree`](RotorAudit/PerturbationsDegreeThree/Challenge.lean) and
  [`PendantCounterexample`](RotorAudit/PendantCounterexample/Challenge.lean)). Each challenge
  rebuilds the model from mathlib primitives (the rotor walk on a locally finite graph, its
  range, circuit times and circuit ranges, recurrence, particle routings, the product law of
  the initial rotors, total variation, doubly periodic graphs, the square lattice with its
  clockwise mechanism, the graph `G_M`, and the cited results). The solution file proves the
  statement from the library through its own `SolutionBasic.lean` (a verbatim copy of the
  challenge's vocabulary) and its own bridge in `RotorAudit/Support/`, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
  is proved, with only the three standard axioms, through independent implementations of the
  Lean kernel. See [`RotorAudit/README.md`](RotorAudit/README.md) and
  [`RotorAudit/COMPARATOR_RUNS.md`](RotorAudit/COMPARATOR_RUNS.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`, `PercolationContinuity` at commit
  `795efb86f191735c5481675763537cfb4ff37e55` and Lattice-Probability at commit
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`, recorded in [`lean-toolchain`](lean-toolchain)
  and [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to the SHA-256
  `007634d2d82fddfd902af49c3e85168461a545224b145998100433250895a930` of `paper/rotor.tex`.

## Size

The library contains 163 Lean files with 37,226 physical lines, on top of mathlib,
`PercolationContinuity` and Lattice-Probability. The comparator sources (20 files, 6,154
lines) are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain).

```bash
# from the repository root, the first time
./bootstrap.sh       # fetch the pinned percolation dependency, lake exe cache get, lake build
# afterwards
lake build           # compile the project
```

`bootstrap.sh` is needed because `lake update` cannot check out the percolation dependency by
itself: the pinned commit `795efb86f191735c5481675763537cfb4ff37e55` of
`anthropics/formal-math` is not reachable from any branch tip of that repository, so Lake's
clone does not contain it and the checkout fails with `fatal: reference is not a tree`. The
script fetches that object by hash and then runs `lake exe cache get` and `lake build`; the CI
workflow does the same fetch. `lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json), which pins the exact dependency revisions. The 2
source dependencies, `PercolationContinuity` and Lattice-Probability, have no prebuilt cache,
so the first build compiles them as well as the library. `import Rotor` loads the whole
development, and `import Rotor.MainTheorems` loads the main theorems and what they use.

The dependencies are pinned to exact commits in [`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- PercolationContinuity: the `percolation` subdirectory of
  `https://github.com/anthropics/formal-math` at `795efb86f191735c5481675763537cfb4ff37e55`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.

To reproduce the axiom reports and build the comparator libraries:

```bash
lake build Rotor.Meta.AxiomsAudit   # print the axioms of the five main theorems
lake build RotorAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

| command | what it guarantees |
|---|---|
| `python3 tools/check_axioms.py` | runs Lean's `#print axioms` on every node's export and reports any node whose closure contains `sorryAx`; `--emit` also rewrites each theorem node's `state:` in the manifest from the result |
| `python3 tools/check_manifest.py` | each frozen statement's bytes match its recorded SHA-256, every file under `Rotor/Frozen/` belongs to exactly one node, and no `axiom`, `admit` or `sorryAx` token, and no unregistered `sorry`, occurs under `Rotor/` |
| `python3 tools/check_warnings.py` | the build of `Rotor` emits no warning other than the `sorry` warnings the manifest authorizes (it authorizes none) |
| `python3 tools/check_coverage.py` | every theorem, lemma, proposition and corollary environment in `paper/rotor.tex` is claimed by a manifest node; the paper's open problems are excluded |
| `python3 tools/check_clauses.py` | every node that transcribes a paper statement has a recorded clause-by-clause reading against it |
| `python3 tools/check_constants.py` | in each frozen statement, an existential constant is bound before the variables the paper says it may not depend on |
| `python3 tools/check_exponents.py` | every exponent in a paper statement appears in its Lean statement, or the difference is recorded with its reason |

Also in `tools/`: `paper_anchors.py` checks that the line ranges in the manifest match the
paper's `\label`s (`--fix` repairs them); `paper_citations.py` does the same for the
`rotor.tex:<a>-<b>` citations in Lean docstrings; `sync_docs.py` regenerates the marked blocks
of this file and of `CORRESPONDENCE.md` from the manifest (`--write` applies, the bare command
checks); `assumptions.py` regenerates `ASSUMPTIONS.md`; `certificate.py` regenerates
`CERTIFICATE.md` (`--check` compares it with the file on disk); `freeze.py` registers or
refreshes a node in the manifest. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for further
building notes.

## Running the comparators

Each comparator pair has a configuration `RotorAudit/<Pair>/comparator.json`, for `<Pair>` one
of `MainSquare`, `MainDegreeThree`, `PerturbationsSquare`, `PerturbationsDegreeThree` and
`PendantCounterexample`, that permits exactly `propext`, `Classical.choice` and `Quot.sound`
and enables the independent nanoda kernel. The comparator checks that the solution proves the
challenge statement, compares their dependency closures, and replays the proof with the Lean
and NanoDa kernels.

To run one pair locally, build `leanprover/comparator`, `lean4export`, `landrun` and
`nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`RotorAudit/COMPARATOR_RUNS.md`](RotorAudit/COMPARATOR_RUNS.md)), and from the repository
root run:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator RotorAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`. The comparator workflow
runs the five pairs one after the other in a single job on GitHub-hosted runners.

There are two continuous-integration workflows: **CI** builds the library, builds the axiom
audit and checks the frozen statements; **Comparator audit** checks all 5 challenge/solution
pairs. Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually from the
[Actions page](https://github.com/nitromannitol/rotor-23/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Rotor.lean                the root module, importing the whole library
Rotor/
  MainTheorems.lean       the main theorems, stated in full
  Frozen/                 the certified statement surface, one frozen statement per file:
                          Main/, Circuits/, Shape/, DegreeThree/, Square/
  External/               the seven cited results, each a Prop
  Bridge/                 the proofs of six of them: SubcriticalDecay (from the percolation
                          library), Kingman (from Lattice-Probability), Abelian (induction
                          on legal routings), OneCircuit (injectivity and degree counts),
                          HolroydPropp and AngelHolroyd (walk propagation)
  Support/                the lemmas and constructions the frozen statements are proved from
  Meta/AxiomsAudit.lean   the axiom report, compiled by `lake build`, not imported by the root
  Basic.lean              the square-lattice model: sites, directions, the step rule
  Model.lean              the model on a general locally finite graph
  Law.lean                the law of the initial rotors: product laws, the uniform law
  Routing.lean, Traversal.lean   particle routings, traversals and departures
  Square.lean, Periodic.lean, Pendant.lean, Percolation.lean, Dual.lean,
  Events.lean, Exploration.lean  the square lattice, doubly periodic graphs,
                          the graph G_M, Bernoulli bond percolation, the dual lattice,
                          the events and the exploration of Section 5
RotorAudit/               the mathlib-only restatements and their solutions
  README.md               what each comparator pair checks
  DESIGN.md               how the pairs are built: vocabulary, bridges
  COMPARATOR_RUNS.md      the comparator pins and results
  <Pair>/                 Challenge.lean, SolutionBasic.lean, Solution.lean, comparator.json
  Support/                one bridge per pair, identifying the vocabulary with the library
ASSUMPTIONS.md            the assumed result, with its Lean statement (generated)
CORRESPONDENCE.md         paper to Lean, node by node
CERTIFICATE.md            generated record of the toolchain, the build, each node's axiom
                          closure and the SHA-256 of each frozen statement
ledger/manifest.yaml      one row per registered statement: hash, paper label, state
paper/rotor.tex           the paper, pinned by the SHA-256 in ledger/manifest.yaml
tools/                    the checkers and generators listed under Building
bootstrap.sh              first-time setup (the percolation dependency)
formalization.yaml        machine-readable metadata: sources, models, tooling, review
CITATION.cff              citation metadata
CONTRIBUTING.md           building notes and the elaboration policy for new files
.github/workflows/        build.yml (CI) and comparator.yml (the comparator audit)
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes,
arXiv:2608.23545, is joint work of Ahmed Bou-Rabee and Yuval Peres.  To cite the
formalization, use the metadata in [`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4), the percolation
library `PercolationContinuity` of
[`anthropics/formal-math`](https://github.com/anthropics/formal-math), which
supplies Kesten's `p_c(ℤ²) = 1/2` and the sharpness of the phase transition,
and the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability);
the comparator audit in [`RotorAudit/`](RotorAudit) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.

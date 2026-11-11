# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
./bootstrap.sh       # first time: fetch the pinned percolation dependency, get the mathlib cache, build
lake build           # afterwards
```

The toolchain is pinned in `lean-toolchain`. The production build is required to emit no Lean
or linter warnings (`python3 tools/check_warnings.py`). The five mathlib-only files
`RotorAudit/*/Challenge.lean` are the only files with a `sorry`: each contains one documented
statement-level `sorry`, checked against its completed solution by `leanprover/comparator`.
`lake build Rotor` builds the library and `lake build RotorAudit` the comparator libraries.
The percolation dependency `PercolationContinuity` is pinned to a commit that is not reachable
from any branch tip of its repository, so `bootstrap.sh` fetches it by hash; see the README.

## The main results and the axiom audit

The main results `Rotor.main_square`, `Rotor.main_degree_three`, `Rotor.perturbations_square`,
`Rotor.perturbations_degree_three` and `Rotor.pendant_counterexample` are in
`Rotor/MainTheorems.lean`. To print their axiom reports:

```bash
lake build Rotor.Meta.AxiomsAudit   # the five main theorems
python3 tools/check_axioms.py       # the axiom closure of every registered node
```

`Rotor/Meta/AxiomsAudit.lean` is not imported by the library root, because a `#print axioms`
command runs again whenever its module is rebuilt. Each report must list exactly `propext`,
`Classical.choice` and `Quot.sound`; the axiom-audit step of the CI workflow fails on any
warning, and `python3 tools/check_manifest.py` rejects an `axiom`, `admit` or `sorryAx` token
under `Rotor/`. The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

## Conventions for Lean files

- No `sorry`, `admit` or new `axiom` in the library; `python3 tools/check_manifest.py` rejects
  them.
- **Frozen statements.** The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Rotor/Frozen/` and `Rotor/External/` is pinned by the SHA-256
  recorded in `ledger/manifest.yaml`. A change there must be registered with
  `python3 tools/freeze.py` and shows up in `python3 tools/check_manifest.py`; proofs after
  the end marker may be changed freely. Statements refer to the paper by LaTeX label.
- New declarations go under `Rotor/`. The dependencies under `.lake/packages/` are read-only.
- **Never run `lake clean`.** It wipes the mathlib oleans and forces a multi-hour rebuild from
  source. To force a project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/Rotor` (and the corresponding `.lake/build/ir/Rotor`) and re-run
  `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not modification time, so `touch`
  does nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the
  module.

### Elaboration policy for new files

These rules keep the elaboration of new files cheap.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`. When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables so that `Real.rpow` and `Real.exp` terms
  never enter a numeric tactic; in particular, no `nlinarith` on goals that
  contain `rpow` or `exp`.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`).
- Never raise `maxHeartbeats`. A default-budget failure is a design signal
  (usually a wrong lemma orientation or a `set`-bound term), not a budget
  problem.
- Keep Lean files under 1500 lines.

## Comparators

Each pair under `RotorAudit/<Pair>/` has a `Challenge.lean` that imports mathlib only, a
`Solution.lean`, a `SolutionBasic.lean` and a `comparator.json` that permits exactly `propext`,
`Classical.choice` and `Quot.sound`. Do not add a declaration to a challenge that the statement
does not need, and do not change a challenge without checking it against the paper's
statement. The command that runs a pair is in [`RotorAudit/README.md`](RotorAudit/README.md)
and [`RotorAudit/COMPARATOR_RUNS.md`](RotorAudit/COMPARATOR_RUNS.md). A missing pair, a
missing tool or a failed kernel check is a failure.

## Continuous integration

- `build.yml` (**CI**) fetches the pinned percolation dependency, builds the library and
  rejects any warning or `sorry` warning, builds the axiom audit module, and runs
  `tools/check_manifest.py`.
- `comparator.yml` (**Comparator audit**) builds `RotorAudit` and runs the comparator on all
  five pairs.

Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually.

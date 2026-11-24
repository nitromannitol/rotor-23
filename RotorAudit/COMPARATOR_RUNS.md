# Comparator runs

## Continuous integration

The workflow `.github/workflows/comparator.yml` runs the official `leanprover/comparator` on all ten pairs in this directory (the five main statements and their five hypothesis-free `*Unconditional` forms) on GitHub's hosted runners whenever a Lean source or the dependency pins change on `main`, with the Lean kernel and the independent `nanoda` kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`). It uses comparator `5756749`, lean4export `v4.35.0-rc2` (matching `lean-toolchain`), nanoda_lib `6ae1f0c` and landrun `811cfff` (v0.1.18). A run passes only if every pair prints `Your solution is okay!`; the results are in the repository's Actions tab.

## Local runs

The five pairs below, the main statements with the Liggett–Schonmann–Stacey hypothesis, were also run on a local Linux machine (kernel 6.17), with both kernels enabled, at the Lean toolchain of the time:

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

### `MainSquare`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (299 s) |

### `MainDegreeThree`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (396 s) |

### `PerturbationsSquare`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (289 s) |

### `PerturbationsDegreeThree`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (300 s) |

### `PendantCounterexample`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (113 s) |

## Reproducing a run

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator RotorAudit/<Pair>/comparator.json
```

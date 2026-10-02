# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory against the statements in this repository, on a local Linux machine (kernel 6.17). Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `MainDegreeThree` | passed (132 s) | passed (178 s) |
| `MainSquare` | passed (186 s) | passed (236 s) |
| `PendantCounterexample` | passed (82 s) | passed (187 s) |
| `PerturbationsDegreeThree` | passed (191 s) | passed (292 s) |
| `PerturbationsSquare` | passed (190 s) | passed (270 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

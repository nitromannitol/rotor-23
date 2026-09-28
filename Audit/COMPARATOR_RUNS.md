# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory on 2026-09-24, at commit `b9303b6`, on a local machine. Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `PendantCounterexample` | passed (124 s) | passed (153 s) |
| `MainDegreeThree` | passed (214 s) | passed (242 s) |
| `MainSquare` | passed (265 s) | passed (330 s) |
| `PerturbationsDegreeThree` | passed (182 s) | passed (243 s) |
| `PerturbationsSquare` | passed (238 s) | passed (353 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

## 2026-09-25 rerun (Lean kernel only)

After discharging `ext-kingman` and `ext-subcritical-decay` (both now proved unconditionally,
`Rotor.Bridge.kingman_holds` and `Rotor.Bridge.subcriticalDecay_holds`) and dropping the now-proved
hypotheses from the frozen statements they carried, the four pairs whose challenge statement changed
(`MainSquare`, `MainDegreeThree`, `PerturbationsSquare`, `PerturbationsDegreeThree`; `PendantCounterexample`'s
statement is unaffected) were rerun with the Lean kernel only (`enable_nanoda` false, the committed
configuration):

| Pair | Lean kernel |
|---|---|
| `MainSquare` | passed |
| `MainDegreeThree` | passed |
| `PerturbationsSquare` | passed |
| `PerturbationsDegreeThree` | passed |

Same tool revisions as above.

## Run of 2026-09-27

Every pair was run again on 2026-09-27, at commit `f5c29c7`, against the current
statements and the published Lattice-Probability pin, on a second local machine
(Linux 6.17), with the same tool revisions as above.

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `MainDegreeThree` | passed (132 s) | passed (178 s) |
| `MainSquare` | passed (186 s) | passed (236 s) |
| `PendantCounterexample` | passed (82 s) | passed (187 s) |
| `PerturbationsDegreeThree` | passed (191 s) | passed (292 s) |
| `PerturbationsSquare` | passed (190 s) | passed (270 s) |

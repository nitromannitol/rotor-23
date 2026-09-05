# rotor-23

A Lean 4 formalization, in progress, of

> **Eulerian walkers on `ℤ²` have range exponent `2/3`**
> Ahmed Bou-Rabee and Yuval Peres

The target is Theorem 1.1 of the paper for the square lattice with the
clockwise rotor mechanism and independent uniform initial rotors: the walk is
recurrent, the rescaled range converges to a deterministic convex body, and
`|R_t| t^{-2/3}` converges to a deterministic positive finite constant.  The
exact frozen surface is being settled with the authors; see
`ledger/QUESTIONS.md`.

## The model

A rotor configuration assigns to each site of `ℤ²` one of the four directions
`N, E, S, W`.  A walker at `X_t` turns the rotor at `X_t` clockwise by one step
and follows it.  `R_t` is the set of sites visited in the first `t` steps.

## Where to start reading

| file | what is in it |
|---|---|
| `Rotor/Basic.lean` | the model: sites, directions, the step rule, `R_t`, `T(n)`, `A_n` |
| `Rotor/Law.lean` | `ℙ₀`, the product of uniform laws on the four directions |
| `Rotor/Support/Guards.lean` | computable witnesses that the model says what the paper says |
| `Rotor/Frozen/` | one frozen statement per file, the contract with the paper |
| `ledger/decisions.md` | every modelling decision, numbered |
| `ledger/QUESTIONS.md` | the open questions to the authors and their answers |
| `CORRESPONDENCE.md` | paper ↔ Lean |
| `paper/rotor.tex` | the paper this formalizes, pinned by hash |

## How a statement is tied to the paper

Each theorem in `Rotor/Frozen/` sits between `-- FROZEN-STATEMENT-BEGIN` and
`-- FROZEN-STATEMENT-END`.  Those bytes are the contract: `ledger/manifest.yaml`
records their SHA-256 and the paper `\label` they transcribe.  The proof follows
the end marker and may be rewritten freely.  Every frozen statement is read
against the paper clause by clause before it is proved, and the reading is
recorded (`tools/check_clauses.py`); the order of its quantifiers is checked
mechanically (`tools/check_constants.py`); its exponents are matched against the
paper's (`tools/check_exponents.py`).

## Building and checking

```
elan toolchain install $(cat lean-toolchain)
lake exe cache get      # optional: prebuilt Mathlib
lake build Rotor
python3 tools/check_manifest.py
python3 tools/check_axioms.py
python3 tools/check_warnings.py
```

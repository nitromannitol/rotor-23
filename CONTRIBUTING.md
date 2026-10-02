# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
./bootstrap.sh       # first time: fetch the pinned percolation dependency, get the Mathlib cache, build
lake build           # afterwards
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The five Mathlib-only files
`Audit/*/Challenge.lean` are the sole exception: each contains one documented
statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/Rotor` (and the
  corresponding `.lake/build/ir/Rotor`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Rotor/Frozen/` and `Rotor/External/` is pinned
  by the SHA-256 recorded in `ledger/manifest.yaml`.  A change there must be
  registered with `python3 tools/freeze.py` and shows up in
  `python3 tools/check_manifest.py`; proofs after the end marker may be changed
  freely.

- **The main results** are in `Rotor/MainTheorems.lean`; the axiom audit is
  `lake build Rotor.Meta.AxiomsAudit`, and the comparator surface is
  `lake build Audit`.

## Elaboration policy for new files

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
- Never run `lake clean`; see the building notes above.

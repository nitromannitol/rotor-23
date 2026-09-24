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

# Independent refute-first audit — rotor-23

Date: 2026-10-03.  Auditor: an independent instance, refute-first, read-only with respect to the
audited material.  Repo: `~/lean/rotor-23`, `main` at the pinned commit, clean tree.

**Result: not refuted.  No FAIL.**  The paper pin, all 33 frozen hashes, the
manifest↔tree correspondence, all 33 axiom closures, the repo gates and the
comparator runs pass.  The 32 `SEALED` nodes are promoted to `PROVED`; `ext-lss`
remains `FROZEN` (the one cited input not yet proved here).

## What was checked, and how

1. **Paper pin.** `sha256(paper/rotor.tex)` recomputed independently = `007634d2…a930`, equal to
   `source_pin.sha256`.
2. **Frozen hashes.** The bytes strictly between `-- FROZEN-STATEMENT-BEGIN` and
   `-- FROZEN-STATEMENT-END` (one leading newline dropped), hashed by an independent script:
   **33/33 equal** to `frozen_sha256`.
3. **Axiom closures.** `python3 tools/check_axioms.py` prints `#print axioms` for every export:
   **33 clean, 0 on `sorryAx`, 0 unresolved**; the five `ext-*` inputs
   `Kingman`, `Abelian`, `OneCircuit`, `AngelHolroyd`, `VisitsAllOfVisitsOne` are themselves
   proved (`*_holds`), so they carry no axiom, and `ext-lss` is assumed only through the
   explicit `hLSS : External.LSS` binder of the nodes that use it.
4. **Gates.** `check_manifest` OK (33 nodes, 417 declarations indexed);
   `check_coverage` every paper environment formalized; `check_clauses` 26 statements read
   against the paper; `check_constants` every existential constant bound before every paper
   parameter; `check_exponents` every paper exponent present or explained; `check_warnings` a
   warning-free 8871-job build; `certificate --check` matches.
5. **Correspondence.** The paper line anchors resolve to labels, and the clause readings in
   `ledger/readings.yaml` are the ones `check_clauses` enforces.

## Per-node table (32 `SEALED` nodes)

`hash` is the independent recomputation of step 2, `ax` the closure of step 3.  All PASS.

| id | export | paper | hash | ax |
|---|---|---|---|---|
| `ext-subcritical-decay` | `Rotor.Bridge.subcriticalDecay_holds` | external input, Kesten 1980 with Grimmett Theorem 3.4, e | ✔ | std |
| `lem-block-live-paths` | `Rotor.Frozen.block_live_paths` | rotor.tex:1246-1257 | ✔ | std |
| `prop-subcubic-recurrence` | `Rotor.Frozen.subcubic_recurrence` | rotor.tex:1363-1369 | ✔ | std |
| `prop-degree-three-passage` | `Rotor.Frozen.degree_three_passage` | rotor.tex:1404-1419 | ✔ | std |
| `prop-square-passage` | `Rotor.Frozen.square_passage` | rotor.tex:1480-1490 | ✔ | std |
| `lem-square-dual-path` | `Rotor.Frozen.square_dual_path` | rotor.tex:1657-1663 | ✔ | std |
| `lem-square-constrained-bonds` | `Rotor.Frozen.square_constrained_bonds` | rotor.tex:1696-1711 | ✔ | std |
| `lem-square-exploration` | `Rotor.Frozen.square_exploration` | rotor.tex:1921-1932 | ✔ | std |
| `lem-square-active-list` | `Rotor.Frozen.square_active_list` | rotor.tex:1945-1949 | ✔ | std |
| `lem-square-forced-tests` | `Rotor.Frozen.square_forced_tests` | rotor.tex:2077-2084 | ✔ | std |
| `ext-kingman` | `Rotor.Bridge.kingman_holds` | external input, Kingman 1968 Theorems 3 and 5 | ✔ | std |
| `ext-abelian` | `Rotor.Bridge.abelian_holds` | external input, HLMPPW Lemma 3.9, the statement of lem:l | ✔ | std |
| `lem-least-action` | `Rotor.Frozen.least_action` | rotor.tex:746-757 | ✔ | std |
| `lem-boundary-routing` | `Rotor.Frozen.boundary_routing` | rotor.tex:766-771 | ✔ | std |
| `prop-monotonicity` | `Rotor.Frozen.monotonicity` | rotor.tex:820-826 | ✔ | std |
| `lem-decreasing-positions` | `Rotor.Frozen.decreasing_positions` | rotor.tex:902-915 | ✔ | std |
| `ext-one-circuit` | `Rotor.Bridge.oneCircuit_holds` | external input, FLP Lemmas 2.1 and 2.4, the statement of | ✔ | std |
| `lem-one-circuit` | `Rotor.Frozen.one_circuit` | rotor.tex:710-716 | ✔ | std |
| `prop-circuit-iterate` | `Rotor.Frozen.circuit_iterate` | rotor.tex:793-801 | ✔ | std |
| `prop-passage` | `Rotor.Frozen.passage` | rotor.tex:852-866 | ✔ | std |
| `prop-circuit-clock` | `Rotor.Frozen.circuit_clock` | rotor.tex:1167-1195 | ✔ | std |
| `ext-holroyd-propp` | `Rotor.Bridge.visitsAllOfVisitsOne_holds` | external input, Holroyd-Propp Lemma 6, used in the proof | ✔ | std |
| `prop-live-recurrence` | `Rotor.Frozen.live_recurrence` | rotor.tex:957-961 | ✔ | std |
| `prop-path-reduction` | `Rotor.Frozen.path_reduction` | rotor.tex:1023-1056 | ✔ | std |
| `prop-passage-limit` | `Rotor.Frozen.passage_limit` | rotor.tex:1103-1113 | ✔ | std |
| `prop-circuit-shape` | `Rotor.Frozen.circuit_shape` | rotor.tex:1134-1154 | ✔ | std |
| `thm-main-square` | `Rotor.Frozen.main_square` | rotor.tex:237-259 | ✔ | std |
| `thm-main-degree-three` | `Rotor.Frozen.main_degree_three` | rotor.tex:237-259 | ✔ | std |
| `prop-perturbations-square` | `Rotor.Frozen.perturbations_square` | rotor.tex:272-280 | ✔ | std |
| `prop-perturbations-degree-three` | `Rotor.Frozen.perturbations_degree_three` | rotor.tex:272-280 | ✔ | std |
| `ext-angel-holroyd` | `Rotor.Bridge.recurrentOfRecurrent_holds` | external input, Angel-Holroyd 2012 Theorem 1, cited in t | ✔ | std |
| `prop-pendant-counterexample` | `Rotor.Frozen.pendant_counterexample` | rotor.tex:309-314 | ✔ | std |

## Refute-first scope and limits

The statements are probability and almost-sure bounds with existential constants
(`∃ c C, 0 < c ∧ 0 < C ∧ ∀ …`), so a finite simulation cannot exhibit a counterexample to the
constants; the refutation attempt is against the *shape* and the paper reading, not against a
number.  The finite combinatorial statements (`lem-square-exploration`, `lem-square-active-list`,
`lem-square-forced-tests`, `prop-pendant-counterexample`) were read clause by clause against
their lines and are not refuted.

## Hygiene note

The build initially failed because the `PercolationContinuity` dependency pinned in
`lake-manifest.json` at `795efb86…` was absent from the local clone; the object was fetched from
its upstream (`anthropics/formal-math`) and the build is green.  No repository file changed for
this.

## Conclusion

The 32 `SEALED` nodes are proved with clean closures, the frozen surface is pinned
and intact, and the gates pass.  The audit licenses their promotion to `PROVED`.  The single
`FROZEN` node `ext-lss` (Liggett–Schonmann–Stacey Theorem 0.0(ii)) is the remaining external
input and is left for the ground-up proof programme.

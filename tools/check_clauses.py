"""Compare how much each paper statement asserts with how much its Lean node does.

Frozen hashes pin statement bytes, and axiom checks verify proofs.  This
checker compares the assertion units of each paper statement with those of its
Lean statement and records their correspondence.

This counts assertion units on each side and reports the pairs where the paper
asserts more:

  paper   displayed equations and enumerated items inside the statement
  Lean    top-level conjuncts of the frozen statement's conclusion

The counts are a heuristic, not a proof of correspondence: one Lean conjunct can
faithfully carry two paper displays, and one paper display can need three Lean
conjuncts.  So a mismatch is a prompt to look, not a verdict, and every node is
listed with its counts so the reader can judge.  Nodes whose `source` names no
paper label are skipped: they have no paper statement to compare against.

    python3 tools/check_clauses.py            # report
    python3 tools/check_clauses.py --strict   # exit 1 if any node is unreviewed
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_clauses.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Nodes whose count mismatch has been looked at and explained.  The value is the
# reason, which is printed, so a stale entry is visible rather than silent.
# Every node with a paper statement must appear here, with a sentence saying
# what the paper asserts and what the Lean statement asserts.  The counts below
# are advisory -- a regex cannot decide correspondence -- so the guarantee this
# file gives is the weaker but honest one: every statement has been read against
# the paper and the reading is written down.  A node missing from this table
# fails the check.
REVIEWED: dict[str, str] = {
    "lem-one-circuit":
        "two sentences, two conjuncts: no repeated traversal on [T(n), T(n+1)), rendered as "
        "distinct times give distinct directed edges with the half-line case through ℕ∞; and "
        "deg(x) departures from each x in A_n when T(n+1) < ∞",
    "lem-least-action":
        "items (a) and (b), two conjuncts; routings are (initial state, actuated-vertex list) "
        "by ruling M-010; m ≤ n is ws.length ≤ vs.length; actuation counts are List.count",
    "lem-boundary-routing":
        "three sentences, three conjuncts: no repeated edge counting the initial edges "
        "(Nodup of boundaryTraversed); finite iff terminates, for every ordering; if so, the "
        "actuated list at any finishing stage is complete and has every complete routing's counts",
    "prop-circuit-iterate":
        "'iff' and 'in that case', two conjuncts; Terminates and Φ are taken with the initial "
        "rotors, as the paper's boundary routing is",
    "prop-monotonicity":
        "one display; the paper's T is U because T is the circuit time",
    "prop-passage":
        "three displays, three conjuncts; the third adds T(n) < ⊤ so that A_n is never read at "
        "its junk value, which is stronger than the paper's identity",
    "lem-decreasing-positions":
        "items (i) and (ii), two conjuncts; in (i) the live path has x_0 ∈ S, x_i ∉ S for i ≥ 1, "
        "ends at y, hence length ≥ 2; in (ii) the path lies in Φ^n({x}) and fails the live "
        "condition at ≤ n-1 internal vertices (liveFailures)",
    "prop-live-recurrence":
        "three assertions, three conjuncts: AllTerminate, T(n) < ⊤ for all n, Recurrent at the "
        "fixed start o",
    "prop-path-reduction":
        "items (i)-(iii), three conjuncts; (i) for every start; (ii) the sup over d(x,y) ≥ R as an "
        "iSup in ℝ≥0∞; (iii) B, κ, c_* before ∀ᵐ, T(n) < ⊤ added, sets drawn relative to o",
    "prop-passage-limit":
        "one display plus continuity, subadditivity, homogeneity, nonnegativity and independence of o "
        "(∃ f before ∀ o); the uniform limit in ε-R₀ form relative to o",
    "prop-circuit-shape":
        "three properties of B, the Hausdorff limit, and the sandwich display: five conjuncts; the "
        "passage function and the passage-ball identity are hypotheses",
    "prop-circuit-clock":
        "the squeeze display, the two asymptotics under (α, β), and the Hausdorff conclusion: "
        "three conjuncts, the o(·) claims as limits of ratios; emb is any drawing",
    "lem-block-live-paths":
        "ε, L₀ first, then L and the strict block hypothesis, then η with the criterion, then δ "
        "with the perturbed criterion; two conclusions as nested conjuncts",
    "thm-main-square":
        "the square case of items (i)-(iii): recurrence, T(n) < ⊤, Hausdorff limit of A_n, the "
        "sandwich (F-001), Hausdorff limit of R_t, the range limit; B, κ, c before ∀ᵐ",
    "thm-main-degree-three":
        "the degree-three case, same six conjuncts with P.emb; split node of thm:main",
    "prop-perturbations-square":
        "∃ δ, then for every product law within δ of uniform: (i) for every start, and under "
        "invariance under any finite-index translation sublattice Λ ≤ ℤ² the (ii)-(iii) "
        "conjunction of thm-main-square; δ is independent of Λ",
    "prop-perturbations-degree-three":
        "the degree-three case of prop:small-perturbations; split node",
    "prop-subcubic-recurrence":
        "one assertion: almost surely no infinite live path, for the uniform law",
    "prop-degree-three-passage":
        "one display; c, C existential before u → v and R (they depend on the graph)",
    "prop-square-passage":
        "one display; c, C existential before u → v and R (they route through the external "
        "subcritical bound)",
    "lem-square-dual-path":
        "one assertion: an open dual path from the right face of the first edge to the right "
        "face of the last edge, with distinct faces as 'path' requires",
    "lem-square-constrained-bonds":
        "one display; c, C existential (they route through the external subcritical bound); "
        "the pattern P⋆ is the explicit six-vertex list",
    "lem-square-exploration":
        "items (i)-(iii), three conjuncts; (iii) is three conditional-probability identities "
        "given a history, one per case",
    "lem-square-active-list":
        "two sentences, two conjuncts, at every stage with a current edge",
    "lem-square-forced-tests":
        "one display with the explicit constants C = 4/3, e^{-c} = (3/4)^{1/3} (ruling F-003)",
    "prop-pendant-counterexample":
        "one assertion: almost-sure transience for every start and every M ≥ 50331645, the "
        "explicit M₀ (ruling F-003); transience is asserted almost surely",
}


def paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$ROTOR_PAPER`."""
    env = os.environ.get("ROTOR_PAPER")
    return Path(env) if env else ROOT / "paper" / "rotor.tex"


RELATION = re.compile(r"\\leq|\\geq|\\neq|\\subseteq|(?<!\\not)\\in\b|<|>|=")


def paper_units(segment: str) -> int:
    """Assertions in a statement: relations inside displays, plus enumerated items.

    Counting displays alone undercounts, because the paper often puts three
    assertions in one display separated by `\\qquad` -- `lem:max-exit` does.
    Counting relation symbols inside displayed math tracks the real number of
    things asserted.  `\\coloneqq` is a definition, not an assertion, and is not
    counted; nor is anything outside a display."""
    body = []
    for m in re.finditer(r"\\begin\{(?:equation|align|gather)\*?\}(.*?)\\end\{(?:equation|align|gather)\*?\}",
                         segment, re.S):
        body.append(m.group(1))
    for m in re.finditer(r"(?<!\\)\\\[(.*?)(?<!\\)\\\]", segment, re.S):
        body.append(m.group(1))
    n = 0
    for b in body:
        b = re.sub(r"\\text\{[^}]*\}", " ", b)
        b = b.replace("\\coloneqq", " ").replace("\\colon", " ")
        b = re.sub(r"\\begin\{cases\}.*?\\end\{cases\}", " ", b, flags=re.S)
        n += len(RELATION.findall(b))
    n += len(re.findall(r"\\item\b", segment))
    return max(n, 1) if body or "\\item" in segment else 0


def lean_conjuncts(block: str) -> int:
    """Top-level `∧` of the conclusion.

    The conclusion begins after the last `:` that sits at bracket depth zero:
    every binder is inside `(`, `{` or `[`, so its own `:` is at depth one or
    more.  Conjuncts are then the depth-zero `∧` after that point."""
    depth, last_colon = 0, None
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            last_colon = i
    concl = block[last_colon + 1:] if last_colon is not None else block
    depth, n = 0, 1
    for ch in concl:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "∧" and depth == 0:
            n += 1
    return n


def main() -> int:
    strict = "--strict" in sys.argv[1:]
    lines = paper_path().read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    rows, flagged, unreviewed = [], [], []
    for node in manifest.get("nodes") or []:
        src = node["source"]
        rng = re.search(r"rotor\.tex:(\d+)-(\d+)", src)
        lab = re.search(r"label ([A-Za-z][A-Za-z0-9:_-]*)", src)
        if not (rng and lab):
            continue
        a, b = int(rng.group(1)), int(rng.group(2))
        segment = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):text.index("-- FROZEN-STATEMENT-END")]
        p, l = paper_units(segment), lean_conjuncts(blk)
        rows.append((node["id"], lab.group(1), p, l))
        if p > l:
            flagged.append(node["id"])
        if node["id"] not in REVIEWED:
            unreviewed.append(node["id"])

    print(f"{'node':26s} {'label':22s} paper  lean")
    for nid, lab, p, l in rows:
        mark = "  <-- paper asserts more" if p > l else ""
        print(f"  {nid:24s} {lab:22s} {p:5d} {l:5d}{mark}")

    print("\nRecorded correspondence, one line per statement:")
    for nid, _, _, _ in rows:
        print(f"  {nid}: {REVIEWED.get(nid, 'NOT REVIEWED')}")

    if unreviewed:
        print(f"\ncheck_clauses: {len(unreviewed)} statement(s) have no recorded "
              f"correspondence: {', '.join(unreviewed)}", file=sys.stderr)
        return 1
    print(f"\ncheck_clauses: OK ({len(rows)} statements, each read against the paper "
          f"and its correspondence recorded; {len(flagged)} where the count heuristic "
          f"says the paper asserts more, all explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

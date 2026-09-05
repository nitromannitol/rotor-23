"""Compare how much each paper statement asserts with how much its Lean node does.

Every other checker here compares a statement with *itself*: the hash pins the
bytes, the axiom check pins the proof.  None of them notices when a frozen
statement quietly asserts less than the paper statement it claims to transcribe.
That is how, in the ORRW formalization this tooling comes from, `lem:schur`
came to be frozen without one of the three displays its paper statement
asserts, while every other gate passed.

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

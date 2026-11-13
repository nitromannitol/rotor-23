#!/usr/bin/env python3
"""Build Rotor and verify its warnings against the frozen manifest.

The only accepted warnings are one Lean `declaration uses 'sorry'` diagnostic
for each manifest theorem in state `DRAFT_SORRY`.  Any missing, duplicate,
misplaced, or differently worded warning makes the check fail.  Only warnings
located in this repository's own modules (`Rotor.lean`, `Rotor/`, `RotorAudit/`)
are counted; warnings that Lean prints for the modules of a dependency are not
this repository's to fix and are ignored.
"""

from __future__ import annotations

from collections import Counter
import re
import subprocess
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_warnings.py: PyYAML is required (pip install pyyaml)")


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
ANSI_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
WARNING_RE = re.compile(r"^warning:\s*(.*)$", re.IGNORECASE)
LOCATION_RE = re.compile(r"(?P<path>.+?\.lean):[0-9]+:[0-9]+: ")
OWN_ROOTS = ("Rotor/", "RotorAudit/")
OWN_FILES = ("Rotor.lean",)
SORRY_WARNING_RE = re.compile(
    r"(?P<path>.+?\.lean):(?P<line>[0-9]+):(?P<column>[0-9]+): "
    r"declaration uses 'sorry'"
)


def expected_draft_files() -> Counter[str]:
    """Return the manifest-authorized warning multiset."""
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    nodes = manifest.get("nodes") or []
    files: list[str] = []
    for node in nodes:
        if node.get("state") != "DRAFT_SORRY":
            continue
        if node.get("kind") != "theorem":
            raise ValueError(
                f"{node.get('id', '<missing id>')}: DRAFT_SORRY node is not a theorem"
            )
        files.append(str(Path(node["file"])))
    return Counter(files)


def repo_relative(path_text: str) -> str:
    """Normalize a Lean diagnostic path to the manifest's repository form."""
    path = Path(path_text)
    if path.is_absolute():
        try:
            path = path.resolve().relative_to(ROOT)
        except ValueError:
            return str(path)
    return str(path)


def is_own_module(warning_text: str) -> bool:
    """Whether a warning is located in a module of this repository.

    A warning without a source location is counted, so that nothing is hidden."""
    location = LOCATION_RE.match(warning_text)
    if location is None:
        return True
    path = repo_relative(location.group("path"))
    return path in OWN_FILES or path.startswith(OWN_ROOTS)


def main() -> int:
    try:
        expected = expected_draft_files()
    except (OSError, KeyError, TypeError, ValueError, yaml.YAMLError) as error:
        print(f"check_warnings: could not parse manifest: {error}", file=sys.stderr)
        return 1

    build = subprocess.run(
        ["lake", "build", "Rotor"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    sys.stdout.write(build.stdout)
    if build.returncode != 0:
        print(
            f"check_warnings: FAIL (lake build Rotor exited {build.returncode})",
            file=sys.stderr,
        )
        return 1

    actual: Counter[str] = Counter()
    unexpected: list[str] = []
    for raw_line in build.stdout.splitlines():
        line = ANSI_RE.sub("", raw_line)
        warning = WARNING_RE.fullmatch(line)
        if warning is None or not is_own_module(warning.group(1)):
            continue
        sorry_warning = SORRY_WARNING_RE.fullmatch(warning.group(1))
        if sorry_warning is None:
            unexpected.append(line)
            continue
        actual[repo_relative(sorry_warning.group("path"))] += 1

    missing = expected - actual
    extra = actual - expected
    if unexpected or missing or extra:
        print("check_warnings: FAIL", file=sys.stderr)
        for line in unexpected:
            print(f"  unexpected warning: {line}", file=sys.stderr)
        for path, count in sorted(missing.items()):
            print(f"  missing {count} warning(s): {path}", file=sys.stderr)
        for path, count in sorted(extra.items()):
            print(f"  extra {count} warning(s): {path}", file=sys.stderr)
        return 1

    print(
        f"check_warnings: OK ({sum(actual.values())} registered sorry warnings)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

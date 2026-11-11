#!/usr/bin/python3 -I
"""Axiom audit of the main theorems.

Usage (from the repository root, after `lake build`):
    python3 -I scripts/axiom_audit.py

Runs `#print axioms` on each main theorem in a temporary file and fails unless every one depends
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. In particular it
fails if any theorem depends on `sorryAx`.
"""

import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
THEOREMS = {
    "CantorSzemeredi.Frozen.MainTheorem": "CantorSzemeredi.cantor_szemeredi",
    "CantorSzemeredi.Frozen.Syndetic": "CantorSzemeredi.cantor_szemeredi_syndetic",
    "CantorSzemeredi.Frozen.Integers": "CantorSzemeredi.cantor_szemeredi_integers",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    lines = [f"import {m}" for m in THEOREMS] + [""] + [f"#print axioms {t}" for t in THEOREMS.values()]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
        path = fh.name
    try:
        res = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)
    out = " ".join(res.stdout.split())
    ok = res.returncode == 0
    for thm in THEOREMS.values():
        m = re.search(r"'" + re.escape(thm) + r"' depends on axioms: \[([^\]]*)\]", out)
        if m is None:
            print(f"{thm}: no axiom report", file=sys.stderr)
            ok = False
            continue
        axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
        bad = axioms - ALLOWED
        print(f"{thm}: {', '.join(sorted(axioms))}" + (f"  (NOT ALLOWED: {', '.join(sorted(bad))})" if bad else ""))
        ok &= not bad
    if not ok:
        print(res.stdout[-3000:] + res.stderr[-2000:], file=sys.stderr)
        print("AXIOM AUDIT FAILED", file=sys.stderr)
        return 1
    print("AXIOM AUDIT OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

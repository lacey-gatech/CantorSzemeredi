#!/usr/bin/python3 -I
"""Local check that Solution proves exactly the Challenge's statements.

Usage (from the repository root, after `lake build Challenge Solution`):
    python3 -I scripts/challenge_match.py

A stand-in for the sandboxed Comparator, which needs Linux. In one Lean process importing only
`Challenge` and another importing only `Solution`, it prints with `pp.all` the type of each
theorem named in `comparator.json` and the full definition of each definition the statements use,
and requires the two printouts to agree after whitespace normalization. It also requires every
Solution theorem to depend only on the axioms permitted in `comparator.json`.
"""

import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFINITIONS = ["CantorSzemeredi.cantorSet", "CantorSzemeredi.cantorEnum",
               "CantorSzemeredi.upperBanachDensity"]


def run(module, theorems, with_axioms):
    lines = [f"import {module}", "", "set_option pp.all true"]
    for t in theorems:
        lines.append(f"#check @{t}")
    for d in DEFINITIONS:
        lines.append(f"#print {d}")
    if with_axioms:
        lines.append("set_option pp.all false")
        lines += [f"#print axioms {t}" for t in theorems]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
        path = fh.name
    try:
        res = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)
    if res.returncode != 0:
        sys.exit(f"lean failed on {module}:\n{res.stdout[-3000:]}{res.stderr[-2000:]}")
    return res.stdout


def blocks(out, names):
    """Split the output into one normalized block per printed name, in order."""
    found, cur, buf = {}, None, []
    start = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem)?\s*@?("
                       + "|".join(re.escape(n) for n in names) + r")(?:\.\{[^}]*\})?\s*:")
    for line in out.split("\n") + ["'END"]:
        m = start.match(line)
        if m or line.startswith("'"):
            if cur:
                found[cur] = " ".join(" ".join(buf).split())
            cur, buf = (m.group(1), [line]) if m else (None, [])
        elif cur:
            buf.append(line)
    return found


def main():
    cfg = json.load(open(os.path.join(ROOT, "comparator.json"), encoding="utf-8"))
    theorems, allowed = cfg["theorem_names"], set(cfg["permitted_axioms"])
    names = theorems + DEFINITIONS
    challenge = blocks(run(cfg["challenge_module"], theorems, False), names)
    solution_out = run(cfg["solution_module"], theorems, True)
    solution = blocks(solution_out, names)
    ok = True
    for n in names:
        same = n in challenge and n in solution and challenge[n] == solution[n]
        print(f"{n}: {'identical' if same else 'DIFFERENT'}")
        ok &= same
    flat = " ".join(solution_out.split())
    for t in theorems:
        m = re.search(r"'" + re.escape(t) + r"' depends on axioms: \[([^\]]*)\]", flat)
        axioms = {a.strip() for a in m.group(1).split(",")} if m else {"<no report>"}
        bad = axioms - allowed
        print(f"{t} axioms: {', '.join(sorted(axioms))}" + (f"  NOT PERMITTED: {sorted(bad)}" if bad else ""))
        ok &= not bad
    print("CHALLENGE MATCH OK" if ok else "CHALLENGE MATCH FAILED", file=sys.stdout if ok else sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

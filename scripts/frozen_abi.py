#!/usr/bin/python3 -I
"""Elaborated-ABI hashes of the frozen declarations.

Usage (from the repository root, after `lake build`):
    python3 -I scripts/frozen_abi.py [--compare docs/approved-statements.lean.txt]

For each frozen module `CantorSzemeredi.Frozen.<M>` and its export, prints the SHA-256 of the
fully elaborated declaration (`#print` with `pp.all` for a definition, `#check @` with `pp.all`
for a theorem, so a theorem's hash does not depend on its proof). The text is normalized
before hashing: whitespace is collapsed, and names of Lean's auxiliary proof constants
(`X._proof_N`) are replaced by `_proof_`.

With `--compare <approved>` (repeatable, one per approved statements file), it also
elaborates each approved file in its own namespace `CantorSzemeredi.Approved<k>` (so names it
declares resolve to its own copies) and reports whether each frozen declaration is identical
to its approved counterpart after the same normalization. Every frozen declaration must be
declared in exactly one approved file. The approved body is elaborated inside a `module` that
publicly imports only the frozen modules of its own declarations.
"""

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NS = "CantorSzemeredi"
LEAN_OPTS = ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3"]


def frozen_modules():
    folder = os.path.join(ROOT, NS, "Frozen")
    out = []
    for f in sorted(os.listdir(folder)):
        if not f.endswith(".lean"):
            continue
        text = open(os.path.join(folder, f), encoding="utf-8").read()
        m = re.search(r"(?m)^(?:noncomputable\s+)?(def|theorem)\s+([A-Za-z_][\w']*)", text)
        out.append((f"{NS}.Frozen." + f[:-5], m.group(2), m.group(1)))
    return out


def normalize(block):
    block = re.sub(r"\b[\w.']+\._proof_\d+\b", "_proof_", block)
    return " ".join(block.split())


def run_lean(text):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write(text)
        path = fh.name
    try:
        res = subprocess.run(["nice", "-n", "5", "lake", "env", "lean"] + LEAN_OPTS + [path],
                             cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)
    if res.returncode != 0 and "error" in res.stdout:
        sys.exit("lean failed:\n" + res.stdout[-4000:] + res.stderr[-2000:])
    return res.stdout


def blocks(output, prefixes):
    lines = output.split("\n")
    pat = "|".join(re.escape(p) for p in prefixes)
    start = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem)\s+(" + pat + r")\.([\w']+)"
                       r"|^@?(" + pat + r")\.([\w']+)(?:\.\{[^}]*\})? :")
    found, current, buf = {}, None, []
    for line in lines + ["/end"]:
        m = start.match(line)
        if m or line.startswith("/"):
            if current:
                found[current] = "\n".join(buf)
            current = (m.group(1) or m.group(3), m.group(2) or m.group(4)) if m else None
            buf = [line] if m else []
        elif current:
            buf.append(line)
    return found


def print_commands(entries):
    lines = ["set_option pp.all true"]
    for ns, name, kind in entries:
        lines.append((f"#print {ns}.{name}") if kind == "def" else (f"#check @{ns}.{name}"))
    return lines


def main():
    mods = frozen_modules()
    args, approved_files = sys.argv[1:], []
    while args:
        if args[0] != "--compare" or len(args) < 2:
            sys.exit("usage: frozen_abi.py [--compare <approved>]...")
        approved_files.append(args[1])
        args = args[2:]
    lines = ["import " + m for m, _, _ in mods] + [""]
    lines += print_commands([(NS, name, kind) for _, name, kind in mods])
    found = blocks(run_lean("\n".join(lines) + "\n"), [NS])
    result = {}
    for module, name, kind in mods:
        frozen = found.get((NS, name))
        if frozen is None:
            sys.exit(f"no output for {name}")
        digest = hashlib.sha256(normalize(frozen).encode("utf-8")).hexdigest()
        result[name] = {"module": module, "kind": kind, "abi_sha256": digest}
    ok, seen = True, set()
    for k, path in enumerate(approved_files, 1):
        ns = f"{NS}.Approved{k}"
        src = open(path, encoding="utf-8").read()
        body = src[src.index("open MeasureTheory"):]
        body = body.replace(f"namespace {NS}", f"namespace {ns}").replace(f"end {NS}", f"end {ns}")
        names = [m.group(1) for m in
                 re.finditer(r"(?m)^(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z_][\w']*)", body)]
        mine = [(m, n, kd) for m, n, kd in mods if n in names]
        if len(mine) != len(names) or seen & set(names):
            sys.exit(f"{path}: its declarations do not match the frozen modules one-to-one")
        seen |= set(names)
        lines = (["module", ""] + ["public import " + m for m, _, _ in mine]
                 + ["", "@[expose] public section", "", body, ""])
        lines += print_commands([(space, n, kd) for _, n, kd in mine for space in (ns, NS)])
        other = blocks(run_lean("\n".join(lines) + "\n"), [ns, NS])
        for _, name, _ in mine:
            text, frozen = other.get((ns, name), ""), other.get((NS, name), "")
            same = bool(text) and bool(frozen) and normalize(
                re.sub(r"\b" + re.escape(ns) + r"\b", NS, text)) == normalize(frozen)
            result[name]["matches_approved"] = same
            ok &= same
    if approved_files and seen != {n for _, n, _ in mods}:
        ok = False
        for _, name, _ in mods:
            result[name].setdefault("matches_approved", False)
    print(json.dumps(result, indent=2))
    if approved_files:
        print("ALL MATCH APPROVED" if ok else "MISMATCH WITH APPROVED", file=sys.stderr)
        return 0 if ok else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/python3 -I
"""Check that every declaration named in the blueprint exists in the Lean development.

Usage (from the repository root, after `lake build`):
    python3 -I scripts/check_blueprint_decls.py

This replaces `leanblueprint checkdecls` for this project. That tool imports every library of
the package, including `Challenge`, which by design re-declares `cantorSet`, `cantorEnum` and
`upperBanachDensity` from Mathlib alone; importing it together with the development is a name
clash and fails before any declaration is checked. This script imports only the
`CantorSzemeredi` library and elaborates `#check @Name` for every name in a `\\lean{...}` macro
of `blueprint/src/chapter/*.tex`.
"""

import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main() -> int:
    modules = sorted(
        str(p.relative_to(ROOT).with_suffix("")).replace(os.sep, ".")
        for p in (ROOT / "CantorSzemeredi").rglob("*.lean")
    )
    if not modules:
        print("check_blueprint_decls: no Lean modules found", file=sys.stderr)
        return 1

    names: list[str] = []
    for tex in sorted((ROOT / "blueprint" / "src" / "chapter").glob("*.tex")):
        for macro in re.finditer(r"\\lean\{([^}]*)\}", tex.read_text(encoding="utf-8")):
            for name in macro.group(1).split(","):
                name = name.strip()
                if name and name not in names:
                    names.append(name)
    if not names:
        print("check_blueprint_decls: no \\lean{...} names found", file=sys.stderr)
        return 1

    source = "\n".join([f"import {m}" for m in modules] + [""] + [f"#check @{n}" for n in names])
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write(source + "\n")
        path = fh.name
    try:
        res = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(path)

    missing = sorted(set(re.findall(r"unknown identifier '([^']+)'", res.stderr + res.stdout)))
    if missing or res.returncode != 0:
        print("BLUEPRINT DECLS FAILED:")
        for name in missing:
            print(f"- not found: {name}")
        if not missing:
            print(res.stderr.strip()[:2000])
        return 1
    print(f"BLUEPRINT DECLS OK ({len(names)} names in {len(modules)} modules)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

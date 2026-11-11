#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

if (( $# != 0 )); then
  printf 'Usage: %s\n' "$0" >&2
  exit 2
fi
if [[ $(uname -s) != Linux ]]; then
  printf 'error: sandboxed Comparator requires Linux and bubblewrap\n' >&2
  exit 1
fi
for required in bwrap lake lean python3 git; do
  if ! command -v "$required" >/dev/null 2>&1; then
    printf 'error: %s is required\n' "$required" >&2
    exit 1
  fi
done
bwrap_path=$(command -v bwrap)
if [[ "$bwrap_path" != /* ]]; then
  printf 'error: bwrap must resolve to an absolute executable path\n' >&2
  exit 1
fi
export COMPARATOR_BWRAP="$bwrap_path"

toolchain=$(tr -d '[:space:]' < lean-toolchain)
if [[ "$toolchain" != leanprover/lean4:v4.35.0 ]]; then
  printf 'error: unexpected lean-toolchain: %s\n' "$toolchain" >&2
  exit 1
fi
version=$(lean --version)
if [[ "$version" != 'Lean (version 4.35.0,'* ]]; then
  printf 'error: active Lean does not match %s: %s\n' "$toolchain" "$version" >&2
  exit 1
fi
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    printf 'error: toolchain %s does not bundle %s\n' "$toolchain" "$tool" >&2
    exit 1
  fi
done
if [[ ! -f Challenge.lean || ! -f Solution.lean || ! -f lake-manifest.json ]]; then
  printf 'error: Challenge.lean, Solution.lean, and lake-manifest.json are required\n' >&2
  exit 1
fi

python3 - <<'PY'
import os
from pathlib import Path

try:
    lines = Path('/proc/meminfo').read_text(encoding='ascii').splitlines()
    line = next(line for line in lines if line.startswith('MemTotal:'))
    _, amount, unit = line.split()
    if unit != 'kB':
        raise ValueError(f'unexpected MemTotal unit: {unit}')
    memory = int(amount) * 1024
    fs = os.statvfs('.')
    free = fs.f_bavail * fs.f_frsize
except (OSError, ValueError, StopIteration) as error:
    raise SystemExit(f'error: cannot check Linux resource capacity: {error}')
print(f'Memory: {memory / 1024**3:.2f} GiB; workspace free: {free / 1024**3:.2f} GiB')
if memory < 14 * 1024**3 or free < 20 * 1024**3:
    raise SystemExit('error: verification needs at least 14 GiB memory and 20 GiB free workspace')
PY

# The only `sorry`s are the three statement-only Challenge holes (comparator.json); the guard
# rejects any other `sorry`, `admit` or `axiom` and checks the frozen statements.
python3 -I scripts/check_frozen_anchors.py --root . --manifest docs/frozen-manifest.json
lake exe cache get
lake build
lake build Challenge Solution
python3 -I scripts/axiom_audit.py
python3 -I scripts/challenge_match.py

umask 077
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict) or "external_kernels" in config:
    raise SystemExit("error: comparator.json must be an object without external_kernels")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
lake comparator --config "$config"

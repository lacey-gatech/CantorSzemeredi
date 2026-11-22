# CantorSzemeredi: working conventions

Lean 4 / Mathlib formalization of *Szemerédi's Theorem Along Cantor Sets of Integers*
(arXiv:2602.15299v2). The paper source is `main.tex` and its section files; the plan is the
blueprint in `blueprint/src/`. `README.md` describes the layout and the checks; read
`docs/WORK_PLAN.md` for status and `docs/ERRATA-AND-DEVIATIONS.md` before changing any statement.

The three main theorems are proved with no `sorry`, on the three standard axioms. Keep it that
way: any change must leave the checks below passing.

## Exclusions

- Do not touch `backup-*` folders or `Report/`. They are working backups of the paper.
- Do not edit `main.tex` or the paper section files as part of formalization.

## Layout and namespaces

| Tree | Namespace | Rule |
|---|---|---|
| `CantorSzemeredi/Frozen/` | `CantorSzemeredi` | **Frozen.** Author-approved statements, one declaration per file, byte-hashed in `docs/frozen-manifest.json`. Only a proof of the form `by exact …` may be filled in. Never restate, rename or reformat these. |
| `CantorSzemeredi/Proof/` | `CantorSzemeredi.Proof` | The proofs: `Structure.lean`, `Dichotomy/`, `Assembly.lean`, `Bridge/`, `ErgodicDecomposition.lean`. |
| `CantorSzemeredi/Port/` | `CSZPort` | Ported from the earlier partial formalization at commit `d29e8f9`, unchanged in their mathematics. Each file names its origin in the header. Includes `Port/VdW/`, the van der Waerden chapter. |
| `Challenge.lean`, `Solution.lean` | `CantorSzemeredi.Palomar` | The Palomar challenge. The three `sorry` in `Challenge.lean` are deliberate and are the only ones allowed in the repository. |

## Lean conventions

- **Every file is a module.** The header is: copyright block, blank line, `module`, blank line,
  `public import …` lines, blank line, module docstring, then `@[expose] public section` and the
  `namespace`. `scripts/check_lean_modules.py` enforces this.
- `autoImplicit` and `relaxedAutoImplicit` are both off (`lakefile.toml`). Bind every variable.
- A new file is picked up automatically: the library globs `CantorSzemeredi.+`. There is no root
  import list to update.
- Sorry-free. Never introduce `sorry`, `admit` or `axiom` outside `Challenge.lean`.
- Blueprint `\lean{...}` names must match Lean names exactly, including the namespace
  (`CSZPort.…` for ported material, `CantorSzemeredi.Proof.…` for the proofs,
  `CantorSzemeredi.…` for the frozen statements).

## Building and checking

```bash
lake exe cache get
lake build
lake build Challenge Solution
python3 -I scripts/axiom_audit.py
python3 -I scripts/check_frozen_anchors.py --root . --manifest docs/frozen-manifest.json
python3 -I scripts/frozen_abi.py --compare docs/approved-statements.lean.txt
python3 -I scripts/check_lean_modules.py --root .
python3 -I scripts/challenge_match.py
```

- Run the whole suite before committing anything that touches Lean. `.github/workflows/lean-build.yml`
  runs it in CI.
- `check_frozen_anchors.py` scans the working directory, so a stray checkout of another copy of
  the project inside the repository will fail it.
- `check_lean_modules.py` reads the git index, so stage new files before running it.
- Per-file check: `lake env lean <file>`. After editing an upstream file run `lake build <module>`
  first, or `lake env lean` uses a stale `.olean`.
- Blueprint: `python3 -I scripts/check_blueprint_decls.py` verifies every `\lean{...}` name
  exists. Do not use `leanblueprint checkdecls`; it imports `Challenge` too and clashes with the
  frozen definitions, and it is deliberately not a dependency (Mathlib is the only one).

## Work order

- Follow the blueprint's document order. One blueprint item, or a small group that builds
  together, per step.
- When a step is done: build, run the checks, update `\lean`/`\leanok` in the chapter, update
  `docs/WORK_PLAN.md`, then commit.
- Never mark an item `\leanok` unless its declaration compiles with no `sorry`. If the Lean
  statement is stronger than or deviates from the blueprint's, say so in a formalization note on
  the item and record it in `docs/ERRATA-AND-DEVIATIONS.md`.

## Git

- Commit only when a step is complete and verified. Never commit partial or broken work.
- Commit messages end with the trailer:
  `Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>`
- Style: short descriptive subject with the blueprint label in parentheses, e.g.
  `Fatou lemma for uniform liminfs (lem:fatou-uniform)`.
- Do not amend or force-push. If history diverges from `origin`, stop and report it.

## Reporting

- Report results faithfully. If a build or check fails, show the output. If a step was skipped,
  say so. Do not call a step done before the build passes and the blueprint is updated.

## Lean/Mathlib pitfalls seen in this project

- `Measurable.indicator` has no named argument `E`; use `measurable_const.indicator hA`.
- `condExp_bot'` needs the goal in `⊥` form; use `change`.
- `integral_sub`/`integral_add` take integrability of the summands, not of the result.
- `MemLp.integrable` takes a `1 ≤ q` argument; `MemLp.coeFn_toLp` is a method.
- For nonnegative reals use `Finset.prod_le_one₀`; `Finset.prod_abs` is `Finset.abs_prod`.
- Renamed: `integral_finset_sum` → `integral_finsetSum`, `integrable_finset_sum` →
  `integrable_finsetSum`, `tendsto_finset_sum` → `tendsto_finsetSum`.
- `zorn_superset_nonempty` returns `Minimal`; membership is `hFmin.1`.
- Nested `SimpleFunc` induction: `induction s using SimpleFunc.induction with | const c hs | add hdisj ihf ihg`.
- `continuous_apply` takes the family as `A :=`.
- Watch `end` placement; a misplaced `end` closes a namespace early.

# CantorSzemeredi: working conventions

Lean 4 / Mathlib formalization of the Cantor–Szemerédi argument (paper source in `main.tex` and the section `.tex` files). The blueprint lives in `blueprint/src/chapter/*.tex`. The plan and status are in `docs/WORK_PLAN.md`; read it first when resuming.

## Exclusions

- Do not touch `backup-*` folders or `Report/`. The user excluded them from the task.
- Do not edit `main.tex` or the paper section files as part of formalization.

## Building and checking

- Full build: `lake build CantorSzemeredi`.
- Single file: `lake env lean <file>`.
- After editing an upstream file, run `lake build <module>` before checking dependents. `lake env lean` otherwise uses a stale `.olean`.
- Axiom check: put `#print axioms <name>` in a scratch file (outside the project) and run it. Only `propext`, `Classical.choice`, `Quot.sound` are acceptable.

## Lean conventions

- Sorry-free. Never mark an item `\leanok` unless its Lean declaration compiles with no `sorry` and the axioms are clean.
- Blueprint names must match Lean names exactly. The `\lean{...}` entries use full names, e.g. `CantorSzemeredi.MPS.wm_extension_tendsto`.
- Each new file gets an import line appended to `CantorSzemeredi.lean` after its build succeeds.
- Structure: `MPS`, `Factor`, `CantorData`, `CSZ`, etc. are in namespace `CantorSzemeredi` (or `CantorSzemeredi.MPS` for the weak-mixing and CSZ results). Check the namespace of the file you are in before naming anything.
- `Factor.CSZ` must be written `D.CSZ` in the place where the factor is named.

## Work order

- Follow the blueprint's document order (chapter by chapter, item by item). Do not skip ahead unless the user asks.
- One step at a time. Each step is one blueprint item or a small group of items that build together.
- When a step is done: build the module, check axioms, update the `\lean` and `\leanok` annotations in the `.tex` chapter, update `docs/WORK_PLAN.md`, then commit and push.

## Git

- Commit only when a step is complete and verified. Do not commit partial or broken work.
- Commit messages end with the trailer:
  `Co-Authored-By: Claude Haiku 5.5 <noreply@anthropic.com>`
- Use the existing commit style: a short imperative or descriptive subject with the blueprint label in parentheses when relevant, e.g. `Van der Waerden chapter formalized (vdw.tex)`.
- Do not amend or force-push. If history diverges from `origin/main`, stop and report it.

## Reporting

- Report results faithfully. If a build or axiom check fails, show the error. If something was skipped, say so.
- Do not present a step as done until the build passes and the blueprint is updated.

## Lessons from earlier work

- `Measurable.indicator` does not take a named argument `E`; use `measurable_const.indicator hA`.
- `condExp_bot'` needs the goal in `⊥` form. Use `change` to get it there.
- `integral_sub` and `integral_add` take the integrability of the summands, not of their difference.
- `MemLp.integrable` takes a `1 ≤ q` argument. `MemLp.coeFn_toLp` is a method.
- For nonnegative reals use `Finset.prod_le_one₀`, not `Finset.prod_le_one`. `Finset.prod_abs` is named `Finset.abs_prod`.
- Renamed Mathlib lemmas: `integral_finset_sum` → `integral_finsetSum`, `integrable_finset_sum` → `integrable_finsetSum`, `tendsto_finset_sum` → `tendsto_finsetSum`.
- `zorn_superset_nonempty` returns `Minimal`; membership is `hFmin.1`.
- Nested induction on `SimpleFunc` uses `induction s using SimpleFunc.induction with | const c hs | add hdisj ihf ihg`.
- `continuous_apply` takes the family as `A :=`.
- Watch `end` placement: a misplaced `end MPS` closes the namespace early.
- Never run `git reset --hard` or `git commit --amend` without first checking that the tree matches what is pushed.

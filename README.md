# Szemerédi's Theorem Along Cantor Sets of Integers — Lean formalization

A formalization in Lean 4 (with Mathlib) of the paper *Szemerédi's Theorem Along Cantor Sets
of Integers*, by Alex Burgin, Anastasios Fragkos, Michael T. Lacey, Dario Mena and
Maria Carmen Reguera.

The LaTeX source of the paper is in this repository: `main.tex`, with sections in
`Intro.tex`, `Prelim.tex`, `weakMixing.tex`, `vanDerWaerden.tex` and `compact.tex`.

## The result

Let `C = {0 = k₀ < k₁ < ⋯}` be an integer Cantor set in base `b`, with digit set `D ∋ 0`.
Then for every invertible measure preserving system `(X, 𝒜, m, T)`, every `A ∈ 𝒜` with
`m A > 0`, and every `ℓ ≥ 1`,

```
liminf_{N-M → ∞}  E_{M ≤ n < N}  m (A ∩ T^{-k_n} A ∩ ⋯ ∩ T^{-ℓ k_n} A)  >  0 .
```

The averages are uniform in the index `n`, so the set of good indices is *syndetic*.
By the Furstenberg correspondence principle, every set of integers of positive upper Banach
density has, for a syndetic set of indices `n`, a positive-density set of `(ℓ+1)`-term
progressions with step `k_n`.

## Blueprint

The blueprint is the plan of the formalization: it restates every definition and result of the
paper in a form intended for Lean, records the dependency graph, and flags the places where
Mathlib infrastructure is missing.

- Source: `blueprint/src/` (`content.tex` plus `chapter/*.tex`).
- Built web version and dependency graph: published to GitHub Pages by
  `.github/workflows/blueprint.yml` on every push to `main`.

Read `blueprint/src/chapter/overview.tex` first; it contains the staging plan.

### Building the blueprint locally

Requires Python 3, a TeX installation, and Graphviz.

```bash
python3 -m venv .venv && source .venv/bin/activate
pip install leanblueprint
leanblueprint pdf     # -> blueprint/print/print.pdf
leanblueprint web     # -> blueprint/web/index.html
leanblueprint checkdecls   # verifies every \lean{...} declaration exists in the Lean code
```

## Building the Lean code

```bash
lake exe cache get
lake build
```

## Repository layout

| Path | Contents |
| --- | --- |
| `main.tex`, `*.tex` | the paper |
| `blueprint/src/` | the blueprint sources |
| `CantorSzemeredi/` | the Lean development |
| `.github/workflows/` | Lean CI, blueprint build and Pages deployment |

The `backup-*/` directories and `Report/` are working backups of the paper and are not part of
the formalization; they are excluded from version control by `.gitignore`.

## Conventions in the blueprint

| Macro | Meaning |
| --- | --- |
| `\lean{Name}` | the Lean declaration(s) stating this item |
| `\leanok` | the Lean statement **and** proof are complete |
| `\uses{...}` | dependencies, used to draw the dependency graph |
| `\notready` | deliberately not yet attempted |

An item carrying `\lean` but no `\leanok` has a Lean *statement* only.

# Szemerédi's Theorem Along Cantor Sets of Integers, in Lean

A Lean 4 / Mathlib formalization of the main results of

> A. Burgin, A. Fragkos, M. T. Lacey, D. Mena, M. C. Reguera,
> *Szemerédi's Theorem Along Cantor Sets of Integers*, arXiv:2602.15299 (v2).

The LaTeX source of the paper is in this repository: `main.tex`, with sections in `Intro.tex`,
`Prelim.tex`, `weakMixing.tex`, `vanDerWaerden.tex` and `compact.tex`. The plan of the
formalization is the blueprint in `blueprint/src/`.

The three main results are proved with no `sorry` (the only `sorry`s are the three deliberate
holes in `Challenge.lean`). Each depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The results

Let `𝒞 = 𝒞_{b,D} = {0 = k₀ < k₁ < k₂ < ⋯}` be the integer Cantor set of numbers whose base-`b`
digits lie in `D ⊆ {0, …, b−1}`, with `b ≥ 3`, `2 ≤ |D| < b` and `0 ∈ D`.

**Theorem `t:CSZ`.** For every `ℓ ≥ 1`, every invertible measure preserving system
`(X, 𝒜, m, T)` and every non-negative `f ∈ L^∞(X)` that is not identically zero,
`liminf_{N−M→∞} 𝔼_{M≤n<N} ∫ ∏_{j=0}^{ℓ} f ∘ T^{j kₙ} dm > 0`.

```lean
theorem cantor_szemeredi
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T m m)
    (f : X → ℝ) (hf : MemLp f ⊤ m) (hf0 : 0 ≤ᵐ[m] f) (hfne : ¬ f =ᵐ[m] 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ M N : ℕ, M + L ≤ N →
      c ≤ (∑ n ∈ Finset.Ico M N,
            ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m) /
          ((N : ℝ) - M)
```

**Corollary `c:syndetic`.** Under the same assumptions, the set of indices `n` with
`∫ ∏_{j=0}^{ℓ} f ∘ T^{j kₙ} dm > 0` is syndetic.

```lean
theorem cantor_szemeredi_syndetic
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (T : X ≃ᵐ X) (hT : MeasurePreserving T m m)
    (f : X → ℝ) (hf : MemLp f ⊤ m) (hf0 : 0 ≤ᵐ[m] f) (hfne : ¬ f =ᵐ[m] 0) :
    ∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧
      0 < ∫ x, ∏ j ∈ Finset.range (ℓ + 1), f ((⇑T)^[j * cantorEnum b D n] x) ∂m
```

**Theorem `t:CSZ-Integers`.** For every `A ⊆ ℤ` of positive upper Banach density, the set of
indices `n ≥ 1` with `d*(A ∩ (A − kₙ) ∩ ⋯ ∩ (A − ℓkₙ)) > 0` is syndetic; for each such `n`, `A`
contains a non-degenerate `(ℓ+1)`-term progression with step `kₙ`.

```lean
theorem cantor_szemeredi_integers
    (b : ℕ) (D : Finset ℕ) (hb : 3 ≤ b) (hDb : D ⊆ Finset.range b)
    (hD2 : 2 ≤ D.card) (hDb' : D.card < b) (hD0 : 0 ∈ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : Set ℤ) (hA : 0 < upperBanachDensity A) :
    (∃ L : ℕ, ∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ n ≤ n₀ + L ∧ 1 ≤ n ∧
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A}) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < upperBanachDensity {a : ℤ | ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A} →
      0 < cantorEnum b D n ∧ ∃ a : ℤ, ∀ j ≤ ℓ, a + j * (cantorEnum b D n : ℤ) ∈ A
```

The definitions they use (`cantorSet`, `cantorEnum`, `upperBanachDensity`) are in
`CantorSzemeredi/Frozen/`. The statements, and these three definitions, were fixed and approved
by A. Fragkos, one of the authors, before any proof was written. Each lives alone in its own
file, and only the proof of a theorem was filled in afterwards;
`docs/approved-statements.lean.txt` is the approved text.

## Blueprint

The blueprint is the plan of the formalization: it restates every definition and result of the
paper in a form intended for Lean, records the dependency graph, and flags where Mathlib
infrastructure is missing. Read `blueprint/src/chapter/overview.tex` first.

Every `\lean{...}` name in the blueprint resolves to a declaration in this repository, and every
item is now marked `\leanok` except `lem:extensions`, which carries a statement only.

| Macro | Meaning |
| --- | --- |
| `\lean{Name}` | the Lean declaration(s) stating this item |
| `\leanok` | the Lean statement **and** proof are complete |
| `\uses{...}` | dependencies, used to draw the dependency graph |

Building it needs Python 3, a TeX installation and Graphviz:

```bash
python3 -m venv .venv && source .venv/bin/activate
pip install leanblueprint
leanblueprint pdf          # -> blueprint/print/print.pdf
leanblueprint web          # -> blueprint/web/index.html
python3 -I scripts/check_blueprint_decls.py   # checks every \lean{...} declaration exists
```

`leanblueprint checkdecls` is not used: it imports every library of the package, including
`Challenge`, which by design re-declares the three definitions from Mathlib alone, so the import
clashes before any name is checked. `scripts/check_blueprint_decls.py` does the same job against
the `CantorSzemeredi` library alone.

`.github/workflows/blueprint.yml` builds the PDF and the web version on every push and runs that
check. Publishing to
GitHub Pages is off until the repository has Pages enabled; set the repository variable
`PUBLISH_PAGES` to `true` to turn it on.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan), which installs the Lean version pinned
in `lean-toolchain` (v4.35.0). Mathlib is pinned to v4.35.0 in `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

The checks, run from the repository root after `lake build`:

```bash
python3 -I scripts/axiom_audit.py
python3 -I scripts/check_frozen_anchors.py --root . --manifest docs/frozen-manifest.json
python3 -I scripts/frozen_abi.py --compare docs/approved-statements.lean.txt
python3 -I scripts/check_lean_modules.py --root .
lake build Challenge Solution
python3 -I scripts/challenge_match.py
```

- `axiom_audit.py` prints the axioms of each main theorem and fails on anything beyond the three
  standard ones.
- `check_frozen_anchors.py` checks the frozen statement files against `docs/frozen-manifest.json`
  (byte hashes, one declaration per file, proofs of the form `by exact …`) and that the project has
  no `sorry`, `admit` or `axiom`.
- `frozen_abi.py` checks that each frozen declaration elaborates to exactly the approved statement.
- `check_lean_modules.py` checks that every Lean file is a module. It reads the git index, so
  run it in a git checkout.
- `challenge_match.py` checks, in separate Lean processes for `Challenge` and `Solution`, that the
  solution's theorems have exactly the challenge's statements and use the same definitions, and
  that they need only the three standard axioms.

## Palomar challenge

`Challenge.lean` states the three theorems with `sorry` in place of a proof, importing only
Mathlib and defining `cantorSet`, `cantorEnum` and `upperBanachDensity` verbatim. `Solution.lean`
proves the same statements from the development; `comparator.json` configures the comparison and
`formalization.yaml` describes the project. The sandboxed Comparator needs Linux and
`bubblewrap`: run `scripts/verify-comparator.sh` there, or the manually dispatched workflow
`palomar-preflight`. These three placeholders in `Challenge.lean` are the only `sorry`s in the
repository.

## Layout

| Path | Contents |
|---|---|
| `main.tex`, `Intro.tex`, `Prelim.tex`, `weakMixing.tex`, `vanDerWaerden.tex`, `compact.tex` | The paper |
| `blueprint/src/` | The blueprint: the plan of the formalization and its dependency graph |
| `CantorSzemeredi/Frozen/` | The three main theorems and the three definitions, one per file |
| `CantorSzemeredi/Proof/` | The proofs: `Structure.lean` (every system is CSZ, given the dichotomy), `Dichotomy/` (the Furstenberg–Zimmer dichotomy), `Assembly.lean` and `Bridge/` (from the general results to the frozen statements), `ErgodicDecomposition.lean` (the ergodic decomposition; proved, not needed by the main theorems) |
| `CantorSzemeredi/Port/` | Files ported from the authors' earlier partial formalization (see below), including `VdW/`, the Cantor-set van der Waerden theorem of §4 |
| `docs/` | Errata and deviations, the frozen-statement manifest, the approved statements, the work plan |
| `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml` | The Palomar challenge, its solution, the comparator configuration and the project metadata |
| `scripts/`, `.github/workflows/` | The checks above, the sandboxed Comparator run, and CI |

The `backup-*/` directories and `Report/` are working backups of the paper, not part of the
formalization; `.gitignore` excludes them.

## How the proof goes

The proof follows the paper. A system is CSZ if the uniform averages in Theorem `t:CSZ` (with
an extra dilation parameter) are positive. The CSZ property passes to weakly mixing and to
compact extensions, and to suprema of chains of factors, so by Zorn's lemma every system is CSZ
once every proper factor has a weakly mixing or compact extension. That is the
Furstenberg–Zimmer dichotomy, which the paper cites. Here it is proved for all measure
preserving systems on standard Borel spaces, without ergodicity. The general case reduces to a
symbolic model on `{0,1}^ℤ`, and Theorem `t:CSZ-Integers` follows by Furstenberg's
correspondence principle.

## Errata and deviations

[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md) lists 1 erratum and 2 deviations
for arXiv:2602.15299v2. None affects the main theorems.

- In v2 the definition of conditional compactness (§2.2) places `min_q` outside the `L^∞` norm.
  Read literally, this excludes standard compact extensions. The formalization uses Moreira's
  form, where the choice of `q` may depend on the point, which is also the form the paper's own
  proofs use. Corrected in v3: the display in `Prelim.tex` now has `min_q` inside the norm.
- The reduction to ergodic systems is replaced by a dichotomy for all standard Borel systems, so
  the ergodic decomposition is not needed (it is proved anyway).

## Earlier formalization and attribution

`CantorSzemeredi/Port/` contains files ported, unchanged in their mathematics, from the authors'
earlier partial formalization at `github.com/lacey-gatech/CantorSzemeredi` (commit `d29e8f9`).
Each file names its origin. The ergodic decomposition and the dichotomy, which that
formalization did not complete, are proved independently in `CantorSzemeredi/Proof/`.

`Port/` also carries the parts of that formalization which the main theorems do not need, and
which are kept because they are proved: `Port/VdW/` (the Cantor-set van der Waerden theorem of
§4), `Port/Dynamics/WMSystem.lean` (weakly mixing systems are CSZ),
`Port/Dynamics/WienerAtoms.lean` and `Port/Dynamics/CompactRoots.lean`.

## Acknowledgements

This formalization made use of [Scott Armstrong's Lean autoformalization skill
files](https://github.com/scottnarmstrong/LeanAutoformalizationSkills). They informed the working
conventions followed here: the author-approved frozen statements, the source-level dependency
graph behind the blueprint, the statement audits, and the Mathlib search and naming practice.

## License

Apache License 2.0; see `LICENSE`.

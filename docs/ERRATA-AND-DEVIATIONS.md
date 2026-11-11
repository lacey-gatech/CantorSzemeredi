# Errata and deviations

This record separates **errata** (places where the source, read literally, is wrong or
incomplete) from **deviations** (choices made in the formalization that differ from the
source's wording or proof without contradicting it). The source is A. Burgin, A. Fragkos,
M. T. Lacey, D. Mena, M. C. Reguera, *Szemerédi's Theorem Along Cantor Sets of Integers*,
arXiv:2602.15299v2. Printed theorem numbers differ between the PDF and HTML renderings of that
version, so locations are given by section and LaTeX label. Entries are counted, not
occurrences.

No erratum affects the main results. `CantorSzemeredi.cantor_szemeredi` (Theorem `t:CSZ`),
`CantorSzemeredi.cantor_szemeredi_syndetic` (Corollary `c:syndetic`) and
`CantorSzemeredi.cantor_szemeredi_integers` (Theorem `t:CSZ-Integers`) are proved as stated, and
depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

| Source | Errata | Deviations |
|---|---|---|
| arXiv:2602.15299v2 | 1 | 2 |

## arXiv:2602.15299v2

### Errata

1. **E1. §2.2, definition of conditionally compact functions (display after "conditionally
   compact if for every ε > 0").** Misplaced quantifier. The display reads
   `sup_{n∈ℤ} min_{1≤q≤r} ‖ ‖Tⁿf − g_q‖_{ℰ|𝒟} ‖_{L^∞(𝒟)} < ε`, so a single approximant `g_q` must
   serve almost every point at once. Read literally this is strictly stronger than the
   definition the paper says it follows (Moreira, Definition 8.2.8), and it excludes standard
   compact extensions. Example: over the circle with an irrational rotation `y ↦ y + β`, take
   the skew product `(y, z) ↦ (y + β, z + y)` on the 2-torus, `𝒟` the σ-algebra of the first
   coordinate, and `f(y, z) = e(z)`. Then `Tⁿf = e(αₙ(y)) f` with `αₙ(y) = ny + n(n−1)β/2`, so
   `‖Tⁿf − Tᵐf‖_{ℰ|𝒟}(y) = |e(αₙ(y)) − e(αₘ(y))|`, whose supremum over `y` is `2` for `n ≠ m`.
   If finitely many `g_q` satisfied the literal condition with `ε < 1`, two exponents `n ≠ m`
   would share a `q`, forcing that supremum below `2ε < 2`. So `f` is not conditionally compact
   in the literal sense, although the extension is isometric, hence compact in Moreira's sense.
   **Correction:** put `min_q` inside the norm, `‖ min_q ‖Tⁿf − g_q‖_{ℰ|𝒟} ‖_{L^∞(𝒟)} < ε`,
   so that the choice of `q` may depend on the point. This is the form the paper's own proof of
   Theorem `t:compactExtension` uses: display `e:net` asks, for almost every `x` and every `n`, that
   `min_ℓ ‖Tⁿf − f_ℓ‖_{ℰ|𝒟}(x) < ε/2`. It is also the form in which the dichotomy (Lemma `l:dichotomy`, cited from Moreira) is proved here.
   **Effect:** none on the stated theorems. The formalization uses the corrected form:
   `CondCompactZ` in [`CantorSzemeredi/Proof/Dichotomy/Defs.lean`](../CantorSzemeredi/Proof/Dichotomy/Defs.lean)
   and `CondCompact` in [`CantorSzemeredi/Port/Dynamics/Extensions.lean`](../CantorSzemeredi/Port/Dynamics/Extensions.lean).
   The counterexample is explained here, not proved in Lean.


### Deviations

1. **V1. §2.3, Proposition `p:reduction` and Theorem `t:ECSZ`: route of the reduction.** The paper
   proves the CSZ property for ergodic systems on compact metric spaces and reduces the general
   case to them through a symbolic model, the ergodic decomposition and Fatou's lemma. The
   formalization proves the dichotomy for every measure preserving system on a standard Borel
   space, without ergodicity (`dichotomy` in
   [`CantorSzemeredi/Proof/Dichotomy/Main.lean`](../CantorSzemeredi/Proof/Dichotomy/Main.lean)),
   so the structure theorem holds for all such systems (`csz_standardBorel`) and is applied
   directly to the symbolic model (`csz_all`, both in
   [`CantorSzemeredi/Proof/Structure.lean`](../CantorSzemeredi/Proof/Structure.lean)).
   Neither the ergodic decomposition nor Fatou's lemma is used. **Effect:** none on the stated
   theorems. The ergodic decomposition is proved anyway, as `exists_ergodic_decomposition` in
   [`CantorSzemeredi/Proof/ErgodicDecomposition.lean`](../CantorSzemeredi/Proof/ErgodicDecomposition.lean).

2. **V2. Introduction, Theorems `t:CSZ`, `t:CSZ-Integers`, Corollary `c:syndetic`: readings
   fixed in the formal statements.** "Invertible measure preserving system" is read as a bijection
   measurable in both directions (`T : X ≃ᵐ X`) preserving a probability measure; "not
   identically zero" for `f ∈ L^∞` as `¬ f =ᵐ[m] 0`; and
   `liminf_{N−M→∞} 𝔼_{M≤n<N} aₙ > 0` as "there are `c > 0` and `L` such that every average over
   an index interval `[M, N)` with `N − M ≥ L` is at least `c`", which is equivalent for the
   bounded non-negative averages involved. The upper Banach density is written as
   `inf_L sup_{N−M≥L}` of the interval densities. **Effect:** these are the statements proved;
   see [`CantorSzemeredi/Frozen/`](../CantorSzemeredi/Frozen/).

## Proof route compared with the paper

The weakly mixing and compact extension steps, the chain lemma, the Cantor-set exponential sums,
the van der Corput inequality, spectral measures and Furstenberg's correspondence principle follow
the paper, through the authors' earlier partial formalization (below). The paper cites the
dichotomy (Furstenberg; Moreira, Proposition 8.6.1) without proof; the formalization proves it
along the Furstenberg–Zimmer route: a function that is not conditionally weakly mixing gives an
atom of a spectral measure on the relatively independent self-joining, hence an eigenfunction of
`T × T` and a pair of fibrewise compact integral operators; the orbit of the resulting function is
fibrewise totally bounded; it is cut to a conditionally compact function by the sublevel sets of
an invariant orbit-complexity function; and the sets whose indicators are approximable by
conditionally compact functions form a compact extension
([`CantorSzemeredi/Proof/Dichotomy/`](../CantorSzemeredi/Proof/Dichotomy/)).

## Relation to the earlier partial formalization

The files in [`CantorSzemeredi/Port/`](../CantorSzemeredi/Port/) are ported, unchanged in their
mathematics, from the authors' earlier partial formalization
`github.com/lacey-gatech/CantorSzemeredi` (commit `d29e8f9`); each file names its origin. The
ergodic decomposition and the dichotomy, which that formalization did not complete, are proved
here independently, in [`CantorSzemeredi/Proof/`](../CantorSzemeredi/Proof/).

That formalization and this one have since been merged into a single repository: `Port/` now also
carries its van der Waerden chapter and the other results listed under "Not needed for the main
theorems" below, and the blueprint in `blueprint/src/` is its plan, with every `\lean{...}` name
pointing into this tree.

## Not needed for the main theorems

These results of the paper are not used by the three main theorems (the paper says so). They are
formalized anyway, among the ported files, and are kept because they are proved:

- the Cantor-set van der Waerden theorem of §4, in
  [`CantorSzemeredi/Port/VdW/`](../CantorSzemeredi/Port/VdW/) (`topological_vdW`, `vdW_infinite`,
  `vdW_finitary`);
- Theorem `t:compactSystem` and the corresponding statement for weakly mixing systems, in
  [`CantorSzemeredi/Port/Dynamics/CompactSystem.lean`](../CantorSzemeredi/Port/Dynamics/CompactSystem.lean)
  and [`CantorSzemeredi/Port/Dynamics/WMSystem.lean`](../CantorSzemeredi/Port/Dynamics/WMSystem.lean);
- Lemma `l:syndeticResidues` (`syndetic_dvd_enum` in
  [`CantorSzemeredi/Port/Cantor/Residues.lean`](../CantorSzemeredi/Port/Cantor/Residues.lean));
- the ergodic decomposition, in
  [`CantorSzemeredi/Proof/ErgodicDecomposition.lean`](../CantorSzemeredi/Proof/ErgodicDecomposition.lean)
  (see deviation V1).

## References used only as references

J. Moreira, *Ergodic theory — notes*, 2020 (lecture notes): Definition 8.2.8 and Proposition
8.6.1, cited by the paper for the dichotomy.
